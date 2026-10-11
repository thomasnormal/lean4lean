import Lean4Lean.Verify.InductiveConstructorCheckerModels

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

private theorem appendRelated {relation : sourceType → targetType → Prop}
    (first : List.Forall₂ relation sourceFirst targetFirst)
    (second : List.Forall₂ relation sourceSecond targetSecond) :
    List.Forall₂ relation (sourceFirst ++ sourceSecond) (targetFirst ++ targetSecond) := by
  induction first with
  | nil => exact second
  | cons head tail induction => exact .cons head induction

private theorem flattenConstructorModels
    (models : List.Forall₂ (TrInductiveType headerEnvironment constructorEnvironment universes) types headers) :
    List.Forall₂ (TrConstructor constructorEnvironment universes)
      (types.flatMap (fun type => type.ctors)) (headers.flatMap (fun header => header.ctors)) := by
  induction models with
  | nil => exact .nil
  | cons head tail induction => exact appendRelated head.2.2.2 induction

private theorem relatedConstructorNames
    (models : List.Forall₂ (TrConstructor environment universes) sources targets) :
    targets.map VConstVal.name = sources.map Constructor.name := by
  induction models with
  | nil => rfl
  | cons head tail induction => simp only [List.map_cons, head.1, induction]

theorem TrInductDecl.constructorModels
    (translated : TrInductDecl headerEnvironment constructorEnvironment universes nparams types declaration) :
    List.Forall₂ (TrConstructor constructorEnvironment universes)
      (types.flatMap (fun type => type.ctors)) declaration.constructorHeaders :=
  flattenConstructorModels translated.2.2

theorem TrInductDecl.constructorNames
    (translated : TrInductDecl headerEnvironment constructorEnvironment universes nparams types declaration) :
    declaration.constructorHeaders.map VConstVal.name =
      types.flatMap (fun type => type.ctors.map Constructor.name) := by
  simpa only [List.map_flatMap] using relatedConstructorNames translated.constructorModels

namespace AddInductive
open private relatedMemberLeft relatedMemberRight
  from Lean4Lean.Verify.InductiveConstructorSemanticReceipts

theorem TypedHeaderReader.paramsAreFVars (model : TypedHeaderReader base stats reader) :
    stats.ParamsAreFVars := by
  intro parameter member
  have listed := Array.mem_toList_iff.mpr member
  rw [model.statsParams, List.toList_toArray] at listed
  obtain ⟨identifier, present, rfl⟩ := List.mem_map.mp listed
  rfl

theorem TypedHeaderReader.paramsNodup (model : TypedHeaderReader base stats reader) :
    stats.params.toList.Nodup := by
  rw [model.statsParams, List.toList_toArray]
  apply List.pairwise_map.mpr
  exact (model.parameters.nodup model.parameterWF).imp fun different equal =>
    different (Expr.fvar.inj equal)

theorem ConstructorSemanticReceipts.flatTypesWF
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) :
    ∀ constructor ∈ receipts.declaration.constructorHeaders, constructor.toVConstant.WF stage.semantic := by
  intro constructor member
  obtain ⟨header, present, member⟩ := List.mem_flatMap.mp member
  exact receipts.constructorTypesWF header present constructor member

theorem ConstructorSemanticReceipts.constantsFresh
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) (fresh : ConstructorsFresh stage.shadow types) :
    ∀ constructor ∈ receipts.declaration.constructorHeaders, stage.semantic.constants constructor.name = none := by
  have nativeEnvironment : stage.model.checker.env = stage.shadow :=
    congrArg TypeChecker.Context.env stage.model.aligned
  have history : TrEnv stage.model.checker.safety stage.shadow stage.semantic := by
    simpa only [nativeEnvironment, stage.semantic_eq] using stage.model.checker.trenv
  intro constructor member
  obtain ⟨source, sourceMember, translated⟩ := relatedMemberRight receipts.translated.constructorModels member
  obtain ⟨type, typeMember, sourceMember⟩ := List.mem_flatMap.mp sourceMember
  have missing := fresh type (Array.mem_toList_iff.mp typeMember) source sourceMember
  rw [translated.1] at missing
  cases found : stage.semantic.constants constructor.name with
  | none => rfl
  | some constant =>
    obtain ⟨information, native, safety⟩ := history.find?_iff.mpr ⟨constant, found⟩
    rw [missing] at native
    cases native

structure ConstructorConstantRegistration
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) (final : Kernel.Environment) where
  semantic : VEnv
  registered : stage.semantic.addConstructorHeaders receipts.declaration.constructorHeaders = some semantic
  semanticWF : semantic.WF
  nativeWF : final.constants.WF
  values : NativeValueFrame actual final
  metadata : stats.ConstructorMetadata root.lparams types isUnsafe final
  safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe

theorem ConstructorConstantRegistration.increase
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) : stage.semantic ≤ registration.semantic :=
  VEnv.addConstructorHeaders.le registration.registered

theorem ConstructorConstantRegistration.definitions
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    registration.semantic.defeqs = stage.semantic.defeqs :=
  VEnv.addConstructorHeaders.defeqs_eq registration.registered

theorem ConstructorConstantRegistration.constants
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (member : constructor ∈ receipts.declaration.constructorHeaders) :
    registration.semantic.constants constructor.name = some constructor.toVConstant :=
  VEnv.addConstructorHeaders.constants registration.registered member

theorem ConstructorSemanticReceipts.registeredConstants
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (checked : checkConstructors types stats isUnsafe { reader with env := actual } = .ok ())
    (accepted : declareConstructors stats types isUnsafe { reader with env := actual } = .ok final) :
    Nonempty (ConstructorConstantRegistration receipts final) := by
  obtain ⟨values, fresh, distinct⟩ := declareConstructors.freshness stats types isUnsafe
    { reader with env := actual } stage.actualWF final accepted
  have semanticFresh := receipts.constantsFresh (fresh.inShadow stage.agreement)
  have semanticDistinct : (receipts.declaration.constructorHeaders.map VConstVal.name).Nodup := by
    simpa only [receipts.translated.constructorNames, ConstructorNames] using distinct
  obtain ⟨semantic, registered⟩ := VEnv.addConstructorHeaders.exists semanticFresh semanticDistinct
  have headerWF := VEnv.addInductHeaders.wf root.Ewf
    (fun header member => (receipts.headersWF header member).2) receipts.registered
  have arities := checkConstructors.arity types stats isUnsafe { reader with env := actual }
    stage.before.model.paramsAreFVars stage.before.model.paramsNodup () checked
  obtain ⟨nativeWF, preserved, metadata⟩ := declareConstructors.metadata stats types isUnsafe
    { reader with env := actual } stage.actualWF arities final accepted
  have universes : reader.lparams = root.lparams :=
    (congrArg TypeChecker.Context.lparams stage.before.model.aligned).symm.trans stage.before.sameUniverses
  exact ⟨{
    semantic, registered,
    semanticWF := VEnv.addConstructorHeaders.wf headerWF receipts.flatTypesWF registered,
    nativeWF, values, metadata := by simpa only [universes] using metadata, safetyBound }⟩

theorem ConstructorConstantRegistration.constructorConstant
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source) :
    ∃ constructor ∈ receipts.declaration.constructorHeaders,
      final.find? source.name = some (.ctorInfo
        (declareConstructors.metadataVal stats root.lparams isUnsafe type.name index source)) ∧
      registration.semantic.constants source.name = some constructor.toVConstant ∧
      TrConstant root.safety registration.semantic
        (.ctorInfo (declareConstructors.metadataVal stats root.lparams isUnsafe type.name index source))
        constructor.toVConstant := by
  have sourceMember : source ∈ types.toList.flatMap (fun type => type.ctors) :=
    List.mem_flatMap.mpr ⟨type, Array.mem_toList_iff.mpr typeMember, List.mem_of_getElem? sourceGet⟩
  obtain ⟨constructor, member, translated⟩ := relatedMemberLeft receipts.translated.constructorModels sourceMember
  refine ⟨constructor, member, (registration.metadata type typeMember index source sourceGet).1, ?_, ?_⟩
  · simpa only [translated.1] using registration.constants member
  · refine ⟨?_, translated.2.1, translated.2.2.mono registration.increase⟩
    simpa only [declareConstructors.metadataVal, ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial] using registration.safetyBound

theorem checkInductiveTypes.constructorConstantContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          Nonempty (ConstructorConstantRegistration receipts final) := by
  apply checkInductiveTypes.withHeaderAxiomContinuation nparams types numNested isUnsafe
    (next := fun stats actual => do
      checkConstructors types stats isUnsafe
      let final ← declareConstructors stats types isUnsafe
      withEnv final (next stats actual))
    (post := fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          Nonempty (ConstructorConstantRegistration receipts final))
    root reader aligned empty different constants definitions ordinary safetyBound
  intro stats current actual stage
  change ((checkConstructors types stats isUnsafe >>= fun _ => _) { current with env := actual }).WF _
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro checked checkedCall
  cases checked
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro final registeredCall
  obtain ⟨values, fresh, distinct⟩ := declareConstructors.freshness stats types isUnsafe
    { current with env := actual } stage.actualWF final registeredCall
  obtain ⟨shadowCall, traces⟩ := stage.acceptedConstructorsFromInitial isUnsafe fresh constructors recursors () checkedCall
  obtain ⟨receipts⟩ := stage.shadowConstructorSemantics empty isUnsafe shadowCall
  have registration := receipts.registeredConstants safetyBound checkedCall registeredCall
  intro result accepted
  exact ⟨stats, current, actual, final, stage, receipts, registration⟩

theorem run.constructorConstantContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          Nonempty (ConstructorConstantRegistration receipts final) := by
  have sameSafety : root.safety = reader.safety := congrArg TypeChecker.Context.safety aligned
  have safetyBound : root.safety ≤ if reader.safety != .safe then .unsafe else .safe := by
    rw [← sameSafety]
    cases mode : root.safety with
    | safe => decide
    | «unsafe» => decide
    | «partial» => exact False.elim (ordinarySafety mode)
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.constructorConstantContinuation nparams types.toArray numNested
    (reader.safety != .safe) _ root reader aligned empty different constants definitions ordinary safetyBound
    constructors recursors

end AddInductive
end Lean4Lean
