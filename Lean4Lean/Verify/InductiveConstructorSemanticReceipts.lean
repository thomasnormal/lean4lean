import Lean4Lean.Verify.InductiveHeaderNativeMetadata

namespace Lean4Lean
open Lean hiding Environment Exception

theorem VEnv.addInductHeaders.sameConstructorLists
    (signatures : List.Forall₂ (fun complete header : VInductiveType =>
      complete.toVConstVal = header.toVConstVal) complete headers) (environment : VEnv) :
    environment.addInductHeaders complete = environment.addInductHeaders headers := by
  induction signatures generalizing environment with
  | nil => rfl
  | @cons complete header remaining headers signature tail induction =>
    have name := congrArg VConstVal.name signature
    have constant := congrArg VConstVal.toVConstant signature
    simp only [VEnv.addInductHeaders, name, constant, induction]

namespace AddInductive
open TypeChecker (MLCtx)

private theorem relatedMemberLeft {relation : leftType → rightType → Prop}
    (related : List.Forall₂ relation left right) (member : value ∈ left) :
    ∃ counterpart ∈ right, relation value counterpart := by
  induction related with
  | nil => simp at member
  | cons head tail induction =>
    rcases List.mem_cons.mp member with equal | member
    · subst value
      exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨counterpart, present, related⟩ := induction member
      exact ⟨counterpart, List.mem_cons_of_mem _ present, related⟩

private theorem relatedMemberRight {relation : leftType → rightType → Prop}
    (related : List.Forall₂ relation left right) (member : value ∈ right) :
    ∃ counterpart ∈ left, relation counterpart value := by
  induction related with
  | nil => simp at member
  | cons head tail induction =>
    rcases List.mem_cons.mp member with equal | member
    · subst value
      exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨counterpart, present, related⟩ := induction member
      exact ⟨counterpart, List.mem_cons_of_mem _ present, related⟩

theorem TypedHeaderReader.constructorTranslation
    (model : TypedHeaderReader base stats reader) (constructor : Constructor) (result : Expr)
    (guarded : reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok ())
    (checked : (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok result) :
    ∃ semantic, TrExprS model.checker.venv model.checker.lparams base.vlctx constructor.type semantic := by
  have sourceFree := checkNoMVarNoFVar.WF reader.env constructor.name constructor.type () guarded
  obtain ⟨semantic, translated⟩ := acceptedSourceTranslation model.checker reader model.aligned model.initialWF
    (sourceFree.mono fun _ impossible => impossible.elim) checked
  exact translated.weakFV'_inv model.checker.Ewf model.history.insertion
    (.refl model.checker.Ewf.ordered model.checker.Δwf)
    (model.checker.mlctx.noBV ▸ translated.closed) (sourceFree.mono fun _ impossible => impossible.elim)

private theorem constructorModels (model : TypedHeaderReader base stats reader) (empty : base = .nil)
    (constructors : List Constructor)
    (accepted : ∀ constructor ∈ constructors, ∃ result,
      reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
      (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok result) :
    ∃ models, List.Forall₂ (TrConstructor model.checker.venv model.checker.lparams) constructors models := by
  induction constructors with
  | nil => exact ⟨[], .nil⟩
  | cons constructor constructors induction =>
    obtain ⟨result, guarded, checked⟩ := accepted constructor (by simp)
    obtain ⟨semantic, translated⟩ := model.constructorTranslation constructor result guarded checked
    obtain ⟨models, remaining⟩ := induction (fun constructor member => accepted constructor (by simp [member]))
    refine ⟨{ name := constructor.name, uvars := model.checker.lparams.length, type := semantic } :: models,
      .cons ⟨rfl, rfl, ?_⟩ remaining⟩
    simpa only [empty, MLCtx.vlctx] using translated

private theorem completeHeaderModels (model : TypedHeaderReader base stats reader) (empty : base = .nil)
    (universes : model.checker.lparams = levels)
    (headers : List.Forall₂ (TrInductiveHeader environment levels) types incomplete)
    (accepted : ∀ type ∈ types, ∀ constructor ∈ type.ctors, ∃ result,
      reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
      (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok result) :
    ∃ complete, List.Forall₂ (TrInductiveType environment model.checker.venv levels) types complete ∧
      List.Forall₂ (fun complete header : VInductiveType => complete.toVConstVal = header.toVConstVal) complete incomplete := by
  induction headers with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons type header types incomplete translated remaining induction =>
    obtain ⟨constructors, constructorTranslations⟩ := constructorModels model empty type.ctors
      (accepted type (by simp))
    obtain ⟨complete, completed, signatures⟩ := induction
      (fun type member => accepted type (by simp [member]))
    refine ⟨{ header with ctors := constructors } :: complete,
      .cons ⟨translated.1, translated.2.1, translated.2.2, ?_⟩ completed, .cons rfl signatures⟩
    simpa only [universes] using constructorTranslations

theorem TypedHeaderReader.constructorDomains (model : TypedHeaderReader base stats reader)
    (types : Array InductiveType) (isUnsafe : Bool) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ finalReader finalIndex terminal finalTarget,
          ∃ trace : AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type
            finalReader finalIndex terminal,
          CheckedConstructorDomainReceipts model.checker.venv model.checker.lparams trace
            base.vlctx.toCtx base.vlctx.toCtx model.parameterModel.vlctx.toCtx finalTarget ∧
          model.checker.venv.IsDefEqCtx model.checker.lparams.length base.vlctx.toCtx
            model.parameterModel.vlctx.toCtx finalTarget ∧
          finalTarget.length = base.vlctx.toCtx.length + stats.params.size :=
  checkConstructors.domainReceiptsAtParameterModel types stats isUnsafe model.checker reader model.aligned
    model.initialWF model.history model.ambient model.parameterBase model.statsParams

theorem HeaderAxiomContinuation.shadowUniverses
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual) :
    stage.model.checker.lparams = root.lparams := by
  have shadow : stage.model.checker.lparams = reader.lparams :=
    congrArg TypeChecker.Context.lparams stage.model.aligned
  have before : stage.before.model.checker.lparams = reader.lparams :=
    congrArg TypeChecker.Context.lparams stage.before.model.aligned
  exact shadow.trans (before.symm.trans stage.before.sameUniverses)

structure ConstructorSemanticReceipts
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual) (isUnsafe : Bool) where
  declaration : VInductDecl
  translated : TrInductDecl root.venv stage.semantic root.lparams nparams types.toList declaration
  registered : root.venv.addInductHeaders declaration.types = some stage.semantic
  headersWF : declaration.HeadersWF root.venv
  domains : ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
    ∃ finalReader finalIndex terminal finalTarget,
      ∃ trace : AcceptedConstructorTrace stats isUnsafe parent { reader with env := stage.shadow }
        0 constructor.type finalReader finalIndex terminal,
      CheckedConstructorDomainReceipts stage.semantic root.lparams trace
        root.mlctx.vlctx.toCtx root.mlctx.vlctx.toCtx stage.model.parameterModel.vlctx.toCtx finalTarget ∧
      stage.semantic.IsDefEqCtx root.lparams.length root.mlctx.vlctx.toCtx
        stage.model.parameterModel.vlctx.toCtx finalTarget ∧
      finalTarget.length = root.mlctx.vlctx.toCtx.length + stats.params.size

theorem HeaderAxiomContinuation.shadowConstructorSemantics
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (isUnsafe : Bool)
    (accepted : checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok ()) :
    Nonempty (ConstructorSemanticReceipts stage isUnsafe) := by
  have traces := checkConstructors.acceptedTraces types stats isUnsafe { reader with env := stage.shadow } () accepted
  have checked : ∀ type ∈ types.toList, ∀ constructor ∈ type.ctors, ∃ result,
      stage.shadow.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
      (monadLift (TypeChecker.checkType constructor.type) : M Expr) { reader with env := stage.shadow } = .ok result := by
    intro type member constructor present
    obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    obtain ⟨result, finalReader, finalIndex, terminal, guarded, sourceChecked, trace⟩ :=
      traces parent bound constructor present
    exact ⟨result, guarded, sourceChecked⟩
  obtain ⟨complete, completed, signatures⟩ := completeHeaderModels stage.model empty stage.shadowUniverses
    stage.before.models checked
  have registered := (VEnv.addInductHeaders.sameConstructorLists signatures root.venv).trans stage.registered
  have headerTypes : ∀ header ∈ complete, header.toVConstant.WF root.venv := by
    intro header member
    obtain ⟨incomplete, member, signature⟩ := relatedMemberLeft signatures member
    have constant := congrArg VConstVal.toVConstant signature
    rw [constant]
    exact stage.before.typesWF incomplete member
  refine ⟨{
    declaration := { uvars := root.lparams.length, nparams, types := complete }
    translated := ⟨rfl, rfl, by simpa only [stage.semantic_eq] using completed⟩
    registered := registered
    headersWF := ?_
    domains := ?_ }⟩
  · intro header member
    obtain ⟨type, present, translated⟩ := relatedMemberRight completed member
    exact ⟨translated.2.1.symm, headerTypes header member⟩
  · simpa only [stage.semantic_eq, stage.shadowUniverses] using
      stage.model.constructorDomains types isUnsafe () accepted

theorem HeaderAxiomContinuation.constructorSemantics
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (isUnsafe : Bool) (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env) :
    (checkConstructors types stats isUnsafe { reader with env := actual }).WF fun _ =>
      Nonempty (ConstructorSemanticReceipts stage isUnsafe) := by
  intro result accepted
  obtain ⟨shadowAccepted, traces⟩ := stage.acceptedConstructorsFromInitial isUnsafe fresh constructors recursors result accepted
  exact stage.shadowConstructorSemantics empty isUnsafe shadowAccepted

theorem checkInductiveTypes.semanticConstructorAxiomContinuation
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
        NativeValueFrame actual final ∧ Nonempty (ConstructorSemanticReceipts stage isUnsafe) := by
  refine (checkInductiveTypes.nativeConstructorAxiomContinuation nparams types numNested isUnsafe next root reader
    aligned empty different constants definitions ordinary safetyBound constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    metadata, actualAccepted, shadowAccepted, traces⟩
  exact ⟨stats, current, actual, final, stage, retained,
    stage.shadowConstructorSemantics empty isUnsafe shadowAccepted⟩

theorem run.semanticConstructorAxiomContinuation (nparams : Nat) (types : List InductiveType)
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
        NativeValueFrame actual final ∧ Nonempty (ConstructorSemanticReceipts stage (reader.safety != .safe)) := by
  refine (run.nativeConstructorAxiomContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    metadata, actualAccepted, shadowAccepted, traces⟩
  exact ⟨stats, current, actual, final, stage, retained,
    stage.shadowConstructorSemantics empty (reader.safety != .safe) shadowAccepted⟩

end AddInductive
end Lean4Lean
