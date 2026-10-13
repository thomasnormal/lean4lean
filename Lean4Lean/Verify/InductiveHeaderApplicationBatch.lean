import Lean4Lean.Verify.InductiveRecursorSignatureInputs

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

private theorem originalLevelTranslation (universes : List Name) :
    (universes.map Level.param).mapM (VLevel.ofLevel universes) =
      some (universes.map fun name => VLevel.param (universes.idxOf name)) := by
  rw [List.mapM_eq_some]
  have relation : ∀ names : List Name, (∀ name ∈ names, name ∈ universes) →
      List.Forall₂ (fun level value => VLevel.ofLevel universes level = some value)
        (names.map Level.param) (names.map fun name => VLevel.param (universes.idxOf name)) := by
    intro names included
    induction names with
    | nil => exact .nil
    | cons name names induction =>
      refine .cons ?_ (induction fun other member => included other (List.mem_cons_of_mem name member))
      simp only [VLevel.ofLevel, List.idxOf_lt_length_iff.mpr (included name List.mem_cons_self), if_pos]
  exact relation universes fun _ member => member

private theorem originalLevelIdentity {universes : List Name} {level : Level} {semantic : VLevel}
    (translated : VLevel.ofLevel universes level = some semantic) :
    semantic.inst (universes.map fun name => VLevel.param (universes.idxOf name)) = semantic := by
  induction level generalizing semantic with
  | zero => cases translated; rfl
  | succ level induction =>
    obtain ⟨value, accepted, equality⟩ := Option.bind_eq_some_iff.mp translated
    injection equality with equality
    subst semantic
    simpa only [VLevel.inst] using congrArg VLevel.succ (induction accepted)
  | max first second firstInduction secondInduction | imax first second firstInduction secondInduction =>
    obtain ⟨left, leftAccepted, remaining⟩ := Option.bind_eq_some_iff.mp translated
    obtain ⟨right, rightAccepted, equality⟩ := Option.bind_eq_some_iff.mp remaining
    injection equality with equality
    subst semantic
    simp only [VLevel.inst, firstInduction leftAccepted, secondInduction rightAccepted]
  | param name =>
    simp only [VLevel.ofLevel] at translated
    split at translated
    · rename_i bound
      cases translated
      simp [VLevel.inst, List.getElem?_eq_getElem bound, List.getElem_idxOf bound]
    · cases translated
  | mvar => cases translated

private theorem originalLevelListIdentity {universes : List Name} {levels : List Level} {values : List VLevel}
    (translated : levels.mapM (VLevel.ofLevel universes) = some values) :
    values.map (VLevel.inst (universes.map fun name => VLevel.param (universes.idxOf name))) = values := by
  apply List.map_id'''
  intro value member
  obtain ⟨level, _, accepted⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp translated) value member
  exact originalLevelIdentity accepted

private theorem originalSourceInstantiation
    {environment : VEnv} {universes : List Name} {virtual : VLCtx} {source : Expr} {semantic : VExpr}
    (translated : TrExprS environment universes virtual source semantic) :
    TrExprS environment universes
      (virtual.instL (universes.map fun name => VLevel.param (universes.idxOf name))) source
      (semantic.instL (universes.map fun name => VLevel.param (universes.idxOf name))) := by
  have mapping := originalLevelTranslation universes
  have levelsWF := VLevel.WF.of_mapM_ofLevel mapping
  have count : (universes.map fun name => VLevel.param (universes.idxOf name)).length = universes.length :=
    List.length_map ..
  induction translated with
  | bvar lookup => exact .bvar (VLCtx.find?_instL lookup)
  | fvar lookup => exact .fvar (VLCtx.find?_instL lookup)
  | sort mapped => simpa only [VExpr.instL, originalLevelIdentity mapped] using TrExprS.sort mapped
  | const lookup mapped arity =>
    simpa only [VExpr.instL, originalLevelListIdentity mapped] using TrExprS.const lookup mapped arity
  | app functionTyped argumentTyped _ _ functionInduction argumentInduction =>
    exact .app (VLCtx.instL_toCtx _ ▸ (count.symm ▸ functionTyped).instL levelsWF)
      (VLCtx.instL_toCtx _ ▸ (count.symm ▸ argumentTyped).instL levelsWF) functionInduction argumentInduction
  | lam domainTyped _ _ domainInduction bodyInduction =>
    exact .lam (VLCtx.instL_toCtx _ ▸ (count.symm ▸ domainTyped).instL levelsWF) domainInduction bodyInduction
  | forallE domainTyped bodyTyped _ _ domainInduction bodyInduction =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ (count.symm ▸ domainTyped).instL levelsWF)
      (VLCtx.instL_toCtx _ ▸ (count.symm ▸ bodyTyped).instL levelsWF) domainInduction bodyInduction
  | letE valueTyped _ _ _ domainInduction valueInduction bodyInduction =>
    exact .letE (VLCtx.instL_toCtx _ ▸ (count.symm ▸ valueTyped).instL levelsWF)
      domainInduction valueInduction bodyInduction
  | lit present _ induction => exact .lit present induction
  | mdata _ induction => exact .mdata induction
  | proj _ projection induction => exact .proj induction (VLCtx.instL_toCtx _ ▸ projection.instL levelsWF)

private theorem originalHeaderConstantInput
    {environment : VEnv} {universes : List Name} {source : Expr}
    (environmentWF : environment.WF) (lookup : environment.constants name = some constant)
    (translated : TrExprS environment universes [] source constant.type)
    (universeCount : universes.length = constant.uvars)
    (model : MLCtx) (modelWF : model.WF environment universes) :
    Nonempty (RecursorConstantInput environment universes model.vlctx name
      (universes.map Level.param) source) := by
  have mapped := originalLevelTranslation universes
  have levelsWF := VLevel.WF.of_mapM_ofLevel mapped
  have sourceTranslated := originalSourceInstantiation translated
  have sourceTranslated : TrExprS environment universes [] source
      (constant.type.instL (universes.map fun name => VLevel.param (universes.idxOf name))) := sourceTranslated
  have sourceTranslated : TrExpr environment universes [] source
      (constant.type.instL (universes.map fun name => VLevel.param (universes.idxOf name))) :=
    sourceTranslated.trExpr environmentWF.ordered
      (show VLCtx.WF environment universes.length [] from trivial)
  have weakening := VLCtx.FVLift.from_nil model.noBV
  obtain ⟨semanticType, strictTranslated, equality⟩ := sourceTranslated.weakFV environmentWF weakening modelWF.tr.wf
  have arity : (universes.map fun name => VLevel.param (universes.idxOf name)).length = constant.uvars :=
    (List.length_map ..).trans universeCount
  have typed : environment.HasType universes.length []
      (.const name (universes.map fun name => VLevel.param (universes.idxOf name)))
      (constant.type.instL (universes.map fun name => VLevel.param (universes.idxOf name))) :=
    .const lookup levelsWF arity
  have typed := (typed.weakN environmentWF.ordered weakening.toCtx).defeqU_r
    environmentWF modelWF.tr.wf.toCtx equality.symm
  exact ⟨{
    semanticType, semanticValue := _, sourceTranslated := strictTranslated,
    sourceTypehood := typed.isType environmentWF.ordered modelWF.tr.wf.toCtx,
    valueTranslated := .const lookup mapped ((List.length_map ..).trans universeCount),
    valueTyped := by simpa only [VExpr.liftN] using typed }⟩

theorem ConstructorConstantRegistration.parentParameterInput
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (parent : Nat) (bound : parent < types.size) :
    Nonempty (HeaderParameterApplicationInput registration.semantic root.lparams
      stage.before.model.checker.mlctx stats types[parent].type) := by
  obtain ⟨input⟩ := stage.before.parameterApplications parent bound
  exact ⟨input.monoEnv ((VEnv.addInductHeaders.le stage.registered).trans registration.increase)⟩

theorem ConstructorConstantRegistration.parentParameterModelWF
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    stage.before.model.checker.mlctx.WF registration.semantic root.lparams := by
  have initial : stage.before.model.checker.mlctx.WF root.venv root.lparams := by
    simpa only [stage.before.sameEnv, stage.before.sameUniverses] using
      stage.before.model.checker.mlctx_wf
  exact initial.monoEnv ((VEnv.addInductHeaders.le stage.registered).trans registration.increase)

def HeaderParameterApplicationBatch (environment : VEnv) (universes : List Name)
    (model : MLCtx) (stats : InductiveStats) (types : Array InductiveType) : Prop :=
  ∀ parent, ∀ bound : parent < types.size,
    ∃ input : HeaderParameterApplicationInput environment universes model stats types[parent].type,
      ∃ value, TrExprS environment universes model.vlctx (mkAppN stats.indConsts[parent]! stats.params) value ∧
        environment.HasType universes.length model.vlctx.toCtx value input.result

theorem ConstructorConstantRegistration.parentParameterApplications
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    HeaderParameterApplicationBatch registration.semantic root.lparams
      stage.before.model.checker.mlctx stats types := by
  intro parent bound
  obtain ⟨parameters⟩ := registration.parentParameterInput parent bound
  have levels := stage.before.levels (by omega)
  obtain ⟨header, member, translated⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l stage.before.models types[parent]
    (Array.mem_toList_iff.mpr (Array.getElem_mem bound))
  have increase := (VEnv.addInductHeaders.le stage.registered).trans registration.increase
  have lookup := registration.increase.constants (VEnv.addInductHeaders.constants stage.registered member)
  obtain ⟨head⟩ := originalHeaderConstantInput registration.semanticWF lookup
    (translated.2.2.mono increase) translated.2.1 _ registration.parentParameterModelWF
  have head : RecursorConstantInput registration.semantic root.lparams
      stage.before.model.checker.mlctx.vlctx types[parent].name stats.levels types[parent].type := by
    simpa only [translated.1, levels] using head
  obtain ⟨value, translated, typed⟩ := head.applyHeaderParameters parameters registration.semanticWF
    registration.parentParameterModelWF
  exact ⟨parameters, value, by simpa only [stage.before.heads parent bound] using translated, typed⟩

theorem checkInductiveTypes.headerParameterApplicationContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (ordinary : reader.allowPrimitive = false)
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
          ∃ registration : ConstructorConstantRegistration receipts final,
            HeaderParameterApplicationBatch registration.semantic root.lparams
              stage.before.model.checker.mlctx stats types := by
  refine (checkInductiveTypes.constructorConstantContinuation nparams types numNested isUnsafe next
    root reader aligned empty different constants definitions ordinary safetyBound constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, ⟨registration⟩⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration, registration.parentParameterApplications⟩

theorem run.headerParameterApplicationContinuation (nparams : Nat) (types : List InductiveType)
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
          ∃ registration : ConstructorConstantRegistration receipts final,
            HeaderParameterApplicationBatch registration.semantic root.lparams
              stage.before.model.checker.mlctx stats types.toArray := by
  refine (run.constructorConstantContinuation nparams types numNested root reader aligned empty
    different constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, ⟨registration⟩⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration, registration.parentParameterApplications⟩

end Lean4Lean.AddInductive
