import Lean4Lean.Verify.InductiveHeaderApplicationBatch

namespace Lean4Lean
open Lean hiding Environment Exception

structure UniverseNameExtension (original target : List Name) : Prop where
  included : ∀ name ∈ original, name ∈ target

def UniverseNameExtension.levels (original target : List Name) : List VLevel :=
  original.map fun name => .param (target.idxOf name)

theorem UniverseNameExtension.levelsLength : (levels original target).length = original.length :=
  List.length_map ..

theorem UniverseNameExtension.levelsWF (extension : UniverseNameExtension original target) :
    ∀ level ∈ levels original target, level.WF target.length := by
  intro level member
  change level ∈ original.map (fun name => VLevel.param (target.idxOf name)) at member
  obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
  exact List.idxOf_lt_length_iff.mpr (extension.included name present)

theorem UniverseNameExtension.levelTranslation (extension : UniverseNameExtension original target)
    {level : Level} {semantic : VLevel} (translated : VLevel.ofLevel original level = some semantic) :
    VLevel.ofLevel target level = some (semantic.inst (levels original target)) := by
  induction level generalizing semantic with
  | zero => cases translated; rfl
  | succ level induction =>
    obtain ⟨value, accepted, equality⟩ := Option.bind_eq_some_iff.mp translated
    injection equality with equality
    subst semantic
    simp [VLevel.ofLevel, VLevel.inst, induction accepted]
  | max first second firstInduction secondInduction | imax first second firstInduction secondInduction =>
    obtain ⟨left, leftAccepted, remaining⟩ := Option.bind_eq_some_iff.mp translated
    obtain ⟨right, rightAccepted, equality⟩ := Option.bind_eq_some_iff.mp remaining
    injection equality with equality
    subst semantic
    simp [VLevel.ofLevel, VLevel.inst, firstInduction leftAccepted, secondInduction rightAccepted]
  | param name =>
    simp only [VLevel.ofLevel] at translated
    split at translated
    · rename_i bound
      cases translated
      have present := extension.included name (List.idxOf_lt_length_iff.mp bound)
      simp [VLevel.ofLevel, List.idxOf_lt_length_iff.mpr present, VLevel.inst, levels,
        List.getElem?_eq_getElem bound, List.getElem_idxOf bound]
    · cases translated
  | mvar => cases translated

theorem UniverseNameExtension.levelListTranslation (extension : UniverseNameExtension original target)
    {native : List Level} {semantic : List VLevel}
    (translated : native.mapM (VLevel.ofLevel original) = some semantic) :
    native.mapM (VLevel.ofLevel target) = some (semantic.map (VLevel.inst (levels original target))) := by
  rw [List.mapM_eq_some] at translated ⊢
  induction translated with
  | nil => exact .nil
  | cons accepted _ induction => exact .cons (extension.levelTranslation accepted) induction

theorem TrExprS.reindexUniverses {environment : VEnv} {original target : List Name}
    {virtual : VLCtx} {source : Expr} {semantic : VExpr}
    (translated : TrExprS environment original virtual source semantic)
    (extension : UniverseNameExtension original target) :
    TrExprS environment target (virtual.instL (UniverseNameExtension.levels original target)) source
      (semantic.instL (UniverseNameExtension.levels original target)) := by
  have levelsWF := extension.levelsWF
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  induction translated with
  | bvar lookup => exact .bvar (VLCtx.find?_instL lookup)
  | fvar lookup => exact .fvar (VLCtx.find?_instL lookup)
  | sort mapped => exact .sort (extension.levelTranslation mapped)
  | const lookup mapped arity => exact .const lookup (extension.levelListTranslation mapped) arity
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

theorem TrExpr.reindexUniverses
    (translated : TrExpr environment original virtual source semantic)
    (extension : UniverseNameExtension original target) :
    TrExpr environment target (virtual.instL (UniverseNameExtension.levels original target)) source
      (semantic.instL (UniverseNameExtension.levels original target)) := by
  obtain ⟨strict, translated, equality⟩ := translated
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  exact ⟨strict.instL (UniverseNameExtension.levels original target), translated.reindexUniverses extension,
    by simpa only [VLCtx.instL_toCtx] using (count.symm ▸ equality).instL extension.levelsWF⟩

namespace TypeChecker

def MLCtx.reindexLevels (levels : List VLevel) : MLCtx → MLCtx
  | .nil => .nil
  | .vlam identifier name domain semantic binder model =>
    .vlam identifier name domain (semantic.instL levels) binder (model.reindexLevels levels)
  | .vlet identifier name domain value semantic semanticValue model =>
    .vlet identifier name domain value (semantic.instL levels) (semanticValue.instL levels)
      (model.reindexLevels levels)

theorem MLCtx.reindexLevels.lctx (model : MLCtx) : (model.reindexLevels levels).lctx = model.lctx := by
  induction model <;> simp_all [MLCtx.reindexLevels, MLCtx.lctx]

theorem MLCtx.reindexLevels.vlctx (model : MLCtx) :
    (model.reindexLevels levels).vlctx = model.vlctx.instL levels := by
  induction model <;> simp_all [MLCtx.reindexLevels, VLCtx.instL, VLocalDecl.instL]

theorem MLCtx.WF.reindexUniverses {model : MLCtx}
    (wellFormed : model.WF environment original) (extension : UniverseNameExtension original target) :
    (model.reindexLevels (UniverseNameExtension.levels original target)).WF environment target := by
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  induction model with
  | nil => trivial
  | vlam identifier name domain semantic binder model induction =>
    obtain ⟨base, fresh, translated, typed⟩ := wellFormed
    exact ⟨induction base, by simpa only [MLCtx.reindexLevels.lctx] using fresh,
      by simpa only [MLCtx.reindexLevels.vlctx] using translated.reindexUniverses extension,
      by simpa only [MLCtx.reindexLevels.vlctx, VLCtx.instL_toCtx] using (count.symm ▸ typed).instL extension.levelsWF⟩
  | vlet identifier name domain value semantic semanticValue model induction =>
    obtain ⟨base, fresh, translated, valueTranslated, typed⟩ := wellFormed
    exact ⟨induction base, by simpa only [MLCtx.reindexLevels.lctx] using fresh,
      by simpa only [MLCtx.reindexLevels.vlctx] using translated.reindexUniverses extension,
      by simpa only [MLCtx.reindexLevels.vlctx] using valueTranslated.reindexUniverses extension,
      by simpa only [MLCtx.reindexLevels.vlctx, VLCtx.instL_toCtx] using (count.symm ▸ typed).instL extension.levelsWF⟩

def VContext.reindexUniverses (checker : VContext) (extension : UniverseNameExtension checker.lparams target) :
    VContext := {
  checker with
  lparams := target
  mlctx := checker.mlctx.reindexLevels (UniverseNameExtension.levels checker.lparams target)
  mlctx_wf := checker.mlctx_wf.reindexUniverses extension
  lctx_eq := (MLCtx.reindexLevels.lctx _).trans checker.lctx_eq }

theorem VContext.reindexUniverses.context (checker : VContext)
    (extension : UniverseNameExtension checker.lparams target) :
    (checker.reindexUniverses extension).toContext = { checker.toContext with lparams := target } := rfl

theorem VState.WF.reindexReset {checker : VContext}
    (wellFormed : ({} : VState).WF checker) (extension : UniverseNameExtension checker.lparams target) :
    ({} : VState).WF (checker.reindexUniverses extension) := by
  apply VState.WF.reset
  intro identifier member
  apply wellFormed.ngen_wf identifier
  simpa [VContext.reindexUniverses, MLCtx.reindexLevels.vlctx, VLCtx.instL_eq_map, VLCtx.fvars] using member

end TypeChecker

namespace ElimNestedInductive

theorem TypedParameterApplications.reindexUniverses
    (arguments : TypedParameterApplications environment original model source replacements values result)
    (extension : UniverseNameExtension original target) :
    TypedParameterApplications environment target (model.reindexLevels (UniverseNameExtension.levels original target))
      (source.instL (UniverseNameExtension.levels original target)) replacements
      (values.map (VExpr.instL (UniverseNameExtension.levels original target)))
      (result.instL (UniverseNameExtension.levels original target)) := by
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  induction arguments with
  | nil => exact .nil
  | cons translated typed _ induction =>
    refine .cons (by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using translated.reindexUniverses extension)
      (by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx, VLCtx.instL_toCtx] using
        (count.symm ▸ typed).instL extension.levelsWF) ?_
    simpa only [VExpr.instL_instN] using induction
  | convertInput equality _ induction =>
    exact .convertInput (by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx, VLCtx.instL_toCtx] using
      (count.symm ▸ equality).instL extension.levelsWF) induction

end ElimNestedInductive

namespace AddInductive

theorem HeaderCheckerAligned.reindexUniverses
    (aligned : HeaderCheckerAligned checker reader) (extension : UniverseNameExtension checker.lparams target) :
    HeaderCheckerAligned (checker.reindexUniverses extension) { reader with lparams := target } := by
  unfold HeaderCheckerAligned at aligned ⊢
  rw [TypeChecker.VContext.reindexUniverses.context]
  exact congrArg (fun context : TypeChecker.Context => { context with lparams := target }) aligned

def HeaderParameterApplicationInput.reindexUniverses
    (input : HeaderParameterApplicationInput environment original model stats source)
    (extension : UniverseNameExtension original target) :
    HeaderParameterApplicationInput environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats source :=
  ⟨input.semantic.instL (UniverseNameExtension.levels original target),
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using input.sourceTranslated.reindexUniverses extension,
    input.values.map (VExpr.instL (UniverseNameExtension.levels original target)),
    input.result.instL (UniverseNameExtension.levels original target), input.arguments.reindexUniverses extension⟩

theorem HeaderParameterApplicationBatch.reindexUniverses
    (batch : HeaderParameterApplicationBatch environment original model stats types)
    (extension : UniverseNameExtension original target) :
    HeaderParameterApplicationBatch environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats types := by
  intro parent bound
  obtain ⟨input, value, translated, typed⟩ := batch parent bound
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  exact ⟨input.reindexUniverses extension, value.instL (UniverseNameExtension.levels original target),
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using translated.reindexUniverses extension,
    by simpa only [HeaderParameterApplicationInput.reindexUniverses, TypeChecker.MLCtx.reindexLevels.vlctx,
      VLCtx.instL_toCtx] using (count.symm ▸ typed).instL extension.levelsWF⟩

theorem getRecLevelParams.universeExtension (elimLevel : Level) (universes : List Name) :
    UniverseNameExtension universes (getRecLevelParams elimLevel universes) := by
  constructor
  intro name member
  unfold getRecLevelParams
  split
  · exact List.mem_cons_of_mem _ member
  · exact member

theorem ConstructorConstantRegistration.parentParameterApplicationsInRecursorUniverses
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) (elimLevel : Level) :
    HeaderParameterApplicationBatch registration.semantic (getRecLevelParams elimLevel root.lparams)
      (stage.before.model.checker.mlctx.reindexLevels
        (UniverseNameExtension.levels root.lparams (getRecLevelParams elimLevel root.lparams))) stats types :=
  registration.parentParameterApplications.reindexUniverses (getRecLevelParams.universeExtension elimLevel root.lparams)

theorem ConstructorConstantRegistration.parentParameterModelWFInRecursorUniverses
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) (elimLevel : Level) :
    (stage.before.model.checker.mlctx.reindexLevels
      (UniverseNameExtension.levels root.lparams (getRecLevelParams elimLevel root.lparams))).WF
        registration.semantic (getRecLevelParams elimLevel root.lparams) :=
  registration.parentParameterModelWF.reindexUniverses (getRecLevelParams.universeExtension elimLevel root.lparams)

theorem run.headerParameterUniverseContinuation (nparams : Nat) (types : List InductiveType)
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
          ∃ registration : ConstructorConstantRegistration receipts final, ∀ elimLevel,
            let universes := getRecLevelParams elimLevel root.lparams
            let model := stage.before.model.checker.mlctx.reindexLevels
              (UniverseNameExtension.levels root.lparams universes)
            model.WF registration.semantic universes ∧
              HeaderParameterApplicationBatch registration.semantic universes model stats types.toArray := by
  refine (run.headerParameterApplicationContinuation nparams types numNested root reader aligned empty
    different constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, registration, _⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration,
    fun elimLevel => ⟨registration.parentParameterModelWFInRecursorUniverses elimLevel,
      registration.parentParameterApplicationsInRecursorUniverses elimLevel⟩⟩

end AddInductive
end Lean4Lean
