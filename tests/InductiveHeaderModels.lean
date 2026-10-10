import Lean4Lean.Verify.InductiveHeaderModels
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ParameterPrefix ContextReserved)
open Lean4Lean.TypeChecker (MLCtx)

namespace InductiveHeaderModelsTest

private def oldId : FVarId := ⟨`RetainedHeaderLocal⟩
private def parameterId : FVarId := ⟨`CanonicalHeaderParameter⟩
private def indexId : FVarId := ⟨`AmbientHeaderIndex⟩
private def base : MLCtx := .vlam oldId `old (.sort .zero) (.sort .zero) .default .nil
private def parameters : MLCtx := .vlam parameterId `parameter (.sort .zero) (.sort .zero) .implicit base
private def ambient : MLCtx := .vlam indexId `index (.fvar parameterId) (.bvar 0) .default parameters

private theorem baseWF (env : VEnv) : base.WF env [] :=
  ⟨trivial, (TrLCtx.nil (env := env) (Us := [])).find?_eq_none.mpr (by simp),
    .sort rfl, _, .sortDF (by trivial) (by trivial) rfl⟩

private theorem parametersWF (env : VEnv) : parameters.WF env [] := by
  refine ⟨baseWF env, ?_, .sort rfl, _, .sortDF (by trivial) (by trivial) rfl⟩
  exact (baseWF env).tr.find?_eq_none.mpr (by simp [base, oldId, parameterId])

private theorem ambientWF (env : VEnv) : ambient.WF env [] := by
  refine ⟨parametersWF env, ?_, .fvar rfl, _, .bvar .zero⟩
  exact (parametersWF env).tr.find?_eq_none.mpr (by simp [parameters, base, oldId, parameterId, indexId])

private theorem parameterHistory : ParameterPrefix base parameters [parameterId] :=
  .snoc .nil

private theorem indexHistory : ParameterPrefix parameters ambient [indexId] :=
  .snoc .nil

private theorem wholeHistory : ParameterPrefix base ambient [parameterId, indexId] :=
  parameterHistory.trans indexHistory

private theorem splitHistory : ∃ middle,
    ParameterPrefix base middle [parameterId] ∧ ParameterPrefix middle ambient [indexId] := by
  simpa using wholeHistory.splitAt 1

private theorem splitBeforeEverything : ∃ middle,
    ParameterPrefix base middle [] ∧ ParameterPrefix middle ambient [parameterId, indexId] := by
  simpa using wholeHistory.splitAt 0

private theorem splitAfterEverything : ∃ middle,
    ParameterPrefix base middle [parameterId, indexId] ∧ ParameterPrefix middle ambient [] := by
  simpa using wholeHistory.splitAt 9

private theorem fullReaderIsNotParameterOnly : ¬ ParameterPrefix base ambient [parameterId] := by
  intro wrong
  have names := wrong.fvars
  simp [ambient, parameters, base] at names

private theorem parameterLookupSurvivesIndices (env : VEnv) :
    ∃ declaration, ambient.lctx.find? parameterId = some declaration ∧ declaration.type = .sort .zero := by
  let declaration := LocalDecl.cdecl base.length parameterId `parameter (.sort .zero) .implicit .default
  have lookup : parameters.lctx.find? parameterId = some declaration := by
    rw [(parametersWF env).find?_eq]
    simp [parameters, declaration, MLCtx.decls, LocalDecl.fvarId]
  exact ⟨declaration, indexHistory.retainsLookup (ambientWF env) lookup, rfl⟩

private theorem defaultPrefixesAreDisjoint :
    ({} : TypeChecker.VState).ngen.namePrefix ≠ (`_ind_fresh : Name) := by decide

private theorem checkerCannotResetAcrossOwnFreshName :
    ¬ ({} : TypeChecker.VState).ngen.Reserves ⟨({} : TypeChecker.VState).ngen.curr⟩ :=
  NameGenerator.not_reserves_self

private def fixtureChecker {nativeEnv : Kernel.Environment} {environments : VEnvs}
    (nativeWF : environments.WF nativeEnv) : TypeChecker.VContext :=
  { TypeChecker.VContext.mk' nativeWF .safe [] {} with
    mlctx := base, mlctx_wf := baseWF _, lctx := base.lctx, lctx_eq := rfl }

private def fixtureReader (nativeEnv : Kernel.Environment) : Context :=
  { env := nativeEnv, lctx := base.lctx, lparams := [], safety := .safe, allowPrimitive := false }

private theorem fixtureResetWF {nativeEnv : Kernel.Environment} {environments : VEnvs}
    (nativeWF : environments.WF nativeEnv) : ({} : TypeChecker.VState).WF (fixtureChecker nativeWF) := by
  apply TypeChecker.VState.WF.reset
  intro identifier member position same
  change identifier ∈ [oldId] at member
  rcases List.mem_singleton.mp member with rfl
  cases same

private theorem fixtureNativeReserved (nativeEnv : Kernel.Environment) :
    ContextReserved (fixtureReader nativeEnv).lctx (fixtureReader nativeEnv).ngen := by
  intro declaration member
  cases declaration with
  | cdecl index identifier name type binder kind =>
    simp [fixtureReader, base, MLCtx.lctx, LocalContext.toList,
      LocalContext.mkLocalDecl] at member
    rcases member with member | member
    · rcases member with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      intro position equality
      cases equality
    · change some (LocalDecl.cdecl index identifier name type binder kind) ∈
        (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at member
      have empty : (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' = [] := by
        change (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' = []
        exact (by simp)
      rw [empty] at member
      cases member
  | ldecl index identifier name type value nondep kind =>
    simp [fixtureReader, base, MLCtx.lctx, LocalContext.toList,
      LocalContext.mkLocalDecl] at member
    change some (LocalDecl.ldecl index identifier name type value nondep kind) ∈
      (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList'
      at member
    have empty : (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' = [] := by
      change (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' = []
      exact (by simp)
    rw [empty] at member
    cases member

private theorem actualBatchDerivesModels
    {nativeEnv : Kernel.Environment} {environments : VEnvs}
    (nativeWF : environments.WF nativeEnv)
    (constants : CanonicalAnnotationConstants (environments.venv .safe))
    (definitions : CanonicalAnnotationDefinitions (environments.venv .safe))
    (nparams : Nat) (types : Array InductiveType) (nonempty : 0 < types.size)
    (stats : InductiveStats) (reader : Context)
    (accepted : checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context))
      (fixtureReader nativeEnv) = .ok (stats, reader)) :
    ∃ normalized terminal firstStats count current,
      (monadLift (TypeChecker.whnf types[0]!.type) : M Expr) (fixtureReader nativeEnv) = .ok normalized ∧
      CheckedHeaderTrace nparams (default : InductiveStats) normalized 0 0 (fixtureReader nativeEnv)
        terminal firstStats count current ∧
      FirstHeaderCheckerModels (fixtureChecker nativeWF) nparams count firstStats.params current terminal := by
  exact checkInductiveTypes.firstModels nparams types _ (fixtureReader nativeEnv) (fixtureChecker nativeWF)
    rfl (fixtureResetWF nativeWF) (fixtureNativeReserved nativeEnv) defaultPrefixesAreDisjoint
    constants definitions nonempty (stats, reader) accepted

private theorem selectedModelDomainComesFromCanonicalPrefix
    (checker : TypeChecker.VContext) (nparams nindices : Nat) (params : Array Expr)
    (reader : Context) (terminal : Expr)
    (models : FirstHeaderCheckerModels checker nparams nindices params reader terminal)
    (index : Nat) (identifier : FVarId) (selected : params[index]? = some (.fvar identifier)) :
    ∃ (parameters : List FVarId) (smaller : MLCtx) (nativeDomain : Expr) (semanticDomain : VExpr),
      params.toList = parameters.map Expr.fvar ∧
      ParameterPrefix checker.mlctx smaller (parameters.take index) ∧ smaller.WF checker.venv checker.lparams ∧
      TrExprS checker.venv checker.lparams smaller.vlctx nativeDomain semanticDomain ∧
      checker.venv.IsType checker.lparams.length smaller.vlctx.toCtx semanticDomain ∧
      ∃ declaration, reader.lctx.find? identifier = some declaration ∧ declaration.type = nativeDomain :=
  models.selectedParameterDomain selected

private def domainAt (position : Nat) : Expr :=
  if position = 0 then
    .app (.const ``outParam [.max .zero (.succ (.succ .zero))]) (.sort (.succ .zero))
  else if position = 1 then
    .app (.const ``semiOutParam [.max .zero (.succ .zero)]) (.bvar 0)
  else if position = 2 then
    mkApp2 (.const ``autoParam [.succ .zero]) (.bvar 1) (.const ``Lean.Syntax.missing [])
  else mkApp2 (.const ``optParam [.max .zero (.succ .zero)]) (.const ``Nat []) (.const ``Nat.zero [])

private def headerSource (count : Nat) : Expr :=
  .mdata {} ((List.range count).foldr (fun position body =>
    .forallE `binder (domainAt position) (.mdata {} body) .implicit) (.sort (.succ .zero)))

private def stage (nparams : Nat) (types : Array InductiveType) : M (InductiveStats × Context) :=
  checkInductiveTypes nparams types fun stats => do return (stats, ← readThe Context)

private def runtimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let mut controls := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    let reader : Context :=
      { env := nativeEnv, lctx := base.lctx, lparams := [], safety, allowPrimitive := false,
        ngen := { namePrefix := `_ind_fresh, idx := 7 }, fuel := { recDepth := 256 } }
    for nparams in [0, 1, 2] do
      for nindices in [0, 1, 2] do
        let count := nparams + nindices
        let types : Array InductiveType := #[{ name := `HeaderModelControl, type := headerSource count, ctors := [] }]
        let .ok (stats, current) := stage nparams types reader
          | throwError "fresh-header model runtime source rejected"
        unless stats.params.size == nparams && stats.nindices == #[nindices] &&
            current.lctx.numIndices == base.length + count && current.ngen.idx == 7 + count do
          throwError "fresh-header model native counts changed"
        for position in [:count] do
          let identifier : FVarId := ⟨.num `_ind_fresh (7 + position)⟩
          let some declaration := current.lctx.find? identifier
            | throwError "fresh-header model lost an allocated native binder"
          let expected := if position = 0 then Expr.sort (.succ .zero)
            else if position = 3 then .const ``Nat [] else .fvar ⟨.num `_ind_fresh 7⟩
          unless declaration.type == expected do
            throwError "fresh-header model stored the wrong peeled/dependent domain"
          if position < nparams then
            unless stats.params[position]! == .fvar identifier do
              throwError "fresh-header model changed canonical parameter identity"
        unless (current.lctx.find? oldId).map LocalDecl.type == some (.sort .zero) do
          throwError "fresh-header model dropped the old base lookup"
        controls := controls + 1
    for nindices in [0, 2] do
      let types : Array InductiveType :=
        #[{ name := `FirstHeaderModelControl, type := headerSource (1 + nindices), ctors := [] },
          { name := `LaterHeaderModelControl, type := headerSource 3, ctors := [] }]
      let .ok (stats, current) := stage 1 types reader
        | throwError "mutual first-header model source rejected"
      unless stats.nindices == #[nindices, 2] && stats.params.size == 1 &&
          current.lctx.numIndices == base.length + 1 + nindices + 2 do
        throwError "later native readers did not retain their extra index suffix"
      controls := controls + 1
    for source in [Expr.forallE `bad (.const ``Nat.zero []) (.sort (.succ .zero)) .default,
        .forallE `bad (.app (.const ``outParam []) (.const ``Nat [])) (.sort (.succ .zero)) .default,
        .forallE `bad (.fvar oldId) (.sort (.succ .zero)) .default] do
      match stage 0 #[{ name := `BadHeaderModelControl, type := source, ctors := [] }] reader with
      | .error _ => controls := controls + 1
      | .ok _ => throwError "invalid/unguarded header model source accepted"
  unless controls == 28 do throwError "fresh-header model runtime control count changed"
  logInfo m!"first-header-model: {controls} runtime controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "first-header-model unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: {axioms.size} dependencies = {repr axioms}"

private def auditModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderModels
    | throwError "first-header-model module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then throwError "first-header-model module-owned axiom {name}"
      auditDeclaration name allowed
  logInfo m!"first-header-model: {declarations} exhaustive production declarations"

run_meta
  let logical := [``propext, ``Quot.sound, ``Classical.choice, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.toList'_insert]
  let admitted := logical ++ [``sorryAx]
  let checker := (← collectAxioms ``TypeChecker.whnf.WF).toList ++
    (← collectAxioms ``TypeChecker.checkType.WF).toList
  let guarded := checker ++ [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq]
  auditModule guarded
  for name in [``baseWF, ``parametersWF, ``ambientWF, ``parameterHistory, ``indexHistory,
      ``wholeHistory, ``splitHistory, ``splitBeforeEverything, ``splitAfterEverything,
      ``fullReaderIsNotParameterOnly, ``defaultPrefixesAreDisjoint, ``checkerCannotResetAcrossOwnFreshName] do
    auditDeclaration name admitted
  for name in [``parameterLookupSurvivesIndices, ``fixtureChecker, ``fixtureResetWF, ``fixtureNativeReserved,
      ``actualBatchDerivesModels, ``selectedModelDomainComesFromCanonicalPrefix] do
    auditDeclaration name guarded
  runtimeControls

end InductiveHeaderModelsTest
