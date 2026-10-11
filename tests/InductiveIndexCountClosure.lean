import Lean4Lean.Verify.InductiveIndexCountClosure
import Lean.Util.CollectAxioms

namespace InductiveIndexCountClosureTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open ElimNestedInductive (ContextReserved)

example
    {environment : VEnv} {universes first second : Nat} {context : List VExpr} {type : VExpr}
    (left : environment.SortArity universes context first type)
    (right : environment.SortArity universes context second type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    first = second := left.uniqueCount right environmentWF contextWF

example
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx count semantic) :
    finalIndices.size - indices.size ≤ count ∧
      environment.SortArity universes.length finalVirtual.toCtx
        (count - (finalIndices.size - indices.size)) finalSemantic := by
  apply TranslatedRecursorIndexTrace.remainingKind <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count resultSemantic) :
    indices.size ≤ count := endpoint.indexBound kind

example
    {stats : InductiveStats} {source terminal sorted : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context} {checker finalChecker : TypeChecker.VContext}
    {semantic resultSemantic : VExpr}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count resultSemantic)
    (accepted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    indices.size = count := endpoint.exactCountOfSortCheck kind accepted

example
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        indices.size ≤ stats.nindices[parent]! := by
  apply RecursorIndexTrace.checkedHeaderIndexBound <;> assumption

example
    {stats : InductiveStats} {source terminal sorted : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (accepted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel) :
    indices.size = stats.nindices[parent]! ∧
      ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
        ∃ indexChecker finalChecker, HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
          input.semantic input.result types elimLevel parent := by
  apply RecursorIndexTrace.checkedHeaderParentOfSortCheck <;> assumption

private def conversionOnlyMethods : TypeChecker.Methods where
  inferType _ _ := throw .deepRecursion
  isDefEqCore _ _ := throw .deepRecursion
  whnfCore source _ _ := pure source
  whnf source := pure source

private theorem conversionOnlyMethodsWF : conversionOnlyMethods.WF where
  inferType _ _ := .throw
  isDefEqCore _ _ := .throw
  whnfCore := by
    intro source cheapRec cheapProj checker state semantic translated
    exact .pure ⟨.rfl, translated.trExpr checker.Ewf.ordered checker.Δwf⟩
  whnf := by
    intro source checker state semantic translated
    exact .pure ⟨.rfl, translated.trExpr checker.Ewf.ordered checker.Δwf⟩

private theorem conversionOnlyMethodsRetainMetadata
    (metadata : MData) (name : Name) (domain body : Expr) (binder : BinderInfo)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    conversionOnlyMethods.whnf (.mdata metadata (.forallE name domain body binder)) context state =
      .ok (.mdata metadata (.forallE name domain body binder), state) := rfl

private theorem conversionContractDoesNotGiveNativeForallShape
    (metadata : MData) (name : Name) (domain body : Expr) (binder : BinderInfo)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    ∃ methods : TypeChecker.Methods, methods.WF ∧ ∃ result : Expr,
      methods.whnf (.mdata metadata (.forallE name domain body binder)) context state = .ok (result, state) ∧
      result.isForall = false := by
  exact ⟨conversionOnlyMethods, conversionOnlyMethodsWF, _,
    conversionOnlyMethodsRetainMetadata metadata name domain body binder context state, rfl⟩

private def telescope : Nat → Expr
  | 0 => .sort .zero
  | count + 1 => .forallE `index (.const ``Nat []) (telescope count) .default

private def hidden (mode : Nat) (source : Expr) : Expr :=
  match mode with
  | 0 => source
  | 1 => .mdata {} source
  | 2 => .letE `hidden (.sort (.succ .zero)) source (.bvar 0) false
  | _ => .app (.lam `hidden (.const ``Nat []) source .default) (.lit (.natVal 0))

private def nativeControls : MetaM Unit := do
  let host ← getEnv
  let mut passed := 0
  let mut under := 0
  let mut converted := 0
  for safety in [.safe, .unsafe] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env := host.toKernelEnv, lparams := [], safety, allowPrimitive }
      for count in [:4] do
        for mode in [:4] do
          let source := hidden mode (telescope count)
          let stats : InductiveStats := {
            levels := [], resultLevel := .zero, indConsts := #[], params := #[], isNotZero := false, nindices := #[count] }
          unless ((monadLift (TypeChecker.checkType source) : M Expr) reader).isOk do
            throwError "native count control lost genuine source typing"
          let capture : Array Expr → M (Array Expr × Context) := fun indices => do return (indices, ← readThe Context)
          let .ok (unchecked, _) := mkRecInfos.loopArgs1 stats source 0 #[] reader.fuel.inductiveFuel capture reader
            | throwError "unchecked native count traversal failed"
          let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reader
            | throwError "actual native count normalization failed"
          let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[] (count + 1) capture reader
            | throwError "actual native normalized count traversal failed"
          unless indices.size == count do throwError "actual normalized traversal changed syntactic telescope arity"
          if (mkRecInfos.loopArgs1 stats normalized 0 #[] count capture reader).isOk then
            throwError "count traversal escaped exact remaining fuel"
          let stale := { stats with nindices := #[count + 1] }
          let .ok (staleIndices, _) := mkRecInfos.loopArgs1 stale normalized 0 #[] (count + 1) capture reader
            | throwError "unchecked stale native count traversal failed"
          unless staleIndices == indices && staleIndices.size != stale.nindices[0]! do
            throwError "unchecked stale numeric array acquired arity eligibility"
          let mut terminal := normalized
          for argument in indices do
            let .forallE _ _ body _ := terminal | throwError "actual count trace lost its binder"
            let .ok opened := (monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) finalReader
              | throwError "actual count trace lost body normalization"
            terminal := opened
          unless ((monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader).isOk do
            throwError "exhausted native count trace lost accepted terminal sort conversion"
          if count > 0 && mode > 0 then
            unless unchecked.isEmpty && indices.size > unchecked.size do
              throwError "hidden unchecked source failed to demonstrate a strict undertraversal"
            if ((monadLift (TypeChecker.ensureSort source) : M Expr) reader).isOk then
              throwError "typed undertraversal acquired terminal sort conversion"
            under := under + 1
          if count == 0 && mode > 0 then
            unless !source.isSort && ((monadLift (TypeChecker.ensureSort source) : M Expr) reader).isOk do
              throwError "zero-arity converted terminal incorrectly required native literal sort syntax"
            converted := converted + 1
          passed := passed + 1
  logInfo m!"{passed} actual normalized zero/one/two/three-index traversals and accepted terminal sort checks pass under both safeties/primitive modes; exact fuel exhaustion and unchecked stale arrays reject eligibility; {under} genuinely typed hidden unchecked sources stop strictly below their normalized count and reject terminal-sort acceptance; {converted} nonliteral zero-arity terminals retain actual sort-check acceptance; metadata/let/beta wrappers covered; no semantic context or strong checker is fabricated"

run_meta
  let environment ← getEnv
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``VEnv.SortArity.forallBody, ``VEnv.SortArity.defeqCtx,
      ``VEnv.IsDefEqU.sort_forallE_inv, ``TranslatedRecursorIndexTrace.finalKind,
      ``acceptedHeaderSortKind, ``RecursorIndexTrace.headerCheckedModels,
      ``HeaderRecursorIndexCheckerEndpoint.parentCheckerOfKind] do
    allowed := allowed ++ (← collectAxioms name)
  for moduleName in [`Lean4Lean.Theory.SortArityCounts, `Lean4Lean.Verify.InductiveIndexCountClosure] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "index count closure module absent"
    let mut owned := 0
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned index count closure axiom {name}"
        let dependencies ← collectAxioms name
        for dependency in dependencies do
          unless allowed.contains dependency do throwError "unexpected index count dependency {dependency} in {name}"
        logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
        owned := owned + 1
    logInfo m!"{moduleName}: {owned} exhaustive owned count declarations audited against unchanged earlier foundations"
  let controlDependencies ← collectAxioms ``conversionContractDoesNotGiveNativeForallShape
  for dependency in controlDependencies do
    unless allowed.contains dependency do throwError "unexpected conversion-contract control dependency {dependency}"
  logInfo m!"conversion-only Methods.WF contract has a formal metadata-head countermodel with {controlDependencies.size} inherited dependencies; this is not the actual native normalizer and supplies no positive frontend/checker receipt"
  nativeControls

end InductiveIndexCountClosureTest
