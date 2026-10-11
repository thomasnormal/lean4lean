import Lean4Lean.Verify.InductiveHeaderIndexApplications
import Lean.Util.CollectAxioms

namespace InductiveHeaderIndexApplicationsTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterApplications ContextReserved)

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

example {environment : VEnv} {universes : List Name} {model : MLCtx}
    (first : environment.IsDefEqU universes.length model.vlctx.toCtx source middle)
    (second : environment.IsDefEqU universes.length model.vlctx.toCtx middle target)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    environment.IsDefEqU universes.length model.vlctx.toCtx source target := by
  have applications : TypedParameterApplications environment universes model source [] [] target :=
    .convertInput first (.convertInput second .nil)
  exact applications.emptyResultEquality environmentWF modelWF sourceWF

example {environment : VEnv} {universes : List Name} {model : MLCtx}
    (first : environment.IsDefEqU universes.length model.vlctx.toCtx source middle)
    (second : environment.IsDefEqU universes.length model.vlctx.toCtx middle target)
    (arguments : TypedParameterApplications environment universes model target
      (replacement :: replacements) values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    ∃ domain body argument remainingValues,
      values = argument :: remainingValues ∧
      environment.IsDefEqU universes.length model.vlctx.toCtx source (.forallE domain body) ∧
      TrExprS environment universes model.vlctx replacement argument ∧
      environment.HasType universes.length model.vlctx.toCtx argument domain ∧
      TypedParameterApplications environment universes model (body.inst argument) replacements remainingValues result := by
  have applications : TypedParameterApplications environment universes model source
      (replacement :: replacements) values result := .convertInput first (.convertInput second arguments)
  exact applications.consView environmentWF modelWF sourceWF

example
    (arguments : TypedParameterApplications environment universes model source [] values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    environment.IsDefEqU universes.length model.vlctx.toCtx source result := by
  apply TypedParameterApplications.emptyResultEquality <;> assumption

example
    (arguments : TypedParameterApplications environment universes model source
      (replacement :: replacements) values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    ∃ domain body argument remainingValues,
      values = argument :: remainingValues ∧
      environment.IsDefEqU universes.length model.vlctx.toCtx source (.forallE domain body) ∧
      TrExprS environment universes model.vlctx replacement argument ∧
      environment.HasType universes.length model.vlctx.toCtx argument domain ∧
      TypedParameterApplications environment universes model (body.inst argument) replacements remainingValues result := by
  apply TypedParameterApplications.consView <;> assumption

example
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (environmentWF : environment.WF) (model : MLCtx) (modelWF : model.WF environment universes)
    (arguments : TypedParameterApplications environment universes model semantic
      (stats.params.toList.drop index) values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (support : IndexParameterNormalizationSupport environment universes model.vlctx parameters) :
    TrExpr environment universes model.vlctx residual resultSemantic := by
  apply RecursorIndexParameterPrefix.normalizedApplications <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic) :
    ∃ resultSemantic, HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic := by
  exact endpoint.withHeaderApplications

example
    {stats : InductiveStats} {source residual terminal : Expr} {afterIndex finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex)
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (model : MLCtx) (modelWF : model.WF environment universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (arguments : TypedParameterApplications environment universes model semantic stats.params.toList values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (parameterSupport : IndexParameterNormalizationSupport environment universes model.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport environment universes trace)
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    ∃ finalModel, HeaderRecursorIndexModelEndpoint environment universes trace model finalModel semantic resultSemantic := by
  apply RecursorIndexTrace.headerApplications <;> assumption

example
    {stats : InductiveStats} {source headerSource terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats headerSource)
    (normalized : (monadLift (TypeChecker.whnf headerSource) : M Expr) reader = .ok source)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ finalModel, HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx
      finalModel input.semantic input.result := by
  apply RecursorIndexTrace.headerApplicationsOfChecker <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic) :
    final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx environment universes finalReader.lctx final.vlctx := by
  apply HeaderRecursorIndexModelEndpoint.context <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (translated : TrExprS environment universes initial.vlctx (mkAppN head stats.params) value)
    (typed : environment.HasType universes.length initial.vlctx.toCtx value resultSemantic) :
    ∃ finalValue terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx finalValue terminalSemantic := by
  apply HeaderRecursorIndexModelEndpoint.applicationOfPartial <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  apply HeaderRecursorIndexModelEndpoint.application <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : HeaderParameterApplicationInput environment universes initial stats headerSource)
    (input : RecursorConstantInput environment universes initial.vlctx name levels headerSource)
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final
      parameters.semantic parameters.result)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  apply HeaderRecursorIndexModelEndpoint.constantInputApplication <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (translated : TrExprS environment universes initial.vlctx (mkAppN head stats.params) value)
    (typed : environment.HasType universes.length initial.vlctx.toCtx value resultSemantic)
    (sorted : terminal.isSort = true) :
    ∃ finalValue, TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      environment.IsType universes.length final.vlctx.toCtx finalValue := by
  apply HeaderRecursorIndexModelEndpoint.parentTypehoodOfPartial <;> assumption

example
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalModel, HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx
        finalModel input.semantic input.result ∧
        ∃ value terminalSemantic, TrExprS checker.venv checker.lparams finalModel.vlctx
          (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          TrExprS checker.venv checker.lparams finalModel.vlctx terminal terminalSemantic ∧
          checker.venv.HasType checker.lparams.length finalModel.vlctx.toCtx value terminalSemantic := by
  apply RecursorIndexTrace.applicationOfHeaderBatch <;> assumption

example {resultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat) (bound : parent < types.size)
    (source : Expr) (fuel : Nat) (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (supports : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current),
      IndexTraceAnnotationSupport checker.venv checker.lparams trace ∧
        IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current)
      (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type) finalModel,
      HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx finalModel input.semantic input.result →
      (∃ value terminalSemantic, TrExprS checker.venv checker.lparams finalModel.vlctx
          (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
        TrExprS checker.venv checker.lparams finalModel.vlctx terminal terminalSemantic ∧
        checker.venv.HasType checker.lparams.length finalModel.vlctx.toCtx value terminalSemantic) →
      (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post := by
  apply mkRecInfos.loopArgs1.headerBatchTraceOfChecker <;> assumption

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters indices mode : Nat) (dependent : Bool := false)
    (levels : List Level := []) : InductiveType :=
  let parameterLevel := levels.headD (.succ .zero)
  let resultLevel := levels.foldl Level.max (.succ .zero)
  let suffix := fun body => (List.range indices).foldr
    (fun _ body => .forallE `index natural body .default) body
  let close := fun wrapped body =>
    let residual := if wrapped then delay (suffix body) mode else suffix body
    if dependent then
      .forallE `carrier (.sort parameterLevel) (.forallE `value (.bvar 0) residual .default) .implicit
    else
      (List.range parameters).foldr (fun _ body => .forallE `carrier (.sort parameterLevel) body .implicit) residual
  let arguments := (List.range (parameters + indices)).toArray.map
    fun index => Expr.bvar (parameters + indices - 1 - index)
  { name, type := close true (.sort resultLevel),
    ctors := [⟨name ++ `mk, close false (mkAppN (.const name levels) arguments)⟩] }

private def consumeParameters (stats : InductiveStats) (source : Expr) (reader : Context)
    (index : Nat := 0) : Except Kernel.Exception (Expr × Nat) :=
  if index < stats.params.size then
    match source with
    | .forallE _ _ body _ => do
      let opened := body.instantiate1 stats.params[index]!
      let normalized ← (monadLift (TypeChecker.whnf opened) : M Expr) reader
      let (residual, changes) ← consumeParameters stats normalized reader (index + 1)
      return (residual, changes + if opened == normalized then 0 else 1)
    | _ => .error .deepRecursion
  else .ok (source, 0)
termination_by stats.params.size - index

private def consumeIndices (source : Expr) (arguments : List Expr) (reader : Context) : Except Kernel.Exception Expr := do
  match arguments with
  | [] => return source
  | argument :: remaining =>
    let .forallE _ _ body _ := source | throw .deepRecursion
    let normalized ← (monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) reader
    consumeIndices normalized remaining reader

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat) (originalUniverses : List Name := []) :
    MetaM (Nat × Nat × Nat × Nat) := do
  let host ← getEnv
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  let elimination := `freshElimination
  for isUnsafe in [false, true] do
    unless (host.addDeclCore 0 (.inductDecl originalUniverses parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected header/index controls {types.map (·.name)}"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := originalUniverses,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, registered) := checkInductiveTypes parameters types (fun stats => do
          let current ← read
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          withEnv actual do
            checkConstructors types stats isUnsafe
            return (stats, current, ← declareConstructors stats types isUnsafe)) reader
        | throwError "header/index parameter registration checkpoint failed"
      let .ok final := run parameters types.toList 0 reader | throwError "header/index complete run failed"
      for environment in [registered, final] do
        let original := { current with env := environment }
        let localReader := recursorIndexContext original `extra .default natural
        let saved : Context := {
          localReader with
          ngen := localReader.ngen.next
          lctx := localReader.lctx.mkLetDecl ⟨localReader.ngen.curr⟩ `saved natural (.lit (.natVal 0)) }
        for context in [original, localReader, saved] do
          for universes in [getRecLevelParams .zero originalUniverses,
              getRecLevelParams (.param elimination) originalUniverses,
              originalUniverses ++ [elimination], originalUniverses.reverse ++ [elimination]] do
            let reached := { context with lparams := universes }
            for parent in [:types.size] do
              let source := types[parent]!.type
              let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
                | throwError "header/index original header WHNF failed"
              let .ok (residual, changes) := consumeParameters stats normalized reached
                | throwError "header/index accepted parameters failed normalized consumption"
              let partialParent := mkAppN stats.indConsts[parent]! stats.params
              let .ok inferred := (monadLift (TypeChecker.checkType partialParent) : M Expr) reached
                | throwError "header/index partial parent failed genuine domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
                | throwError "header/index normalized partial-parent residual mismatch"
              let .ok residualKind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
                | throwError "header/index normalized residual strict checking failed"
              unless ((monadLift (TypeChecker.ensureSort residualKind) : M Expr) reached).isOk do
                throwError "header/index normalized residual is not a type"
              let capture := fun indices => do return (indices, ← readThe Context)
              let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[]
                  reached.fuel.inductiveFuel capture reached
                | throwError "header/index actual binder loop failed"
              let .ok (suffixIndices, suffixReader) := mkRecInfos.loopArgs1 stats residual stats.params.size #[]
                  (reached.fuel.inductiveFuel - stats.params.size) capture reached
                | throwError "header/index exact remaining-fuel suffix failed"
              unless indices == suffixIndices && finalReader.ngen == suffixReader.ngen &&
                  localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
                throwError "header/index parameter prefix changed actual index context"
              let .ok terminal := consumeIndices residual indices.toList finalReader
                | throwError "header/index selected indices failed normalized consumption"
              unless terminal.isSort do throwError "header/index accepted terminal is not a sort"
              let .ok appliedType := (monadLift (TypeChecker.checkType (mkAppN partialParent indices)) : M Expr) finalReader
                | throwError "header/index full parent application failed genuine index-domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq appliedType terminal) : M Bool) finalReader
                | throwError "header/index full application differs from actual normalized terminal"
              unless ((monadLift (TypeChecker.ensureSort appliedType) : M Expr) finalReader).isOk do
                throwError "header/index full parent is not a type"
              passed := passed + 1
              changed := changed + changes
              initialChanges := initialChanges + if source == normalized then 0 else 1
              unless parameters == 0 do
                let wrongReader := recursorIndexContext reached `wrongParameter .default natural
                let wrongStats := { stats with params := stats.params.set! 0 (.fvar ⟨reached.ngen.curr⟩) }
                unless wrongStats.params.all (·.isFVar) do throwError "wrong-domain control lost all-free-variable boundary"
                let .ok (wrongIndices, wrongFinal) := mkRecInfos.loopArgs1 wrongStats normalized 0 #[]
                    wrongReader.fuel.inductiveFuel capture wrongReader
                  | throwError "unchecked wrong-domain binder loop unexpectedly failed"
                if ((monadLift (TypeChecker.checkType
                    (mkAppN (mkAppN stats.indConsts[parent]! wrongStats.params) wrongIndices)) : M Expr) wrongFinal).isOk then
                  throwError "wrong-domain free-variable parameters acquired typed application eligibility"
                rejected := rejected + 1
  return (passed, changed, rejected, initialChanges)

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderIndexApplications
    | throwError "header/index module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``TypedParameterApplications.apply, ``TypedParameterApplications.weakFV,
      ``RecursorIndexParameterPrefix.normalizedTranslation, ``RecursorIndexTrace.parameterized,
      ``TranslatedRecursorIndexTrace.application, ``TranslatedRecursorIndexTrace.mixedContext,
      ``acceptedHeaderNormalization, ``mkRecInfos.loopArgs1.scopedTrace, ``RecursorIndexTrace.completeParameters] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "header/index owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "header/index unexpected {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      count := count + 1
  logInfo m!"header/index: {count} exhaustive owned declarations audited against genuine prior foundations"

run_meta
  auditModule
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  for (types, parameters, universes) in [
      (#[family `HeaderIndexZero 0 0 0], 0, []),
      (#[family `HeaderIndexZeroLet 0 1 1], 0, []),
      (#[family `HeaderIndexZeroBeta 0 2 2], 0, []),
      (#[family `HeaderIndexZeroMetadata 0 1 3], 0, []),
      (#[family `HeaderIndexOne 1 1 0], 1, []),
      (#[family `HeaderIndexTwoLet 2 2 1], 2, []),
      (#[family `HeaderIndexTwoBeta 2 1 2], 2, []),
      (#[family `HeaderIndexTwoMetadata 2 2 3], 2, []),
      (#[family `HeaderIndexDependent 2 1 1 true], 2, []),
      (#[family `HeaderIndexMutualFirst 2 1 1 true, family `HeaderIndexMutualSecond 2 2 2 true], 2, []),
      (#[family `HeaderIndexUniverse 2 2 1 true [.param `universe]], 2, [`universe]),
      (#[family `HeaderIndexReordered 2 1 2 true [.param `universe, .param `otherUniverse]],
        2, [`universe, `otherUniverse])] do
    let (accepted, conversions, failed, initial) ← checkBatch types parameters universes
    passed := passed + accepted
    changed := changed + conversions
    rejected := rejected + failed
    initialChanges := initialChanges + initial
  unless changed > 0 && initialChanges > 0 && rejected > 0 do
    throwError "header/index controls missed conversions, zero-parameter input normalization, or rejection"
  logInfo m!"{passed} actual normalized header/index applications passed; {changed} parameter-opening WHNF changes, {initialChanges} original-header changes and {rejected} unchecked wrong-domain free-variable arrays rejected; zero/one/two/dependent parameters, differing mutual index counts, original/fresh/reordered universes, registered/full-run environments, original/local/let contexts, both safeties/primitive modes and let/beta/metadata wrappers checked; exact remaining fuel, index arrays, name generators, local declarations, residual and full-application typehood agree; runtime controls do not fabricate semantic contexts"

end InductiveHeaderIndexApplicationsTest
