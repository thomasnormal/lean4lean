import Lean4Lean.Verify.InductiveRecursorIndexParameters
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (TypedParameterArguments ContextReserved)

namespace InductiveRecursorIndexParametersTest

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex) :
    stats.params.size ≤ afterIndex := parameters.complete

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex) :
    afterIndex = max index stats.params.size := parameters.count

example (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (complete : stats.params.size ≤ finalIndex) :
    ∃ residual afterIndex, RecursorIndexParameterPrefix stats reader source index residual afterIndex :=
  trace.parameterPrefix complete

example (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ index + declareConstructors.arity 0 source) :
    stats.params.size ≤ finalIndex := trace.completeParameters parameterFVars arity

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader) :
    RecursorIndexTrace stats residual afterIndex indices reader terminal finalIndex finalIndices finalReader :=
  parameters.indexSuffix trace

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (annotations : IndexTraceAnnotationSupport environment universes trace) :
    IndexTraceAnnotationSupport environment universes (parameters.indexSuffix trace) :=
  parameters.annotationSuffix annotations

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    IndexTraceNormalizationSupport environment universes (parameters.indexSuffix trace) :=
  parameters.normalizationSuffix normalizations

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) :
    IndexParameterNormalizationSupport checker.venv checker.lparams checker.vlctx parameters :=
  parameters.normalizationSupport checker aligned initialWF

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (telescope : SortTelescope source) :
    IndexParameterNormalizationSupport environment universes virtual parameters :=
  parameters.normalizationSupport_ofSortTelescope telescope

example (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (environmentWF : environment.WF) (model : MLCtx) (modelWF : model.WF environment universes)
    (arguments : TypedParameterArguments environment universes model semantic
      (stats.params.toList.drop index) values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (support : IndexParameterNormalizationSupport environment universes model.vlctx parameters) :
    TrExpr environment universes model.vlctx residual resultSemantic :=
  parameters.normalizedTranslation environmentWF model modelWF arguments translated support

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex)
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (model : MLCtx) (modelWF : model.WF environment universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (arguments : TypedParameterArguments environment universes model semantic stats.params.toList values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (parameterSupport : IndexParameterNormalizationSupport environment universes model.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport environment universes trace)
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    ∃ finalModel, ParameterizedRecursorIndexModelEndpoint environment universes trace model finalModel semantic :=
  trace.parameterized parameters environmentWF constants definitions model modelWF native reserved
    arguments translated parameterSupport annotations normalizations

example (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen) (complete : stats.params.size ≤ finalIndex)
    (arguments : TypedParameterArguments checker.venv checker.lparams checker.mlctx semantic
      stats.params.toList values resultSemantic)
    (translated : checker.TrExpr source semantic)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ finalModel, ParameterizedRecursorIndexModelEndpoint checker.venv checker.lparams trace
      checker.mlctx finalModel semantic :=
  trace.parameterizedOfChecker checker aligned initialWF constants definitions reserved complete
    arguments translated annotations normalizations

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic) :
    final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx environment universes finalReader.lctx final.vlctx := endpoint.context

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic :=
  endpoint.application environmentWF initialWF headTranslated headTyped

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic :=
  endpoint.constantInputApplication input environmentWF initialWF

example (stats : InductiveStats) (source : Expr) (fuel : Nat)
    (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (arguments : TypedParameterArguments checker.venv checker.lparams checker.mlctx semantic
      stats.params.toList values resultSemantic)
    (translated : checker.TrExpr source semantic)
    (supports : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current),
      IndexTraceAnnotationSupport checker.venv checker.lparams trace ∧
        IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current) finalModel,
      ParameterizedRecursorIndexModelEndpoint checker.venv checker.lparams trace
        checker.mlctx finalModel semantic → (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post :=
  mkRecInfos.loopArgs1.parameterizedTraceOfChecker stats source fuel next reader post checker aligned
    initialWF constants definitions reserved parameterFVars arity arguments translated supports nextWF

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (sorted : terminal.isSort = true) :
    ∃ value, TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      environment.IsType universes.length final.vlctx.toCtx value :=
  endpoint.parentTypehood environmentWF initialWF headTranslated headTyped sorted

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (sorted : terminal.isSort = true) :
    ∃ value, TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      environment.IsType universes.length final.vlctx.toCtx value :=
  endpoint.constantInputParentTypehood input environmentWF initialWF sorted

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ identifiers : List FVarId, ∃ bound : identifiers.length ≤ final.length,
      indices.toList = identifiers.map Expr.fvar ∧ ∃ abstraction level,
        TrExprS environment universes final.vlctx
          (final.mkForall identifiers.length bound (.sort elimLevel)) abstraction ∧
        environment.HasType universes.length final.vlctx.toCtx abstraction (.sort level) :=
  endpoint.indexAbstraction environmentWF mapped

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS environment universes initial.vlctx stats.indConsts[parent]! headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (terminalSort : terminal = .sort terminalLevel)
    (mapped : VLevel.ofLevel universes terminalLevel = some level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled, RecursorMajorOpening environment universes stats parent indices
      finalReader final.vlctx rawSemantic peeled level :=
  endpoint.majorOpening environmentWF initialWF constants definitions reserved
    headTranslated headTyped terminalSort mapped uniform

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (head : stats.indConsts[parent]! = .const name levels)
    (terminalSort : terminal = .sort terminalLevel)
    (mapped : VLevel.ofLevel universes terminalLevel = some level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled, RecursorMajorOpening environment universes stats parent indices
      finalReader final.vlctx rawSemantic peeled level :=
  endpoint.constantInputMajorOpening input environmentWF initialWF constants definitions reserved
    head terminalSort mapped uniform

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (opening : RecursorMajorOpening environment universes stats parent indices finalReader
      final.vlctx rawSemantic peeled majorLevel)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (native : initial.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ motiveSemantic motiveLevel, RecursorMotiveDomainTranslation environment universes
      stats parent indices finalReader final.vlctx peeled elimLevel motiveSemantic motiveLevel :=
  endpoint.motiveDomainTranslation opening environmentWF initialWF native reserved mapped

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def indexedFamily (name : Name) (parameters : Nat) (mode : Nat := 0) : InductiveType :=
  let close := fun wrapped body => (List.range parameters).foldr
    (fun index body => .forallE `carrier sortType
      (if wrapped && index + 1 == parameters then delay body mode else body) .implicit) body
  let parent := mkAppN (.const name [])
    (((List.range parameters).toArray.map fun index => .bvar (parameters - index)).push (.bvar 0))
  { name, type := close true (.forallE `index natural sortType .default),
    ctors := [⟨name ++ `mk, close false (.forallE `index natural parent .default)⟩] }

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

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let environment := host.toKernelEnv
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected index-parameter controls {types.map (·.name)}"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 1 isUnsafe
          return (stats, ← read, actual)) reader | throwError "index-parameter headers failed"
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
        throwError "index-parameter constructors failed checking"
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual }
        | throwError "index-parameter constructors failed registration"
      unless (run parameters types.toList 1 reader).isOk do throwError "index-parameter full run failed"
      let actualReader := { current with env := registered }
      let .ok elimLevel := getElimLevel stats types actualReader | throwError "index-parameter elimination failed"
      let .ok (_, motiveReader) := mkRecInfos.loopInd1 stats types elimLevel 0 #[]
          (fun infos => do return (infos, ← readThe Context)) actualReader
        | throwError "index-parameter actual motive pass failed"
      for reached in [actualReader, motiveReader] do
        let checkedReader := { reached with lparams := getRecLevelParams elimLevel universes }
        for parent in [:types.size] do
          let source := types[parent]!.type
          let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
            | throwError "index-parameter initial normalization failed"
          let .ok (residual, prefixChanges) := consumeParameters stats normalized reached
            | throwError "accepted header lacks complete normalized parameters"
          let capture := fun indices => do return (indices, ← readThe Context)
          let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[]
              reached.fuel.inductiveFuel capture reached
            | throwError "index-parameter full index loop failed"
          let .ok (suffixIndices, suffixReader) := mkRecInfos.loopArgs1 stats residual stats.params.size #[]
              (reached.fuel.inductiveFuel - stats.params.size) capture reached
            | throwError "index-parameter remaining-fuel suffix failed"
          unless indices == suffixIndices && finalReader.ngen == suffixReader.ngen &&
              localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
            throwError "index prefix changed actual index allocation or reader"
          let .ok inferred := (monadLift (TypeChecker.checkType residual) : M Expr) checkedReader
            | throwError "index-parameter residual strict checking failed"
          unless ((monadLift (TypeChecker.ensureSort inferred) : M Expr) checkedReader).isOk do
            throwError "index-parameter residual source is not a type"
          let applied := mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices
          let .ok appliedType := (monadLift (TypeChecker.checkType applied) : M Expr)
              { finalReader with lparams := checkedReader.lparams }
            | throwError "index-parameter actual parent application failed"
          unless ((monadLift (TypeChecker.ensureSort appliedType) : M Expr)
              { finalReader with lparams := checkedReader.lparams }).isOk do
            throwError "index-parameter saturated parent application is not a type"
          outcomes := outcomes + 1
          changes := changes + prefixChanges
          unless parameters == 0 do
            let wrongReader := recursorIndexContext reached `wrongParameter .default natural
            let wrongStats := { stats with params := stats.params.set! 0 (.fvar ⟨reached.ngen.curr⟩) }
            unless wrongStats.params.all (·.isFVar) do
              throwError "wrong-domain parameter control lost its all-free-variable boundary"
            let .ok (wrongIndices, wrongFinalReader) := mkRecInfos.loopArgs1 wrongStats normalized 0 #[]
                wrongReader.fuel.inductiveFuel capture wrongReader
              | throwError "unchecked wrong-domain parameter traversal no longer succeeds"
            let wrongApplied := mkAppN (mkAppN stats.indConsts[parent]! wrongStats.params) wrongIndices
            if ((monadLift (TypeChecker.checkType wrongApplied) : M Expr)
                { wrongFinalReader with lparams := checkedReader.lparams }).isOk then
              throwError "wrong-domain all-free-variable parameters acquired typed application eligibility"
            rejected := rejected + 1
      unless types.isEmpty || parameters == 0 do
        let unchecked := sortType
        unless (mkRecInfos.loopArgs1 stats unchecked 0 #[] actualReader.fuel.inductiveFuel
            (fun _ => pure ()) actualReader).isOk do
          throwError "index-parameter unchecked early-stop boundary changed"
        if (consumeParameters stats unchecked actualReader).isOk then
          throwError "incomplete unchecked source obtained complete parameter prefix"
        let invalid := types.modify 0 fun type => { type with type := sortType }
        if (checkInductiveTypes parameters invalid (fun _ => pure ()) reader).isOk then
          throwError "incomplete header obtained accepted parameter eligibility"
  return (outcomes, changes, rejected)

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRecursorIndexParameters
    | throwError "index-parameter module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``RecursorIndexTrace, ``IndexTraceAnnotationSupport, ``IndexTraceNormalizationSupport,
      ``VEnv.IsDefEqU.forallE_inv, ``TrExprS.inst, ``acceptedHeaderNormalization,
      ``SortTelescope.normalizedTranslation, ``RecursorIndexTrace.translated,
      ``TranslatedRecursorIndexTrace.mixedContext, ``TranslatedRecursorIndexTrace.application,
      ``TypedParameterArguments.apply, ``mkRecInfos.loopArgs1.scopedTrace,
      ``IndexMLCtxExtension.typedAbstraction, ``TranslatedRecursorIndexTrace.majorOpening,
      ``TranslatedRecursorIndexTrace.motiveDomainTranslation] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index-parameter owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "index-parameter unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"index parameters: {count} exhaustive owned declarations audited against genuine prior foundations"

run_meta
  auditModule
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for (types, parameters) in [
      (#[], 0), (#[{ name := `IndexPrefixEmpty, type := sortType, ctors := [] }], 0),
      (#[indexedFamily `IndexPrefixZero 0], 0), (#[indexedFamily `IndexPrefixOne 1], 1),
      (#[indexedFamily `IndexPrefixTwo 2], 2), (#[indexedFamily `IndexPrefixLet 2 1], 2),
      (#[indexedFamily `IndexPrefixBeta 2 2], 2), (#[indexedFamily `IndexPrefixMetadata 1 3], 1),
      (#[indexedFamily `IndexPrefixMutualFirst 2 1, indexedFamily `IndexPrefixMutualSecond 2 2], 2)] do
    let (passed, changed, failed) ← checkBatch types parameters
    outcomes := outcomes + passed
    changes := changes + changed
    rejected := rejected + failed
  let dependent : InductiveType := {
    name := `IndexPrefixDependent,
    type := .forallE `carrier sortType (.forallE `value (.bvar 0)
      (delay (.forallE `index natural sortType .default) 1) .default) .implicit,
    ctors := [⟨`IndexPrefixDependent.mk, .forallE `carrier sortType (.forallE `value (.bvar 0)
      (.forallE `index natural (mkAppN (.const `IndexPrefixDependent [])
        #[.bvar 2, .bvar 1, .bvar 0]) .default) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[dependent] 2
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  let universeLevel := Level.param `universe
  let polymorphic : InductiveType := {
    name := `IndexPrefixPolymorphic,
    type := .forallE `carrier (.sort universeLevel)
      (delay (.forallE `value (.bvar 0) (.sort universeLevel) .default) 2) .implicit,
    ctors := [⟨`IndexPrefixPolymorphic.mk, .forallE `carrier (.sort universeLevel)
      (.forallE `value (.bvar 0) (mkAppN (.const `IndexPrefixPolymorphic [universeLevel])
        #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[polymorphic] 1 [`universe]
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  unless changes > 0 do throwError "index-parameter controls never changed a parameter-opening normal form"
  unless rejected > 0 do throwError "index-parameter controls never rejected incompatible free-variable arguments"
  logInfo m!"{outcomes} index-parameter controls passed both safeties and primitive modes in initial and reached actual motive readers; {changes} parameter-opening WHNF changes; {rejected} unchecked wrong-domain all-free-variable parameter traversals reject typed application eligibility; exact remaining fuel, index arrays, name generators, every local declaration, residual typehood and saturated parent application typing agree; unchecked incomplete prefixes retain no accepted eligibility; runtime controls do not fabricate semantic contexts"

end InductiveRecursorIndexParametersTest
