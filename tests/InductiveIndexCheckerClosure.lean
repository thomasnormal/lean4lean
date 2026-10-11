import Lean4Lean.Verify.InductiveIndexCheckerClosure
import Lean.Util.CollectAxioms

namespace InductiveIndexCheckerClosureTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

example {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic) :
    TrEnv finalChecker.safety finalChecker.env checker.venv := by
  simpa only [endpoint.checkerContext.1] using finalChecker.trenv

example
    {environment : VEnv} {universes : List Name} {virtual : VLCtx} {reader : Context}
    {name : Name} {domain body : Expr} {binder : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (correspondence : TrLCtx environment universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS environment universes virtual (.forallE name domain body binder)
      (.forallE semantic bodySemantic))
    (domainTyped : environment.HasType universes.length virtual.toCtx semantic (.sort level)) :
    ∃ peeled, PeeledIndexOpening environment universes reader virtual name domain body binder
      semantic bodySemantic level peeled := by
  apply translatedForallIndexOpening_unrestricted <;> assumption

example
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (indexOnly : stats.params.size ≤ index)
    (translated : checker.TrExprS source semantic) :
    ∃ (finalChecker : TypeChecker.VContext) (finalSemantic : VExpr) (identifiers : List FVarId),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      IndexMLCtxExtension checker.mlctx identifiers finalChecker.mlctx ∧
      finalIndices.toList = indices.toList ++ identifiers.map Expr.fvar ∧
      TranslatedRecursorIndexTrace checker.venv checker.lparams trace checker.vlctx semantic
        finalChecker.vlctx finalSemantic := by
  apply RecursorIndexTrace.checkedIndexModels <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic) :
    HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace
      checker.mlctx finalChecker.mlctx semantic resultSemantic := by
  exact endpoint.model

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic) :
    finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker := by
  exact endpoint.checkerContext

example
    {stats : InductiveStats} {source headerSource terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats headerSource)
    (normalized : (monadLift (TypeChecker.whnf headerSource) : M Expr) reader = .ok source) :
    ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result := by
  apply RecursorIndexTrace.headerCheckedModels <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic) :
    ∃ finalValue terminalSemantic,
      finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType finalValue terminalSemantic := by
  apply HeaderRecursorIndexCheckerEndpoint.applicationOfPartial <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic) (sorted : terminal.isSort = true) :
    ∃ finalValue, finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.IsType finalValue := by
  apply HeaderRecursorIndexCheckerEndpoint.parentTypehoodOfPartial <;> assumption

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
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        ∃ value terminalSemantic,
          finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType value terminalSemantic := by
  apply RecursorIndexTrace.checkedHeaderBatch <;> assumption

example {resultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat) (bound : parent < types.size)
    (source : Expr) (fuel : Nat) (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current)
      (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type)
      finalChecker,
      HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result →
      (∃ value terminalSemantic,
        finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
        finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType value terminalSemantic) →
      (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post := by
  apply mkRecInfos.loopArgs1.checkedHeaderBatchTrace <;> assumption

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def annotationDomain (mode : Nat) (carrier : Expr) : Expr :=
  let equivalent := Level.max .zero (.succ .zero)
  let nested := Expr.app (.const ``outParam [equivalent]) (.app (.const ``semiOutParam [.succ .zero]) carrier)
  if mode == 1 then nested
  else if mode == 2 then .app (.app (.const ``optParam [equivalent]) nested) (.lit (.natVal 0))
  else if mode == 3 then .app (.app (.const ``autoParam [equivalent]) nested) (.const ``Lean.Syntax.missing [])
  else if mode == 4 then .mdata {} nested
  else carrier

private theorem nonuniformDomain (level : VLevel) :
    ¬ UniformAnnotationUniverse [] (annotationDomain 1 natural) level := by
  intro uniform
  cases level <;> simp [annotationDomain, natural, UniformAnnotationUniverse, VLevel.ofLevel] at uniform

example {environment : VEnv} {virtual : VLCtx} {reader : Context}
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (correspondence : TrLCtx environment [] reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS environment [] virtual (.forallE name (annotationDomain 1 natural) body binder)
      (.forallE semantic bodySemantic))
    (domainTyped : environment.HasType 0 virtual.toCtx semantic (.sort level)) :
    ∃ peeled, PeeledIndexOpening environment [] reader virtual name (annotationDomain 1 natural) body binder
      semantic bodySemantic level peeled :=
  translatedForallIndexOpening_unrestricted environmentWF constants definitions correspondence reserved translated domainTyped

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters indices mode : Nat) (dependent : Bool := false)
    (levels : List Level := []) (annotationMode : Nat := 0) : InductiveType :=
  let parameterLevel := levels.headD (.succ .zero)
  let resultLevel := levels.foldl Level.max (.succ .zero)
  let suffix := fun body => (List.range indices).foldr
    (fun _ body => .forallE `index (annotationDomain annotationMode natural) body .default) body
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

private def dependentIndices (name : Name) (parameters : Nat) : InductiveType :=
  let close := fun annotated body =>
    let body := .forallE `indexType sortType (.forallE `indexValue
      (if annotated then annotationDomain 1 (.bvar 0) else .bvar 0) body .default) .implicit
    (List.range parameters).foldr (fun _ body => .forallE `carrier sortType body .implicit) body
  let arguments := (List.range (parameters + 2)).toArray.map fun index => Expr.bvar (parameters + 1 - index)
  { name, type := close true (.sort (.succ (.succ .zero))),
    ctors := [⟨name ++ `mk, close false (mkAppN (.const name []) arguments)⟩] }

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

private def consumeIndices (source : Expr) (arguments : List Expr) (reader : Context) :
    Except Kernel.Exception (Expr × Nat) := do
  match arguments with
  | [] => return (source, 0)
  | argument :: remaining =>
    let .forallE _ domain body _ := source | throw .deepRecursion
    let .fvar identifier := argument | throw .deepRecursion
    let some declaration := reader.lctx.find? identifier | throw .deepRecursion
    unless declaration.type == peelTypeAnnotations domain do throw .deepRecursion
    let normalized ← (monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) reader
    let (terminal, changes) ← consumeIndices normalized remaining reader
    return (terminal, changes + if domain == peelTypeAnnotations domain then 0 else 1)

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat) (originalUniverses : List Name := []) :
    MetaM (Nat × Nat × Nat × Nat × Nat) := do
  let host ← getEnv
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  let mut peeled := 0
  let elimination := `freshElimination
  for isUnsafe in [false, true] do
    unless (host.addDeclCore 0 (.inductDecl originalUniverses parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected index checker closure controls {types.map (·.name)}"
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
        | throwError "index checker closure parameter registration checkpoint failed"
      let .ok final := run parameters types.toList 0 reader | throwError "index checker closure complete run failed"
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
            if ({} : TypeChecker.State).ngen.namePrefix == reached.ngen.namePrefix then
              throwError "index checker closure actual reader aliases the reset checker namespace"
            for parent in [:types.size] do
              let source := types[parent]!.type
              let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
                | throwError "index checker closure original header WHNF failed"
              let .ok (residual, changes) := consumeParameters stats normalized reached
                | throwError "index checker closure accepted parameters failed normalized consumption"
              let partialParent := mkAppN stats.indConsts[parent]! stats.params
              let .ok inferred := (monadLift (TypeChecker.checkType partialParent) : M Expr) reached
                | throwError "index checker closure partial parent failed genuine domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
                | throwError "index checker closure normalized partial-parent residual mismatch"
              let .ok residualKind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
                | throwError "index checker closure normalized residual strict checking failed"
              unless ((monadLift (TypeChecker.ensureSort residualKind) : M Expr) reached).isOk do
                throwError "index checker closure normalized residual is not a type"
              let capture := fun indices => do return (indices, ← readThe Context)
              let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[]
                  reached.fuel.inductiveFuel capture reached
                | throwError "index checker closure actual binder loop failed"
              let .ok (suffixIndices, suffixReader) := mkRecInfos.loopArgs1 stats residual stats.params.size #[]
                  (reached.fuel.inductiveFuel - stats.params.size) capture reached
                | throwError "index checker closure exact remaining-fuel suffix failed"
              unless indices == suffixIndices && finalReader.ngen == suffixReader.ngen &&
                  localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
                throwError "index checker closure parameter prefix changed actual index context"
              let .ok (terminal, peelings) := consumeIndices residual indices.toList finalReader
                | throwError "index checker closure selected indices failed normalized consumption"
              unless terminal.isSort do throwError "index checker closure accepted terminal is not a sort"
              let .ok appliedType := (monadLift (TypeChecker.checkType (mkAppN partialParent indices)) : M Expr) finalReader
                | throwError "index checker closure full parent application failed genuine index-domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq appliedType terminal) : M Bool) finalReader
                | throwError "index checker closure full application differs from actual normalized terminal"
              unless ((monadLift (TypeChecker.ensureSort appliedType) : M Expr) finalReader).isOk do
                throwError "index checker closure full parent is not a type"
              passed := passed + 1
              peeled := peeled + peelings
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
  return (passed, changed, rejected, initialChanges, peeled)

private def rejectionControls : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let mut rejected := 0
  let mut nativeRejected := 0
  let mut stopped := 0
  for isUnsafe in [false, true] do
    for source in [
        .forallE `index (.app (.const ``outParam []) natural) sortType .default,
        .forallE `index (.app (.app (.const ``optParam [.succ .zero]) natural) sortType) sortType .default,
        .forallE `index (.app (.app (.const ``autoParam [.succ .zero]) natural) (.lit (.natVal 0))) sortType .default,
        natural] do
      let types : Array InductiveType := #[{ name := `IndexCheckerRejected, type := source, ctors := [] }]
      if (host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none).isOk then
        throwError "native kernel accepted malformed annotation or nonsort header"
      nativeRejected := nativeRejected + 1
      for allowPrimitive in [false, true] do
        let reader : Context := {
          env := host.toKernelEnv, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
        if (checkInductiveTypes 0 types (fun _ => pure ()) reader).isOk ||
            (run 0 types.toList 0 reader).isOk then
          throwError "malformed annotation or nonsort header acquired accepted eligibility"
        rejected := rejected + 1
        if source == natural then
          unless ((monadLift (TypeChecker.checkType source) : M Expr) reader).isOk do
            throwError "unchecked nonsort terminal lost its genuine source typehood"
          let stats : InductiveStats := {
            levels := [], resultLevel := .zero, indConsts := #[], params := #[], isNotZero := false }
          let .ok indices := mkRecInfos.loopArgs1 stats source 0 #[] reader.fuel.inductiveFuel pure reader
            | throwError "unchecked nonsort terminal no longer stops the native binder loop"
          unless indices.isEmpty do throwError "unchecked nonsort terminal unexpectedly allocated indices"
          if ((monadLift (TypeChecker.ensureSort source) : M Expr) reader).isOk then
            throwError "source typehood plus stopped traversal manufactured terminal-sort eligibility"
          stopped := stopped + 1
  return (rejected, nativeRejected, stopped)

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexCheckerClosure
    | throwError "index checker closure module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``TrExprS.peeledAnonymousBodyTranslation, ``translatedHeaderOpeningWithSemantics,
      ``acceptedHeaderNormalization, ``IndexMLCtxExtension.trans,
      ``RecursorIndexTrace.headerApplicationsOfChecker, ``RecursorIndexTrace.applicationOfHeaderBatch,
      ``HeaderRecursorIndexModelEndpoint.parentTypehoodOfPartial,
      ``mkRecInfos.loopArgs1.scopedTrace, ``RecursorIndexTrace.completeParameters] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index checker closure owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "index checker closure unexpected {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      count := count + 1
  logInfo m!"index checker closure: {count} exhaustive owned declarations audited against genuine prior foundations"

run_meta
  auditModule
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  let mut peeled := 0
  for (types, parameters, universes) in [
      (#[family `IndexCheckerZero 0 0 0], 0, []),
      (#[family `IndexCheckerZeroLet 0 1 1], 0, []),
      (#[family `IndexCheckerZeroBeta 0 2 2], 0, []),
      (#[family `IndexCheckerZeroMetadata 0 1 3], 0, []),
      (#[family `IndexCheckerOne 1 1 0], 1, []),
      (#[family `IndexCheckerTwoLet 2 2 1], 2, []),
      (#[family `IndexCheckerTwoBeta 2 1 2], 2, []),
      (#[family `IndexCheckerTwoMetadata 2 2 3], 2, []),
      (#[family `IndexCheckerDependent 2 1 1 true], 2, []),
      (#[family `IndexCheckerMutualFirst 2 1 1 true, family `IndexCheckerMutualSecond 2 2 2 true], 2, []),
      (#[family `IndexCheckerUniverse 2 2 1 true [.param `universe]], 2, [`universe]),
      (#[family `IndexCheckerReordered 2 1 2 true [.param `universe, .param `otherUniverse]],
        2, [`universe, `otherUniverse]),
      (#[family `IndexCheckerNonuniform 0 2 0 false [] 1], 0, []),
      (#[family `IndexCheckerOptional 1 1 1 false [] 2], 1, []),
      (#[family `IndexCheckerAutomatic 2 2 2 true [] 3], 2, []),
      (#[family `IndexCheckerMetadataBarrier 2 1 3 true [] 4], 2, []),
      (#[family `IndexCheckerMutualAnnotatedFirst 2 1 1 true [] 1,
          family `IndexCheckerMutualAnnotatedSecond 2 2 2 true [] 2], 2, []),
      (#[dependentIndices `IndexCheckerDependentIndicesZero 0], 0, []),
      (#[dependentIndices `IndexCheckerDependentIndicesTwo 2], 2, [])] do
    let (accepted, conversions, failed, initial, peelings) ← checkBatch types parameters universes
    passed := passed + accepted
    changed := changed + conversions
    rejected := rejected + failed
    initialChanges := initialChanges + initial
    peeled := peeled + peelings
  unless changed > 0 && initialChanges > 0 && rejected > 0 && peeled > 0 do
    throwError "index checker closure controls missed conversions, zero-parameter input normalization, or rejection"
  let (malformed, nativeMalformed, nonsort) ← rejectionControls
  logInfo m!"{passed} actual normalized index checker closure applications passed; {changed} parameter-opening WHNF changes, {initialChanges} original-header changes, {peeled} actually peeled stored index domains and {rejected} unchecked wrong-domain free-variable arrays rejected; {malformed} malformed/nonsort header controls and {nativeMalformed} corresponding native declarations rejected; {nonsort} genuinely type-valued unchecked stopped traversals retain no terminal-sort eligibility; zero/one/two/dependent parameters, differing mutual index counts, original/fresh/reordered universes, registered/full-run environments, original/local/let contexts, both safeties/primitive modes, let/beta/metadata wrappers, nonuniform nested outParam/semiOutParam/optParam/autoParam chains, metadata barriers and dependent index domains checked; exact remaining fuel, index arrays, name generators, local declarations, residual and full-application typehood agree; runtime controls do not fabricate semantic contexts"

end InductiveIndexCheckerClosureTest
