import Lean4Lean.Verify.InductiveHeaderTelescopeTransport
namespace InductiveHeaderTelescopeTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams) (state : TypeChecker.State)
    (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeInferMethodCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferType' expression inferOnly actualMethods)
      (TypeChecker.Inner.inferType' expression inferOnly shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.inferType'.headerAxiomMethodTransport _ _ _ _ agreement locals safety parameters _ _ _ callbacks

private def sortType : Expr := .sort (.succ .zero)

private def natural : Expr := .const ``Nat []

private def terminal : Expr := .const `TelescopeTerminal []

private def sortAlias : Expr := .const `TelescopeSortAlias []

private def valueType : Expr := .const `TelescopeValueType []

private def number (value : Nat) : Expr := .lit (.natVal value)

private def beta (value : Expr) : Expr := .app (.lam `beta natural (.bvar 0) .default) value

private def sameState (first second : TypeChecker.State) : Bool :=
  first.ngen.namePrefix == second.ngen.namePrefix && first.ngen.idx == second.ngen.idx &&
    first.inferTypeI.toList == second.inferTypeI.toList && first.inferTypeC.toList == second.inferTypeC.toList &&
    first.whnfCoreCache.toList == second.whnfCoreCache.toList && first.whnfCache.toList == second.whnfCache.toList &&
    first.eqvManager.toNodeMap.toList == second.eqvManager.toNodeMap.toList &&
    (first.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) ==
      (second.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) &&
    first.failure.toList == second.failure.toList && first.unfold.toList == second.unfold.toList

private def seededState : TypeChecker.State :=
  let (_, manager) := EquivManager.toNode natural {}
  { ngen := { namePrefix := `_telescope_seed, idx := 47 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert sortAlias sortType }

private def step {resultType : Type} (input : Expr) (value : resultType) : TypeChecker.M resultType := fun context state =>
  let marker := .const (Name.num `_telescope_step state.ngen.idx) []
  let trace := mkAppN (.const `TelescopeTrace []) #[input, number context.lctx.numIndices]
  let (_, manager) := state.eqvManager.toNode marker
  .ok (value, { state with
    ngen := state.ngen.next
    inferTypeI := state.inferTypeI.insert marker trace
    inferTypeC := state.inferTypeC.insert marker trace
    whnfCoreCache := state.whnfCoreCache.insert marker input
    whnfCache := state.whnfCache.insert marker input
    eqvManager := manager
    failure := state.failure.insert (input, marker)
    unfold := state.unfold.insert marker trace })

private def methods (terminalType : Expr) (normalize : Bool) (equal := true) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    inferType := fun expression _ context state =>
      if expression.hasLooseBVars || (expression.isFVar && !context.lctx.containsFVar expression) then
        .error (.other "telescope callback received unopened input")
      else step expression
        (if expression == terminal then terminalType else if expression.isLit then valueType
          else if normalize then sortAlias else sortType) context state
    whnf := fun expression => step expression (if expression == sortAlias then sortType else expression)
    isDefEqCore := fun first second => step (.app first second) equal }

private def unreachedNormalization (_ : Expr) : TypeChecker.M Expr :=
  throw (.other "unreached normalization callback")

private def checkResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State))
    (expected : Expr) (state : TypeChecker.State) (calls : Nat) : MetaM TypeChecker.State := do
  let .ok (first, firstState) := actual | throwError "native telescope rejected expected result {repr expected}"
  let .ok (second, secondState) := shadow | throwError "shadow telescope rejected accepted result"
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "telescope changed result or complete state: {repr first}, {repr second}, expected {repr expected}"
  unless firstState.ngen.idx == state.ngen.idx + calls do
    throwError "telescope reached incorrect callback/allocation count: {firstState.ngen.idx}, expected {state.ngen.idx + calls}"
  return firstState

private def checkAllocation (context : TypeChecker.Context) (state : TypeChecker.State) (letBinder : Bool) : MetaM Unit := do
  let expected := .fvar ⟨state.ngen.curr⟩
  let allocation : TypeChecker.RecM Expr :=
    let continuation := fun fresh => do
      let opened ← readThe TypeChecker.Context
      let some declaration := opened.lctx.findFVar? fresh | throw (.other "allocated local missing")
      unless fresh == expected && declaration.type == natural && declaration.userName == `allocated &&
          opened.lctx.numIndices == context.lctx.numIndices + 1 &&
          opened.eagerReduce == context.eagerReduce && opened.safety == context.safety && opened.lparams == context.lparams do
        throw (.other "allocation changed reader or fresh name")
      if letBinder then
        let .ldecl _ _ _ _ value nondependent _ := declaration | throw (.other "let allocation became local declaration")
        unless value == number 4 && !nondependent do throw (.other "let allocation changed value or nondependent flag")
      else
        let .cdecl _ _ _ _ binder _ := declaration | throw (.other "local allocation became let declaration")
        unless binder == .implicit do throw (.other "local allocation changed binder info")
      step fresh fresh
    if letBinder then withLetDecl `allocated natural (number 4) continuation
    else withLocalDecl `allocated .implicit natural continuation
  let action : TypeChecker.RecM Expr := do
    let fresh ← allocation
    let restored ← readThe TypeChecker.Context
    unless restored.lctx.numIndices == context.lctx.numIndices && !restored.lctx.containsFVar fresh do
      throw (.other "allocation leaked scoped reader")
    return fresh
  let result := action (TypeChecker.Methods.withFuel 0) context state
  let _ ← checkResult result result expected state 2

private def checkSynthetic (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let lambda := .lam `first natural (.lam `second (.bvar 0) terminal .implicit) .default
  let lambdaType := .forallE `first natural (.forallE `second (.bvar 0) natural .implicit) .default
  let forallType := .forallE `first natural (.forallE `second (.bvar 0) terminal .implicit) .default
  let letType := .letE `first natural (number 4) (.letE `second (.bvar 0) (.bvar 0) terminal true) true
  for inferOnly in [false, true] do
    for normalize in [false, true] do
      let domainCalls := if inferOnly then 0 else if normalize then 2 else 1
      let callbacks := methods (beta natural) normalize
      let alternate := { callbacks with
        inferType := fun expression mode =>
          if inferOnly && expression != terminal then throw (.other "unreached lambda domain inference")
          else callbacks.inferType expression mode
        whnf := if inferOnly || !normalize then unreachedNormalization else callbacks.whnf
        whnfCore := fun expression _ _ => step expression expression }
      let _ ← checkResult (TypeChecker.Inner.inferLambda terminal inferOnly callbacks actual state)
        (TypeChecker.Inner.inferLambda terminal inferOnly alternate shadow state) natural state 1
      let finalState ← checkResult (TypeChecker.Inner.inferLambda lambda inferOnly callbacks actual state)
        (TypeChecker.Inner.inferLambda lambda inferOnly alternate shadow state) lambdaType state (2 * domainCalls + 3)
      unless inferOnly do
        let firstId := Name.num state.ngen.namePrefix (state.ngen.idx + domainCalls)
        let secondDomainIndex := state.ngen.idx + domainCalls + 1
        let marker : Expr := .const (Name.num `_telescope_step secondDomainIndex) []
        unless finalState.whnfCoreCache[marker]? == some (.fvar ⟨firstId⟩) do
          throwError "lambda second domain was not instantiated with post-check fresh name"
      let forallCallbacks := methods (if normalize then sortAlias else sortType) normalize
      let forallAlternate := { forallCallbacks with
        whnf := if normalize then forallCallbacks.whnf else unreachedNormalization
        whnfCore := fun expression _ _ => step expression natural }
      let resultLevel := mkLevelIMax' (.succ .zero) (mkLevelIMax' (.succ .zero) (.succ .zero))
      let _ ← checkResult (TypeChecker.Inner.inferForall terminal inferOnly forallCallbacks actual state)
        (TypeChecker.Inner.inferForall terminal inferOnly forallAlternate shadow state) sortType state (if normalize then 2 else 1)
      let _ ← checkResult (TypeChecker.Inner.inferForall forallType inferOnly forallCallbacks actual state)
        (TypeChecker.Inner.inferForall forallType inferOnly forallAlternate shadow state) (.sort resultLevel)
        state (if normalize then 8 else 5)
      let letCalls := if inferOnly then 0 else if normalize then 4 else 3
      let firstId := Name.num state.ngen.namePrefix (state.ngen.idx + letCalls)
      for retain in [false, true] do
        let terminalType := if retain then .fvar ⟨firstId⟩ else natural
        let expected := if retain then .letE `first natural (number 4) (.bvar 0) false else natural
        let letCallbacks := methods (beta terminalType) normalize
        let letAlternate := { letCallbacks with
          inferType := fun expression mode =>
            if inferOnly && expression != terminal then throw (.other "unreached let checking inference")
            else letCallbacks.inferType expression mode
          whnf := if inferOnly || !normalize then unreachedNormalization else letCallbacks.whnf
          isDefEqCore := if inferOnly then fun _ _ => throw (.other "unreached let comparison") else letCallbacks.isDefEqCore
          whnfCore := fun expression _ _ => step expression sortAlias }
        let letState ← checkResult (TypeChecker.Inner.inferLet letType inferOnly letCallbacks actual state)
          (TypeChecker.Inner.inferLet letType inferOnly letAlternate shadow state) expected state (2 * letCalls + 3)
        unless inferOnly do
          let expectedManager := letState.eqvManager.addEquiv valueType natural
          unless expectedManager.toNodeMap.toList == letState.eqvManager.toNodeMap.toList &&
              (expectedManager.uf.arr.map fun node => (node.parent, node.rank)) ==
                (letState.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) do
            throwError "let comparison lost native equivalence-manager insertion"
        unless retain do
          let _ ← checkResult (TypeChecker.Inner.inferLet terminal inferOnly letCallbacks actual state)
            (TypeChecker.Inner.inferLet terminal inferOnly letAlternate shadow state) natural state 1
    let variableBody := .lam `argument natural (.bvar 0) .default
    let callbacks := methods natural false
    let _ ← checkResult (TypeChecker.Inner.inferLambda variableBody inferOnly callbacks actual state)
      (TypeChecker.Inner.inferLambda variableBody inferOnly callbacks shadow state)
      (.forallE `argument natural sortType .default) state (if inferOnly then 2 else 3)
  let rejecting := methods natural false false
  let accepting := methods natural false true
  unless !(TypeChecker.Inner.inferLet letType false rejecting actual state).isOk &&
      (TypeChecker.Inner.inferLet letType false accepting shadow state).isOk &&
      (TypeChecker.Inner.inferLet letType true rejecting actual state).isOk do
    throwError "let checked comparison control lost reached-mode distinction"
  let badDomain := { accepting with inferType := fun _ _ => step natural natural }
  unless !(TypeChecker.Inner.inferLambda lambda false badDomain actual state).isOk &&
      (TypeChecker.Inner.inferLambda lambda true badDomain actual state).isOk &&
      !(TypeChecker.Inner.inferForall forallType true badDomain actual state).isOk &&
      !(TypeChecker.Inner.inferLet letType false badDomain actual state).isOk &&
      (TypeChecker.Inner.inferLet letType true badDomain actual state).isOk do
    throwError "telescope sort checking ran in wrong inference mode"
  let variableForall := .forallE `argument natural (.bvar 0) .default
  let wrongTerminal := { accepting with
    inferType := fun expression _ => step expression (if expression == natural then sortType else natural) }
  let .error (.typeExpected _ localContext source) := TypeChecker.Inner.inferForall variableForall true wrongTerminal actual state |
    throwError "forall terminal did not reject an unsorted inferred body type"
  unless source == .bvar 0 && localContext.numIndices == actual.lctx.numIndices + 1 do
    throwError "forall terminal changed native uninstantiated error source or reached local reader"

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (parent : Name) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 1000
  let alternate := TypeChecker.Methods.withFuel 1001
  let lambda := .lam `argument natural (.bvar 0) .implicit
  let lambdaType := .forallE `argument natural natural .implicit
  let forallType := .forallE `argument natural natural .default
  let letType := .letE `value natural (number 4) (.bvar 0) true
  let dependentLet := .letE `type sortType natural (.lam `argument (.bvar 0) (.bvar 0) .default) true
  let dependentType := .letE `type sortType natural (.forallE `argument (.bvar 0) (.bvar 1) .default) false
  let parentType := .const parent []
  let parentLambda := .lam `argument parentType (.bvar 0) .default
  let parentForall := .forallE `argument parentType parentType .default
  let parentLet := .letE `value parentType (.fvar ⟨`TelescopeHeaderWitness⟩) (.bvar 0) true
  let cases := [(TypeChecker.Inner.inferLambda, lambda, lambdaType),
    (TypeChecker.Inner.inferForall, forallType, sortType),
    (TypeChecker.Inner.inferLet, letType, natural), (TypeChecker.Inner.inferLet, dependentLet, dependentType),
    (TypeChecker.Inner.inferLambda, parentLambda, parentForall),
    (TypeChecker.Inner.inferForall, parentForall, sortType), (TypeChecker.Inner.inferLet, parentLet, parentType)]
  for inferOnly in [false, true] do
    for (helper, expression, expected) in cases do
      let first := helper expression inferOnly callbacks actual state
      let second := helper expression inferOnly alternate shadow state
      let .ok (_, finalState) := first | throwError "native methods rejected telescope"
      let _ ← checkResult first second expected state (finalState.ngen.idx - state.ngen.idx)
      let firstEntry := TypeChecker.Inner.inferType' expression inferOnly callbacks actual state
      let secondEntry := TypeChecker.Inner.inferType' expression inferOnly alternate shadow state
      let .ok (_, entryState) := firstEntry | throwError "native inference entry rejected telescope"
      let _ ← checkResult firstEntry secondEntry expected state (entryState.ngen.idx - state.ngen.idx)

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType) : MetaM Unit := do
  for isUnsafe in [false, true] do
    unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected telescope header fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "telescope header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView environment headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "telescope checkpoint lost constructor acceptance"
      let outer := (LocalContext.empty.mkLocalDecl ⟨`TelescopeOuter⟩ `outer natural .default).mkLocalDecl
        ⟨`TelescopeHeaderWitness⟩ `witness (.const types[0]!.name []) .default
      let actualReader : TypeChecker.Context :=
        { env := actual, lctx := outer, safety := reader.safety, eagerReduce := true, lparams := [`TelescopeUniverse], fuel := { whnf := 8 } }
      let shadowReader := { actualReader with env := shadow, eagerReduce := false, fuel := { whnf := 12, recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        for letBinder in [false, true] do
          checkAllocation actualReader state letBinder
          checkAllocation shadowReader state letBinder
        checkSynthetic actualReader shadowReader state
        checkNative actualReader shadowReader state types[0]!.name

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderTelescopeTransport |
    throwError "telescope transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "telescope transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "telescope transport unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native telescope transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `TelescopeSingle]
  checkBatch host environment #[family `TelescopeFirstFamily, family `TelescopeSecondFamily]
  logInfo "native telescope allocation, reached callbacks, sort gates, comparison, closure and restoration passed"

end InductiveHeaderTelescopeTransportTest
