import Lean4Lean.Verify.InductiveHeaderComparisonHelperTransport

namespace InductiveHeaderComparisonHelperTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

deriving instance Repr for Lean.LBool

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.tryEtaStructCore first second actualMethods)
      (TypeChecker.Inner.tryEtaStructCore first second shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.tryEtaStructCore.transport _ _ _ _ agreement _ _ _ callbacks

example (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (headers : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : ConstructorsFresh actual types) (parent : Name) :
    Except.SuccessTransport (nativeUnitLikeMetadata actual parent) (nativeUnitLikeMetadata shadow parent) :=
  nativeUnitLikeMetadata.transport agreement parent (NativeProjectionMetadataFrame.ofConstructorFreshness agreement headers fresh parent)

private def natural : Expr := .const ``Nat []

private def sortType : Expr := .sort (.succ .zero)

private def firstSource : Expr := .fvar ⟨`HelperFirstSource⟩

private def secondSource : Expr := .fvar ⟨`HelperSecondSource⟩

private def firstType : Expr := .const `HelperFirstType []

private def secondType : Expr := .const `HelperSecondType []

private def typeAlias : Expr := .const `HelperTypeAlias []

private def number (value : Nat) : Expr := .lit (.natVal value)

private def marker (index : Nat) : Expr := .const (Name.num `_comparison_helper_step index) []

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
  { ngen := { namePrefix := `_comparison_helper_seed, idx := 97 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert typeAlias sortType }

private def trace (input : Expr) (context : TypeChecker.Context) : Expr :=
  mkAppN (.const `HelperTrace []) #[input, number context.lctx.numIndices]

private def step {resultType : Type} (input : Expr) (value : resultType) : TypeChecker.M resultType := fun context state =>
  let key := marker state.ngen.idx
  let receipt := trace input context
  let (_, manager) := state.eqvManager.toNode key
  .ok (value, { state with
    ngen := state.ngen.next
    inferTypeI := state.inferTypeI.insert key receipt
    inferTypeC := state.inferTypeC.insert key receipt
    whnfCoreCache := state.whnfCoreCache.insert key input
    whnfCache := state.whnfCache.insert key input
    eqvManager := manager
    failure := state.failure.insert (input, key)
    unfold := state.unfold.insert key receipt })

private def methods (first second firstResult secondResult : Expr) (propositional := true)
    (reject : Option (Expr × Expr) := none) (normalized : Expr := typeAlias) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    inferType := fun expression inferOnly =>
      if !inferOnly then throw (.other "unreached checked inference")
      else if expression == first then step expression firstResult
      else if expression == second then step expression secondResult
      else if expression == firstResult then step expression (.sort (if propositional then .zero else .succ .zero))
      else throw (.other "unreached inference input")
    whnf := fun expression => step expression (if expression == typeAlias then normalized else expression)
    isDefEqCore := fun first second => step (.app first second) (reject != some (first, second)) }

private def checkResult [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State))
    (expected : resultType) (state : TypeChecker.State) (calls : Nat) : MetaM TypeChecker.State := do
  let (first, firstState) ← ofExceptKernelException actual
  let (second, secondState) ← ofExceptKernelException shadow
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "comparison helper changed result or complete state: {repr first}, {repr second}, expected {repr expected}"
  unless firstState.ngen.idx == state.ngen.idx + calls do
    throwError "comparison helper callback count: {firstState.ngen.idx}, expected {state.ngen.idx + calls}"
  return firstState

private def checkTrace (state : TypeChecker.State) (index : Nat) (input : Expr) (context : TypeChecker.Context) : MetaM Unit := do
  unless state.inferTypeI[marker index]? == some (trace input context) do
    throwError "comparison helper changed reached input, order or reader at {index}"

private def checkScripts (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let unusable := TypeChecker.Methods.withFuel 0
  let lambda := .lam `argument natural (.bvar 0) .implicit
  let functionType := .forallE `etaArgument natural natural .strictImplicit
  let eta :=
    { methods lambda secondSource sortType typeAlias true none functionType with
      isDefEqCore := fun original proposed =>
        match proposed with
        | .lam name domain body binder =>
          if original == lambda && name == `etaArgument && domain == natural &&
              body == .app secondSource (.bvar 0) && binder == .strictImplicit then step (.app original proposed) true
          else throw (.other "eta callback changed the generated lambda metadata")
        | _ => throw (.other "eta callback did not receive a lambda") }
  let expanded := .lam `etaArgument natural (.app secondSource (.bvar 0)) .strictImplicit
  let returned ← checkResult (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource eta actual state)
    (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource eta shadow state) true state 3
  checkTrace returned state.ngen.idx secondSource actual
  checkTrace returned (state.ngen.idx + 1) typeAlias actual
  checkTrace returned (state.ngen.idx + 2) (.app lambda expanded) actual
  unless (returned.eqvManager.isEquiv false lambda expanded).1 do throwError "eta comparison lost equivalence insertion"
  let direct := methods lambda secondSource sortType functionType
  let _ ← checkResult (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource direct actual state)
    (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource direct shadow state) true state 3
  let nonfunction := methods lambda secondSource sortType natural
  let _ ← checkResult (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource nonfunction actual state)
    (TypeChecker.Inner.tryEtaExpansionCore lambda secondSource nonfunction shadow state) false state 2
  let etaFalse := methods lambda secondSource sortType typeAlias true (some (lambda, expanded)) functionType
  let _ ← checkResult (TypeChecker.Inner.tryEtaExpansion lambda secondSource etaFalse actual state)
    (TypeChecker.Inner.tryEtaExpansion lambda secondSource etaFalse shadow state) false state 3
  let _ ← checkResult (TypeChecker.Inner.tryEtaExpansion secondSource lambda eta actual state)
    (TypeChecker.Inner.tryEtaExpansion secondSource lambda eta shadow state) true state 3
  for (first, second) in [(firstSource, secondSource), (lambda, lambda)] do
    let _ ← checkResult (TypeChecker.Inner.tryEtaExpansion first second unusable actual state)
      (TypeChecker.Inner.tryEtaExpansion first second unusable shadow state) false state 0
  for equal in [false, true] do
    let rejection := if equal then none else some (firstType, secondType)
    let proof := methods firstSource secondSource firstType secondType true rejection
    let proofResult ← checkResult (TypeChecker.Inner.isDefEqProofIrrel firstSource secondSource proof actual state)
      (TypeChecker.Inner.isDefEqProofIrrel firstSource secondSource proof shadow state) equal.toLBool state 5
    for (offset, input) in [(0, firstSource), (1, firstType), (2, .sort .zero), (3, secondSource), (4, .app firstType secondType)] do
      checkTrace proofResult (state.ngen.idx + offset) input actual
  let nonproof := { methods firstSource secondSource firstType secondType false with
    isDefEqCore := fun _ _ => throw (.other "unreached proof comparison") }
  let _ ← checkResult (TypeChecker.Inner.isDefEqProofIrrel firstSource secondSource nonproof actual state)
    (TypeChecker.Inner.isDefEqProofIrrel firstSource secondSource nonproof shadow state) LBool.undef state 3
  let raw := { unusable with isDefEqCore := fun first second => step (.app first second) true }
  for (first, second, expected, calls) in [(Expr.natZero, number 0, LBool.true, 0), (number 0, number 4, .undef, 0),
      (number 3, .app (.const ``Nat.succ []) (number 4), .true, 1), (firstSource, secondSource, .undef, 0)] do
    let offset ← checkResult (TypeChecker.Inner.isDefEqOffset first second raw actual state)
      (TypeChecker.Inner.isDefEqOffset first second raw shadow state) expected state calls
    if calls == 1 then
      checkTrace offset state.ngen.idx (.app (number 2) (number 4)) actual
      unless !(offset.eqvManager.isEquiv false (number 2) (number 4)).1 do throwError "offset unexpectedly inserted an equivalence"
  let rawFalse := { unusable with isDefEqCore := fun first second => step (.app first second) false }
  let _ ← checkResult (TypeChecker.Inner.isDefEqOffset (number 3) (number 4) rawFalse actual state)
    (TypeChecker.Inner.isDefEqOffset (number 3) (number 4) rawFalse shadow state) LBool.false state 1
  for text in ["", "hello", "λ🦀"] do
    let literal := .lit (.strVal text)
    let constructor := .app (.const ``String.ofList []) secondSource
    for equal in [false, true] do
      let callbacks := if equal then raw else rawFalse
      let converted ← checkResult (TypeChecker.Inner.tryStringLitExpansionCore literal constructor callbacks actual state)
        (TypeChecker.Inner.tryStringLitExpansionCore literal constructor callbacks shadow state) equal.toLBool state 1
      checkTrace converted state.ngen.idx (.app (.strLitToConstructor text) constructor) actual
      unless !(converted.eqvManager.isEquiv false (.strLitToConstructor text) constructor).1 do
        throwError "string expansion unexpectedly inserted an equivalence"
      let _ ← checkResult (TypeChecker.Inner.tryStringLitExpansion constructor literal callbacks actual state)
        (TypeChecker.Inner.tryStringLitExpansion constructor literal callbacks shadow state) equal.toLBool state 1
    for invalid in [secondSource, .app (.const ``String.ofList [.zero]) secondSource, .app constructor secondSource] do
      let _ ← checkResult (TypeChecker.Inner.tryStringLitExpansion literal invalid unusable actual state)
        (TypeChecker.Inner.tryStringLitExpansion literal invalid unusable shadow state) LBool.undef state 0
  let productType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let constructor := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, number 3, number 4]
  for (reject, expected, calls) in [(none, true, 5), (some (productType, productType), false, 3),
      (some (.proj ``Prod 0 firstSource, number 3), false, 4), (some (.proj ``Prod 1 firstSource, number 4), false, 5)] do
    let callbacks := methods firstSource constructor productType productType true reject
    let structureResult ← checkResult (TypeChecker.Inner.tryEtaStructCore firstSource constructor callbacks actual state)
      (TypeChecker.Inner.tryEtaStructCore firstSource constructor callbacks shadow state) expected state calls
    if calls > 3 then checkTrace structureResult (state.ngen.idx + 3) (.app (.proj ``Prod 0 firstSource) (number 3)) actual
    if calls > 4 then checkTrace structureResult (state.ngen.idx + 4) (.app (.proj ``Prod 1 firstSource) (number 4)) actual
  let structureCallbacks := methods firstSource constructor productType productType
  let _ ← checkResult (TypeChecker.Inner.tryEtaStruct constructor firstSource structureCallbacks actual state)
    (TypeChecker.Inner.tryEtaStruct constructor firstSource structureCallbacks shadow state) true state 5
  for invalid in [secondSource, natural, .const ``Prod.mk [.zero, .zero], .app constructor (number 5),
      .app (.const ``Nat.succ []) (number 3)] do
    let _ ← checkResult (TypeChecker.Inner.tryEtaStructCore firstSource invalid unusable actual state)
      (TypeChecker.Inner.tryEtaStructCore firstSource invalid unusable shadow state) false state 0
  let missing := .const `HelperMissingConstructor []
  unless !(TypeChecker.Inner.tryEtaStruct firstSource missing unusable actual state).isOk &&
      !(TypeChecker.Inner.tryEtaStruct firstSource missing unusable shadow state).isOk do
    throwError "symmetric structure eta swallowed a reached constructor lookup error"
  let unitType := .const ``PUnit [.succ .zero]
  let unitConstructor := .const ``PUnit.unit [.succ .zero]
  let unitEta := methods firstSource unitConstructor unitType unitType
  let _ ← checkResult (TypeChecker.Inner.tryEtaStructCore firstSource unitConstructor unitEta actual state)
    (TypeChecker.Inner.tryEtaStructCore firstSource unitConstructor unitEta shadow state) true state 3
  for (type, expected, calls) in [(unitType, true, 4), (natural, false, 2), (.const ``Bool [], false, 2),
      (productType, false, 2), (number 3, false, 2)] do
    let callbacks := methods firstSource secondSource type type
    let unitResult ← checkResult (TypeChecker.Inner.isDefEqUnitLike firstSource secondSource callbacks actual state)
      (TypeChecker.Inner.isDefEqUnitLike firstSource secondSource callbacks shadow state) expected state calls
    if expected then
      unless unitResult.eqvManager.toNodeMap[unitType]? == none do
        throwError "unit-like comparison unexpectedly inserted an equivalence"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 1000
  let alternate := TypeChecker.Methods.withFuel 1001
  let productType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let unitType := .const ``PUnit [.succ .zero]
  let truth := .const ``True []
  let locals := actual.lctx.mkLocalDecl ⟨`HelperPair⟩ `pair productType .default
    |>.mkLocalDecl ⟨`HelperUnitFirst⟩ `unitFirst unitType .default
    |>.mkLocalDecl ⟨`HelperUnitSecond⟩ `unitSecond unitType .default
    |>.mkLocalDecl ⟨`HelperProofFirst⟩ `proofFirst truth .default
    |>.mkLocalDecl ⟨`HelperProofSecond⟩ `proofSecond truth .default
  let actual := { actual with lctx := locals }
  let shadow := { shadow with lctx := locals }
  let source := .fvar ⟨`HelperPair⟩
  let constructor := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, .proj ``Prod 0 source, .proj ``Prod 1 source]
  let function := .const ``Nat.succ []
  let lambda := .lam `argument natural (.app function (.bvar 0)) .default
  let booleanChecks := [(TypeChecker.Inner.tryEtaExpansionCore lambda function, true),
    (TypeChecker.Inner.tryEtaStructCore source constructor, true),
    (TypeChecker.Inner.isDefEqUnitLike (.fvar ⟨`HelperUnitFirst⟩) (.fvar ⟨`HelperUnitSecond⟩), true)]
  for (action, expected) in booleanChecks do
    let .ok (result, finalState) := action callbacks actual state | throwError "native recursive helper rejected"
    let .ok (shadowResult, shadowState) := action alternate shadow state | throwError "shadow recursive helper rejected"
    unless result == expected && shadowResult == expected && sameState finalState shadowState do
      throwError "native recursive Boolean helper changed result or state"
  let text := "λ"
  let literal := .lit (.strVal text)
  let threeChecks := [TypeChecker.Inner.isDefEqProofIrrel (.fvar ⟨`HelperProofFirst⟩) (.fvar ⟨`HelperProofSecond⟩),
    TypeChecker.Inner.isDefEqOffset (number 3) (number 3), TypeChecker.Inner.tryStringLitExpansionCore literal (.strLitToConstructor text)]
  for action in threeChecks do
    let .ok (result, finalState) := action callbacks actual state | throwError "native recursive three-valued helper rejected"
    let .ok (shadowResult, shadowState) := action alternate shadow state | throwError "shadow recursive three-valued helper rejected"
    unless result == LBool.true && shadowResult == LBool.true && sameState finalState shadowState do
      throwError "native recursive three-valued helper changed result or state"

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .forallE `index natural (.app (.const name []) (.bvar 0)) .default⟩] }

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType)
    (indices : Array Expr := #[]) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok nativeHost := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected comparison helper header fixture"
    let parentType := mkAppN (.const types[0]!.name []) indices
    unless (nativeHost.addDeclCore 0 (.defnDecl
        { name := types[0]!.name ++ `identity, levelParams := [],
          type := .forallE `argument parentType parentType .default,
          value := .lam `argument parentType (.bvar 0) .default,
          hints := .opaque, safety := if isUnsafe then .unsafe else .safe }) none).isOk do
      throwError "native kernel rejected comparison helper identity fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "comparison helper header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual } |
        throwError "comparison helper constructor registration failed"
      let sharedShadow := types.toList.foldl (fun view type => type.ctors.foldl (fun view constructor =>
        match registered.find? constructor.name with | some information => view.add information | none => view) view) shadow
      let locals := LocalContext.empty.mkLocalDecl ⟨`HelperStored⟩ `stored natural .default
      let actualReader : TypeChecker.Context := { env := actual, lctx := locals, safety := reader.safety, eagerReduce := true, fuel := { whnf := 8 } }
      let shadowReader := { actualReader with env := shadow, eagerReduce := false, fuel := { whnf := 12, recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkScripts actualReader shadowReader state
        checkNative actualReader shadowReader state
        let unit := methods firstSource secondSource parentType parentType
        let before := TypeChecker.Inner.isDefEqUnitLike firstSource secondSource unit actualReader state
        let shadowBefore := TypeChecker.Inner.isDefEqUnitLike firstSource secondSource unit shadowReader state
        if indices.isEmpty then
          unless !before.isOk do throwError "new unit parent reached an absent constructor successfully"
          let _ ← checkResult shadowBefore shadowBefore false state 2
          let registeredReader := { actualReader with env := registered }
          let sharedReader := { shadowReader with env := sharedShadow }
          let .ok (true, _) := TypeChecker.Inner.isDefEqUnitLike firstSource secondSource unit registeredReader state |
            throwError "registered unit parent failed actual comparison"
          let .ok (false, _) := TypeChecker.Inner.isDefEqUnitLike firstSource secondSource unit sharedReader state |
            throwError "registered unit parent erased the axiom-shadow metadata barrier"
          let constructor := .const types[0]!.ctors[0]!.name []
          let eta := methods firstSource constructor parentType parentType
          let .ok (true, _) := TypeChecker.Inner.tryEtaStructCore firstSource constructor eta registeredReader state |
            throwError "registered eta parent failed actual comparison"
          let .ok (false, _) := TypeChecker.Inner.tryEtaStructCore firstSource constructor eta sharedReader state |
            throwError "registered eta parent erased the axiom-shadow metadata barrier"
        else
          let _ ← checkResult before shadowBefore false state 2

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderComparisonHelperTransport |
    throwError "comparison helper transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "comparison helper module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "comparison helper unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native comparison helpers: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `HelperSingle]
  checkBatch host environment #[family `HelperFirstFamily, family `HelperSecondFamily]
  checkBatch host environment #[indexedFamily `HelperIndexed] #[number 0]
  logInfo "native comparison helper inputs, proposition gates, metadata, short-circuiting and staging barriers passed"

end InductiveHeaderComparisonHelperTransportTest
