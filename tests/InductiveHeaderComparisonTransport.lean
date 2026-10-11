import Lean4Lean.Verify.InductiveHeaderComparisonTransport

namespace InductiveHeaderComparisonTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

deriving instance Repr for Lean.LBool

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .lambda actualMethods shadowMethods actualContext shadowContext state first second substitution) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEqLambda first second substitution actualMethods)
      (TypeChecker.Inner.isDefEqLambda first second substitution shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.isDefEqLambda.transport _ _ _ _ _ _ _ _ callbacks

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeAppComparisonCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEqApp first second actualMethods)
      (TypeChecker.Inner.isDefEqApp first second shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.isDefEqApp.transport _ _ _ _ _ _ _ callbacks

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .forall actualMethods shadowMethods actualContext shadowContext state first second substitution) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEqForall first second substitution actualMethods)
      (TypeChecker.Inner.isDefEqForall first second substitution shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.isDefEqForall.transport _ _ _ _ _ _ _ _ callbacks

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (useHash : Bool)
    (callbacks : ∀ nextState, TypeChecker.Inner.nativeQuickProbe first second useHash actualContext state = .ok (false, nextState) →
      NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.quickIsDefEq first second useHash actualMethods)
      (TypeChecker.Inner.quickIsDefEq first second useHash shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.quickIsDefEq.transport _ _ _ _ _ _ _ _ callbacks

private def natural : Expr := .const ``Nat []

private def sortType : Expr := .sort (.succ .zero)

private def number (value : Nat) : Expr := .lit (.natVal value)

private def marker (index : Nat) : Expr := .const (Name.num `_comparison_step index) []

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
  { ngen := { namePrefix := `_comparison_seed, idx := 83 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert sortType natural }

private def localReceipt (expression : Expr) (context : TypeChecker.Context) : Expr :=
  if expression.isFVar then
    match context.lctx.findFVar? expression with
    | some declaration =>
      let binderCode := match declaration.binderInfo with
        | .default => 0
        | .implicit => 1
        | .strictImplicit => 2
        | .instImplicit => 3
      mkAppN (.const declaration.userName []) #[declaration.type, number binderCode]
    | none => default
  else default

private def trace (first second : Expr) (context : TypeChecker.Context) : Expr :=
  mkAppN (.const `ComparisonTrace [])
    #[first, second, number context.lctx.numIndices, localReceipt first context, localReceipt second context]

private def step (first second : Expr) (equal : Bool) : TypeChecker.M Bool := fun context state =>
  let key := marker state.ngen.idx
  let receipt := trace first second context
  let (_, manager) := state.eqvManager.toNode key
  .ok (equal, { state with
    ngen := state.ngen.next
    inferTypeI := state.inferTypeI.insert key receipt
    inferTypeC := state.inferTypeC.insert key receipt
    whnfCoreCache := state.whnfCoreCache.insert key first
    whnfCache := state.whnfCache.insert key second
    eqvManager := manager
    failure := state.failure.insert (first, second)
    unfold := state.unfold.insert key receipt })

private def methods (reject : Option (Expr × Expr) := none) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    isDefEqCore := fun first second context state =>
      if first.hasLooseBVars || second.hasLooseBVars ||
          (first.isFVar && !context.lctx.containsFVar first) ||
          (second.isFVar && !context.lctx.containsFVar second) then
        .error (.other "comparison callback received unopened input")
      else step first second (reject != some (first, second)) context state }

private def onlyComparison (expected : Expr × Expr) (equal : Bool) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    isDefEqCore := fun first second =>
      if (first, second) == expected then step first second equal
      else throw (.other "unreached comparison callback") }

private def checkResult [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State))
    (expected : resultType) (state : TypeChecker.State) (advancement : Nat) : MetaM TypeChecker.State := do
  let .ok (first, firstState) := actual | throwError "native comparison helper rejected {repr expected}"
  let .ok (second, secondState) := shadow | throwError "shadow comparison helper rejected accepted result"
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "comparison helper changed result or complete state: {repr first}, {repr second}, expected {repr expected}"
  unless firstState.ngen.idx == state.ngen.idx + advancement do
    throwError "comparison helper callback/allocation count: {firstState.ngen.idx}, expected {state.ngen.idx + advancement}"
  return firstState

private def checkTrace (state : TypeChecker.State) (index : Nat) (first second : Expr)
    (context : TypeChecker.Context) : MetaM Unit := do
  unless state.inferTypeI[marker index]? == some (trace first second context) do
    throwError "comparison helper changed reached input, order, binder type or local reader at {index}"

private def checkScripts (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let accepting := methods
  let alternate := { accepting with whnf := fun _ => throw (.other "unreached shadow normalization") }
  let firstDomain := .const `ComparisonFirstDomain []
  let secondDomain := .const `ComparisonSecondDomain []
  for kind in [NativeBinderKind.lambda, .forall] do
    let compare : Expr → Expr → Array Expr → TypeChecker.RecM Bool :=
      match kind with
      | .lambda => fun first second substitution => TypeChecker.Inner.isDefEqLambda first second substitution
      | .forall => fun first second substitution => TypeChecker.Inner.isDefEqForall first second substitution
    let closedFirst := kind.node `first natural (number 3) .implicit
    let closedSecond := kind.node `second natural (number 4) .default
    let closed ← checkResult (compare closedFirst closedSecond #[] accepting actual state)
      (compare closedFirst closedSecond #[] alternate shadow state) true state 1
    checkTrace closed state.ngen.idx (number 3) (number 4) actual
    let terminalRejecting := onlyComparison (number 3, number 4) false
    let _ ← checkResult (compare closedFirst closedSecond #[] terminalRejecting actual state)
      (compare closedFirst closedSecond #[] terminalRejecting shadow state) false state 1
    let first := kind.node `first firstDomain (.bvar 0) .implicit
    let second := kind.node `second secondDomain (.bvar 0) .strictImplicit
    let opened ← checkResult (compare first second #[] accepting actual state)
      (compare first second #[] alternate shadow state) true state 3
    unless (opened.eqvManager.isEquiv false firstDomain secondDomain).1 do
      throwError "accepted domain comparison lost equivalence insertion"
    checkTrace opened state.ngen.idx firstDomain secondDomain actual
    let checkedState := { state with ngen := state.ngen.next }
    let fresh := .fvar ⟨checkedState.ngen.curr⟩
    let openedContext := actual.openLocal checkedState `second .strictImplicit secondDomain
    checkTrace opened (state.ngen.idx + 2) fresh fresh openedContext
    let rejecting := onlyComparison (firstDomain, secondDomain) false
    let rejected ← checkResult (compare first second #[] rejecting actual state)
      (compare first second #[] rejecting shadow state) false state 1
    unless !(rejected.eqvManager.isEquiv false firstDomain secondDomain).1 do
      throwError "false domain comparison inserted an equivalence"
    let nestedFirst := kind.node `outer natural (kind.node `inner (.bvar 0) (.bvar 1) .implicit) .default
    let nestedSecond := kind.node `renamed natural (kind.node `renamed (.bvar 0) (.bvar 1) .default) .implicit
    let nested ← checkResult (compare nestedFirst nestedSecond #[] accepting actual state)
      (compare nestedFirst nestedSecond #[] alternate shadow state) true state 3
    let outerFresh := .fvar ⟨state.ngen.curr⟩
    let outerContext := actual.openLocal state `renamed .implicit natural
    let innerState := state.allocateLocal
    let innerContext := outerContext.openLocal innerState `renamed .default outerFresh
    checkTrace nested (state.ngen.idx + 2) outerFresh outerFresh innerContext
    let substitutedFirst := kind.node `first (.bvar 0) (.bvar 1) .default
    let substitutedSecond := kind.node `second (.bvar 0) (.bvar 1) .implicit
    let substituted ← checkResult (compare substitutedFirst substitutedSecond #[natural] accepting actual state)
      (compare substitutedFirst substitutedSecond #[natural] alternate shadow state) true state 2
    checkTrace substituted (state.ngen.idx + 1) natural natural (actual.openLocal state `second .implicit natural)
    let otherKind := match kind with | .lambda => NativeBinderKind.forall | .forall => .lambda
    let _ ← checkResult (compare closedFirst (otherKind.node `other natural (number 4) .default) #[] accepting actual state)
      (compare closedFirst (otherKind.node `other natural (number 4) .default) #[] alternate shadow state) true state 1
  let firstHead := .const `ComparisonFirstHead []
  let secondHead := .const `ComparisonSecondHead []
  let first := mkAppN firstHead #[number 1, number 2, number 3]
  let second := mkAppN secondHead #[number 4, number 5, number 6]
  let arguments ← checkResult (TypeChecker.Inner.isDefEqArgs first second accepting actual state)
    (TypeChecker.Inner.isDefEqArgs first second alternate shadow state) true state 3
  unless !(arguments.eqvManager.isEquiv false firstHead secondHead).1 do
    throwError "argument-only comparison unexpectedly compared heads"
  for offset in [0:3] do
    checkTrace arguments (state.ngen.idx + offset) (number (3 - offset)) (number (6 - offset)) actual
  let application ← checkResult (TypeChecker.Inner.isDefEqApp first second accepting actual state)
    (TypeChecker.Inner.isDefEqApp first second alternate shadow state) true state 4
  unless (application.eqvManager.isEquiv false firstHead secondHead).1 do
    throwError "application head comparison lost equivalence insertion"
  checkTrace application state.ngen.idx firstHead secondHead actual
  for offset in [0:3] do
    checkTrace application (state.ngen.idx + offset + 1) (number (offset + 1)) (number (offset + 4)) actual
  for (pair, expectedCalls) in [((firstHead, secondHead), 1), ((number 1, number 4), 2), ((number 2, number 5), 3), ((number 3, number 6), 4)] do
    let rejecting := methods (some pair)
    let _ ← checkResult (TypeChecker.Inner.isDefEqApp first second rejecting actual state)
      (TypeChecker.Inner.isDefEqApp first second rejecting shadow state) false state expectedCalls
  let headRejecting := onlyComparison (firstHead, secondHead) false
  let _ ← checkResult (TypeChecker.Inner.isDefEqApp first second headRejecting actual state)
    (TypeChecker.Inner.isDefEqApp first second headRejecting shadow state) false state 1
  let rejecting := onlyComparison (number 3, number 6) false
  let _ ← checkResult (TypeChecker.Inner.isDefEqArgs first second rejecting actual state)
    (TypeChecker.Inner.isDefEqArgs first second rejecting shadow state) false state 1
  let unusable := TypeChecker.Methods.withFuel 0
  for (first, second, expectedArgs) in [(firstHead, secondHead, true), (first, secondHead, false)] do
    let _ ← checkResult (TypeChecker.Inner.isDefEqArgs first second unusable actual state)
      (TypeChecker.Inner.isDefEqArgs first second unusable shadow state) expectedArgs state 0
    let _ ← checkResult (TypeChecker.Inner.isDefEqApp first second unusable actual state)
      (TypeChecker.Inner.isDefEqApp first second unusable shadow state) false state 0
  let shorter := .app secondHead (number 4)
  let _ ← checkResult (TypeChecker.Inner.isDefEqArgs first shorter accepting actual state)
    (TypeChecker.Inner.isDefEqArgs first shorter alternate shadow state) false state 1
  let _ ← checkResult (TypeChecker.Inner.isDefEqApp first shorter unusable actual state)
    (TypeChecker.Inner.isDefEqApp first shorter unusable shadow state) false state 0
  for useHash in [false, true] do
    for (first, second, expected) in [(natural, natural, LBool.true), (.sort (.max .zero .zero), .sort .zero, .true),
        (number 1, number 2, .false), (first, secondHead, .undef), (.mvar ⟨`ComparisonSameMeta⟩, .mvar ⟨`ComparisonSameMeta⟩, .true)] do
      let _ ← checkResult (TypeChecker.Inner.quickIsDefEq first second useHash unusable actual state)
        (TypeChecker.Inner.quickIsDefEq first second useHash unusable shadow state) expected state 0
    let cachedState := { state with eqvManager := state.eqvManager.addEquiv first second }
    let _ ← checkResult (TypeChecker.Inner.quickIsDefEq first second false unusable actual cachedState)
      (TypeChecker.Inner.quickIsDefEq first second false unusable shadow cachedState) LBool.true cachedState 0
    unless first.hash != second.hash do throwError "hash-guard fixture unexpectedly collided"
    let _ ← checkResult (TypeChecker.Inner.quickIsDefEq first second true unusable actual cachedState)
      (TypeChecker.Inner.quickIsDefEq first second true unusable shadow cachedState) LBool.undef cachedState 0
    let firstLambda := .lam `first natural (number 1) .default
    let secondLambda := .lam `second natural (number 2) .implicit
    let _ ← checkResult (TypeChecker.Inner.quickIsDefEq firstLambda secondLambda useHash accepting actual state)
      (TypeChecker.Inner.quickIsDefEq firstLambda secondLambda useHash alternate shadow state) LBool.true state 1
    let firstForall := .forallE `first natural (number 1) .default
    let secondForall := .forallE `second natural (number 2) .implicit
    let _ ← checkResult (TypeChecker.Inner.quickIsDefEq firstForall secondForall useHash accepting actual state)
      (TypeChecker.Inner.quickIsDefEq firstForall secondForall useHash alternate shadow state) LBool.true state 1
    let _ ← checkResult (TypeChecker.Inner.quickIsDefEq (.mdata {} firstHead) (.mdata {} secondHead) useHash accepting actual state)
      (TypeChecker.Inner.quickIsDefEq (.mdata {} firstHead) (.mdata {} secondHead) useHash alternate shadow state) LBool.true state 1
  let empty : Array Expr := #[]
  let _ ← checkResult (TypeChecker.Inner.isDefEqApp.loop empty empty rfl 0 unusable actual state)
    (TypeChecker.Inner.isDefEqApp.loop empty empty rfl 0 unusable shadow state) true state 0
  let single := #[natural]
  for index in [1, 2, 33] do
    let _ ← checkResult (TypeChecker.Inner.isDefEqApp.loop single single rfl index unusable actual state)
      (TypeChecker.Inner.isDefEqApp.loop single single rfl index unusable shadow state) true state 0
  let restoration : TypeChecker.RecM (Bool × Nat) := do
    let equal ← TypeChecker.Inner.isDefEqLambda (.lam `first natural (.bvar 0) .default)
      (.lam `second natural (.bvar 0) .implicit)
    return (equal, (← readThe TypeChecker.Context).lctx.numIndices)
  let _ ← checkResult (restoration accepting actual state) (restoration alternate shadow state)
    (true, actual.lctx.numIndices) state 2

private def beta (value : Expr) : Expr := .app (.lam `identity natural (.bvar 0) .default) value

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (parentType : Expr) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 1000
  let alternate := TypeChecker.Methods.withFuel 1001
  let first := .lam `first natural (.bvar 0) .default
  let second := .lam `renamed natural (beta (.bvar 0)) .implicit
  let firstForall := .forallE `first natural natural .default
  let secondForall := .forallE `renamed natural (.letE `alias sortType natural (.bvar 0) true) .implicit
  let firstApplication := .app (.const ``Nat.succ []) (number 3)
  let secondApplication := .app (.const ``Nat.succ []) (beta (number 3))
  let parentFirst := .lam `first parentType (.bvar 0) .default
  let parentSecond := .lam `renamed parentType (.bvar 0) .implicit
  for (first, second, compare) in [(first, second, TypeChecker.Inner.isDefEqLambda),
      (firstForall, secondForall, TypeChecker.Inner.isDefEqForall), (parentFirst, parentSecond, TypeChecker.Inner.isDefEqLambda)] do
    let .ok (equal, finalState) := compare first second callbacks actual state |
      throwError "native recursive binder comparison rejected"
    let .ok (shadowEqual, shadowState) := compare first second alternate shadow state |
      throwError "shadow recursive binder comparison rejected"
    unless equal && shadowEqual && sameState finalState shadowState do throwError "native recursive binder comparison changed"
  for compare in [TypeChecker.Inner.isDefEqArgs, TypeChecker.Inner.isDefEqApp] do
    let .ok (equal, finalState) := compare firstApplication secondApplication callbacks actual state |
      throwError "native recursive application comparison rejected"
    let .ok (shadowEqual, shadowState) := compare firstApplication secondApplication alternate shadow state |
      throwError "shadow recursive application comparison rejected"
    unless equal && shadowEqual && sameState finalState shadowState do throwError "native recursive application comparison changed"
  for useHash in [false, true] do
    for (first, second) in [(first, second), (firstForall, secondForall), (.mdata {} firstApplication, .mdata {} secondApplication)] do
      let .ok (equal, finalState) := TypeChecker.Inner.quickIsDefEq first second useHash callbacks actual state |
        throwError "native recursive quick comparison rejected"
      let .ok (shadowEqual, shadowState) := TypeChecker.Inner.quickIsDefEq first second useHash alternate shadow state |
        throwError "shadow recursive quick comparison rejected"
      unless equal == LBool.true && shadowEqual == LBool.true && sameState finalState shadowState do
        throwError "native recursive quick comparison changed"

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .forallE `index natural (.app (.const name []) (.bvar 0)) .default⟩] }

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType)
    (indices : Array Expr := #[]) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok nativeHost := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected comparison header fixture"
    let parentType := mkAppN (.const types[0]!.name []) indices
    let identityDeclaration := Declaration.defnDecl
      { name := types[0]!.name ++ `identity, levelParams := [],
        type := .forallE `argument parentType parentType .default,
        value := .lam `argument parentType (.bvar 0) .default,
        hints := .opaque, safety := if isUnsafe then .unsafe else .safe }
    unless (nativeHost.addDeclCore 0 identityDeclaration none).isOk do
      throwError "native kernel rejected explicit comparison binder definition"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (_, _, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "comparison header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView environment headers
      let locals := LocalContext.empty.mkLocalDecl ⟨`ComparisonStored⟩ `stored natural .default
      let actualReader : TypeChecker.Context := { env := actual, lctx := locals, safety := reader.safety, eagerReduce := true, fuel := { whnf := 8 } }
      let shadowReader := { actualReader with env := shadow, eagerReduce := false, fuel := { whnf := 12, recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkScripts actualReader shadowReader state
        checkNative actualReader shadowReader state parentType

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderComparisonTransport |
    throwError "comparison transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "comparison transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "comparison transport unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native comparison transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `ComparisonSingle]
  checkBatch host environment #[family `ComparisonFirstFamily, family `ComparisonSecondFamily]
  checkBatch host environment #[indexedFamily `ComparisonIndexed] #[number 0]
  logInfo "native binder comparison, accepted prefixes, quick cache and opposite application traversal orders passed"

end InductiveHeaderComparisonTransportTest
