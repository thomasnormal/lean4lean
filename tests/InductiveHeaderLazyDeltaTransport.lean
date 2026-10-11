import Lean4Lean.Verify.InductiveHeaderLazyDeltaTransport

namespace InductiveHeaderLazyDeltaTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

deriving instance BEq, Repr for TypeChecker.ReductionStatus
deriving instance BEq, Repr for NativeDeltaSide
deriving instance BEq, Repr for NativeLazyDeltaPlan

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeLazyDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.lazyDeltaReduction first second actualMethods)
      (TypeChecker.Inner.lazyDeltaReduction first second shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.lazyDeltaReduction.headerAxiomTransport _ _ _ _ agreement policy budget _ _ _ callbacks

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (firstNotDelta : TypeChecker.Inner.isDelta actualContext.env first = none)
    (secondNotDelta : TypeChecker.Inner.isDelta actualContext.env second = none) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.lazyDeltaReductionStep first second actualMethods)
      (TypeChecker.Inner.lazyDeltaReductionStep first second shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.lazyDeltaReductionStep.headerAxiomTransport _ _ _ _ agreement
  simp only [nativeLazyDeltaPlan, firstNotDelta, secondNotDelta, NativeLazyDeltaStepCallbacks]

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) : NativeDeltaNatCallbacks methods methods context context state expression := by
  constructor
  · intros; exact Except.SuccessTransport.refl _
  · intros; constructor <;> intros <;> exact Except.SuccessTransport.refl _

private def natural : Expr := .const ``Nat []
private def sortType : Expr := .sort (.succ .zero)
private def number (value : Nat) : Expr := .lit (.natVal value)
private def foreign : Expr := .fvar ⟨`DeltaForeign⟩
private def otherForeign : Expr := .fvar ⟨`DeltaOtherForeign⟩
private def identity : Expr := .lam `argument natural (.bvar 0) .default
private def low : Expr := .const `DeltaLow []
private def high : Expr := .const `DeltaHigh []
private def equalOther : Expr := .const `DeltaEqualOther []
private def regular (argument : Expr) : Expr := .app (.const `DeltaRegular []) argument
private def coreInput (first second : Expr) : Expr := mkAppN (.const `DeltaCore []) #[first, second]
private def normalizationInput (expression : Expr) (cheapRec cheapProj : Bool) : Expr :=
  mkAppN (.const `DeltaWhnfCore []) #[expression, toExpr cheapRec, toExpr cheapProj]
private def naturalInput (expression : Expr) : Expr := .app (.const `DeltaWhnf []) expression
private def marker (index : Nat) : Expr := .const (Name.num `_delta_step index) []

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
  { ngen := { namePrefix := `_delta_seed, idx := 113 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert natural sortType }

private def trace (input : Expr) (context : TypeChecker.Context) : Expr :=
  mkAppN (.const `DeltaTrace []) #[input, number context.lctx.numIndices]

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

private def methods (comparison := false) (normalizeCore : Expr → Expr := id)
    (normalizeNat : Expr → Expr := id) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    isDefEqCore := fun first second => step (coreInput first second) comparison
    whnfCore := fun expression cheapRec cheapProj =>
      step (normalizationInput expression cheapRec cheapProj) (normalizeCore expression)
    whnf := fun expression => step (naturalInput expression) (normalizeNat expression) }

private def checkResult (actual shadow : Except Kernel.Exception (TypeChecker.ReductionStatus × TypeChecker.State))
    (expected : TypeChecker.ReductionStatus) (context : TypeChecker.Context) (state : TypeChecker.State)
    (inputs : List Expr) : MetaM TypeChecker.State := do
  let (first, firstState) ← ofExceptKernelException actual
  let (second, secondState) ← ofExceptKernelException shadow
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "lazy delta result/complete-state mismatch: {repr first}, {repr second}, expected {repr expected}"
  unless firstState.ngen.idx == state.ngen.idx + inputs.length do
    throwError "lazy delta callback count mismatch: {firstState.ngen.idx}, expected {state.ngen.idx + inputs.length}"
  for index in [:inputs.length] do
    unless firstState.inferTypeI[marker (state.ngen.idx + index)]? == some (trace inputs[index]! context) do
      throwError "lazy delta callback input/order/reader mismatch at {index}"
  return firstState

private def checkStep (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr)
    (callbacks : TypeChecker.Methods) (expected : TypeChecker.ReductionStatus) (inputs : List Expr) : MetaM TypeChecker.State := do
  let native := TypeChecker.Inner.lazyDeltaReductionStep first second callbacks actual state
  let transported := TypeChecker.Inner.lazyDeltaReductionStep first second callbacks shadow state
  let plan := nativeLazyDeltaPlan actual.env state first second
  unless plan == nativeLazyDeltaPlan shadow.env state first second do
    throwError "header shadow changed native pointer/cache policy"
  let factored := TypeChecker.Inner.nativeLazyDeltaRun plan first second callbacks actual state
  let finalState ← checkResult native transported expected actual state inputs
  let _ ← checkResult native factored expected actual state inputs
  return finalState

private def checkLoop (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr)
    (callbacks : TypeChecker.Methods) (expected : TypeChecker.ReductionStatus) (inputs : List Expr) : MetaM Unit := do
  let native := TypeChecker.Inner.lazyDeltaReduction first second callbacks actual state
  let transported := TypeChecker.Inner.lazyDeltaReduction first second callbacks shadow state
  let _ ← checkResult native transported expected actual state inputs
  let factored : TypeChecker.RecM TypeChecker.ReductionStatus := do
    match ← TypeChecker.Inner.nativeLazyDeltaRound first second with
    | .continue nextFirst nextSecond => TypeChecker.Inner.lazyDeltaReduction.loop nextFirst nextSecond (actual.fuel.lazyDelta - 1)
    | result => pure result
  let _ ← checkResult native (factored callbacks actual state) expected actual state inputs

private def checkScripts (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let _ ← checkStep actual shadow state foreign otherForeign (TypeChecker.Methods.withFuel 0) (.unknown foreign otherForeign) []
  let _ ← checkStep actual shadow state low foreign (methods) (.continue (number 5) foreign)
    [normalizationInput (number 5) false true]
  let _ ← checkStep actual shadow state foreign low (methods) (.continue foreign (number 5))
    [normalizationInput (number 5) false true]
  let projection := .proj ``Prod 0 foreign
  for normalized in [projection, number 5] do
    let callbacks := methods false (fun expression => if expression == projection then normalized else expression)
    for reverse in [false, true] do
      let first := if reverse then projection else low
      let second := if reverse then low else projection
      let fallback := if reverse then .continue projection (number 5) else .continue (number 5) projection
      let unfoldedProjection := if reverse then .continue (number 5) low else .continue low (number 5)
      let _ ← checkStep actual shadow state first second callbacks
        (if normalized == projection then fallback else unfoldedProjection)
        (if normalized == projection then [normalizationInput projection false false, normalizationInput (number 5) false true]
          else [normalizationInput projection false false])
  let _ ← checkStep actual shadow state low high (methods) (.continue low (number 6))
    [normalizationInput (number 6) false true]
  let _ ← checkStep actual shadow state high low (methods) (.continue (number 6) low)
    [normalizationInput (number 6) false true]
  let _ ← checkStep actual shadow state low equalOther (methods) (.bool false)
    [normalizationInput (number 5) false true, normalizationInput (number 6) false true]
  for hint in [`DeltaAbbrev, `DeltaOpaque] do
    let first := .app (.const hint []) (number 1)
    let second := .app (.const hint []) (number 2)
    unless nativeLazyDeltaPlan actual.env state first second == .both false do
      throwError "nonregular hints entered the fast argument path"
    let _ ← checkStep actual shadow state first second (methods) (.continue (.app identity (number 1)) (.app identity (number 2)))
      [normalizationInput (.app identity (number 1)) false true, normalizationInput (.app identity (number 2)) false true]
  let first := regular (number 1)
  let second := regular (number 2)
  unless nativeLazyDeltaPlan actual.env state first second == .both true do
    throwError "identical regular native record did not enter the fast argument path"
  for accepted in [false, true] do
    let finalState ← checkStep actual shadow state first second (methods accepted)
      (if accepted then .bool true else .continue (.app identity (number 1)) (.app identity (number 2)))
      (if accepted then [coreInput (number 1) (number 2)] else
        [coreInput (number 1) (number 2), normalizationInput (.app identity (number 1)) false true,
          normalizationInput (.app identity (number 2)) false true])
    unless TypeChecker.Inner.failedBefore finalState.failure first second == !accepted do
      throwError "argument failure was not cached after its returned state, or success cached a failure"
    unless finalState.inferTypeI[marker state.ngen.idx]? == some (trace (coreInput (number 1) (number 2)) actual) do
      throwError "failure caching discarded the argument callback's state"
  let .ok ((), cachedState) := TypeChecker.Inner.cacheFailure first second actual state |
    throwError "failure insertion unexpectedly failed"
  unless nativeLazyDeltaPlan actual.env cachedState second first == .both false do
    throwError "symmetric failure cache did not suppress the fast argument path"
  let _ ← checkStep actual shadow cachedState second first (methods true)
    (.continue (.app identity (number 2)) (.app identity (number 1)))
    [normalizationInput (.app identity (number 2)) false true, normalizationInput (.app identity (number 1)) false true]
  let polyFirst := .app (.const `DeltaPoly [.zero]) (number 1)
  let polySecond := .app (.const `DeltaPoly [.succ .zero]) (number 2)
  let finalState ← checkStep actual shadow state polyFirst polySecond (methods true)
    (.continue (.app identity (number 1)) (.app identity (number 2)))
    [normalizationInput (.app identity (number 1)) false true, normalizationInput (.app identity (number 2)) false true]
  unless TypeChecker.Inner.failedBefore finalState.failure polyFirst polySecond do
    throwError "different universe lists did not cache failure before both unfolds"
  let distinctRecord := .app (.const `DeltaPoly [.zero]) (number 2)
  unless nativeLazyDeltaPlan actual.env state first distinctRecord == .both false do
    throwError "equal hints on distinct native records bypassed the pointer guard"
  let distinctState ← checkStep actual shadow state first distinctRecord (methods true)
    (.continue (.app identity (number 1)) (.app identity (number 2)))
    [normalizationInput (.app identity (number 1)) false true, normalizationInput (.app identity (number 2)) false true]
  unless !TypeChecker.Inner.failedBefore distinctState.failure first distinctRecord do
    throwError "different universes cached failure outside the fast pointer/application guard"
  for result in [number 5, number 7, foreign] do
    let callbacks := methods false (fun _ => result)
    let _ ← checkStep actual shadow state low equalOther callbacks (.bool true)
      [normalizationInput (number 5) false true, normalizationInput (number 6) false true]
  let normalizedFirst := .mdata {} foreign
  let normalizedSecond := .mdata {} otherForeign
  for equal in [false, true] do
    let callbacks := methods equal (fun expression => if expression == number 5 then normalizedFirst else normalizedSecond)
    let _ ← checkStep actual shadow state low equalOther callbacks (.bool equal)
      [normalizationInput (number 5) false true, normalizationInput (number 6) false true, coreInput foreign otherForeign]
  unless normalizedFirst.hash != normalizedSecond.hash do
    throwError "cached quick-probe fixture did not distinguish expression hashes"
  let probeState := { state with eqvManager := state.eqvManager.addEquiv normalizedFirst normalizedSecond }
  let cachedCallbacks := { methods false (fun expression => if expression == number 5 then normalizedFirst else normalizedSecond) with
    isDefEqCore := fun _ _ => throw (.other "unreached cached-probe body") }
  let _ ← checkStep actual shadow probeState low equalOther cachedCallbacks (.bool true)
    [normalizationInput (number 5) false true, normalizationInput (number 6) false true]
  let rejecting := { methods with whnfCore := fun _ _ _ => throw (.other "delta callback rejected") }
  unless !(TypeChecker.Inner.lazyDeltaReductionStep low foreign rejecting actual state).isOk do
    throwError "delta callback rejection was swallowed"
  let .ok _ := TypeChecker.Inner.lazyDeltaReductionStep low foreign (methods) shadow state |
    throwError "directional error control lost shadow acceptance"

private def checkLoopScripts (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let exhaustedActual := { actual with fuel := { actual.fuel with lazyDelta := 0 } }
  let exhaustedShadow := { shadow with fuel := { shadow.fuel with lazyDelta := 0 } }
  for context in [exhaustedActual, exhaustedShadow] do
    let .error .deterministicTimeout := TypeChecker.Inner.lazyDeltaReduction (number 0) (number 0) (methods true) context state |
      throwError "zero lazy-delta fuel did not fail before offset comparison"
  checkLoop actual shadow state (number 0) (number 0) (TypeChecker.Methods.withFuel 0) (.bool true) []
  for equal in [false, true] do
    checkLoop actual shadow state (number 3) (number 4) (methods equal) (.bool equal)
      [coreInput (number 2) (number 3)]
  let sum := mkAppN (.const ``Nat.add []) #[foreign, otherForeign]
  let callbacks := methods true id (fun expression => if expression == foreign then number 8 else number 9)
  let eagerActual := { actual with eagerReduce := true }
  let eagerShadow := { shadow with eagerReduce := true }
  checkLoop eagerActual eagerShadow state sum low callbacks (.bool true)
    [naturalInput foreign, naturalInput otherForeign, coreInput (number 17) low]
  checkLoop eagerActual eagerShadow state low sum callbacks (.bool true)
    [naturalInput foreign, naturalInput otherForeign, coreInput low (number 17)]
  let closedSum := mkAppN (.const ``Nat.add []) #[number 8, number 9]
  checkLoop eagerActual eagerShadow state sum closedSum (methods true) (.bool true)
    [naturalInput foreign, naturalInput (number 8), naturalInput (number 9), coreInput sum (number 17)]
  let reversedSum := mkAppN (.const ``Nat.add []) #[otherForeign, foreign]
  checkLoop eagerActual eagerShadow state sum reversedSum (methods true) (.bool true)
    [naturalInput foreign, naturalInput otherForeign, coreInput otherForeign foreign, coreInput foreign otherForeign]
  let lazyActual := { actual with eagerReduce := false }
  let lazyShadow := { shadow with eagerReduce := false }
  checkLoop lazyActual lazyShadow state closedSum low (methods true) (.bool true)
    [naturalInput (number 8), naturalInput (number 9), coreInput (number 17) low]
  let gateActual := TypeChecker.Inner.nativeLazyDeltaRound sum foreign callbacks eagerActual state
  let gateShadow := TypeChecker.Inner.nativeLazyDeltaRound sum foreign callbacks lazyShadow state
  unless (gateActual matches .ok (.bool true, _)) && !(gateShadow matches .ok (.bool true, _)) do
    throwError "mismatched eager readers were silently treated as an aligned natural-reduction gate"
  checkLoop lazyActual lazyShadow state foreign otherForeign (TypeChecker.Methods.withFuel 0) (.unknown foreign otherForeign) []
  checkLoop lazyActual lazyShadow state low foreign (methods) (.unknown (number 5) foreign)
    [normalizationInput (number 5) false true]
  for context in [{ lazyActual with fuel := { lazyActual.fuel with lazyDelta := 1 } },
      { lazyShadow with fuel := { lazyShadow.fuel with lazyDelta := 1 } }] do
    let .error .deterministicTimeout := TypeChecker.Inner.lazyDeltaReduction low foreign (methods) context state |
      throwError "continuation did not consume exactly one unit of lazy-delta fuel"
  let shortReader := { lazyActual with fuel := { lazyActual.fuel with lazyDelta := 1 } }
  unless !(TypeChecker.Inner.lazyDeltaReduction low foreign (methods) shortReader state).isOk &&
      (TypeChecker.Inner.lazyDeltaReduction low foreign (methods) lazyShadow state).isOk do
    throwError "directional larger-budget control was replaced by equality of error actions"
  for native in [``reduceNat, ``reduceBool] do
    for reverse in [false, true] do
      let unsupported := .app (.const native []) low
      let first := if reverse then foreign else unsupported
      let second := if reverse then unsupported else foreign
      let .error (.other _) := TypeChecker.Inner.lazyDeltaReduction first second (methods) lazyActual state |
        throwError "unsupported native reducer was not checked before the delta step"
      let .error (.other _) := TypeChecker.Inner.lazyDeltaReduction first second (methods) lazyShadow state |
        throwError "shadow swallowed unsupported native-reducer rejection"

private def definitions : List DefinitionVal :=
  [{ name := `DeltaLow, levelParams := [], type := natural, value := number 5, hints := .regular 1, safety := .safe },
   { name := `DeltaHigh, levelParams := [], type := natural, value := number 6, hints := .regular 8, safety := .safe },
   { name := `DeltaEqualOther, levelParams := [], type := natural, value := number 6, hints := .regular 1, safety := .safe }] ++
  ([(`DeltaRegular, ReducibilityHints.regular 3), (`DeltaAbbrev, .abbrev), (`DeltaOpaque, .opaque), (`DeltaPoly, .regular 3)].map
    fun (name, hints) =>
      { name
        levelParams := if name == `DeltaPoly then [`level] else []
        type := .forallE `argument natural natural .default
        value := identity
        hints
        safety := .safe })

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .forallE `index natural (.app (.const name []) (.bvar 0)) .default⟩] }

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok _ := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected lazy-delta staging fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok actual := checkInductiveTypes 0 types (fun stats =>
          declareInductiveTypes stats 0 types 0 isUnsafe) reader | throwError "lazy-delta header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      let locals := LocalContext.empty.mkLocalDecl ⟨`DeltaStored⟩ `stored natural .default
      let actualReader : TypeChecker.Context :=
        { env := actual, lctx := locals, safety := reader.safety, eagerReduce := true, fuel := { lazyDelta := 3, recDepth := 6 } }
      let shadowReader := { actualReader with env := shadow, fuel := { lazyDelta := 8, recDepth := 2 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkScripts actualReader shadowReader state
        checkLoopScripts actualReader shadowReader state
        for type in types do
          let parent := .const type.name []
          let _ ← checkStep actualReader shadowReader state parent foreign (TypeChecker.Methods.withFuel 0) (.unknown parent foreign) []
        for (first, second, expected) in [(low, number 5, true), (high, number 6, true), (regular (number 5), number 5, true),
            (regular (number 5), regular (number 6), false), (equalOther, low, false)] do
          let native := TypeChecker.Methods.withFuel 12
          let result := TypeChecker.Inner.lazyDeltaReduction first second native actualReader state
          let transported := TypeChecker.Inner.lazyDeltaReduction first second native shadowReader state
          let (value, finalState) ← ofExceptKernelException result
          let (shadowValue, shadowState) ← ofExceptKernelException transported
          unless value == .bool expected && shadowValue == .bool expected && sameState finalState shadowState do
            throwError "recursive native lazy-delta comparison lost complete-state transport"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderLazyDeltaTransport |
    throwError "lazy-delta transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "lazy-delta module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "lazy-delta unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native lazy delta: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let mut host ← getEnv
  for definition in definitions do
    let .ok updated := host.addDeclCore 0 (.defnDecl definition) none |
      throwError "native kernel rejected lazy-delta definition fixture {definition.name}"
    host := updated
  let environment := host.toKernelEnv
  checkBatch host environment #[family `DeltaSingle]
  checkBatch host environment #[family `DeltaFirstFamily, family `DeltaSecondFamily]
  checkBatch host environment #[indexedFamily `DeltaIndexed]
  logInfo "native lazy-delta policy, callback states, projection priority, caching, natural gate and fuel controls passed"

end InductiveHeaderLazyDeltaTransportTest
