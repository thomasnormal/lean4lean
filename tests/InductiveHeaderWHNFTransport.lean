import Lean4Lean.Verify.InductiveHeaderWHNFTransport

namespace InductiveHeaderWHNFTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions Lean.Kernel.Environment.irBaseExts from Lean.Environment

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) : NativeWhnfCallbacks methods methods context context state expression := by
  constructor
  · intros
    constructor <;> intros <;> exact Except.SuccessTransport.refl _
  · intros
    exact Except.SuccessTransport.refl _

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (expression : Expr)
    (callbacks : NativeWhnfCallbacks actualMethods shadowMethods actualContext shadowContext state expression.consumeMData)
    (budget : NativeWhnfEntryReceipt actualContext state expression.consumeMData →
      actualContext.whnfBudget ≤ shadowContext.whnfBudget) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.whnf' expression actualMethods)
      (TypeChecker.Inner.whnf' expression shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.whnf'.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext
    agreement locals state expression callbacks budget

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (first second : Expr) : NativeNatOperands methods methods context context state first second := by
  constructor <;> intros <;> exact Except.SuccessTransport.refl _

private def sortType : Expr := .sort (.succ .zero)

private def natural : Expr := .const ``Nat []

private def number (value : Nat) : Expr := .lit (.natVal value)

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

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
  { ngen := { namePrefix := `_whnf_transport, idx := 71 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert (.const `FullAlias []) sortType }

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  let marker := .const (Name.num `_full_step state.ngen.idx) []
  let (_, manager) := state.eqvManager.toNode marker
  .ok (value, { state with
    ngen := { state.ngen with idx := state.ngen.idx + 1 }
    inferTypeI := state.inferTypeI.insert marker sortType
    inferTypeC := state.inferTypeC.insert marker sortType
    whnfCoreCache := state.whnfCoreCache.insert marker marker
    whnfCache := state.whnfCache.insert marker marker
    eqvManager := manager
    failure := state.failure.insert (marker, sortType)
    unfold := state.unfold.insert marker marker })

private def methods (normalize : Expr → Expr) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    whnf := fun expression => step (normalize expression)
    whnfCore := fun expression _ _ => step expression }

private def alternateMethods (normalize : Expr → Expr) : TypeChecker.Methods :=
  { methods normalize with inferType := fun _ _ => step sortType }

private def withoutValue (environment : Kernel.Environment) (name : Name) : Kernel.Environment :=
  match environment.find? name with
  | some info =>
    let constants := { environment.constants with map₁ := environment.constants.map₁.erase name }
    let cleared := Lean.Kernel.Environment.mk constants environment.quotInit environment.diagnostics environment.const2ModIdx
      (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment) environment.header
    cleared.add (.axiomInfo { toConstantVal := info.toConstantVal, isUnsafe := info.isUnsafe })
  | none => environment

private def checkResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State))
    (expected : Option Expr := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "full normalization changed its result or complete state"
    if let some value := expected then
      unless first == value do throwError "full normalization returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "full normalization rejected an expected successful result"
  | _, _ => throwError "full normalization changed success/failure"

private def checkWhnf (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr)
    (normalize : Expr → Expr) (expected : Expr) (calls : Nat) (cached : Bool := true) : MetaM Unit := do
  let actualResult := TypeChecker.Inner.whnf' expression (methods normalize) actual state
  let shadowResult := TypeChecker.Inner.whnf' expression (alternateMethods normalize) shadow state
  checkResult actualResult shadowResult expected
  let .ok (_, finalState) := actualResult | throwError "full normalization callback fixture failed"
  unless finalState.ngen.idx == state.ngen.idx + calls do
    throwError "full normalization reached {finalState.ngen.idx - state.ngen.idx} callbacks, expected {calls}"
  let input := expression.consumeMData
  unless finalState.whnfCache[input]? == (if cached then some expected else state.whnfCache[input]?) do
    throwError "full normalization changed its entry cache policy"

private def checkNatural (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let first := .const `FullFirst []
  let second := .const `FullSecond []
  let normalize := fun expression => if expression == first then number 8 else if expression == second then number 3 else expression
  let cases := [(``Nat.add, number 11), (``Nat.mul, number 24), (``Nat.pow, number 512),
    (``Nat.sub, number 5), (``Nat.beq, toExpr false), (``Nat.ble, toExpr false),
    (``Nat.shiftLeft, number 64), (``Nat.div, number 2), (``Nat.shiftRight, number 1), (``Nat.mod, number 2)]
  for (name, expected) in cases do
    let expression := mkAppN (.const name []) #[first, second]
    let direct := TypeChecker.Inner.reduceNat expression (methods normalize) actual state
    let shadowDirect := TypeChecker.Inner.reduceNat expression (alternateMethods normalize) shadow state
    match direct, shadowDirect with
    | .ok (some result, finalState), .ok (some shadowResult, shadowState) =>
      unless result == expected && shadowResult == expected && sameState finalState shadowState &&
          finalState.ngen.idx == state.ngen.idx + 2 do
        throwError "native natural operator {name} lost reached operand transport"
    | _, _ => throwError "native natural operator {name} rejected its accepted operands"
    checkWhnf actual shadow state expression normalize expected 3
  checkWhnf actual shadow state (.app (.const ``Nat.succ []) first) normalize (number 9) 2
  checkWhnf actual shadow state (mkAppN (.const ``Nat.add []) #[.const ``Nat.zero [], second]) normalize (number 3) 3
  for name in [``Nat.beq, ``Nat.ble] do
    let matching := fun expression => if expression == first || expression == second then number 3 else expression
    checkWhnf actual shadow state (mkAppN (.const name []) #[first, second]) matching (toExpr true) 3
  for failed in [first, second] do
    let rejecting := { methods normalize with whnf := fun input =>
      if input == failed then fun _ _ => .error .deterministicTimeout else step (normalize input) }
    let expression := mkAppN (.const ``Nat.add []) #[first, second]
    unless !(TypeChecker.Inner.reduceNat expression rejecting actual state).isOk &&
        (TypeChecker.Inner.reduceNat expression (alternateMethods normalize) shadow state).isOk do
      throwError "directional operand-error control lost its asymmetric acceptance"
  let noDeltaActual := { actual with env := withoutValue (withoutValue actual.env ``Nat.add) ``Nat.pow }
  let noDeltaShadow := { shadow with env := withoutValue (withoutValue shadow.env ``Nat.add) ``Nat.pow }
  for normalizedFirst in [first, number 8] do
    let rejecting := fun expression => if expression == first then normalizedFirst else expression
    let expression := mkAppN (.const ``Nat.add []) #[first, second]
    let direct := TypeChecker.Inner.reduceNat expression (methods rejecting) actual state
    let .ok (none, finalState) := direct | throwError "natural rejection did not return none"
    unless finalState.ngen.idx == state.ngen.idx + (if normalizedFirst == first then 1 else 2) do
      throwError "natural rejection invoked an unreached operand"
    checkWhnf noDeltaActual noDeltaShadow state expression rejecting expression (if normalizedFirst == first then 2 else 3)
  let exponent := .const `FullExponent []
  let capped := fun expression => if expression == first then number 2 else if expression == exponent then
    number (TypeChecker.Inner.reducePowMaxExp + 1) else expression
  let expression := mkAppN (.const ``Nat.pow []) #[first, exponent]
  checkWhnf noDeltaActual noDeltaShadow state expression capped expression 3
  let atCap := fun expression => if expression == first then number 1 else if expression == exponent then
    number TypeChecker.Inner.reducePowMaxExp else expression
  checkWhnf actual shadow state expression atCap (number 1) 3
  for expression in [first, .app first second, mkAppN first #[first, second],
      mkAppN (.fvar ⟨`FullNaturalLocal⟩) #[first, second],
      .app (.const ``Nat.succ [.zero]) first, mkAppN (.const ``Nat.add []) #[first, second, first]] do
    let .ok (none, finalState) := TypeChecker.Inner.reduceNat expression (methods normalize) actual state |
      throwError "unsupported natural dispatch did not return none"
    unless sameState state finalState do throwError "unsupported natural dispatch invoked a callback"

private def checkEntry (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let exhausted := TypeChecker.Methods.withFuel 0
  let cached := .const `FullCached []
  let locals := actual.lctx.mkLocalDecl ⟨`FullLocal⟩ `parameter natural .default
  let current := { actual with lctx := locals, fuel := { whnf := 0, whnfEager := 0 } }
  let shadowCurrent := { shadow with lctx := locals, fuel := { whnf := 0, whnfEager := 0 } }
  for expression in [Expr.bvar 0, .sort .zero, .mvar ⟨`FullMeta⟩, .forallE `argument natural natural .default,
      number 2, .fvar ⟨`FullLocal⟩, .fvar ⟨`FullMissing⟩] do
    let seeded := { state with whnfCache := state.whnfCache.insert expression cached }
    for input in [expression, .mdata {} (.mdata {} expression)] do
      checkResult (TypeChecker.Inner.whnf' input exhausted current seeded)
        (TypeChecker.Inner.whnf' input exhausted shadowCurrent seeded) expression
      let .ok (_, finalState) := TypeChecker.Inner.whnf' input exhausted current seeded |
        throwError "easy full normalization used fuel"
      unless sameState seeded finalState do throwError "easy full normalization changed state"
  for expression in [natural, .lam `argument natural (.bvar 0) .default, .app cached cached,
      .letE `value natural cached (.bvar 0) false, .proj ``Prod 0 cached] do
    let seeded := { state with whnfCache := state.whnfCache.insert expression cached }
    checkResult (TypeChecker.Inner.whnf' expression exhausted current seeded)
      (TypeChecker.Inner.whnf' expression exhausted shadowCurrent seeded) cached
    let wrapper := .mdata {} (.mdata {} expression)
    let wrappedState := { seeded with whnfCache := seeded.whnfCache.insert wrapper natural }
    checkResult (TypeChecker.Inner.whnf' wrapper exhausted current wrappedState)
      (TypeChecker.Inner.whnf' wrapper exhausted shadowCurrent wrappedState) cached
    let .ok (_, finalState) := TypeChecker.Inner.whnf' wrapper exhausted current wrappedState |
      throwError "cached full normalization used fuel"
    unless sameState finalState wrappedState do throwError "cached full normalization changed state"
  let cold := .lam `argument natural (.bvar 0) .default
  unless !(TypeChecker.Inner.whnf' cold exhausted current state).isOk &&
      (TypeChecker.Inner.whnf' cold exhausted { shadowCurrent with fuel := { whnf := 1, whnfEager := 1 } } state).isOk do
    throwError "directional zero-fuel control lost its asymmetric acceptance"
  for nondependent in [false, true] do
    let locals := actual.lctx.mkLetDecl ⟨`FullLet⟩ `value natural (number 4) nondependent
    let current := { actual with lctx := locals }
    let shadowCurrent := { shadow with lctx := locals }
    checkWhnf current shadowCurrent state (.fvar ⟨`FullLet⟩) id (number 4) 1
    let seeded := { state with whnfCache := state.whnfCache.insert (.fvar ⟨`FullLet⟩) cached }
    checkResult (TypeChecker.Inner.whnf' (.fvar ⟨`FullLet⟩) exhausted { current with fuel := { whnf := 0 } } seeded)
      (TypeChecker.Inner.whnf' (.fvar ⟨`FullLet⟩) exhausted { shadowCurrent with fuel := { whnf := 0 } } seeded) cached
  for name in [``reduceBool, ``reduceNat] do
    let expression := .app (.const name []) (.const `FullNativeFunction [])
    unless !(TypeChecker.Inner.whnf' expression (methods id) actual state).isOk &&
        !(TypeChecker.Inner.whnf' expression (alternateMethods id) shadow state).isOk do
      throwError "unsupported native reduction stopped rejecting"

private def addDefinition (environment : Kernel.Environment) (name : Name) (parameters : List Name) (type value : Expr)
    (safety : DefinitionSafety := .safe) : Kernel.Environment :=
  environment.add (.defnInfo { name, levelParams := parameters, type, value, hints := .abbrev, safety })

private def checkUnfold (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let first := .const `FullChainFirst []
  let second := .const `FullChainSecond []
  let actualEnv := addDefinition (addDefinition actual.env `FullChainFirst [] natural second)
    `FullChainSecond [] natural (number 13)
  let shadowEnv := addDefinition (addDefinition shadow.env `FullChainFirst [] natural second)
    `FullChainSecond [] natural (number 13)
  let current := { actual with env := actualEnv, eagerReduce := false, fuel := { whnf := 3, whnfEager := 0 } }
  let shadowCurrent := { shadow with env := shadowEnv, eagerReduce := true, fuel := { whnf := 0, whnfEager := 7 } }
  checkWhnf current shadowCurrent state first id (number 13) 0
  let tooSmall := { current with fuel := { whnf := 2 } }
  unless !(TypeChecker.Inner.whnf' first (methods id) tooSmall state).isOk do
    throwError "unfolding chain did not consume its final stopping step"
  let wrongBudget := { current with eagerReduce := true }
  unless !(TypeChecker.Inner.whnf' first (methods id) wrongBudget state).isOk do
    throwError "full normalization ignored eager budget selection"
  let insufficientShadow := { shadowCurrent with fuel := { whnfEager := 2 } }
  unless !(TypeChecker.Inner.whnf' first (alternateMethods id) insufficientShadow state).isOk do
    throwError "insufficient shadow fuel did not reject"
  for eager in [false, true] do
    let current := { current with eagerReduce := eager, fuel := { whnf := 3, whnfEager := 3 } }
    checkWhnf current shadowCurrent state (.mdata {} (.mdata {} first)) id (number 13) 0
  let parameter := Level.param `FullUniverse
  let aliasType := .sort parameter
  let aliasValue := .sort parameter
  let actualEnv := addDefinition actualEnv `FullPoly [`FullUniverse] aliasType aliasValue
  let shadowEnv := addDefinition shadowEnv `FullPoly [`FullUniverse] aliasType aliasValue
  let current := { current with env := actualEnv }
  let shadowCurrent := { shadowCurrent with env := shadowEnv }
  let polyExpression := .const `FullPoly [.succ .zero]
  checkWhnf current shadowCurrent state polyExpression id sortType 0
  let saved := .sort (.succ (.succ .zero))
  let seeded := { state with unfold := state.unfold.insert polyExpression saved }
  checkWhnf current shadowCurrent seeded polyExpression id saved 0
  for expression in [.const `FullPoly [], .const `FullPoly [.zero, .zero]] do
    checkWhnf current shadowCurrent state expression id expression 0
  let unsafeActual := addDefinition actualEnv `FullUnsafe [] natural (number 9) .unsafe
  let unsafeShadow := addDefinition shadowEnv `FullUnsafe [] natural (number 9) .unsafe
  checkWhnf { current with env := unsafeActual } { shadowCurrent with env := unsafeShadow }
    state (.const `FullUnsafe []) id (.const `FullUnsafe []) 0
  let zeroAlias := .const `FullChainSecond []
  let stale := { state with unfold := state.unfold.insert zeroAlias saved }
  checkWhnf current shadowCurrent stale zeroAlias id (number 13) 0
  let functionType := .forallE `value natural natural .default
  let stop := .const `FullApplicationStop []
  let stopInfo : ConstantInfo := .axiomInfo { name := `FullApplicationStop, levelParams := [], type := functionType, isUnsafe := false }
  let actualEnv := addDefinition (actualEnv.add stopInfo) `FullApplicationAlias [] functionType stop
  let shadowEnv := addDefinition (shadowEnv.add stopInfo) `FullApplicationAlias [] functionType stop
  let expression := .app (.const `FullApplicationAlias []) (number 6)
  let expected : Expr := .app stop (number 6)
  let callbacks : TypeChecker.Methods := { methods id with
    whnfCore := fun input _ _ context currentState =>
      match step input context currentState with
      | .error error => .error error
      | .ok (result, finalState) => .ok (result, { finalState with whnfCache := finalState.whnfCache.insert expression saved }) }
  let alternate := { callbacks with inferType := fun _ _ => step sortType }
  let actualResult := TypeChecker.Inner.whnf' expression callbacks { current with env := actualEnv } state
  let shadowResult := TypeChecker.Inner.whnf' expression alternate { shadowCurrent with env := shadowEnv } state
  checkResult actualResult shadowResult expected
  let .ok (_, finalState) := actualResult | throwError "full cache overwrite fixture failed"
  unless finalState.ngen.idx == state.ngen.idx + 2 && finalState.whnfCache[expression]? == some expected do
    throwError "full loop reread its outer cache or skipped its final overwrite"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 1000
  let shadowCallbacks := TypeChecker.Methods.withFuel 1001
  let zero := .const ``Nat.zero []
  let localName : FVarId := ⟨`FullNativeLet⟩
  let proofName : FVarId := ⟨`FullNativeProof⟩
  let productName : FVarId := ⟨`FullNativeProduct⟩
  let equality := mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, zero]
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let locals := actual.lctx.mkLetDecl localName `value natural zero
    |>.mkLocalDecl proofName `proof equality .default
    |>.mkLocalDecl productName `pair product .default
  let actual := { actual with lctx := locals }
  let shadow := { shadow with lctx := locals }
  let identity := .lam `value natural (.bvar 0) .default
  let addition := mkAppN (.const ``Nat.add []) #[number 4, number 5]
  let natMotive := .lam `major natural natural .default
  let natMinor := .lam `predecessor natural (.lam `recursive natural (.app (.const ``Nat.succ []) (.bvar 0)) .default) .default
  let natRecursor := mkAppN (.const ``Nat.rec [.succ .zero]) #[natMotive, zero, natMinor, number 3]
  let productMotive := .lam `pair product natural .default
  let productMinor := .lam `first natural (.lam `second natural (.bvar 1) .default) .default
  let productRecursor := mkAppN (.const ``Prod.rec [.succ .zero, .zero, .zero])
    #[natural, natural, productMotive, productMinor, .fvar productName]
  let eqMotive := .lam `target natural
    (.lam `proof (mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, .bvar 0]) natural .default) .default
  let eqRecursor := mkAppN (.const ``Eq.rec [.succ .zero, .succ .zero])
    #[natural, zero, eqMotive, zero, zero, .fvar proofName]
  let cases := [(natural, natural), (.app identity (number 3), number 3),
    (.letE `value natural addition (.bvar 0) false, number 9),
    (.app (.const ``Nat.succ []) zero, number 1), (addition, number 9), (.fvar localName, zero),
    (.proj ``Prod 1 (mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, zero, number 2]), number 2),
    (natRecursor, number 3), (eqRecursor, zero), (productRecursor, .proj ``Prod 0 (.fvar productName))]
  for (expression, expected) in cases do
    let .ok (_, acceptedState) := callbacks.inferType expression false actual state |
      throwError "native checker rejected complete full normalization fixture"
    let .ok (_, shadowState) := shadowCallbacks.inferType expression false shadow state |
      throwError "shadow checker rejected complete full normalization fixture"
    checkResult (TypeChecker.Inner.whnf' expression callbacks actual acceptedState)
      (TypeChecker.Inner.whnf' expression shadowCallbacks shadow shadowState) expected

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList false) none).isOk do
    throwError "native kernel rejected full normalization header fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "full normalization header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView environment headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "full normalization header checkpoint lost accepted constructors"
      let actualReader : TypeChecker.Context := { env := actual, safety := reader.safety, fuel := { whnf := 4 } }
      let shadowReader := { actualReader with
        env := shadow
        safety := .unsafe
        eagerReduce := true
        lparams := [`FullUnusedUniverse]
        fuel := { whnf := 0, whnfEager := 8 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkNatural actualReader shadowReader state
        checkEntry actualReader shadowReader state
        checkUnfold actualReader shadowReader state
        checkNative actualReader shadowReader state

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderWHNFTransport |
    throwError "full normalization transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "full normalization module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "full normalization unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"full normalization transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `FullSingle]
  checkBatch host environment #[family `FullFirstFamily, family `FullSecondFamily]
  logInfo "native full normalization, natural operands, unfolding, exact states, cache policies and fuel budgets passed"

end InductiveHeaderWHNFTransportTest
