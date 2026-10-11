import Lean4Lean.Verify.InductiveHeaderWHNFCoreTransport

namespace InductiveHeaderWHNFCoreTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (cheapRec cheapProj : Bool) :
    NativeCoreCallbacks methods methods context context state expression cheapRec cheapProj := by
  constructor <;> intros <;> exact Except.SuccessTransport.refl _

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool)
    (locals : actualContext.lctx = shadowContext.lctx)
    (callbacks : NativeCoreCallbacks actualMethods shadowMethods actualContext shadowContext state
      expression.consumeMData cheapRec cheapProj) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.whnfCore'.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext
    state expression cheapRec cheapProj locals callbacks

private def sortType : Expr := .sort (.succ .zero)

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
  let (_, manager) := EquivManager.toNode (.const ``Nat []) {}
  { ngen := { namePrefix := `_whnf_core_transport, idx := 59 }
    inferTypeI := ({} : InferCache).insert (.const ``Nat []) sortType
    inferTypeC := ({} : InferCache).insert (.const ``Nat []) sortType
    whnfCoreCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    whnfCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (.const ``Nat [], sortType)
    unfold := ({} : InferCache).insert (.const `CoreAlias []) sortType }

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  let marker := .const (Name.num `_core_step state.ngen.idx) []
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

private def methods (normalize : Expr → Expr) : TypeChecker.Methods := {
  whnf := fun expression => step (normalize expression)
  whnfCore := fun expression _ _ => step (normalize expression)
  inferType := fun _ _ => throw (.other "unexpected core inference")
  isDefEqCore := fun _ _ => throw (.other "unexpected core comparison") }

private def checkResult {resultType : Type} [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State)) (expected : Option resultType := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "native core transport changed its result or complete state"
    if let some value := expected then
      unless first == value do throwError "native core returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "native core rejected an expected successful result"
  | _, _ => throwError "native core transport changed success/failure"

private def checkCore (actual shadow : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (callbacks : TypeChecker.Methods) (cheapRec cheapProj : Bool)
    (expected : Expr) (steps : Nat) (cached : Option Expr) : MetaM Unit := do
  let result := TypeChecker.Inner.whnfCore' expression cheapRec cheapProj callbacks actual state
  checkResult result (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj callbacks shadow state) (some expected)
  let .ok (_, finalState) := result | throwError "native core callback fixture failed"
  unless finalState.ngen.idx == state.ngen.idx + steps do
    throwError "native core skipped or duplicated a reached callback"
  unless finalState.whnfCoreCache[expression.consumeMData]? == cached do
    throwError "native core changed its branch-specific cache policy for {repr expression}"

private def checkCallbacks (template : RecursorVal) (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) (cheapRec cheapProj : Bool) : MetaM Unit := do
  let natural := .const ``Nat []
  let zero := .const ``Nat.zero []
  let final := .const `CoreFinal []
  let cached := .const `CoreCached []
  let saved := if !cheapRec && !cheapProj then some final else none
  let exhausted := TypeChecker.Methods.withFuel 0
  let easy := [Expr.bvar 0, .sort .zero, .mvar ⟨`CoreMeta⟩, .forallE `argument natural natural .default,
    natural, .lam `argument natural (.bvar 0) .default, .lit (.natVal 2)]
  for expression in easy do
    let state := { state with whnfCoreCache := state.whnfCoreCache.insert expression cached }
    checkCore actual shadow state expression exhausted cheapRec cheapProj expression 0 (some cached)
    checkCore actual shadow state (.mdata {} (.mdata {} expression)) exhausted cheapRec cheapProj expression 0 (some cached)
  let localName : FVarId := ⟨`CoreLocal⟩
  let missing : Expr := .fvar ⟨`CoreMissing⟩
  for nondependent in [false, true] do
    let locals := actual.lctx.mkLetDecl localName `value natural zero nondependent
    let current := { actual with lctx := locals }
    let shadowCurrent := { shadow with lctx := locals }
    let expression := .fvar localName
    let callbacks := methods (fun expression => if expression == zero then final else expression)
    checkCore current shadowCurrent state expression callbacks cheapRec cheapProj final 1 none
    let seeded := { state with whnfCoreCache := state.whnfCoreCache.insert expression cached }
    checkCore current shadowCurrent seeded expression exhausted cheapRec cheapProj cached 0 (some cached)
  let locals := actual.lctx.mkLocalDecl localName `parameter natural .default
  let current := { actual with lctx := locals }
  let shadowCurrent := { shadow with lctx := locals }
  for expression in [.fvar localName, missing] do
    let seeded := { state with whnfCoreCache := state.whnfCoreCache.insert expression cached }
    checkCore current shadowCurrent seeded expression exhausted cheapRec cheapProj expression 0 (some cached)
  let letExpression := .letE `value natural zero (.bvar 0) false
  let letCallbacks := methods (fun expression => if expression == zero then final else expression)
  checkCore actual shadow state letExpression letCallbacks cheapRec cheapProj final 1 saved
  let first := .const `CoreFirst []
  let second := .const `CoreSecond []
  let pair := .const `CorePair []
  let function := .const `CoreFunction []
  let identity := .lam `argument natural (.bvar 0) .default
  let nested := .lam `first natural (.lam `second natural (mkAppN pair #[.bvar 1, .bvar 0]) .default) .default
  let applied := .lam `argument natural (.app function (.bvar 0)) .default
  let betaCases := [(identity, #[first], first),
    (nested, #[first], .lam `second natural (mkAppN pair #[first, .bvar 0]) .default),
    (nested, #[first, second], mkAppN pair #[first, second]),
    (applied, #[first, second], mkAppN function #[first, second])]
  for (normalized, arguments, nextInput) in betaCases do
    let head := .const `CoreBetaHead []
    let expression := mkAppN head arguments
    let callbacks := methods (fun expression =>
      if expression == head then normalized else if expression == nextInput then final else expression)
    checkCore actual shadow state expression callbacks cheapRec cheapProj final 2 saved
    let wrapper := .mdata {} (.mdata {} expression)
    let seeded := { state with whnfCoreCache := state.whnfCoreCache.insert wrapper cached }
    checkCore actual shadow seeded wrapper callbacks cheapRec cheapProj final 2 saved
  let head := .const `CoreRebuiltHead []
  let expression := mkAppN head #[first, second]
  for normalized in [Expr.bvar 0, .sort .zero, .mvar ⟨`CoreRebuiltMeta⟩, .fvar ⟨`CoreRebuiltLocal⟩,
      .forallE `argument natural natural .default, .const `CoreNewHead [], .lit (.natVal 3),
      .letE `value natural zero (.bvar 0) false, .proj ``Prod 0 missing, .mdata {} natural] do
    let nextInput := mkAppN normalized #[first, second]
    let callbacks := methods (fun expression =>
      if expression == head then normalized else if expression == nextInput then final else expression)
    checkCore actual shadow state expression callbacks cheapRec cheapProj final 2 saved
  checkCore actual shadow state expression (methods id) cheapRec cheapProj expression 1 none
  let product := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, first, second]
  let source := .fvar ⟨`CoreProjectionSource⟩
  let projection := .proj ``Prod 1 source
  let callbacks := methods (fun expression =>
    if expression == source then product else if expression == second then final else expression)
  checkCore actual shadow state projection callbacks cheapRec cheapProj final 2 saved
  let missed := .proj ``Prod 9 source
  checkCore actual shadow state missed callbacks cheapRec cheapProj missed 1
    (if !cheapRec && !cheapProj then some missed else none)
  let text := "core projection"
  let callbacks := methods (fun expression =>
    if expression == source then .lit (.strVal text)
    else if expression == .strLitToConstructor text then product
    else if expression == second then final else expression)
  checkCore actual shadow state projection callbacks cheapRec cheapProj final 3 saved
  let info : RecursorVal := { template with
    name := `CoreNative.rec
    levelParams := []
    type := .forallE `major natural natural .default
    numParams := 0, numMotives := 0, numMinors := 0, numIndices := 0
    rules := [{ ctor := ``Nat.zero, nfields := 0, rhs := .const `CoreReduced [] }]
    k := false }
  let current := { actual with env := actual.env.add (.recInfo info) }
  let shadowCurrent := { shadow with env := shadow.env.add (.recInfo info) }
  let major := .fvar ⟨`CoreRecursorMajor⟩
  let recursor := .app (.const info.name []) major
  let callbacks := methods (fun expression =>
    if expression == major then zero else if expression == .const `CoreReduced [] then final else expression)
  checkCore current shadowCurrent state recursor callbacks cheapRec cheapProj final 3 none
  for expression in [letExpression, projection, recursor, mkAppN head #[first, second]] do
    let seeded := { state with whnfCoreCache := state.whnfCoreCache.insert expression cached }
    checkCore current shadowCurrent seeded expression exhausted cheapRec cheapProj cached 0 (some cached)
  let rejected := TypeChecker.Inner.whnfCore' letExpression cheapRec cheapProj exhausted actual state
  checkResult rejected (TypeChecker.Inner.whnfCore' letExpression cheapRec cheapProj exhausted shadow state)
  let .error _ := rejected | throwError "reached core callback did not exhaust fuel"
  let .ok _ := TypeChecker.Inner.whnfCore' letExpression cheapRec cheapProj letCallbacks shadow state |
    throwError "directional core failure control lost its accepted shadow"
  let current := { actual with lctx := actual.lctx.mkLetDecl localName `value natural first }
  let shadowCurrent := { shadow with lctx := shadow.lctx.mkLetDecl localName `value natural second }
  let callbacks := methods id
  let .ok (actualLocal, _) := TypeChecker.Inner.whnfCore' (.fvar localName) cheapRec cheapProj callbacks current state |
    throwError "actual local-context negative control failed"
  let .ok (shadowLocal, _) := TypeChecker.Inner.whnfCore' (.fvar localName) cheapRec cheapProj callbacks shadowCurrent state |
    throwError "shadow local-context negative control failed"
  unless actualLocal == first && shadowLocal == second do
    throwError "environment lookup agreement unexpectedly replaced local-context equality"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State)
    (cheapRec cheapProj : Bool) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 100
  let natural := .const ``Nat []
  let zero := .const ``Nat.zero []
  let localName : FVarId := ⟨`NativeCoreLet⟩
  let proofName : FVarId := ⟨`NativeCoreProof⟩
  let productName : FVarId := ⟨`NativeCoreProduct⟩
  let equality := mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, zero]
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let locals := actual.lctx.mkLetDecl localName `value natural zero
    |>.mkLocalDecl proofName `proof equality .default
    |>.mkLocalDecl productName `pair product .default
  let actual := { actual with lctx := locals }
  let shadow := { shadow with lctx := locals }
  let natMotive := .lam `major natural natural .default
  let natMinor := .lam `predecessor natural (.lam `recursive natural (.app (.const ``Nat.succ []) (.bvar 0)) .default) .default
  let natRecursor := mkAppN (.const ``Nat.rec [.succ .zero]) #[natMotive, zero, natMinor, .lit (.natVal 3)]
  let productMotive := .lam `pair product natural .default
  let productMinor := .lam `first natural (.lam `second natural (.bvar 1) .default) .default
  let productRecursor := mkAppN (.const ``Prod.rec [.succ .zero, .zero, .zero])
    #[natural, natural, productMotive, productMinor, .fvar productName]
  let eqMotive := .lam `target natural
    (.lam `proof (mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, .bvar 0]) natural .default) .default
  let eqRecursor := mkAppN (.const ``Eq.rec [.succ .zero, .succ .zero])
    #[natural, zero, eqMotive, zero, zero, .fvar proofName]
  let terms := [(Expr.fvar localName, zero),
    (.letE `value natural zero (.bvar 0) false, zero),
    (.app (.lam `value natural (.bvar 0) .default) zero, zero),
    (.proj ``Prod 1 (mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, zero, .lit (.natVal 2)]), .lit (.natVal 2)),
    (natRecursor, .lit (.natVal 3)), (eqRecursor, zero),
    (productRecursor, .proj ``Prod 0 (.fvar productName))]
  for (expression, expected) in terms do
    let checked := callbacks.inferType expression false actual state
    checkResult checked (callbacks.inferType expression false shadow state)
    let .ok _ := checked | throwError "native checker rejected the full core expression"
    let result := TypeChecker.Inner.whnfCore' expression cheapRec cheapProj callbacks actual state
    let shadowResult := TypeChecker.Inner.whnfCore' expression cheapRec cheapProj callbacks shadow state
    checkResult result shadowResult
    let .ok (normalized, finalState) := result | throwError "native core rejected an accepted expression"
    let .ok (shadowNormalized, shadowState) := shadowResult | throwError "shadow core rejected an accepted expression"
    checkResult (callbacks.whnf normalized actual finalState) (callbacks.whnf shadowNormalized shadow shadowState) (some expected)

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment) (types : Array InductiveType)
    (template : RecursorVal) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList false) none).isOk do
    throwError "native kernel rejected core transport header fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "core transport header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView env headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "core transport header checkpoint lost accepted constructors"
      let actualReader : TypeChecker.Context := { env := actual, safety := reader.safety }
      let shadowReader := { actualReader with env := shadow }
      let differentReader := { shadowReader with
        safety := .unsafe
        eagerReduce := true
        lparams := [`unusedUniverse]
        fuel := { recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            checkCallbacks template actualReader shadowReader state cheapRec cheapProj
            checkCallbacks template actualReader differentReader state cheapRec cheapProj
            checkNative actualReader shadowReader state cheapRec cheapProj

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderWHNFCoreTransport |
    throwError "native core transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "native core transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "native core unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native core transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  let some (.recInfo template) := environment.find? ``Eq.rec | throwError "native Eq recursor absent"
  checkBatch host environment #[family `CoreSingle] template
  checkBatch host environment #[family `CoreFirst, family `CoreSecond] template
  logInfo "native whnfCore checkpoints, exact beta inputs, complete states, native cache policies and accepted recursive terms passed"

end InductiveHeaderWHNFCoreTransportTest
