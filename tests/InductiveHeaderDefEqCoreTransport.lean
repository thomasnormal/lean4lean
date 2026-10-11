import Lean4Lean.Verify.InductiveHeaderDefEqCoreTransport

namespace InductiveHeaderDefEqCoreTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions Lean.Kernel.Environment.irBaseExts from Lean.Environment

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqCoreCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEqCore' first second actualMethods)
      (TypeChecker.Inner.isDefEqCore' first second shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.isDefEqCore'.headerAxiomTransport _ _ _ _ agreement policy budget _ _ _ callbacks

private def natural : Expr := .const ``Nat []
private def sortType : Expr := .sort (.succ .zero)
private def number (value : Nat) : Expr := .lit (.natVal value)
private def firstSource : Expr := .fvar ⟨`CoreFirstSource⟩
private def secondSource : Expr := .fvar ⟨`CoreSecondSource⟩
private def proofType : Expr := .const `CoreProofType []
private def marker (index : Nat) : Expr := .const (Name.num `_defeq_core_step index) []
private def coreInput (first second : Expr) : Expr := mkAppN (.const `CoreCompare []) #[first, second]
private def inferenceInput (expression : Expr) : Expr := .app (.const `CoreInfer []) expression
private def normalizationInput (expression : Expr) (cheapRec cheapProj : Bool) : Expr :=
  mkAppN (.const `CoreWhnfCore []) #[expression, toExpr cheapRec, toExpr cheapProj]
private def fullInput (expression : Expr) : Expr := .app (.const `CoreWhnf []) expression

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
  { ngen := { namePrefix := `_defeq_core_seed, idx := 127 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert natural sortType }

private def trace (input : Expr) (context : TypeChecker.Context) : Expr :=
  mkAppN (.const `CoreTrace []) #[input, number context.lctx.numIndices]

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

private def methods (comparison := false) (infer : Expr → Expr := fun expression =>
    if expression == .sort .zero then sortType else .sort .zero)
    (normalizeCore : Expr → Bool → Expr := fun expression _ => expression)
    (normalizeFull : Expr → Expr := id) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    isDefEqCore := fun first second => step (coreInput first second) comparison
    inferType := fun expression inferOnly =>
      if inferOnly then step (inferenceInput expression) (infer expression)
      else throw (.other "unreached checked inference")
    whnfCore := fun expression cheapRec cheapProj =>
      step (normalizationInput expression cheapRec cheapProj) (normalizeCore expression cheapProj)
    whnf := fun expression => step (fullInput expression) (normalizeFull expression) }

private def checkResult (actual shadow : Except Kernel.Exception (Bool × TypeChecker.State))
    (expected : Bool) (context : TypeChecker.Context) (state : TypeChecker.State) (inputs : List Expr) : MetaM TypeChecker.State := do
  let (first, firstState) ← ofExceptKernelException actual
  let (second, secondState) ← ofExceptKernelException shadow
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "comparison core changed result/complete state: {first}, {second}, expected {expected}"
  unless firstState.ngen.idx == state.ngen.idx + inputs.length do
    throwError "comparison core callback count {firstState.ngen.idx}, expected {state.ngen.idx + inputs.length}"
  for index in [:inputs.length] do
    unless firstState.inferTypeI[marker (state.ngen.idx + index)]? == some (trace inputs[index]! context) do
      throwError "comparison core callback input/order/reader mismatch at {index}"
  return firstState

private def checkCore (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr)
    (callbacks : TypeChecker.Methods) (expected : Bool) (inputs : List Expr) : MetaM TypeChecker.State := do
  let native := TypeChecker.Inner.isDefEqCore' first second callbacks actual state
  let transported := TypeChecker.Inner.isDefEqCore' first second callbacks shadow state
  let factored := TypeChecker.Inner.nativeDefEqEntry first second callbacks actual state
  let finalState ← try checkResult native transported expected actual state inputs catch error =>
    throwError "comparison core inputs {repr first}, {repr second}: {error.toMessageData}"
  let _ ← checkResult native factored expected actual state inputs
  return finalState

private def cheapInputs (first second : Expr) : List Expr :=
  [normalizationInput first false true, normalizationInput second false true]

private def proofMissInputs (first : Expr) : List Expr :=
  [inferenceInput first, inferenceInput (.sort .zero), fullInput sortType]

private def unchangedInputs (first second : Expr) : List Expr :=
  cheapInputs first second ++ proofMissInputs first ++
    [normalizationInput first false false, normalizationInput second false false,
      inferenceInput first, fullInput (.sort .zero)]

private def withoutValue (environment : Kernel.Environment) (name : Name) : Kernel.Environment :=
  match environment.find? name with
  | some information =>
    let constants := { environment.constants with map₁ := environment.constants.map₁.erase name }
    let cleared := Lean.Kernel.Environment.mk constants environment.quotInit environment.diagnostics environment.const2ModIdx
      (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment) environment.header
    cleared.add (.axiomInfo { toConstantVal := information.toConstantVal, isUnsafe := information.isUnsafe })
  | none => environment

private def checkEarly (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let exhaustedActual := { actual with fuel := { actual.fuel with lazyDelta := 0 } }
  let exhaustedShadow := { shadow with fuel := { shadow.fuel with lazyDelta := 0 } }
  let _ ← checkCore exhaustedActual exhaustedShadow state (number 5) (number 5) (TypeChecker.Methods.withFuel 0) true []
  let _ ← checkCore exhaustedActual exhaustedShadow state (number 5) (number 6) (TypeChecker.Methods.withFuel 0) false []
  for equal in [false, true] do
    for pair in [(.mdata {} firstSource, .mdata {} secondSource),
        (.lam `first natural firstSource .default, .lam `second natural secondSource .default),
        (.forallE `first natural firstSource .default, .forallE `second natural secondSource .default)] do
      let _ ← checkCore exhaustedActual exhaustedShadow state pair.1 pair.2 (methods equal) equal
        [coreInput firstSource secondSource]
  let target := .const ``true []
  let accepting := methods false (normalizeFull := fun _ => target)
  let _ ← checkCore actual shadow state firstSource target accepting true [fullInput firstSource]
  let lazyActual := { actual with eagerReduce := false }
  let lazyShadow := { shadow with eagerReduce := false }
  let replacement := methods false (normalizeCore := fun _ _ => number 5) (normalizeFull := fun _ => target)
  let _ ← checkCore lazyActual lazyShadow state firstSource target replacement true (cheapInputs firstSource target)
  let closed := .const `CoreClosed []
  let _ ← checkCore lazyActual lazyShadow state closed target accepting true [fullInput closed]
  let misses := methods false (normalizeCore := fun _ _ => number 5)
  let _ ← checkCore actual shadow state firstSource target misses true (fullInput firstSource :: cheapInputs firstSource target)
  let actualShortcut := TypeChecker.Inner.nativeDefEqBoolShortcut firstSource target accepting actual state
  let shadowShortcut := TypeChecker.Inner.nativeDefEqBoolShortcut firstSource target accepting lazyShadow state
  unless (actualShortcut matches .ok (true, _)) && (shadowShortcut matches .ok (false, _)) do
    throwError "Boolean shortcut erased the eager-reader policy boundary"

private def checkNormalization (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let _ ← checkCore actual shadow state firstSource secondSource (methods) false (unchangedInputs firstSource secondSource)
  for equal in [false, true] do
    let normalized := methods false (normalizeCore := fun expression _ =>
      if expression == firstSource || equal then number 5 else number 6)
    let _ ← checkCore actual shadow state firstSource secondSource normalized equal (cheapInputs firstSource secondSource)
    let metadata := methods equal (normalizeCore := fun expression _ => .mdata {} expression)
    let _ ← checkCore actual shadow state firstSource secondSource metadata equal
      (cheapInputs firstSource secondSource ++ [coreInput firstSource secondSource])
  let cachedOriginal := { state with eqvManager := state.eqvManager.addEquiv firstSource secondSource }
  unless firstSource.hash != secondSource.hash do throwError "initial hash guard fixture has equal hashes"
  let _ ← checkCore actual shadow cachedOriginal firstSource secondSource (methods) false (unchangedInputs firstSource secondSource)
  let normalizedFirst := .mdata {} firstSource
  let normalizedSecond := .mdata {} secondSource
  let cachedNormalized := { state with eqvManager := state.eqvManager.addEquiv normalizedFirst normalizedSecond }
  let noBody := { methods false (normalizeCore := fun expression _ => .mdata {} expression) with
    isDefEqCore := fun _ _ => throw (.other "unreached non-hash normalized probe body") }
  let _ ← checkCore actual shadow cachedNormalized firstSource secondSource noBody true (cheapInputs firstSource secondSource)
  for equal in [false, true] do
    let changedFull := methods equal (normalizeCore := fun expression cheap => if cheap then expression else .mdata {} expression)
    let changedState ← checkCore actual shadow state firstSource secondSource changedFull equal
      (cheapInputs firstSource secondSource ++ proofMissInputs firstSource ++
        [normalizationInput firstSource false false, normalizationInput secondSource false false,
          coreInput normalizedFirst normalizedSecond])
    unless changedState.eqvManager.toNodeMap[normalizedFirst]? == none &&
        changedState.eqvManager.toNodeMap[normalizedSecond]? == none do
      throwError "full-normalization restart inserted wrapper equivalence around the raw method core"
  let rejected := { methods with whnfCore := fun _ _ _ => throw (.other "core normalization rejected") }
  unless !(TypeChecker.Inner.isDefEqCore' firstSource secondSource rejected actual state).isOk &&
      (TypeChecker.Inner.isDefEqCore' firstSource secondSource (methods) shadow state).isOk do
    throwError "directional normalization rejection was replaced by equality of error actions"

private def checkProofAndDelta (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  for equal in [false, true] do
    let propositional := methods equal (fun expression => if expression == proofType then .sort .zero else proofType)
    let _ ← checkCore actual shadow state firstSource secondSource propositional equal
      (cheapInputs firstSource secondSource ++ [inferenceInput firstSource, inferenceInput proofType, fullInput (.sort .zero),
        inferenceInput secondSource, coreInput proofType proofType])
  let successors := methods true (normalizeCore := fun expression _ => if expression == firstSource then number 3 else number 4)
  let _ ← checkCore actual shadow state firstSource secondSource successors false (cheapInputs firstSource secondSource)
  let first := .const `CoreDelta []
  let _ ← checkCore actual shadow state first secondSource (methods) false
    (cheapInputs first secondSource ++ proofMissInputs first ++ [normalizationInput (number 5) false true,
      normalizationInput (number 5) false false, normalizationInput secondSource false false,
      inferenceInput (number 5), fullInput (.sort .zero)])
  let exhausted := { actual with fuel := { actual.fuel with lazyDelta := 0 } }
  let .error .deterministicTimeout := TypeChecker.Inner.isDefEqCore' firstSource secondSource (methods) exhausted state |
    throwError "undefined proof comparison bypassed exhausted lazy-delta fuel"
  let _ ← checkCore actual shadow state firstSource secondSource (methods) false (unchangedInputs firstSource secondSource)

private def checkSimpleAndFallback (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  for equal in [false, true] do
    let firstProjection := .proj `FirstProjectionParent 1 firstSource
    let secondProjection := .proj `SecondProjectionParent 1 secondSource
    let _ ← checkCore actual shadow state firstProjection secondProjection (methods equal) equal
      (cheapInputs firstProjection secondProjection ++ proofMissInputs firstProjection ++ [coreInput firstSource secondSource] ++
        if equal then [] else [normalizationInput firstProjection false false, normalizationInput secondProjection false false,
          inferenceInput firstProjection, fullInput (.sort .zero)])
  let firstApplication := .app firstSource (number 1)
  let secondApplication := .app secondSource (number 2)
  let applications := methods true
  let _ ← checkCore actual shadow state firstApplication secondApplication applications true
    (cheapInputs firstApplication secondApplication ++ proofMissInputs firstApplication ++
      [normalizationInput firstApplication false false, normalizationInput secondApplication false false,
        coreInput firstSource secondSource, coreInput (number 1) (number 2)])
  let _ ← checkCore actual shadow state firstApplication secondApplication (methods false) false
    (cheapInputs firstApplication secondApplication ++ proofMissInputs firstApplication ++
      [normalizationInput firstApplication false false, normalizationInput secondApplication false false,
        coreInput firstSource secondSource, inferenceInput firstApplication, fullInput (.sort .zero)])
  let sourceLambda := .lam `source natural firstSource .default
  let inferredFunction := .forallE `argument natural natural .implicit
  let eta := methods true (fun expression => if expression == inferredFunction then sortType else if expression == secondSource then inferredFunction
    else if expression == .sort .zero then sortType else .sort .zero)
  let etaExpected := .lam `argument natural (.app secondSource (.bvar 0)) .implicit
  let _ ← checkCore actual shadow state sourceLambda secondSource eta true
    (cheapInputs sourceLambda secondSource ++ proofMissInputs sourceLambda ++
      [normalizationInput sourceLambda false false, normalizationInput secondSource false false,
        inferenceInput secondSource, fullInput inferredFunction, coreInput sourceLambda etaExpected])
  let _ ← checkCore actual shadow state secondSource sourceLambda eta true
    (cheapInputs secondSource sourceLambda ++ [inferenceInput secondSource, inferenceInput inferredFunction, fullInput sortType,
      normalizationInput secondSource false false, normalizationInput sourceLambda false false,
      inferenceInput secondSource, fullInput inferredFunction, coreInput sourceLambda etaExpected])
  let productType := mkAppN (.const ``Prod [.succ .zero, .succ .zero]) #[natural, natural]
  let productConstructor := mkAppN (.const ``Prod.mk [.succ .zero, .succ .zero]) #[natural, natural, number 1, number 2]
  let product := methods true (fun expression => if expression == productType then sortType else productType)
  let _ ← checkCore actual shadow state firstSource productConstructor product true
    (cheapInputs firstSource productConstructor ++ [inferenceInput firstSource, inferenceInput productType, fullInput sortType,
      normalizationInput firstSource false false, normalizationInput productConstructor false false,
      inferenceInput firstSource, inferenceInput productConstructor, coreInput productType productType,
      coreInput (.proj ``Prod 0 firstSource) (number 1), coreInput (.proj ``Prod 1 firstSource) (number 2)])
  let unitType := .const ``PUnit [.succ .zero]
  for equal in [false, true] do
    let unit := methods equal (fun expression => if expression == unitType then sortType else unitType)
    let _ ← checkCore actual shadow state firstSource secondSource unit equal
      (cheapInputs firstSource secondSource ++ [inferenceInput firstSource, inferenceInput unitType, fullInput sortType,
        normalizationInput firstSource false false, normalizationInput secondSource false false,
        inferenceInput firstSource, fullInput unitType, inferenceInput secondSource, coreInput unitType unitType])
  let string := .lit (.strVal "α")
  let expanded := .app (.const ``String.ofList []) firstSource
  for reverse in [false, true] do
    let first := if reverse then expanded else string
    let second := if reverse then string else expanded
    for context in [actual, shadow] do
      let .ok (false, _) := TypeChecker.Inner.isDefEqCore' first second (methods true) context state |
        throwError "delta unfolding did not precede the string fallback in the full core"
    let noDeltaActual := { actual with env := withoutValue actual.env ``String.ofList }
    let noDeltaShadow := { shadow with env := withoutValue shadow.env ``String.ofList }
    let _ ← checkCore noDeltaActual noDeltaShadow state first second (methods true) true
      (cheapInputs first second ++ proofMissInputs first ++
        [normalizationInput first false false, normalizationInput second false false,
          coreInput (Expr.strLitToConstructor "α") expanded])

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .forallE `index natural (.app (.const name []) (.bvar 0)) .default⟩] }

private def checkMetadataBarrier (actual shadow registered shared : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Expr) (indexed : Bool) : MetaM Unit := do
  let callbacks := methods true (fun expression => if expression == parent then sortType else parent)
  let before := TypeChecker.Inner.isDefEqCore' firstSource secondSource callbacks actual state
  let shadowBefore := TypeChecker.Inner.isDefEqCore' firstSource secondSource callbacks shadow state
  if indexed then
    let .ok (false, firstState) := before | throwError "indexed-parent core did not reject unit metadata"
    let .ok (false, secondState) := shadowBefore | throwError "indexed shadow-parent core did not reject unit metadata"
    unless sameState firstState secondState do throwError "indexed-parent core changed complete state"
  else
    unless !before.isOk do throwError "header-only core accepted missing unit constructor metadata"
    let .ok (false, _) := shadowBefore | throwError "axiom-shadow core lost its unit metadata rejection"
    let .ok (true, _) := TypeChecker.Inner.isDefEqCore' firstSource secondSource callbacks registered state |
      throwError "registered actual core did not reach accepting unit metadata"
    let .ok (false, _) := TypeChecker.Inner.isDefEqCore' firstSource secondSource callbacks shared state |
      throwError "shared-constructor axiom shadow erased the complete-core metadata barrier"

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType)
    (indices : Array Expr := #[]) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok _ := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected comparison-core header fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "comparison-core header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual } |
        throwError "comparison-core constructor registration failed"
      let sharedShadow := types.toList.foldl (fun view type => type.ctors.foldl (fun view constructor =>
        match registered.find? constructor.name with | some information => view.add information | none => view) view) shadow
      let locals := LocalContext.empty.mkLocalDecl ⟨`CoreStored⟩ `stored natural .default
      let actualReader : TypeChecker.Context :=
        { env := actual, lctx := locals, safety := reader.safety, eagerReduce := true, fuel := { lazyDelta := 4, recDepth := 8 } }
      let shadowReader := { actualReader with env := shadow, fuel := { lazyDelta := 9, recDepth := 3 } }
      let parent := mkAppN (.const types[0]!.name []) indices
      for state in [({} : TypeChecker.State), seededState] do
        checkEarly actualReader shadowReader state
        checkNormalization actualReader shadowReader state
        checkProofAndDelta actualReader shadowReader state
        checkSimpleAndFallback actualReader shadowReader state
        checkMetadataBarrier actualReader shadowReader { actualReader with env := registered }
          { shadowReader with env := sharedShadow } state parent (!indices.isEmpty)
        for (first, second, expected) in [(number 3, number 4, false), (.const `CoreDelta [], number 5, true),
            (.const `CoreDelta [], number 6, false), (toExpr ("α" : String), toExpr ("β" : String), false)] do
          let native := TypeChecker.Methods.withFuel 16
          let (value, finalState) ← ofExceptKernelException (TypeChecker.Inner.isDefEqCore' first second native actualReader state)
          let (shadowValue, shadowState) ← ofExceptKernelException (TypeChecker.Inner.isDefEqCore' first second native shadowReader state)
          unless value == expected && shadowValue == expected && sameState finalState shadowState do
            throwError "recursive native comparison core lost its expected result/complete state"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderDefEqCoreTransport |
    throwError "comparison-core transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "comparison-core module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "comparison-core unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native comparison core: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let .ok host := host.addDeclCore 0 (.defnDecl
      { name := `CoreDelta, levelParams := [], type := natural, value := number 5, hints := .regular 1, safety := .safe }) none |
    throwError "native kernel rejected comparison-core delta fixture"
  let environment := host.toKernelEnv
  checkBatch host environment #[family `CoreSingle]
  checkBatch host environment #[family `CoreFirstFamily, family `CoreSecondFamily]
  checkBatch host environment #[indexedFamily `CoreIndexed] #[number 0]
  logInfo "complete native comparison-core gates, reached callbacks, state sequencing and metadata barriers passed"

end InductiveHeaderDefEqCoreTransportTest
