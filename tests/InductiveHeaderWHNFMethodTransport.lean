import Lean4Lean.Verify.InductiveHeaderWHNFMethodTransport

namespace InductiveHeaderWHNFMethodTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

private def natural : Expr := .const ``Nat []
private def sortType : Expr := .sort (.succ .zero)
private def major : Expr := .fvar ⟨`MethodMajor⟩
private def zero : Expr := .const ``Nat.zero []
private def successor : Expr := .app (.const ``Nat.succ []) zero

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
  { ngen := { namePrefix := `_whnf_method, idx := 83 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert (.const `MethodAlias []) sortType }

private def step {resultType : Type} (tag : Name) (value : resultType) : TypeChecker.M resultType := fun _ state =>
  let marker := .const (Name.num tag state.ngen.idx) []
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

private def traceMethods (equal : Bool) : TypeChecker.Methods := {
  whnf := fun expression => step `MethodFull (if expression == major then zero else expression)
  whnfCore := fun expression cheapRec cheapProj =>
    step (if cheapRec then if cheapProj then `MethodCoreBoth else `MethodCoreRec
      else if cheapProj then `MethodCoreProj else `MethodCore)
      (if expression == major then successor else expression)
  inferType := fun expression _ => step `MethodInfer (if expression == natural then sortType else natural)
  isDefEqCore := fun _ _ => step `MethodCompare equal }

private theorem traceTransport (equal : Bool) (actual shadow : TypeChecker.Context) :
    NativeMethodTransport (traceMethods equal) (traceMethods equal) actual shadow := by
  constructor <;> intros <;> intro result accepted <;> exact accepted

example (equal : Bool) (actual shadow : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actual.env shadow.env)
    (parents : NativeRecursorParentFrame actual.env shadow.env)
    (quotInit : actual.env.quotInit = shadow.env.quotInit) (state : TypeChecker.State)
    (expression : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj (traceMethods equal))
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj (traceMethods equal)) actual shadow state :=
  (traceTransport equal actual shadow).recursorReduction agreement parents quotInit state expression cheapRec cheapProj

example (equal : Bool) (actual shadow : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actual.env shadow.env)
    (parents : NativeRecursorParentFrame actual.env shadow.env)
    (quotInit : actual.env.quotInit = shadow.env.quotInit) (locals : actual.lctx = shadow.lctx)
    (budget : actual.whnfBudget ≤ shadow.whnfBudget) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.whnf' expression (traceMethods equal))
      (TypeChecker.Inner.whnf' expression (traceMethods equal)) actual shadow state :=
  (traceTransport equal actual shadow).whnfStep agreement parents quotInit locals budget state expression

example (agreement : HeaderAxiomLookupAgreement changed actual shadow)
    (parents : NativeRecursorParentsClosed original)
    (origins : ∀ name info, actual.find? name = some (.recInfo info) → original.find? name = some (.recInfo info))
    (retained : ∀ name header, original.find? name = some (.inductInfo header) →
      shadow.find? name = some (.inductInfo header)) : NativeRecursorParentFrame actual shadow :=
  .ofNativeOrigins agreement parents origins retained

example (depth : Nat) (actual shadow : TypeChecker.Context)
    (transport : NativeMethodTransport (TypeChecker.Methods.withFuel depth) (TypeChecker.Methods.withFuel depth) actual shadow)
    (agreement : HeaderAxiomLookupAgreement changed actual.env shadow.env)
    (parents : NativeRecursorParentFrame actual.env shadow.env)
    (quotInit : actual.env.quotInit = shadow.env.quotInit) (locals : actual.lctx = shadow.lctx)
    (budget : actual.whnfBudget ≤ shadow.whnfBudget) (state : TypeChecker.State) (expression : Expr)
    (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel (depth + 1)).whnfCore expression cheapRec cheapProj)
      ((TypeChecker.Methods.withFuel (depth + 1)).whnfCore expression cheapRec cheapProj) actual shadow state :=
  (TypeChecker.Methods.withFuel.normalizationStep depth actual shadow transport agreement parents quotInit locals budget).1
    state expression cheapRec cheapProj

example (actual shadow : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actual.env shadow.env)
    (parents : NativeRecursorParentFrame actual.env shadow.env)
    (quotInit : actual.env.quotInit = shadow.env.quotInit) (locals : actual.lctx = shadow.lctx)
    (budget : actual.whnfBudget ≤ shadow.whnfBudget) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel 1).whnf expression)
      ((TypeChecker.Methods.withFuel 1).whnf expression) actual shadow state :=
  (TypeChecker.Methods.withFuel.normalizationDepthOne actual shadow agreement parents quotInit locals budget).2 state expression

example (normalize : Expr → TypeChecker.RecM Expr) (methods : TypeChecker.Methods)
    (context : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport
      (inductiveReduceRec context.env expression normalize TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq methods)
      (inductiveReduceRec context.env expression normalize TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq methods)
      context context state := by
  apply inductiveReduceRec.headerAxiomNormalizationTransport normalize methods methods context context
    (changed := fun _ => False) (fun _ => .inl rfl) state expression
  all_goals intros; first | rfl | exact Except.SuccessTransport.refl _

private def checkResult {resultType : Type} [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State))
    (expected : Option resultType := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "method-step result or complete state differs"
    if let some expected := expected then
      unless first == expected do throwError "method-step returned {repr first}, expected {repr expected}"
  | .error _, .error _ =>
    if expected.isSome then throwError "method-step rejected an expected success"
  | _, _ => throwError "method-step changed acceptance"

private def checkRecursors (template : RecursorVal) (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  for isK in [false, true] do
    let info : RecursorVal := { template with
      name := `MethodDispatch.rec, levelParams := []
      type := .forallE `major natural sortType .default
      numParams := 0, numMotives := 0, numMinors := 0, numIndices := 0, k := isK
      rules := [{ ctor := ``Nat.zero, nfields := 0, rhs := .lit (.natVal 17) },
        { ctor := ``Nat.succ, nfields := 1, rhs := .lam `field natural (.lit (.natVal 23)) .default }] }
    let actual := { actual with env := actual.env.add (.recInfo info) }
    let shadow := { shadow with env := shadow.env.add (.recInfo info) }
    let expression := .app (.const info.name []) major
    for equal in [false, true] do
      let methods := traceMethods equal
      for cheapRec in [false, true] do
        for cheapProj in [false, true] do
          let expected := if cheapRec && (!isK || !equal) then
            some (.app (.lam `field natural (.lit (.natVal 23)) .default) zero)
            else some (.lit (.natVal 17))
          let run := fun reader => TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods reader state
          checkResult (run actual) (run shadow) (some expected)
          let .ok (_, finalState) := run actual | throwError "derived recursor callback fixture failed"
          let steps := if isK then 5 else 1
          unless finalState.ngen.idx == state.ngen.idx + steps do
            throwError "K/major callback sequencing changed"
          let finalTag := if cheapRec then if cheapProj then `MethodCoreBoth else `MethodCoreRec else `MethodFull
          let tags := if isK then #[`MethodInfer, finalTag, `MethodInfer, `MethodCompare, finalTag] else #[finalTag]
          for index in [:tags.size] do
            let marker : Expr := .const (Name.num tags[index]! (state.ngen.idx + index)) []
            unless finalState.unfold[marker]?.isSome do
              throwError "cheap-rec/cheap-proj normalization selected the wrong method"

private def checkNormalization (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let methods := traceMethods true
  let applications := [
    .letE `value natural (.lit (.natVal 2)) (.bvar 0) false,
    .app (.lam `value natural (.bvar 0) .default) (.lit (.natVal 2)),
    .proj ``Prod 0 (mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, zero, successor]),
    .app (.const ``Nat.succ []) zero,
    mkAppN (.const ``Nat.add []) #[zero, .lit (.natVal 2)]]
  for expression in applications do
    for cheapRec in [false, true] do
      for cheapProj in [false, true] do
        checkResult (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods actual state)
          (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods shadow state)
    checkResult (TypeChecker.Inner.whnf' expression methods actual state)
      (TypeChecker.Inner.whnf' expression methods shadow state)
  let native := TypeChecker.Methods.withFuel 50
  for (expression, expected) in [
      (.app (.const ``Nat.succ []) zero, .lit (.natVal 1)),
      (mkAppN (.const ``Nat.add []) #[.lit (.natVal 2), .lit (.natVal 3)], .lit (.natVal 5)),
      (.letE `value natural (.lit (.natVal 7)) (.bvar 0) false, .lit (.natVal 7))] do
    checkResult (native.whnf expression actual state) (native.whnf expression shadow state) (some expected)
  for expression in [natural, .lit (.natVal 4), .fvar ⟨`MethodLocal⟩,
      .mdata {} (.lit (.natVal 4)), .app (.const ``Nat.succ []) zero] do
    let shallow := TypeChecker.Methods.withFuel 1
    checkResult (shallow.whnf expression actual state) (shallow.whnf expression shadow state)
  let exhausted := TypeChecker.Methods.withFuel 0
  let .error .deepRecursion := exhausted.whnf natural actual state |
    throwError "depth-zero normalization unexpectedly accepted"
  let .error .deepRecursion := exhausted.whnf natural shadow state |
    throwError "depth-zero shadow normalization unexpectedly accepted"

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (types : Array InductiveType) : MetaM Unit := do
  let some (.recInfo template) := environment.find? ``Nat.rec | throwError "native Nat recursor absent"
  for isUnsafe in [false, true] do
    let .ok _ := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected the method-step header fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (_, _, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "method-step header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      for (name, information) in actual.constants.toList do
        if let .recInfo info := information then
          let some (.recInfo originalInfo) := environment.find? name |
            throwError "header staging introduced a recursor"
          unless originalInfo == info do throwError "header staging changed an old recursor"
          let some (.inductInfo _) := shadow.find? info.getMajorInduct |
            throwError "old recursor lost its shadow inductive parent"
      let locals := LocalContext.empty.mkLocalDecl ⟨`MethodLocal⟩ `local natural .default
      let actualReader : TypeChecker.Context :=
        { env := actual, lctx := locals, safety := reader.safety,
          eagerReduce := true, fuel := { recDepth := 8, whnfEager := 8 } }
      let shadowReader := { actualReader with env := shadow, eagerReduce := false, fuel := { recDepth := 3, whnf := 12 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkRecursors template actualReader shadowReader state
        checkNormalization actualReader shadowReader state
      let changed := types[0]!.name
      let barrier : RecursorVal := { template with
        name := `MethodBarrier.rec
        type := .forallE `major (.const changed []) sortType .default,
        numParams := 0, numMotives := 0, numMinors := 0, numIndices := 0 }
      let barrierActual := actual.add (.recInfo barrier)
      let barrierShadow := shadow.add (.recInfo barrier)
      let some (.inductInfo _) := barrierActual.find? barrier.getMajorInduct |
        throwError "new-parent recursor actual metadata absent"
      let some (.axiomInfo _) := barrierShadow.find? barrier.getMajorInduct |
        throwError "new-parent recursor metadata barrier disappeared"

private def auditModule (moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "method-step module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "module-owned axiom {name}"
      let axioms ← collectAxioms name
      let logic := [``propext, ``Classical.choice, ``Quot.sound]
      let allowed := if name == ``HeaderAxiomLookupAgreement.stableOriginalInductiveParent then
        logic ++ [``Lean.PersistentHashMap.findAux_isSome] else logic
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"{moduleName}: {count} exhaustive production declarations audited"

run_meta
  for moduleName in [`Lean4Lean.Verify.InductiveHeaderRecursorTransport,
      `Lean4Lean.Verify.InductiveHeaderReductionTransport, `Lean4Lean.Verify.InductiveHeaderWHNFMethodTransport] do
    auditModule moduleName
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `MethodSingle]
  checkBatch host environment #[family `MethodFirst, family `MethodSecond]
  logInfo "native normalization method-step, cheap policies, staging origins, complete states and metadata barriers passed"

end InductiveHeaderWHNFMethodTransportTest
