import Lean4Lean.Verify.InductiveHeaderRecursiveTransport

namespace InductiveHeaderRecursiveTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

private def natural : Expr := .const ``Nat []
private def sortType : Expr := .sort (.succ .zero)
private def zero : Expr := .lit (.natVal 0)

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .app (.const name []) zero⟩] }

private def headerFields (header : InductiveVal) :=
  (header.name, header.levelParams, header.type, header.numParams, header.numIndices,
    header.all, header.ctors, header.numNested, header.isRec, header.isUnsafe, header.isReflexive)

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
  { ngen := { namePrefix := `_recursive_header, idx := 101 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert (.const `RecursiveAlias []) sortType }

example (actual : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed actual.env shadow) (depth : Nat)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (result : Expr × TypeChecker.State)
    (accepted : (TypeChecker.Methods.withFuel depth).inferType expression inferOnly actual state = .ok result) :
    (TypeChecker.Methods.withFuel depth).inferType expression inferOnly { actual with env := shadow } state = .ok result :=
  (TypeChecker.Methods.withFuel.headerAxiomTransport depth metadata _ _ ⟨rfl, rfl⟩).inferType state expression inferOnly result accepted

example (actual : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed actual.env shadow)
    (state : TypeChecker.State) (expression : Expr) (result : Expr × TypeChecker.State)
    (accepted : TypeChecker.checkType expression actual state = .ok result) :
    TypeChecker.checkType expression { actual with env := shadow } state = .ok result :=
  TypeChecker.checkType.headerAxiomTransport actual shadow metadata state expression result accepted

example (actual : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed actual.env shadow)
    (state : TypeChecker.State) (expression : Expr) (result : Expr × TypeChecker.State)
    (accepted : TypeChecker.ensureType expression actual state = .ok result) :
    TypeChecker.ensureType expression { actual with env := shadow } state = .ok result :=
  TypeChecker.ensureType.headerAxiomTransport actual shadow metadata state expression result accepted

example (actual : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed actual.env shadow) (depth : Nat)
    (state : TypeChecker.State) (name : Name) (binder : BinderInfo) (type : Expr) (argument : Expr) :
    NativeMethodTransport (TypeChecker.Methods.withFuel depth) (TypeChecker.Methods.withFuel depth)
      ((actual.openLocal state name binder type).inferComparisonContext argument)
      (({ actual with env := shadow } : TypeChecker.Context).openLocal state name binder type |>.inferComparisonContext argument) :=
  TypeChecker.Methods.withFuel.headerAxiomTransport depth metadata _ _
    ((NativeHeaderReaderFrame.mk rfl rfl).openLocal state name binder type |>.inferComparisonContext argument)

example (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (constructorHeaders : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : ConstructorsFresh actual types) (constructors : NativeConstructorParentClosure actual)
    (recursors : ∀ name information, actual.find? name = some (.recInfo information) →
      ∃ header, shadow.find? information.getMajorInduct = some (.inductInfo header))
    (quotInit : actual.quotInit = shadow.quotInit) :
    NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual shadow :=
  .beforeConstructors agreement constructorHeaders fresh constructors recursors quotInit

private def checkResult {resultType : Type} [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State))
    (expected : Option resultType := none) : MetaM Unit := do
  match actual with
  | .error _ =>
    if expected.isSome then throwError "native recursive checker rejected an expected success"
  | .ok (value, state) =>
    let .ok (shadowValue, shadowState) := shadow | throwError "shadow rejected an accepted recursive computation"
    unless value == shadowValue && sameState state shadowState do
      throwError "recursive header transport changed its result or complete state"
    if let some expected := expected then
      unless value == expected do throwError "native recursive result {repr value}, expected {repr expected}"

private def checkMethods (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (parent : Expr) : MetaM Unit := do
  let identity : Expr := .lam `value natural (.bvar 0) .default
  let dependentLambda : Expr := .lam `type sortType (.lam `value (.bvar 0) (.bvar 0) .default) .default
  let dependentForall : Expr := .forallE `type sortType (.forallE `value (.bvar 0) (.bvar 1) .default) .default
  let dependentLet : Expr := .letE `type sortType natural (.letE `value (.bvar 0) zero (.bvar 0) false) false
  let eagerArgument := mkAppN (.const `eagerReduce [.succ .zero]) #[natural, zero]
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, .lit (.natVal 2), .lit (.natVal 3)]
  let locals := actual.lctx.mkLocalDecl ⟨`RecursivePair⟩ `pair product .default |>
    fun locals => locals.mkLocalDecl ⟨`RecursiveFirst⟩ `first parent .default |>
      fun locals => locals.mkLocalDecl ⟨`RecursiveSecond⟩ `second parent .default
  let actual := { actual with lctx := locals }
  let shadow := { shadow with lctx := locals }
  let expressions := [natural, zero, parent, identity, dependentLambda, dependentForall, dependentLet,
    .app identity zero, .app identity eagerArgument, .proj ``Prod 0 pair,
    .proj ``Prod 1 (.fvar ⟨`RecursivePair⟩), .mdata {} dependentLambda,
    mkAppN (.const ``Nat.add []) #[.lit (.natVal 2), .lit (.natVal 3)],
    .lit (.strVal "α")]
  for depth in [0, 1, 2, 4, 16] do
    let methods := TypeChecker.Methods.withFuel depth
    for expression in expressions do
      for inferOnly in [false, true] do
        checkResult (methods.inferType expression inferOnly actual state) (methods.inferType expression inferOnly shadow state)
      checkResult (methods.whnf expression actual state) (methods.whnf expression shadow state)
      for cheapRec in [false, true] do
        for cheapProj in [false, true] do
          checkResult (methods.whnfCore expression cheapRec cheapProj actual state)
            (methods.whnfCore expression cheapRec cheapProj shadow state)
    for (first, second) in [(zero, zero), (zero, .lit (.natVal 1)), (identity, identity),
        (dependentLambda, .lam `other sortType (.lam `value (.bvar 0) (.bvar 0) .default) .default),
        (dependentForall, .forallE `other sortType (.forallE `value (.bvar 0) (.bvar 1) .default) .default),
        (.app identity zero, zero), (dependentLet, zero),
        (.fvar ⟨`RecursiveFirst⟩, .fvar ⟨`RecursiveSecond⟩)] do
      checkResult (methods.isDefEqCore first second actual state) (methods.isDefEqCore first second shadow state)
      checkResult (TypeChecker.Inner.isDefEq first second methods actual state)
        (TypeChecker.Inner.isDefEq first second methods shadow state)
  for (expression, expected) in [(identity, Expr.forallE `value natural natural .default),
      (.app identity eagerArgument, natural), (dependentLet, .letE `type sortType natural (.bvar 0) false),
      (.proj ``Prod 1 (.fvar ⟨`RecursivePair⟩), natural)] do
    checkResult (TypeChecker.checkType expression actual state) (TypeChecker.checkType expression shadow state) (some expected)
  checkResult (TypeChecker.ensureType parent actual state) (TypeChecker.ensureType parent shadow state) (some sortType)
  checkResult (TypeChecker.isDefEq (.app identity zero) zero actual state)
    (TypeChecker.isDefEq (.app identity zero) zero shadow state) (some true)

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (types : Array InductiveType) (indices : Array Expr := #[]) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok _ := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected the recursive header fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "recursive header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      unless actual.quotInit == shadow.quotInit do throwError "recursive quotient gate differs"
      for type in types do
        let some (.inductInfo header) := actual.find? type.name | throwError "entered recursive header absent"
        unless header.ctors == type.ctors.map Constructor.name do throwError "entered constructor-name metadata differs"
        for constructor in type.ctors do
          unless (actual.find? constructor.name).isNone do throwError "before-constructor freshness failed"
      for (name, information) in actual.constants.toList do
        if let .ctorInfo information := information then
          let some (.inductInfo parent) := actual.find? information.induct |
            throwError "native constructor-parent closure failed"
          unless parent.ctors.contains name do throwError "native constructor-parent membership failed"
          let some (.inductInfo shadowParent) := shadow.find? information.induct |
            throwError "native constructor lost its shadow inductive parent"
          unless headerFields parent == headerFields shadowParent do throwError "native constructor-parent lookup changed"
        if let .recInfo information := information then
          let some (.inductInfo _) := shadow.find? information.getMajorInduct |
            throwError "native recursor lost its shadow inductive parent"
      for eagerReduce in [false, true] do
        let actualReader : TypeChecker.Context :=
          { env := actual, safety := reader.safety, eagerReduce, fuel := { recDepth := 50, whnf := 20, whnfEager := 30, lazyDelta := 20 } }
        let shadowReader := { actualReader with env := shadow }
        let parent := mkAppN (.const types[0]!.name []) indices
        for state in [({} : TypeChecker.State), seededState] do
          checkMethods actualReader shadowReader state parent
      if indices.isEmpty then
        let .ok registered := declareConstructors stats types isUnsafe { current with env := actual } |
          throwError "recursive metadata barrier constructor registration failed"
        let sharedShadow := types.toList.foldl (fun view type => type.ctors.foldl (fun view constructor =>
          match registered.find? constructor.name with | some information => view.add information | none => view) view) shadow
        let parent : Expr := .const types[0]!.name []
        let locals := LocalContext.empty.mkLocalDecl ⟨`BarrierFirst⟩ `first parent .default |>
          fun locals => locals.mkLocalDecl ⟨`BarrierSecond⟩ `second parent .default
        let actualReader : TypeChecker.Context :=
          { env := registered, lctx := locals, safety := reader.safety, fuel := { recDepth := 50 } }
        let shadowReader := { actualReader with env := sharedShadow }
        let .error _ := TypeChecker.isDefEq (.fvar ⟨`BarrierFirst⟩) (.fvar ⟨`BarrierSecond⟩)
            { actualReader with env := actual } {} |
          throwError "before-constructor actual unit metadata unexpectedly accepted"
        let .ok (false, _) := TypeChecker.isDefEq (.fvar ⟨`BarrierFirst⟩) (.fvar ⟨`BarrierSecond⟩)
            { shadowReader with env := shadow } {} |
          throwError "before-constructor shadow did not retain directional rejection control"
        let .ok (true, _) := TypeChecker.isDefEq (.fvar ⟨`BarrierFirst⟩) (.fvar ⟨`BarrierSecond⟩) actualReader {} |
          throwError "registered unit-like actual comparison did not accept"
        let .ok (false, _) := TypeChecker.isDefEq (.fvar ⟨`BarrierFirst⟩) (.fvar ⟨`BarrierSecond⟩) shadowReader {} |
          throwError "registered constructor metadata barrier disappeared"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderRecursiveTransport |
    throwError "recursive transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "recursive module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "recursive unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native recursive header transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `RecursiveSingle]
  checkBatch host environment #[family `RecursiveFirstFamily, family `RecursiveSecondFamily]
  checkBatch host environment #[indexedFamily `RecursiveIndexed] #[zero]
  logInfo "simultaneous native methods, public checking, scoped/eager readers, complete states and metadata barriers passed"

end InductiveHeaderRecursiveTransportTest
