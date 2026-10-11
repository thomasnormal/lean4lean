import Lean4Lean.Verify.InductiveHeaderNormalizationTransport

open Lean hiding Environment Exception
open Lean4Lean

namespace InductiveHeaderNormalizationTransportTest
open AddInductive

example : Except.SuccessTransport (.error "actual" : Except String Nat)
    (.error 17 : Except Nat Nat) := nofun

example : Except.SuccessTransport (.error "actual" : Except String Nat)
    (.ok 7 : Except Nat Nat) := nofun

example : Except.SuccessTransport (.ok 7 : Except String Nat) (.ok 7 : Except Nat Nat) := by
  intro value accepted
  cases Except.ok.inj accepted
  rfl

example (actual : Except String Nat) (shadow : Except Nat Nat)
    (initial : Except.SuccessTransport actual shadow)
    (actualNext : Nat → Except String Bool) (shadowNext : Nat → Except Nat Bool)
    (continuation : ∀ value, actual = .ok value →
      Except.SuccessTransport (actualNext value) (shadowNext value)) :
    Except.SuccessTransport (actual >>= actualNext) (shadow >>= shadowNext) :=
  Except.SuccessTransport.bind actual shadow actualNext shadowNext initial continuation

example (actual shadow : TypeChecker.M Expr) (actualNext shadowNext : Expr → TypeChecker.M Bool)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (initial : TypeChecker.M.SuccessTransport actual shadow actualContext shadowContext state)
    (continuation : ∀ value finalState, actual actualContext state = .ok (value, finalState) →
      TypeChecker.M.SuccessTransport (actualNext value) (shadowNext value)
        actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport (actual >>= actualNext) (shadow >>= shadowNext)
      actualContext shadowContext state :=
  TypeChecker.M.SuccessTransport.bind actual shadow actualNext shadowNext
    actualContext shadowContext state initial continuation

example (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr)
    (inference : TypeChecker.M.SuccessTransport (actualMethods.inferType expression true)
      (shadowMethods.inferType expression true) actualContext shadowContext state)
    (normalization : ∀ type finalState,
      actualMethods.inferType expression true actualContext state = .ok (type, finalState) →
      TypeChecker.M.SuccessTransport (actualMethods.whnf type) (shadowMethods.whnf type)
        actualContext shadowContext finalState) :
    (TypeChecker.Inner.isProp expression actualMethods actualContext state).WF fun result =>
      TypeChecker.Inner.isProp expression shadowMethods shadowContext state = .ok result :=
  TypeChecker.Inner.isProp.transport actualMethods shadowMethods actualContext shadowContext
    state expression inference normalization

example (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (level : Level) (source : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.ensureSortCore (.sort level) source actualMethods)
      (TypeChecker.Inner.ensureSortCore (.sort level) source shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.ensureSortCore.transport actualMethods shadowMethods actualContext shadowContext state
    (.sort level) source (fun impossible => False.elim (impossible rfl))

example (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (name : Name) (domain body source : Expr) (binder : BinderInfo) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.ensureForallCore (.forallE name domain body binder) source actualMethods)
      (TypeChecker.Inner.ensureForallCore (.forallE name domain body binder) source shadowMethods)
      actualContext shadowContext state :=
  TypeChecker.Inner.ensureForallCore.transport actualMethods shadowMethods actualContext shadowContext state
    (.forallE name domain body binder) source (fun impossible => False.elim (impossible rfl))

private def sortType : Expr := .sort (.succ .zero)

private def quantified : Expr := .forallE `argument sortType sortType .default

private def family (name : Name) (parameters : Nat) : InductiveType :=
  let close := fun body => (List.range parameters).foldr (fun _ body =>
    .forallE `parameter sortType body .implicit) body
  let arguments := (List.range parameters).toArray.map fun index => .bvar (parameters - index - 1)
  { name, type := close sortType, ctors := [⟨name ++ `mk, close (mkAppN (.const name []) arguments)⟩] }

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
  { ngen := { namePrefix := `_normalization_transport, idx := 23 }
    inferTypeI := ({} : InferCache).insert (.const ``Nat []) sortType
    inferTypeC := ({} : InferCache).insert (.const ``Nat []) sortType
    whnfCoreCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    whnfCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (.const ``Nat [], sortType)
    unfold := ({} : InferCache).insert (.const `NormalizationSortAlias []) sortType }

private def checkResult {resultType : Type} [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State))
    (expected : Option resultType := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "normalization transport changed its result or complete state"
    if let some value := expected then
      unless first == value do
        throwError "normalization transport returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "normalization transport rejected an expected successful result"
  | _, _ => throwError "normalization transport changed success/failure"

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  .ok (value, { state with
    ngen := { state.ngen with idx := state.ngen.idx + 1 }
    whnfCache := state.whnfCache.insert (.const `NormalizationStep []) sortType })

private def returning (normalized inferred : Expr) (equal : Bool) : TypeChecker.Methods := {
  whnf := fun _ => step normalized
  whnfCore := fun _ _ _ => step normalized
  inferType := fun _ _ => step inferred
  isDefEqCore := fun _ _ => step equal }

private def checkCallbacks (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  let input := .const `NormalizationInput []
  let failing := TypeChecker.Methods.withFuel 0
  checkResult (TypeChecker.Inner.ensureSortCore sortType input failing actualContext state)
    (TypeChecker.Inner.ensureSortCore sortType input failing shadowContext state) (some sortType)
  checkResult (TypeChecker.Inner.ensureForallCore quantified input failing actualContext state)
    (TypeChecker.Inner.ensureForallCore quantified input failing shadowContext state) (some quantified)
  for normalized in [sortType, quantified, input] do
    let methods := returning normalized sortType true
    checkResult (TypeChecker.Inner.ensureSortCore input input methods actualContext state)
      (TypeChecker.Inner.ensureSortCore input input methods shadowContext state)
      (if normalized.isSort then some normalized else none)
    checkResult (TypeChecker.Inner.ensureForallCore input input methods actualContext state)
      (TypeChecker.Inner.ensureForallCore input input methods shadowContext state)
      (if normalized.isForall then some normalized else none)
    unless (TypeChecker.Inner.ensureSortCore input input methods actualContext state).isOk == normalized.isSort &&
        (TypeChecker.Inner.ensureForallCore input input methods actualContext state).isOk == normalized.isForall do
      throwError "normalization guards accepted the wrong terminal form"
  unless !(TypeChecker.Inner.ensureSortCore input input failing actualContext state).isOk &&
      (TypeChecker.Inner.ensureSortCore input input (returning sortType sortType true) shadowContext state).isOk do
    throwError "directional guard control did not distinguish failing actual and successful shadow callbacks"
  checkResult (TypeChecker.Inner.ensureSortCore input input failing actualContext state)
    (TypeChecker.Inner.ensureSortCore input input failing shadowContext state)
  checkResult (TypeChecker.Inner.ensureForallCore input input failing actualContext state)
    (TypeChecker.Inner.ensureForallCore input input failing shadowContext state)
  for normalized in [Expr.prop, sortType] do
    let methods := returning normalized sortType true
    let actual := TypeChecker.Inner.isProp input methods actualContext state
    checkResult actual (TypeChecker.Inner.isProp input methods shadowContext state) (some (normalized == .prop))
    let .ok (_, finalState) := actual | throwError "stateful isProp callback failed"
    unless finalState.ngen.idx == state.ngen.idx + 2 do
      throwError "isProp did not preserve the two accepted callback state transitions"
  for equal in [false, true] do
    let methods := returning sortType sortType equal
    let actual := TypeChecker.Inner.isDefEq input sortType methods actualContext state
    checkResult actual (TypeChecker.Inner.isDefEq input sortType methods shadowContext state) (some equal)
    let .ok (_, finalState) := actual | throwError "stateful isDefEq callback failed"
    unless finalState.ngen.idx == state.ngen.idx + 1 do throwError "isDefEq lost its callback state"
    unless (EquivManager.isEquiv false input sortType finalState.eqvManager).fst == equal do
      throwError "isDefEq changed the native equivalence-manager update"
  checkResult (TypeChecker.Inner.isProp input failing actualContext state)
    (TypeChecker.Inner.isProp input failing shadowContext state)
  checkResult (TypeChecker.Inner.isDefEq input sortType failing actualContext state)
    (TypeChecker.Inner.isDefEq input sortType failing shadowContext state)
  let field := .const ``Nat.zero []
  let expanded := .app (.const ``Nat.succ []) field
  let text := "transport"
  let methods := { (returning (.lit (.strVal text)) sortType true) with
    whnf := fun expression => step (if expression == Expr.strLitToConstructor text then expanded
      else .lit (.strVal text)) }
  for cheapRec in [false, true] do
    for cheapProj in [false, true] do
      let actual := TypeChecker.Inner.reduceProj 0 input cheapRec cheapProj methods actualContext state
      checkResult actual
        (TypeChecker.Inner.reduceProj 0 input cheapRec cheapProj methods shadowContext state) (some (some field))
      let .ok (_, finalState) := actual | throwError "string expansion callback failed"
      unless finalState.ngen.idx == state.ngen.idx + 2 do throwError "projection lost string-expansion state"

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment) (parameters : Nat)
    (types : Array InductiveType) : MetaM Unit := do
  unless types.isEmpty || (host.addDeclCore 0 (.inductDecl [] parameters types.toList false) none).isOk do
    throwError "native kernel rejected normalization fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          return (stats, ← read, actual)) reader
        | throwError "normalization header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo information) => information
        | _ => default
      let shadow := headerAxiomView env headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "normalization checkpoint did not reach accepted constructor registration"
      let checker : TypeChecker.Context := { env := actual, safety := reader.safety }
      let shadowChecker := { checker with env := shadow }
      let methods := TypeChecker.Methods.withFuel 100
      let field := .const ``Nat.zero []
      let successor := .app (.const ``Nat.succ []) field
      let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[.const ``Nat [], .const ``Nat [], field, successor]
      for state in [({} : TypeChecker.State), seededState] do
        checkCallbacks checker shadowChecker state
        let differentReader := { shadowChecker with
          safety := .unsafe
          eagerReduce := true
          lparams := [`otherUniverse]
          fuel := { recDepth := 0 } }
        checkCallbacks checker differentReader state
        for expression in [sortType, quantified, .const `NormalizationSortAlias [],
            .const `NormalizationForallAlias [], field, .const `NormalizationMissing []] do
          checkResult (TypeChecker.Inner.ensureSortCore expression expression methods checker state)
            (TypeChecker.Inner.ensureSortCore expression expression methods shadowChecker state)
          checkResult (TypeChecker.Inner.ensureForallCore expression expression methods checker state)
            (TypeChecker.Inner.ensureForallCore expression expression methods shadowChecker state)
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            for (expression, index, expected) in [(successor, 0, if cheapProj then some field else none), (successor, 1, none),
                (pair, 0, some field), (pair, 1, some successor), (pair, 2, none), (sortType, 0, none),
                (.app sortType field, 0, none), (.const ``Nat [], 0, none)] do
              checkResult (TypeChecker.Inner.reduceProj index expression cheapRec cheapProj methods checker state)
                (TypeChecker.Inner.reduceProj index expression cheapRec cheapProj methods shadowChecker state)
                (some expected)
            for expression in [.lit (.strVal ""), .lit (.strVal "Lean"), .const `NormalizationMissing []] do
              checkResult (TypeChecker.Inner.reduceProj 0 expression cheapRec cheapProj methods checker state)
                (TypeChecker.Inner.reduceProj 0 expression cheapRec cheapProj methods shadowChecker state)
            for type in types do
              checkResult (TypeChecker.Inner.reduceProj 0 (.const type.name []) cheapRec cheapProj methods checker state)
                (TypeChecker.Inner.reduceProj 0 (.const type.name []) cheapRec cheapProj methods shadowChecker state)
                (some none)
              for constructor in type.ctors do
                if (actual.find? constructor.name).isSome || (shadow.find? constructor.name).isSome then
                  throwError "normalization fixture registered a future constructor too early"
                checkResult (TypeChecker.Inner.reduceProj 0 (.const constructor.name []) cheapRec cheapProj methods checker state)
                  (TypeChecker.Inner.reduceProj 0 (.const constructor.name []) cheapRec cheapProj methods shadowChecker state)
                unless !(TypeChecker.Inner.reduceProj 0 (.const constructor.name []) cheapRec cheapProj
                    methods checker state).isOk do
                  throwError "projection accepted a missing future constructor"
        for expression in [field, .sort .zero, .const ``Nat []] do
          checkResult (TypeChecker.Inner.isProp expression methods checker state)
            (TypeChecker.Inner.isProp expression methods shadowChecker state)
          checkResult (TypeChecker.Inner.isDefEq expression expression methods checker state)
            (TypeChecker.Inner.isDefEq expression expression methods shadowChecker state) (some true)

private def auditModules : MetaM Unit := do
  let environment ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for module in [`Lean4Lean.Verify.TypeChecker.Transport, `Lean4Lean.Verify.InductiveHeaderNormalizationTransport] do
    let some moduleIndex := environment.getModuleIdx? module | throwError "normalization transport module absent"
    let mut count := 0
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "normalization transport module-owned axiom {name}"
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do throwError "normalization unexpected dependency {dependency} in {name}"
          if dependency == ``sorryAx then throwError "normalization transport inherits sorryAx: {name}"
        logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
        count := count + 1
    logInfo m!"{module}: {count} exhaustive production declarations audited"

run_meta
  auditModules
  let imported ← getEnv
  let mut host := imported
  let mut env := imported.toKernelEnv
  for definition in ([
      { name := `NormalizationSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
        value := sortType, hints := .abbrev, safety := .safe },
      { name := `NormalizationForallAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
        value := quantified, hints := .abbrev, safety := .safe }] : List DefinitionVal) do
    let .ok nextHost := host.addDeclCore 0 (.defnDecl definition) none
      | throwError "native normalization seed failed"
    let .ok nextEnv := Lean4Lean.addDecl env (.defnDecl definition) true
      | throwError "normalization seed failed"
    host := nextHost
    env := nextEnv
  checkBatch host env 0 #[family `NormalizationSingle 0]
  checkBatch host env 1 #[family `NormalizationMutualFirst 1, family `NormalizationMutualSecond 1]
  checkBatch host env 0 #[]
  logInfo "native pre-constructor normalization/projection checkpoints, both safety/primitive flags, accepted-prefix state updates, string expansion, complete cache preservation, missing-name and wrong-form controls passed"

end InductiveHeaderNormalizationTransportTest
