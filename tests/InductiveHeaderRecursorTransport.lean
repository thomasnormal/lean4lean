import Lean4Lean.Verify.InductiveHeaderRecursorTransport

namespace InductiveHeaderRecursorTransportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

example {root : TypeChecker.VContext} {original reader : Context} {parameters : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual : Kernel.Environment}
    (stage : HeaderAxiomContinuation root original parameters types stats reader actual)
    (parent : Name) (header : InductiveVal)
    (present : reader.env.constants.find? parent = some (.inductInfo header)) :
    actual.find? parent = stage.shadow.find? parent :=
  stage.lookups.stableOriginalInductiveParent stage.values parent header present

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
  { ngen := { namePrefix := `_recursor_transport, idx := 31 }
    inferTypeI := ({} : InferCache).insert (.const ``Nat []) sortType
    inferTypeC := ({} : InferCache).insert (.const ``Nat []) sortType
    whnfCoreCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    whnfCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (.const ``Nat [], sortType)
    unfold := ({} : InferCache).insert (.const `RecursorAlias []) sortType }

private def checkResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State))
    (expected : Option Expr := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "recursor adaptation changed its expression or complete state"
    if let some value := expected then
      unless first == value do throwError "recursor adaptation returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "recursor adaptation rejected an expected successful result"
  | _, _ => throwError "recursor adaptation changed success/failure"

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  .ok (value, { state with
    ngen := { state.ngen with idx := state.ngen.idx + 1 }
    whnfCache := state.whnfCache.insert (.const `RecursorStep []) sortType })

private def callbacks (source inferred propertyType : Expr) (equal : Bool) : TypeChecker.Methods := {
  whnf := fun expression => step expression
  whnfCore := fun expression _ _ => step expression
  inferType := fun expression _ => step (if expression == source then inferred else propertyType)
  isDefEqCore := fun _ _ => step equal }

private def runK (info : RecursorVal) (expression : Expr) (methods : TypeChecker.Methods)
    (reader : TypeChecker.Context) (state : TypeChecker.State) : Except Kernel.Exception (Expr × TypeChecker.State) :=
  toCtorWhenK reader.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
    info expression methods reader state

private def runStructure (parent : Name) (expression : Expr) (methods : TypeChecker.Methods)
    (reader : TypeChecker.Context) (state : TypeChecker.State) : Except Kernel.Exception (Expr × TypeChecker.State) :=
  toCtorWhenStruct reader.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType parent expression methods reader state

private def checkKCallbacks (info : RecursorVal) (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  unless info.k && info.getMajorInduct == ``Eq do throwError "K fixture did not select the native Eq recursor"
  let source := .fvar ⟨`RecursorProof⟩
  let zero := .const ``Nat.zero []
  let parameter := .const ``Nat []
  let metavariable := .mvar ⟨`RecursorMeta⟩
  let types := [sortType, .const ``Bool [], mkAppN (.const ``Eq [.succ .zero]) #[parameter, zero, zero],
    mkAppN (.const ``Eq [.succ .zero]) #[parameter, zero, metavariable],
    mkAppN (.const ``Eq [.succ .zero]) #[metavariable, zero, zero]]
  for type in types do
    for equal in [false, true] do
      let methods := callbacks source type type equal
      let eligible := type.getAppFn.isConstOf info.getMajorInduct &&
        !((type.getAppArgs[info.numParams]?).any Expr.hasExprMVar)
      let selected := if eligible then mkNullaryCtor actual.env type info.numParams else none
      let expected := if eligible && equal then selected.getD source else source
      let result := runK info source methods actual state
      checkResult result (runK info source methods shadow state) (some expected)
      let .ok (_, finalState) := result | throwError "K callback fixture failed"
      unless finalState.ngen.idx == state.ngen.idx + (if eligible && selected.isSome then 4 else 2) do
        throwError "K adaptation lost a callback state transition"
  let failing := TypeChecker.Methods.withFuel 0
  checkResult (runK info source failing actual state) (runK info source failing shadow state)
  let emptyParent : RecursorVal := { info with
    type := .forallE `major (.const ``False []) Expr.prop .default
    numParams := 0
    numMotives := 0
    numMinors := 0
    numIndices := 0 }
  let emptyMethods := callbacks source (.const ``False []) sortType true
  checkResult (runK emptyParent source emptyMethods actual state)
    (runK emptyParent source emptyMethods shadow state) (some source)

private def checkStructureCallbacks (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  let source := .fvar ⟨`RecursorStructure⟩
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[.const ``Nat [], .const ``Nat []]
  let constructor := mkAppN (.const ``Prod.mk [.zero, .zero])
    #[.const ``Nat [], .const ``Nat [], .const ``Nat.zero [], .const ``Nat.zero []]
  let failing := TypeChecker.Methods.withFuel 0
  for (parent, expression) in [(``Nat, source), (``Prod, constructor), (`RecursorMissingParent, source)] do
    checkResult (runStructure parent expression failing actual state)
      (runStructure parent expression failing shadow state) (some expression)
  for type in [sortType, .const ``Bool [], product] do
    for propertyType in [Expr.prop, sortType] do
      let methods := callbacks source type propertyType true
      let matching := type.getAppFn.isConstOf ``Prod
      let expected := if matching && propertyType != .prop then expandEtaStruct actual.env type source else source
      let result := runStructure ``Prod source methods actual state
      checkResult result (runStructure ``Prod source methods shadow state) (some expected)
      let .ok (_, finalState) := result | throwError "structure callback fixture failed"
      unless finalState.ngen.idx == state.ngen.idx + (if matching then 4 else 2) do
        throwError "structure adaptation lost its reached callback state"
  checkResult (runStructure ``Prod source failing actual state) (runStructure ``Prod source failing shadow state)

private def checkChangedParent (actual shadow : TypeChecker.Context) (type : InductiveType)
    (info : RecursorVal) (state : TypeChecker.State) : MetaM Unit := do
  let source := .fvar ⟨`RecursorChangedParent⟩
  let parent := .const type.name []
  let synthetic : RecursorVal := { info with
    name := `RetainedMalformed.rec
    levelParams := []
    type := .forallE `major parent Expr.prop .default
    numParams := 0
    numMotives := 0
    numMinors := 0
    numIndices := 0
    rules := [{ ctor := type.name ++ `mk, nfields := 0, rhs := .const ``Nat.zero [] }]
    k := true }
  let methods := callbacks source parent Expr.prop true
  let .ok (adapted, _) := runK synthetic source methods actual state | throwError "actual changed-parent K control failed"
  let .ok (unchanged, _) := runK synthetic source methods shadow state | throwError "shadow changed-parent K control failed"
  unless adapted == .const (type.name ++ `mk) [] && unchanged == source && adapted != unchanged do
    throwError "changed-parent control did not expose the necessary eligibility obligation"
  let oldActual := { actual with env := actual.env.add (.recInfo synthetic) }
  let oldShadow := { shadow with env := shadow.env.add (.recInfo synthetic) }
  let expression := .app (.const synthetic.name []) source
  let reduce := fun (reader : TypeChecker.Context) => inductiveReduceRec reader.env expression TypeChecker.Inner.whnf
    TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq methods reader state
  let .ok (first, _) := reduce oldActual | throwError "actual malformed-parent recursor control failed"
  let .ok (second, _) := reduce oldShadow | throwError "shadow malformed-parent recursor control failed"
  unless first == some (.const ``Nat.zero []) && second == none do
    throwError "exact old recursor records unexpectedly sufficed without stable parent metadata"

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment) (types : Array InductiveType)
    (info : RecursorVal) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList false) none).isOk do
    throwError "native kernel rejected recursor transport fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "recursor header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView env headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "recursor checkpoint did not reach accepted constructor registration"
      let checker : TypeChecker.Context := { env := actual, safety := reader.safety }
      let shadowChecker := { checker with env := shadow }
      let methods := TypeChecker.Methods.withFuel 100
      let zero := .const ``Nat.zero []
      let equality := mkAppN (.const ``Eq [.succ .zero]) #[.const ``Nat [], zero, zero]
      let product := mkAppN (.const ``Prod [.zero, .zero]) #[.const ``Nat [], .const ``Nat []]
      let proofName : FVarId := ⟨`NativeRecursorProof⟩
      let productName : FVarId := ⟨`NativeRecursorProduct⟩
      let locals := checker.lctx.mkLocalDecl proofName `proof equality .default
        |>.mkLocalDecl productName `product product .default
      for state in [({} : TypeChecker.State), seededState] do
        checkKCallbacks info checker shadowChecker state
        checkStructureCallbacks checker shadowChecker state
        let differentReader := { shadowChecker with
          safety := .unsafe
          eagerReduce := true
          lparams := [`unusedUniverse]
          fuel := { recDepth := 0 } }
        checkKCallbacks info checker differentReader state
        checkStructureCallbacks checker differentReader state
        let nativeActual := { checker with lctx := locals }
        let nativeShadow := { shadowChecker with lctx := locals }
        checkResult (runK info (.fvar proofName) methods nativeActual state)
          (runK info (.fvar proofName) methods nativeShadow state) (mkNullaryCtor actual equality info.numParams)
        checkResult (runStructure ``Prod (.fvar productName) methods nativeActual state)
          (runStructure ``Prod (.fvar productName) methods nativeShadow state)
          (some (expandEtaStruct actual product (.fvar productName)))
        for type in types do
          unless getFirstCtor actual type.name != getFirstCtor shadow type.name &&
              actual.isStructureLike type.name && !shadow.isStructureLike type.name do
            throwError "changed-parent fixture lost its native metadata difference"
          checkChangedParent checker shadowChecker type info state

private def auditModules : MetaM Unit := do
  let environment ← getEnv
  let logic := [``propext, ``Classical.choice, ``Quot.sound]
  for module in [`Lean4Lean.Verify.TypeChecker.Transport, `Lean4Lean.Verify.InductiveHeaderRecursorTransport] do
    let some moduleIndex := environment.getModuleIdx? module | throwError "recursor transport module absent"
    let mut count := 0
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "recursor transport module-owned axiom {name}"
        let axioms ← collectAxioms name
        let allowed := if name == ``HeaderAxiomLookupAgreement.stableOriginalInductiveParent then
          logic ++ [``Lean.PersistentHashMap.findAux_isSome] else logic
        for dependency in axioms do
          unless allowed.contains dependency do throwError "recursor unexpected dependency {dependency} in {name}"
          if dependency == ``sorryAx then throwError "recursor transport inherits sorryAx: {name}"
        logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
        count := count + 1
    logInfo m!"{module}: {count} exhaustive production declarations audited"

run_meta
  auditModules
  let imported ← getEnv
  let environment := imported.toKernelEnv
  let some (.recInfo info) := environment.find? ``Eq.rec | throwError "native Eq recursor absent"
  checkBatch imported environment #[family `RecursorSingle] info
  checkBatch imported environment #[family `RecursorMutualFirst, family `RecursorMutualSecond] info
  logInfo "native K/structure pre-constructor checkpoints, complete states, metavariable scans, original-parent stability and malformed retained-rec-parent negative controls passed"

end InductiveHeaderRecursorTransportTest
