import Lean4Lean.Verify.InductiveHeaderProjectionTransport

namespace InductiveHeaderProjectionTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions Lean.Kernel.Environment.irBaseExts from Lean.Environment

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams) (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeHeaderInferCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferType' expression inferOnly actualMethods)
      (TypeChecker.Inner.inferType' expression inferOnly shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.inferType'.headerAxiomCallbackTransport _ _ _ _ agreement locals safety parameters _ _ _ callbacks

example (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (headers : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : ConstructorsFresh actual types) (parent : Name) : NativeProjectionMetadataFrame actual shadow parent :=
  NativeProjectionMetadataFrame.ofConstructorFreshness agreement headers fresh parent

private def sortType : Expr := .sort (.succ .zero)

private def natural : Expr := .const ``Nat []

private def truth : Expr := .const ``True []

private def source : Expr := .fvar ⟨`ProjectionSource⟩

private def typeAlias : Expr := .const `ProjectionTypeAlias []

private def number (value : Nat) : Expr := .lit (.natVal value)

private def replaceConstant (environment : Kernel.Environment) (information : ConstantInfo) : Kernel.Environment :=
  let constants := { environment.constants with
    map₁ := environment.constants.map₁.insert information.name information
    map₂ := environment.constants.map₂.erase information.name }
  Lean.Kernel.Environment.mk constants environment.quotInit environment.diagnostics environment.const2ModIdx
    (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment) environment.header

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
  { ngen := { namePrefix := `_projection_seed, idx := 71 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert typeAlias sortType }

private def step {resultType : Type} (input : Expr) (value : resultType) : TypeChecker.M resultType := fun context state =>
  let marker := .const (Name.num `_projection_step state.ngen.idx) []
  let trace := mkAppN (.const `ProjectionTrace []) #[input, number context.lctx.numIndices]
  let (_, manager) := state.eqvManager.toNode marker
  .ok (value, { state with
    ngen := state.ngen.next
    inferTypeI := state.inferTypeI.insert marker trace
    inferTypeC := state.inferTypeC.insert marker trace
    whnfCoreCache := state.whnfCoreCache.insert marker input
    whnfCache := state.whnfCache.insert marker input
    eqvManager := manager
    failure := state.failure.insert (input, marker)
    unfold := state.unfold.insert marker trace })

private def methods (normalized : Expr) (rootProp domainsProp : Bool) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    whnf := fun expression => step expression (if expression == typeAlias then normalized else expression)
    inferType := fun expression inferOnly =>
      if !inferOnly then throw (.other "unreached checked proposition inference")
      else step expression (.sort (if rootProp && (expression == normalized || domainsProp) then .zero else .succ .zero))
    isDefEqCore := fun _ _ => throw (.other "unreached projection comparison")
    whnfCore := fun _ _ _ => throw (.other "unreached projection whnfCore") }

private def checkResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State))
    (expected : Expr) (state : TypeChecker.State) (calls : Option Nat := none) : MetaM TypeChecker.State := do
  let .ok (first, firstState) := actual | throwError "actual projection rejected {repr expected}"
  let .ok (second, secondState) := shadow | throwError "shadow projection rejected accepted result"
  unless first == expected && second == expected && sameState firstState secondState do
    throwError "projection changed result or complete state: {repr first}, {repr second}, expected {repr expected}"
  if let some count := calls then
    unless firstState.ngen.idx == state.ngen.idx + count do
      throwError "projection callback count {firstState.ngen.idx}, expected {state.ngen.idx + count}"
  return firstState

private def invalid (result : Except Kernel.Exception (Expr × TypeChecker.State)) : Bool :=
  match result with
  | .error (.invalidProj _ _ _) => true
  | _ => false

private def checkScript (actual shadow : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (levels : List Level) (arguments : Array Expr) (dependent : Bool)
    (first second : Expr) : MetaM Unit := do
  let normalized := mkAppN (.const parent levels) arguments
  for rootProp in [false, true] do
    for domainsProp in [false, true] do
      let callbacks := methods normalized rootProp domainsProp
      let alternate := { callbacks with isDefEqCore := fun _ _ => step natural true }
      for (index, expected) in [(0, first), (1, second)] do
        let actualResult := TypeChecker.Inner.inferProj parent index source typeAlias callbacks actual state
        let shadowResult := TypeChecker.Inner.inferProj parent index source typeAlias alternate shadow state
        if rootProp && !domainsProp then
          unless invalid actualResult && invalid shadowResult do throwError "projection skipped a reached proposition-domain restriction"
        else
          let calls := 6 + index + (if rootProp then 2 + (if dependent && index == 1 then 2 else 0) else 0)
          let finalState ← checkResult actualResult shadowResult expected state calls
          let .some (.inductInfo header) := actual.env.find? parent | throwError "script parent metadata missing"
          let [constructor] := header.ctors | throwError "script parent lacks singleton constructor"
          let some information := actual.env.find? constructor | throwError "script constructor absent"
          let marker : Expr := .const (Name.num `_projection_step (state.ngen.idx + 1)) []
          unless finalState.whnfCoreCache[marker]? == some (information.instantiateTypeLevelParams levels) do
            throwError "projection parameter loop did not normalize its exact initial constructor type"

private def checkScripts (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let familyType : Expr := .lam `argument natural natural .default
  checkScript actual shadow state ``Prod [.zero, .zero] #[natural, natural] false natural natural
  checkScript actual shadow state ``Sigma [.zero, .zero] #[natural, familyType] true natural
    (.app familyType (.proj ``Sigma 0 source))
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let callbacks := methods product false false
  let alternate := { callbacks with whnfCore := fun expression _ _ => step expression expression }
  for (parent, index, structureType) in [(``Sigma, 0, product), (``Prod, 0, .sort .zero),
      (``Prod, 0, .const ``Prod [.zero, .zero]), (``Prod, 2, product), (``Prod, 3, product),
      (``Nat, 0, natural), (``Option, 0, mkApp (.const ``Option [.zero]) natural)] do
    unless invalid (TypeChecker.Inner.inferProj parent index source structureType callbacks actual state) &&
        invalid (TypeChecker.Inner.inferProj parent index source structureType alternate shadow state) do
      throwError "projection wrong-head/arity/constructor/field control did not reject"
  let rejecting := { callbacks with whnf := fun expression => step expression (.sort .zero) }
  unless !(TypeChecker.Inner.inferProj ``Prod 0 source typeAlias rejecting actual state).isOk &&
      (TypeChecker.Inner.inferProj ``Prod 0 source typeAlias alternate shadow state).isOk do
    throwError "projection normalization control lost directional acceptance"
  let .some (.inductInfo header) := actual.env.find? ``Prod | throwError "Prod metadata absent"
  let [constructor] := header.ctors | throwError "Prod constructors changed"
  let some information := actual.env.find? constructor | throwError "Prod constructor absent"
  let forged : InductiveVal :=
    { header with name := constructor, type := information.type, levelParams := information.levelParams, ctors := [] }
  let taggedActual := { actual with env := replaceConstant actual.env (.inductInfo forged) }
  let taggedShadow := { shadow with env := replaceConstant shadow.env (headerAxiomInfo forged) }
  let .some (.inductInfo _) := taggedActual.env.find? constructor | throwError "raw constructor-tag control did not replace actual lookup"
  let .some (.axiomInfo _) := taggedShadow.env.find? constructor | throwError "raw constructor-tag control did not replace shadow lookup"
  let _ ← checkResult (TypeChecker.Inner.inferProj ``Prod 0 source product callbacks taggedActual state)
    (TypeChecker.Inner.inferProj ``Prod 0 source product alternate taggedShadow state) natural state (some 6)
  let missingHeader := { header with name := `ProjectionMissingParent, ctors := [`ProjectionMissingCtor] }
  let missingActual := { actual with env := actual.env.add (.inductInfo missingHeader) }
  let missingType := mkAppN (.const missingHeader.name [.zero, .zero]) #[natural, natural]
  unless !(TypeChecker.Inner.inferProj missingHeader.name 0 source missingType callbacks missingActual state).isOk do
    throwError "projection accepted a missing constructor"
  let axiomShadow := { shadow with env := replaceConstant shadow.env (headerAxiomInfo header) }
  let .some (.axiomInfo _) := axiomShadow.env.find? ``Prod | throwError "raw parent-tag control did not replace parent lookup"
  unless (TypeChecker.Inner.inferProj ``Prod 0 source product callbacks actual state).isOk &&
      invalid (TypeChecker.Inner.inferProj ``Prod 0 source product alternate axiomShadow state) do
    throwError "projection metadata barrier vanished despite identical retained constructor signatures"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let familyType : Expr := .lam `argument natural natural .default
  let predicate : Expr := .lam `argument natural truth .default
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let sigma := mkAppN (.const ``Sigma [.zero, .zero]) #[natural, familyType]
  let subtype := mkAppN (.const ``Subtype [.succ .zero]) #[natural, predicate]
  let conjunction := mkAppN (.const ``And []) #[truth, truth]
  let existential := mkAppN (.const ``Exists [.succ .zero]) #[natural, predicate]
  let cases := [(``Prod, product, 0, natural), (``Prod, product, 1, natural),
    (``Sigma, sigma, 0, natural), (``Sigma, sigma, 1, .app familyType (.proj ``Sigma 0 source)),
    (``Subtype, subtype, 0, natural), (``Subtype, subtype, 1, .app predicate (.proj ``Subtype 0 source)),
    (``And, conjunction, 0, truth), (``And, conjunction, 1, truth)]
  let callbacks := TypeChecker.Methods.withFuel 1000
  let alternate := TypeChecker.Methods.withFuel 1001
  for (parent, structureType, index, expected) in cases do
    let locals := actual.lctx.mkLocalDecl ⟨`ProjectionSource⟩ `source structureType .default
    let actualReader := { actual with lctx := locals }
    let shadowReader := { shadow with lctx := locals }
    let _ ← checkResult (TypeChecker.Inner.inferProj parent index source structureType callbacks actualReader state)
      (TypeChecker.Inner.inferProj parent index source structureType alternate shadowReader state) expected state
    for inferOnly in [false, true] do
      let expression := .proj parent index source
      let _ ← checkResult (TypeChecker.Inner.inferType' expression inferOnly callbacks actualReader state)
        (TypeChecker.Inner.inferType' expression inferOnly alternate shadowReader state) expected state
  for index in [0, 1] do
    unless invalid (TypeChecker.Inner.inferProj ``Exists index source existential callbacks actual state) &&
        invalid (TypeChecker.Inner.inferProj ``Exists index source existential alternate shadow state) do
      throwError "native existential projection violated the propositional dependent-field restriction"

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .forallE `field natural (.const name []) .default⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default,
    ctors := [⟨name ++ `mk, .forallE `index natural (.app (.const name []) (.bvar 0)) .default⟩] }

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (types : Array InductiveType) (indices : Array Expr := #[]) : MetaM Unit := do
  for isUnsafe in [false, true] do
    let .ok nativeHost := host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none |
      throwError "native kernel rejected projection header fixture"
    let nativeSourceType := mkAppN (.const types[0]!.name []) indices
    let projectionDeclaration := Declaration.defnDecl
      { name := types[0]!.name ++ `project, levelParams := [],
        type := .forallE `source nativeSourceType natural .default,
        value := .lam `source nativeSourceType (.proj types[0]!.name 0 (.bvar 0)) .default,
        hints := .opaque, safety := if isUnsafe then .unsafe else .safe }
    unless (nativeHost.addDeclCore 0 projectionDeclaration none).isOk do
      throwError "native kernel rejected explicit fixture projection definition"
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "projection header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView environment headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
        throwError "projection checkpoint lost constructor acceptance"
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual } |
        throwError "projection fixture failed constructor registration"
      let outer := LocalContext.empty.mkLocalDecl ⟨`ProjectionOuter⟩ `outer natural .default
      let actualReader : TypeChecker.Context := { env := actual, lctx := outer, safety := reader.safety, eagerReduce := true, fuel := { whnf := 8 } }
      let shadowReader := { actualReader with env := shadow, eagerReduce := false, fuel := { whnf := 12, recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkScripts actualReader shadowReader state
        checkNative actualReader shadowReader state
        let parent := types[0]!.name
        let structureType := mkAppN (.const parent []) indices
        let callbacks := TypeChecker.Methods.withFuel 1000
        let alternate := TypeChecker.Methods.withFuel 1001
        let sourceLocals := outer.mkLocalDecl ⟨`ProjectionSource⟩ `source structureType .default
        let parentActualReader := { actualReader with lctx := sourceLocals }
        let parentShadowReader := { shadowReader with lctx := sourceLocals }
        let before := TypeChecker.Inner.inferProj parent 0 source structureType callbacks parentActualReader state
        unless !before.isOk && invalid (TypeChecker.Inner.inferProj parent 0 source structureType alternate parentShadowReader state) do
          throwError "staged new-parent projection accepted before future constructors"
        let registeredReader := { parentActualReader with env := registered }
        let after := TypeChecker.Inner.inferProj parent 0 source structureType callbacks registeredReader state
        let _ ← checkResult after after natural state
        unless invalid (TypeChecker.Inner.inferProj parent 0 source structureType alternate parentShadowReader state) do
          throwError "registered new-parent projection transported through an axiom shadow"
        for inferOnly in [false, true] do
          let expression := .proj parent 0 source
          let actualEntry := TypeChecker.Inner.inferType' expression inferOnly callbacks registeredReader state
          let _ ← checkResult actualEntry actualEntry natural state
          unless invalid (TypeChecker.Inner.inferType' expression inferOnly alternate parentShadowReader state) do
            throwError "registered new-parent inference entry transported through an axiom shadow"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderProjectionTransport |
    throwError "projection transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "projection transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "projection transport unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native projection transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `ProjectionSingle]
  checkBatch host environment #[family `ProjectionFirstFamily, family `ProjectionSecondFamily]
  checkBatch host environment #[indexedFamily `ProjectionIndexedFamily] #[number 4]
  logInfo "native projection loops, reached propositions, metadata/freshness frames and axiom-shadow barriers passed"

end InductiveHeaderProjectionTransportTest
