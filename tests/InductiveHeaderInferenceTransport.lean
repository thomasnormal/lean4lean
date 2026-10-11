import Lean4Lean.Verify.InductiveHeaderInferenceTransport

namespace InductiveHeaderInferenceTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions Lean.Kernel.Environment.irBaseExts from Lean.Environment

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) : NativeInferAppCallbacks methods methods context context state expression := by
  constructor
  · exact Except.SuccessTransport.refl _
  · intros
    constructor
    intros
    exact Except.SuccessTransport.refl _

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (inferOnly : Bool) : NativeInferCallbacks methods methods context context state expression inferOnly := by
  constructor
  · intros
    constructor
    · exact Except.SuccessTransport.refl _
    · intros
      constructor
      intros
      exact Except.SuccessTransport.refl _
  all_goals intros; exact Except.SuccessTransport.refl _

example (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeInferCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferType' expression inferOnly actualMethods)
      (TypeChecker.Inner.inferType' expression inferOnly shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.inferType'.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext
    agreement locals safety parameters state expression inferOnly callbacks

private def sortType : Expr := .sort (.succ .zero)

private def natural : Expr := .const ``Nat []

private def number (value : Nat) : Expr := .lit (.natVal value)

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def withoutConstants (environment : Kernel.Environment) (names : List Name) : Kernel.Environment :=
  let constants := { environment.constants with
    map₁ := names.foldl (fun entries name => entries.erase name) environment.constants.map₁
    map₂ := names.foldl (fun entries name => entries.erase name) environment.constants.map₂ }
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
  { ngen := { namePrefix := `_inference_transport, idx := 83 }
    inferTypeI := ({} : InferCache).insert natural sortType
    inferTypeC := ({} : InferCache).insert natural sortType
    whnfCoreCache := ({} : InferCache).insert natural natural
    whnfCache := ({} : InferCache).insert natural natural
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (natural, sortType)
    unfold := ({} : InferCache).insert (.const `InferenceAlias []) sortType }

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  let marker := .const (Name.num `_infer_step state.ngen.idx) []
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

private def methods (infer : Expr → Bool → Expr) (normalize : Expr → Expr) (equal : Bool := true) : TypeChecker.Methods :=
  { TypeChecker.Methods.withFuel 0 with
    inferType := fun expression inferOnly => step (infer expression inferOnly)
    whnf := fun expression => step (normalize expression)
    isDefEqCore := fun _ _ => step equal }

private def checkResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State))
    (expected : Option Expr := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "native inference changed its result or complete state"
    if let some value := expected then
      unless first == value do throwError "native inference returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "native inference rejected an expected successful result"
  | _, _ => throwError "native inference changed success/failure"

private def seedInference (state : TypeChecker.State) (expression value : Expr) (inferOnly : Bool) : TypeChecker.State :=
  if inferOnly then { state with inferTypeI := state.inferTypeI.insert expression value }
  else { state with inferTypeC := state.inferTypeC.insert expression value }

private def checkInference (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr)
    (inferOnly : Bool) (actualMethods shadowMethods : TypeChecker.Methods) (expected : Expr) (calls : Nat := 0) : MetaM Unit := do
  let actualResult := TypeChecker.Inner.inferType' expression inferOnly actualMethods actual state
  let shadowResult := TypeChecker.Inner.inferType' expression inferOnly shadowMethods shadow state
  checkResult actualResult shadowResult expected
  let .ok (_, finalState) := actualResult | throwError "native inference checkpoint failed"
  unless finalState.ngen.idx == state.ngen.idx + calls && (finalState.inferenceCache inferOnly)[expression]? == some expected do
    throwError "native inference changed its callback count or final selected cache insertion"

private def checkApplications (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let head := .const `InferenceHead []
  let typeAlias := .const `InferenceTypeAlias []
  let first := number 4
  let second := number 5
  let functionType := .forallE `first natural (.forallE `second natural (.bvar 1) .default) .default
  let identityType := .forallE `first natural (.bvar 0) .default
  let normalized := .forallE `second natural (.bvar 0) .default
  let cases := [(#[], functionType, functionType, 1),
    (#[first], functionType, .forallE `second natural first .default, 1),
    (#[first, second], functionType, first, 1),
    (#[typeAlias, second], identityType, second, 2),
    (#[first, second], typeAlias, first, 2)]
  for (arguments, initialType, expected, calls) in cases do
    let expression := mkAppN head arguments
    let callbacks := methods (fun _ inferOnly => if inferOnly then initialType else natural)
      (fun expression => if expression == typeAlias then (if initialType == typeAlias then functionType else normalized) else expression)
    let alternate := { callbacks with whnfCore := fun expression _ _ => step expression }
    let actualResult := TypeChecker.Inner.inferApp expression callbacks actual state
    let shadowResult := TypeChecker.Inner.inferApp expression alternate shadow state
    checkResult actualResult shadowResult expected
    let .ok (_, finalState) := actualResult | throwError "native inferApp checkpoint failed"
    unless finalState.ngen.idx == state.ngen.idx + calls do throwError "native inferApp visited an unreached normalization"
    unless arguments.isEmpty do checkInference actual shadow state expression true callbacks alternate expected calls
  let expression := mkAppN head #[first]
  let rejecting := methods (fun _ _ => typeAlias) id
  let accepting := methods (fun _ _ => typeAlias) (fun _ => normalized)
  unless !(TypeChecker.Inner.inferApp expression rejecting actual state).isOk &&
      (TypeChecker.Inner.inferApp expression accepting shadow state).isOk do
    throwError "directional application normalization control lost asymmetric acceptance"
  let wrapped := .mdata {} (.app head first)
  let stale := .const `InferenceStale []
  let overwriting : TypeChecker.Methods := { methods (fun _ _ => functionType) id with
    inferType := fun _ _ context currentState =>
      match step functionType context currentState with
      | .error error => .error error
      | .ok (result, finalState) => .ok (result, seedInference (seedInference finalState wrapped stale true) wrapped stale false) }
  let alternate := { overwriting with whnfCore := fun expression _ _ => step expression }
  let expected := .forallE `second natural first .default
  checkInference actual shadow state wrapped true overwriting alternate expected 1
  let .ok (_, finalState) := TypeChecker.Inner.inferType' wrapped true overwriting actual state |
    throwError "inference cache overwrite control failed"
  unless finalState.inferTypeI[wrapped]? == some expected && finalState.inferTypeC[wrapped]? == some stale do
    throwError "inference cache reread a stale body insertion or overwrote the other mode"

private def checkEntries (actual shadow : TypeChecker.Context) (state : TypeChecker.State) (header : Name) : MetaM Unit := do
  let exhausted := TypeChecker.Methods.withFuel 0
  let cached := .const `InferenceCached []
  let locals := actual.lctx.mkLocalDecl ⟨`InferenceLocal⟩ `parameter natural .default
  let current := { actual with lctx := locals, lparams := [`InferenceUniverse] }
  let shadowCurrent := { shadow with lctx := locals, lparams := [`InferenceUniverse] }
  let parameter := Level.param `InferenceUniverse
  for inferOnly in [false, true] do
    for (expression, expected) in [(number 7, natural), (.lit (.strVal "transport"), .const ``String []),
        (.sort parameter, .sort (.succ parameter)), (.const header [], sortType), (.fvar ⟨`InferenceLocal⟩, natural)] do
      checkInference current shadowCurrent state expression inferOnly exhausted exhausted expected
      let opposite := seedInference state expression cached (!inferOnly)
      checkInference current shadowCurrent opposite expression inferOnly exhausted exhausted expected
      let wrapped := .mdata {} (.mdata {} expression)
      checkInference current shadowCurrent state wrapped inferOnly exhausted exhausted expected
      let .ok (_, finalState) := TypeChecker.Inner.inferType' wrapped inferOnly exhausted current state |
        throwError "metadata inference failed"
      unless (finalState.inferenceCache inferOnly)[expression]? == some expected &&
          (finalState.inferenceCache inferOnly)[Expr.mdata {} expression]? == some expected do
        throwError "metadata inference omitted an inner or wrapper cache entry"
      let seeded := seedInference state wrapped cached inferOnly
      checkInference current shadowCurrent seeded wrapped inferOnly exhausted exhausted cached
      let .ok (_, finalState) := TypeChecker.Inner.inferType' wrapped inferOnly exhausted current seeded |
        throwError "metadata cache-hit inference failed"
      unless sameState seeded finalState do throwError "metadata cache hit reached its child"
    for expression in [Expr.mvar ⟨`InferenceMeta⟩, .fvar ⟨`InferenceMissing⟩,
        .sort (.param `InferenceUnknownUniverse), .const header [.zero]] do
      let seeded := seedInference state expression cached inferOnly
      checkInference current shadowCurrent seeded expression inferOnly exhausted exhausted cached
      let .ok (_, finalState) := TypeChecker.Inner.inferType' expression inferOnly exhausted current seeded |
        throwError "closed inference cache hit failed"
      unless sameState seeded finalState do throwError "closed inference cache hit changed state"
    for expression in [Expr.bvar 0, .app (.const ``Nat.succ []) (.bvar 0), .mdata {} (.bvar 2)] do
      let seeded := seedInference state expression cached inferOnly
      unless !(TypeChecker.Inner.inferType' expression inferOnly exhausted current seeded).isOk &&
          !(TypeChecker.Inner.inferType' expression inferOnly exhausted shadowCurrent seeded).isOk do
        throwError "loose-variable rejection occurred after an invalid cache hit"
    for expression in [Expr.mvar ⟨`InferenceMeta⟩, .fvar ⟨`InferenceMissing⟩] do
      unless !(TypeChecker.Inner.inferType' expression inferOnly exhausted current state).isOk do
        throwError "unsupported or missing-variable inference stopped rejecting"
  let unknownSort := .sort (.param `InferenceUnknownUniverse)
  unless (TypeChecker.Inner.inferType' unknownSort true exhausted current state).isOk &&
      !(TypeChecker.Inner.inferType' unknownSort false exhausted current state).isOk do
    throwError "inference-only universe checking no longer differs from checked inference"
  let knownSort := .sort parameter
  unless (TypeChecker.Inner.inferType' knownSort false exhausted current state).isOk &&
      !(TypeChecker.Inner.inferType' knownSort false exhausted { shadowCurrent with lparams := [] } state).isOk do
    throwError "universe-reader negative control did not distinguish checked inference"
  let differentLocals := actual.lctx.mkLocalDecl ⟨`InferenceLocal⟩ `parameter sortType .default
  let .ok (actualType, _) := TypeChecker.Inner.inferType' (.fvar ⟨`InferenceLocal⟩) false exhausted current state |
    throwError "actual local-reader negative control failed"
  let .ok (shadowType, _) := TypeChecker.Inner.inferType' (.fvar ⟨`InferenceLocal⟩) false exhausted
      { shadowCurrent with lctx := differentLocals } state | throwError "shadow local-reader negative control failed"
  unless actualType == natural && shadowType == sortType do
    throwError "header lookup agreement unexpectedly determined the local reader"
  if actual.safety == .unsafe then
    unless (TypeChecker.Inner.inferType' (.const header []) false exhausted actual state).isOk &&
        !(TypeChecker.Inner.inferType' (.const header []) false exhausted { shadow with safety := .safe } state).isOk do
      throwError "safety-reader negative control failed to distinguish checked headers"
  for (literal, missing, expected) in [(Literal.natVal 3, [``Nat], natural),
      (.strVal "transport", [``Char.ofNat], .const ``String []),
      (.strVal "transport", [``String.ofList], .const ``String [])] do
    let current := { actual with env := withoutConstants actual.env missing }
    let shadowCurrent := { shadow with env := withoutConstants shadow.env missing }
    checkInference current shadowCurrent state (.lit literal) true exhausted exhausted expected
    unless !(TypeChecker.Inner.inferType' (.lit literal) false exhausted current state).isOk &&
        !(TypeChecker.Inner.inferType' (.lit literal) false exhausted shadowCurrent state).isOk do
      throwError "checked literal inference skipped native signature-presence checks"

private def checkCheckedApplication (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let function : Expr := .fvar ⟨`InferenceFunction⟩
  let functionType := .forallE `value natural natural .default
  let locals := actual.lctx.mkLocalDecl ⟨`InferenceFunction⟩ `function functionType .default
  let current := { actual with lctx := locals, eagerReduce := false }
  let shadowCurrent := { shadow with lctx := locals, eagerReduce := false }
  let eager := mkAppN (.const ``eagerReduce [.succ .zero]) #[natural, number 4]
  let callbacks : TypeChecker.Methods := { methods (fun _ _ => natural) id with
    isDefEqCore := fun _ _ context currentState =>
      if context.eagerReduce then step true context currentState else .error (.other "comparison was not eager") }
  let alternate := { callbacks with whnfCore := fun expression _ _ => step expression }
  let seeded := seedInference state eager natural false
  let expression := .app function eager
  checkInference current shadowCurrent seeded expression false callbacks alternate natural 1
  let .ok (_, finalState) := TypeChecker.Inner.inferType' expression false callbacks current seeded |
    throwError "checked eager application failed"
  unless !(callbacks.isDefEqCore natural natural current finalState).isOk do
    throwError "eager application changed its outer reader"
  for argument in [number 4, .app (.const ``eagerReduce [.succ .zero]) natural] do
    let seeded := seedInference state argument natural false
    unless !(TypeChecker.Inner.inferType' (.app function argument) false callbacks current seeded).isOk do
      throwError "non-eager argument shape activated eager comparison"
  let accepting := methods (fun _ _ => natural) id
  checkInference current shadowCurrent state (.app function (number 4)) false accepting
    { accepting with whnfCore := fun expression _ _ => step expression } natural 1
  let rejecting := methods (fun _ _ => natural) id false
  unless !(TypeChecker.Inner.inferType' (.app function (number 4)) false rejecting current state).isOk do
    throwError "checked application stopped rejecting a false comparison"
  let functionAlias := .const `InferenceFunctionAlias []
  let seeded := seedInference state function functionAlias false
  let normalizing := methods (fun _ _ => natural) (fun expression => if expression == functionAlias then functionType else expression)
  checkInference current shadowCurrent seeded (.app function (number 4)) false normalizing
    { normalizing with whnfCore := fun expression _ _ => step expression } natural 2
  let badFunction := seedInference state function natural false
  unless !(TypeChecker.Inner.inferType' (.app function (number 4)) false accepting current badFunction).isOk do
    throwError "checked application accepted a non-function type"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let callbacks := TypeChecker.Methods.withFuel 1000
  let shadowCallbacks := TypeChecker.Methods.withFuel 1001
  let identity := .lam `value natural (.bvar 0) .default
  let functionType := .forallE `value natural natural .default
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, number 2, number 3]
  let cases := [(identity, functionType), (.forallE `value natural natural .default, sortType),
    (.letE `value natural (number 2) (.bvar 0) false, natural), (.app identity (number 4), natural),
    (pair, product), (.proj ``Prod 1 pair, natural),
    (mkAppN (.const ``Nat.add []) #[number 4, number 5], natural),
    (mkAppN (.const ``eagerReduce [.succ .zero]) #[natural, number 4], natural)]
  for inferOnly in [false, true] do
    for (expression, expected) in cases do
      let checked := callbacks.inferType expression false actual state
      let shadowChecked := shadowCallbacks.inferType expression false shadow state
      checkResult checked shadowChecked expected
      let .ok (_, checkedState) := checked | throwError "native checker rejected complete inference fixture"
      let .ok (_, shadowState) := shadowChecked | throwError "shadow checker rejected complete inference fixture"
      checkResult (TypeChecker.Inner.inferType' expression inferOnly callbacks actual state)
        (TypeChecker.Inner.inferType' expression inferOnly shadowCallbacks shadow state) expected
      checkResult (TypeChecker.Inner.inferType' expression inferOnly callbacks actual checkedState)
        (TypeChecker.Inner.inferType' expression inferOnly shadowCallbacks shadow shadowState) expected

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList false) none).isOk do
    throwError "native kernel rejected inference transport header fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env := environment, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "inference transport header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView environment headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "inference transport checkpoint lost accepted constructors"
      let actualReader : TypeChecker.Context := { env := actual, safety := reader.safety, fuel := { whnf := 8 } }
      let shadowReader := { actualReader with env := shadow, fuel := { whnf := 12, recDepth := 0 } }
      for state in [({} : TypeChecker.State), seededState] do
        checkApplications actualReader shadowReader state
        checkEntries actualReader shadowReader state types[0]!.name
        checkCheckedApplication actualReader shadowReader state
        checkNative actualReader shadowReader state

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderInferenceTransport |
    throwError "inference transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "inference transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "inference transport unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native inference transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkBatch host environment #[family `InferenceSingle]
  checkBatch host environment #[family `InferenceFirstFamily, family `InferenceSecondFamily]
  logInfo "native inference, reached application loops, selected caches, metadata and eager comparison passed"

end InductiveHeaderInferenceTransportTest
