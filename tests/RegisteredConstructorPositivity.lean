import Lean4Lean.Verify.InductivePositivity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace RegisteredConstructorPositivityTest

private def stage (nparams : Nat) (types : Array InductiveType) (numNested : Nat := 0) :
    M (InductiveStats × Context) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types numNested false) do
      checkConstructors types stats false
      return (stats, ← readThe Context)

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ (stats : InductiveStats) (current : Context) (headers : Kernel.Environment),
      stats.HeaderSizes types.size → stats.ParamsCount nparams types.size →
      stats.ParamsAreFVars → stats.params.toList.Nodup → ctx.HeaderFrame current →
      stats.SafeConstructorTraces types PositivityWHNF { current with env := headers } →
      (next stats { current with env := headers }).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        next stats) ctx).WF post :=
  checkInductiveTypes.registeredSafeConstructors nparams types numNested next ctx post hnext

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) (numNested : Nat) :
    (stage nparams types numNested ctx).WF fun result =>
      result.1.RegisteredSafeConstructorTraces nparams types ctx result.2 :=
  checkInductiveTypes.getRegisteredSafeConstructorTraces nparams types numNested ctx

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (stats : InductiveStats) (root : Context)
    (hchecked : stage nparams types numNested ctx = .ok (stats, root)) :
    stats.RegisteredSafeConstructorTraces nparams types ctx root :=
  checkInductiveTypes.getRegisteredSafeConstructorTraces nparams types numNested ctx _ hchecked

example (ctx root : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hchecked : stats.RegisteredSafeConstructorTraces nparams types ctx root)
    (parent : Nat) (hparent : parent < types.size) (ctor : Constructor)
    (hctor : ctor ∈ types[parent].ctors) :
    ∃ terminal, SafeConstructorTrace stats PositivityWHNF parent root 0 ctor.type terminal :=
  hchecked.2.2.2.2.2 parent hparent ctor hctor

example (ctx root : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hchecked : stats.RegisteredSafeConstructorTraces nparams types ctx root) :
    root.lparams = ctx.lparams ∧ root.safety = ctx.safety ∧
      root.allowPrimitive = ctx.allowPrimitive ∧ root.fuel = ctx.fuel := by
  obtain ⟨_, _, _, _, hframe, _⟩ := hchecked
  exact ⟨hframe.lparams, hframe.safety, hframe.allowPrimitive, hframe.fuel⟩

example (ctx root : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hchecked : stats.RegisteredSafeConstructorTraces nparams types ctx root)
    (hnonempty : types.size ≠ 0) : stats.params.size = nparams := by
  simpa [InductiveStats.ParamsCount, hnonempty] using hchecked.2.1

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def fuelValues (fuel : FuelConfig) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (fuel.whnf, fuel.whnfEager, fuel.lazyDelta, fuel.etaExpand, fuel.recDepth, fuel.inductiveFuel)

private def checkRoot (ctx root : Context) (stats : InductiveStats)
    (nparams numNested : Nat) (types : Array InductiveType) : MetaM Unit := do
  unless stats.params.size == (if types.isEmpty then 0 else nparams) &&
      stats.nindices.size == types.size && stats.indConsts.size == types.size &&
      stats.params.all Expr.isFVar && stats.params.toList.eraseDups.length == stats.params.size do
    throwError "incorrect checked statistics"
  let scopes := stats.params.size + stats.nindices.foldl (· + ·) 0
  let expectedNames := scopes.fold (fun _ _ ngen => ngen.next) ctx.ngen
  unless root.lparams == ctx.lparams && root.safety == ctx.safety &&
      root.allowPrimitive == ctx.allowPrimitive && fuelValues root.fuel == fuelValues ctx.fuel &&
      root.ngen.curr == expectedNames.curr && root.lctx.numIndices == ctx.lctx.numIndices + scopes do
    throwError "incorrect registered trace-root context"
  let natHeader (env : Kernel.Environment) := (env.find? ``Nat).map (·.type)
  unless natHeader root.env == natHeader ctx.env do
    throwError "header registration changed an imported constant"
  for parent in [:types.size] do
    let type := types[parent]!
    let some (.inductInfo info) := root.env.find? type.name
      | throwError "missing registered header {type.name}"
    unless info.type == type.type && info.numParams == nparams &&
        info.numIndices == stats.nindices[parent]! && info.numNested == numNested &&
        info.levelParams == ctx.lparams && info.isUnsafe == false do
      throwError "incorrect installed datatype header {type.name}"
    for ctor in type.ctors do
      unless root.env.contains ctor.name == false do
        throwError "prefix unexpectedly registered constructor {ctor.name}"

private def checkStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Bool) (numNested : Nat := 0) : MetaM Unit := do
  let result := stage nparams types numNested ctx
  unless result.isOk == expected do
    match result with
    | .error error =>
      throwError "incorrect registered-prefix outcome for {types.map (·.name)}: \
        {error.toMessageData (← getOptions)}"
    | .ok _ => throwError "unexpected registered-prefix success for {types.map (·.name)}"
  if let .ok (stats, root) := result then
    checkRoot ctx root stats nparams numNested types

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``checkInductiveTypes.registeredSafeConstructors
  audit ``checkInductiveTypes.getRegisteredSafeConstructorTraces
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let natType := Expr.const ``Nat []
  let zero := Expr.const `RegisteredZero []
  let one := Expr.const `RegisteredOne []
  let other := Expr.const `RegisteredOther []
  let two := Expr.const `RegisteredTwo []
  let base : Constructor := { name := `RegisteredBase, type := zero }
  let recursive : Constructor := {
    name := `RegisteredRecursive, type := .forallE `value zero zero .default }
  let positive : Constructor := {
    name := `RegisteredPositive, type := .forallE `function
      (.forallE `index natType zero .default) zero .implicit }
  let negative : Constructor := {
    name := `RegisteredNegative, type := .forallE `function
      (.forallE `value zero natType .default) zero .default }
  let parameterOnly : Constructor := {
    name := `RegisteredParameter, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterRecursive : Constructor := {
    name := `RegisteredTail, type := closeParams 1
      (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let parameterField : Constructor := {
    name := `RegisteredValue, type := closeParams 1
      (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `RegisteredMutual, type := closeParams 1
      (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherCtor : Constructor := {
    name := `RegisteredOtherCtor, type := closeParams 1 (.app other (.bvar 0)) }
  let twoCtor : Constructor := {
    name := `RegisteredTwoCtor, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  checkStage ctx 0 #[] true
  checkStage ctx 0 #[header `RegisteredZero 0 []] true
  checkStage ctx 0 #[header `RegisteredZero 0 [base, recursive, positive]] true
  checkStage ctx 1 #[header `RegisteredOne 1 [parameterOnly, parameterField, parameterRecursive]] true
  checkStage ctx 2 #[header `RegisteredTwo 2 [twoCtor]] true
  checkStage ctx 1 #[header `RegisteredOne 1 [parameterOnly, mutualCtor],
    header `RegisteredOther 1 [otherCtor]] true 2
  checkStage { ctx with
    ngen := { namePrefix := `RegisteredSeed, idx := 12 }
    lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing sortType }
    1 #[header `RegisteredOne 1 [parameterOnly, parameterRecursive]] true
  checkStage { ctx with allowPrimitive := true } 0 #[header `RegisteredZero 0 [base]] true
  checkStage ctx 0 #[header `RegisteredZero 0 [base, negative]] false
  checkStage ctx 0 #[header `RegisteredZero 0 [base, recursive],
    header `RegisteredOther 0 [{ negative with type := (.forallE `function
      (.forallE `value other zero .default) other .default) }]] false
  checkStage ctx 0 #[header `RegisteredZero 0 [], header `RegisteredZero 0 []] false
  checkStage ctx 0 #[header ``Nat 0 []] false
  checkStage ctx 0 #[{ name := `RegisteredOpenHeader, type := .fvar ⟨`Open⟩, ctors := [] }] false
  checkStage ctx 1 #[header `RegisteredZero 0 []] false
  checkStage ctx 0 #[header `RegisteredZero 0 [],
    { name := `RegisteredProp, type := .sort .zero, ctors := [] }] false
  checkStage ctx 1 #[header `RegisteredOne 1 [parameterOnly,
    { name := `RegisteredWrongDomain, type := .forallE `A natType (.app one natType) .default }]] false
  checkStage ctx 1 #[header `RegisteredOne 1 [parameterOnly],
    header `RegisteredOther 1 [otherCtor, parameterOnly]] false
  checkStage ctx 1 #[header `RegisteredOne 1 [
    { name := `RegisteredOpenReturn, type := .app one (.fvar ⟨ctx.ngen.curr⟩) }]] false
  checkStage ctx 0 #[header `RegisteredZero 0 [base,
    { name := `RegisteredIllTyped, type := .app natType natType }]] false
  checkStage ctx 0 #[header `RegisteredZero 0 [base, base]] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    0 #[header `RegisteredZero 0 [base]] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    1 #[header `RegisteredOne 1 [parameterOnly, parameterRecursive]] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
    1 #[header `RegisteredOne 1 [parameterOnly, parameterRecursive]] true
  checkStage { ctx with safety := .unsafe } 0 #[header `RegisteredZero 0 [negative]] false
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `RegisteredPoly [polyLevel]
  checkStage { ctx with lparams := [`u] } 1 #[{
    name := `RegisteredPoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `RegisteredPolyCtor
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }] true
  let indexed := Expr.const `RegisteredIndexed []
  let indexedOther := Expr.const `RegisteredIndexedOther []
  let indexedTypes : Array InductiveType := #[{
    name := `RegisteredIndexed
    type := closeParams 1 (.forallE `index natType sortType .default)
    ctors := [{
      name := `RegisteredIndexedCtor
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }, {
    name := `RegisteredIndexedOther
    type := closeParams 1 (.forallE `index natType sortType .default)
    ctors := [{
      name := `RegisteredIndexedOtherCtor
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexedOther [.bvar 1, .bvar 0]) .default) }] }]
  checkStage ctx 1 indexedTypes true
  let .ok (stats, root) := stage 1 indexedTypes 0 ctx
    | throwError "failed indexed context-boundary fixture"
  unless root.lctx.numIndices == stats.lctx.numIndices + 1 &&
      root.ngen.idx == ctx.ngen.idx + 3 do
    throwError "trace root must include later indices absent from stats.lctx"
  logInfo "26 registered-prefix outcomes and indexed context boundary passed"

end RegisteredConstructorPositivityTest
