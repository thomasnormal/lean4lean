import Lean4Lean.Verify.InductiveRegistration
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace SafeConstructorRegistrationTest

private def stage (nparams : Nat) (types : Array InductiveType) (numNested : Nat := 0) :
    M (InductiveStats × Context × Kernel.Environment) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types numNested false) do
      checkConstructors types stats false
      let root ← readThe Context
      withEnv (← declareConstructors stats types false) do
        return (stats, root, (← readThe Context).env)

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (next : InductiveStats → Context → M α) (ctx : Context) (hwf : ctx.env.constants.WF)
    (post : α → Prop) (hnext : ∀ stats root env,
      stats.SafeConstructorRegistration nparams types numNested ctx root env →
      (next stats root { root with env }).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats types false) do
          next stats root) ctx).WF post :=
  checkInductiveTypes.safeConstructorRegistration nparams types numNested next ctx hwf post hnext

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (stage nparams types numNested ctx).WF fun result =>
      result.1.SafeConstructorRegistration nparams types numNested ctx result.2.1 result.2.2 :=
  checkInductiveTypes.getSafeConstructorRegistration nparams types numNested ctx hwf

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (hwf : ctx.env.constants.WF) (stats : InductiveStats)
    (env : Kernel.Environment) (hchecked : stage nparams types numNested ctx = .ok (stats, root, env)) :
    stats.SafeConstructorRegistration nparams types numNested ctx root env :=
  checkInductiveTypes.getSafeConstructorRegistration nparams types numNested ctx hwf _ hchecked

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (stats : InductiveStats) (env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested ctx root env)
    (parent : Nat) (hparent : parent < types.size) (ctor : Constructor)
    (hctor : ctor ∈ types[parent].ctors) :
    ∃ terminal, SafeConstructorTrace stats PositivityWHNF parent root 0 ctor.type terminal :=
  hregistration.traces.2.2.2.2.2 parent hparent ctor hctor

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (stats : InductiveStats) (env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested ctx root env)
    (type : InductiveType) (htype : type ∈ types) (index : Nat) (ctor : Constructor)
    (hctor : type.ctors[index]? = some ctor) :
    env.find? ctor.name = some (.ctorInfo
      (declareConstructors.metadataVal stats ctx.lparams false type.name index ctor)) :=
  (hregistration.constructorMetadata type htype index ctor hctor).1

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (stats : InductiveStats) (env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested ctx root env) :
    ∀ name info, ctx.env.find? name = some info → env.find? name = some info :=
  hregistration.preservesOriginal

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (stats : InductiveStats) (env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested ctx root env) :
    DeclaredParameterMetadata nparams types env :=
  hregistration.declaredParameters

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (ctx root : Context) (stats : InductiveStats) (env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested ctx root env) :
    root.env.constants.WF ∧ env.constants.WF :=
  ⟨hregistration.headerWF, hregistration.resultWF⟩

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def checkPreserved (original env : Kernel.Environment) (name : Name) : MetaM Unit := do
  let some before := original.find? name | throwError "missing preservation fixture {name}"
  let some after := env.find? name | throwError "lost preservation fixture {name}"
  unless before.name == after.name && before.type == after.type &&
      before.levelParams == after.levelParams && before.safety == after.safety do
    throwError "changed preservation fixture {name}"

private def checkHeader (env : Kernel.Environment) (expected : InductiveVal) : MetaM Unit := do
  let some (.inductInfo actual) := env.find? expected.name
    | throwError "missing header {expected.name}"
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.numParams == expected.numParams &&
      actual.numIndices == expected.numIndices && actual.numNested == expected.numNested &&
      actual.isUnsafe == expected.isUnsafe && actual.all == expected.all &&
      actual.ctors == expected.ctors && actual.isRec == expected.isRec &&
      actual.isReflexive == expected.isReflexive do
    throwError "incorrect header metadata {expected.name}"

private def checkCtor (stats : InductiveStats) (root : Context) (env : Kernel.Environment)
    (type : InductiveType) (index : Nat) (ctor : Constructor) : MetaM Unit := do
  unless root.env.contains ctor.name == false do
    throwError "trace root must precede constructor registration"
  let some (.ctorInfo actual) := env.find? ctor.name | throwError "missing constructor {ctor.name}"
  let expected := declareConstructors.metadataVal stats root.lparams false type.name index ctor
  unless actual == expected &&
      actual.numParams + actual.numFields == declareConstructors.arity 0 ctor.type do
    throwError "incorrect constructor metadata {ctor.name}"

private def checkResult (ctx root : Context) (env : Kernel.Environment) (stats : InductiveStats)
    (nparams numNested : Nat) (types : Array InductiveType) : MetaM Unit := do
  let scopes := stats.params.size + stats.nindices.foldl (· + ·) 0
  let expectedNames := scopes.fold (fun _ _ ngen => ngen.next) ctx.ngen
  unless stats.params.size == (if types.isEmpty then 0 else nparams) &&
      root.ngen.curr == expectedNames.curr && root.lctx.numIndices == ctx.lctx.numIndices + scopes &&
      root.lparams == ctx.lparams && root.safety == ctx.safety do
    throwError "incorrect rooted checked statistics"
  checkPreserved ctx.env root.env ``Nat
  checkPreserved root.env env ``Nat
  for parent in [:types.size] do
    let type := types[parent]!
    let expected := declareInductiveTypes.metadataVal stats nparams types numNested false
      ctx.lparams type stats.nindices[parent]!
    checkHeader root.env expected
    checkHeader env expected
    for index in [:type.ctors.length] do
      checkCtor stats root env type index type.ctors[index]!

private def checkStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Bool) (numNested : Nat := 0) : MetaM Unit := do
  let result := stage nparams types numNested ctx
  unless result.isOk == expected do
    match result with
    | .error error =>
      throwError "incorrect safe-registration outcome for {types.map (·.name)}: \
        {error.toMessageData (← getOptions)}"
    | .ok _ => throwError "unexpected safe-registration success for {types.map (·.name)}"
  if let .ok (stats, root, env) := result then
    checkResult ctx root env stats nparams numNested types

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        interfaces.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let maps := [``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert]
  let arity := [``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq,
    ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``InductiveStats.SafeConstructorRegistration.preservesOriginal []
  audit ``InductiveStats.SafeConstructorRegistration.declaredParameters []
  audit ``checkInductiveTypes.safeConstructorRegistration (maps ++ arity)
  audit ``checkInductiveTypes.getSafeConstructorRegistration (maps ++ arity)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let natType := Expr.const ``Nat []
  let zero := Expr.const `SafeRegZero []
  let one := Expr.const `SafeRegOne []
  let other := Expr.const `SafeRegOther []
  let two := Expr.const `SafeRegTwo []
  let base : Constructor := { name := `SafeRegZero.base, type := zero }
  let recursive : Constructor := {
    name := `SafeRegZero.recursive, type := .forallE `value zero zero .default }
  let positive : Constructor := {
    name := `SafeRegZero.positive, type := .forallE `function
      (.forallE `index natType zero .default) zero .implicit }
  let negative : Constructor := {
    name := `SafeRegZero.negative, type := .forallE `function
      (.forallE `value zero natType .default) zero .default }
  let parameterOnly : Constructor := {
    name := `SafeRegOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterRecursive : Constructor := {
    name := `SafeRegOne.tail, type := closeParams 1
      (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let parameterField : Constructor := {
    name := `SafeRegOne.value, type := closeParams 1
      (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let parameterNegative : Constructor := {
    name := `SafeRegOne.negative, type := closeParams 1
      (.forallE `function (.forallE `tail (.app one (.bvar 0)) (.bvar 1) .default)
        (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `SafeRegOne.mutual, type := closeParams 1
      (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherCtor : Constructor := {
    name := `SafeRegOther.base, type := closeParams 1 (.app other (.bvar 0)) }
  let twoCtor : Constructor := {
    name := `SafeRegTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  checkStage ctx 0 #[] true
  checkStage ctx 0 #[header `SafeRegZero 0 []] true
  checkStage ctx 0 #[header `SafeRegZero 0 [base, recursive, positive]] true
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly, parameterField, parameterRecursive]] true
  checkStage ctx 2 #[header `SafeRegTwo 2 [twoCtor]] true
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly, mutualCtor],
    header `SafeRegOther 1 [otherCtor]] true 2
  checkStage { ctx with
    ngen := { namePrefix := `SafeRegSeed, idx := 12 }
    lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing sortType }
    1 #[header `SafeRegOne 1 [parameterOnly, parameterRecursive]] true
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `SafeRegPoly [polyLevel]
  checkStage { ctx with lparams := [`u] } 1 #[{
    name := `SafeRegPoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `SafeRegPoly.base
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }] true
  let indexed := Expr.const `SafeRegIndexed []
  let indexedOther := Expr.const `SafeRegIndexedOther []
  let indexedTypes : Array InductiveType := #[{
    name := `SafeRegIndexed
    type := closeParams 1 (.forallE `index natType sortType .default)
    ctors := [{
      name := `SafeRegIndexed.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }, {
    name := `SafeRegIndexedOther
    type := closeParams 1 (.forallE `index natType sortType .default)
    ctors := [{
      name := `SafeRegIndexedOther.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexedOther [.bvar 1, .bvar 0]) .default) }] }]
  checkStage ctx 1 indexedTypes true
  checkStage ctx 0 #[header `SafeRegZero 0 [base, negative]] false
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly, parameterNegative]] false
  checkStage ctx 0 #[header `SafeRegZero 0 [], header `SafeRegZero 0 []] false
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly], header `SafeRegOther 1 [
    { otherCtor with name := parameterOnly.name }]] false
  checkStage ctx 0 #[header `SafeRegZero 0 [{ base with name := `SafeRegZero }]] false
  checkStage ctx 0 #[header `SafeRegZero 0 [{ base with name := ``Nat.zero }]] false
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly,
    { name := `SafeRegWrongDomain, type := .forallE `A natType (.app one natType) .default }]] false
  checkStage ctx 1 #[header `SafeRegOne 1 [parameterOnly],
    header `SafeRegOther 1 [otherCtor, { parameterOnly with name := `SafeRegWrongParent }]] false
  checkStage ctx 2 #[header `SafeRegTwo 2 [{ twoCtor with type := (
    closeParams 1 (.mkAppList two [.bvar 0, natType])) }]] false
  checkStage ctx 2 #[header `SafeRegTwo 2 [{ twoCtor with type := (
    closeParams 2 (.mkAppList two [.bvar 0, .bvar 1])) }]] false
  checkStage ctx 1 #[header `SafeRegOne 1 [
    { name := `SafeRegOpen, type := .app one (.fvar ⟨ctx.ngen.curr⟩) }]] false
  checkStage ctx 0 #[header `SafeRegZero 0 [base,
    { name := `SafeRegIllTyped, type := .app natType natType }]] false
  checkStage ctx 1 #[{
    name := `SafeRegIndexed
    type := indexedTypes[0]!.type
    ctors := [{ name := `SafeRegMissingIndex, type := closeParams 1 (.app indexed (.bvar 0)) }] }] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    0 #[header `SafeRegZero 0 [base]] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    1 #[header `SafeRegOne 1 [parameterOnly, parameterRecursive]] false
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
    1 #[header `SafeRegOne 1 [parameterOnly, parameterRecursive]] true
  checkStage { ctx with safety := .unsafe } 0 #[header `SafeRegZero 0 [negative]] false
  let .ok (stats, root, env) := stage 1 indexedTypes 0 ctx
    | throwError "failed registered indexed-root boundary"
  unless root.lctx.numIndices == stats.lctx.numIndices + 1 &&
      root.ngen.idx == ctx.ngen.idx + 3 && root.env.contains `SafeRegIndexed.base == false &&
      env.contains `SafeRegIndexed.base do
    throwError "header trace root must remain distinct from constructor environment"
  logInfo "26 safe-registration outcomes and distinct header-root boundary passed"

end SafeConstructorRegistrationTest
