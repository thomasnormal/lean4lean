import Lean4Lean.Verify.TypeChecker.InferenceHeadFrame
import Lean.Util.CollectAxioms

namespace InferenceHeadFrameTest
open Lean hiding Environment Exception
open Lean4Lean

private structure DependentPair where
  value : Nat
  proof : value = value

private def identityControl (value : Nat) : Nat := value

private def lambdaControl (first second : Nat) : Nat := first + second

private def letControl : Nat :=
  let first := 3
  let second := first + 1
  second

private def projectionControl (pair : Nat × Nat) : Nat := pair.1

private def dependentProjectionControl (pair : DependentPair) : pair.value = pair.value := pair.proof

private def propProjectionControl (proof : True ∧ True) : True := proof.left

private def eagerControl : Nat := identityControl (eagerReduce 3)

example (expression : Expr) (inferOnly : Bool) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (TypeChecker.Inner.inferType' expression inferOnly methods).HeadWF (fun _ => True) :=
  TypeChecker.Inner.inferType'.headWF expression inferOnly methods valid

example (expression : Expr) (inferOnly : Bool) :
    ((TypeChecker.Methods.withFuel 1).inferType expression inferOnly).HeadWF (fun _ => True) :=
  TypeChecker.Methods.withFuel.inferType_succ_headWF 0 TypeChecker.Methods.withFuel.zero_headWF
    expression inferOnly

private def cleanCaches (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => !entry.2.isMData && !entry.2.isLet) &&
    state.whnfCache.toList.all (fun entry => !entry.2.isMData && !entry.2.isLet)

private def declarationValue (name : Name) : MetaM Expr := do
  let some (.defnInfo information) := (← getEnv).find? name
    | throwError "native inference fixture definition absent: {name}"
  return information.value

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let identity ← declarationValue ``identityControl
  let lambda ← declarationValue ``lambdaControl
  let letValue ← declarationValue ``letControl
  let projection ← declarationValue ``projectionControl
  let dependentProjection ← declarationValue ``dependentProjectionControl
  let propProjection ← declarationValue ``propProjectionControl
  let eager ← declarationValue ``eagerControl
  let natural := .const ``Nat []
  let literal := .lit (.natVal 7)
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, literal]
  let trueProof := .const ``True.intro []
  let conjunction := mkAppN (.const ``And.intro []) #[.const ``True [], .const ``True [], trueProof, trueProof]
  let localVariable := .fvar ⟨`inferenceLocal⟩
  let localLet := .fvar ⟨`inferenceLet⟩
  let locals := ({} : LocalContext).mkLocalDecl ⟨`inferenceLocal⟩ `local natural .default
    |>.mkLetDecl ⟨`inferenceLet⟩ `localLet natural literal
  let closed := #[literal, .lit (.strVal "native"), .sort .zero, .sort (.succ .zero),
    natural, .const ``Nat.succ [], identity, lambda, letValue, projection, dependentProjection,
    propProjection, eager, .app identity literal, .mdata {} (.app identity literal),
    .forallE `first natural (.forallE `second natural natural .default) .default,
    .letE `first natural literal (.letE `second natural (.bvar 0) (.bvar 0) false) false,
    .proj ``Prod 0 pair, .proj ``And 0 conjunction]
  let mut expected := #[]
  for expression in closed do expected := expected.push (← Meta.inferType expression)
  let expressions := closed ++ #[localVariable, localLet]
  expected := expected ++ #[natural, natural]
  let methods := TypeChecker.Methods.withFuel 128
  let malformed := #[.bvar 0, .mvar ⟨`missingMeta⟩, .fvar ⟨`missingLocal⟩,
    .const `missingConstant [], .app literal literal, .proj ``Nat 0 literal,
    .proj ``Prod 0 literal, .proj ``Prod 2 pair]
  let mismatches := #[.sort (.param `missingLevel), .app (.const ``Nat.succ []) (.const ``True.intro []),
    .letE `bad natural (.const ``True.intro []) (.bvar 0) false,
    .lam `bad literal (.bvar 0) .default, .forallE `bad literal natural .default]
  let mut successes := 0
  let mut failures := 0
  let mut projectionFailures := 0
  let mut oneFuelSuccesses := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eagerMode in [false, true] do
      let context : TypeChecker.Context := { env := environment, lctx := locals, safety, eagerReduce := eagerMode }
      for inferOnly in [false, true] do
        for source in [:expressions.size] do
          let expression := expressions[source]!
          let mut state : TypeChecker.State := {}
          for _ in [:2] do
            let .ok (inferred, finalState) := TypeChecker.Inner.inferType' expression inferOnly methods context state
              | throwError "native inference positive fixture rejected at {source}, inferOnly={inferOnly}"
            unless cleanCaches finalState do throwError "native inference corrupted WHNF caches"
            unless (cond inferOnly finalState.inferTypeI finalState.inferTypeC)[expression]? == some inferred do
              throwError "native inference did not insert into the selected inference cache"
            let .ok (equal, comparedState) := TypeChecker.Inner.isDefEq inferred expected[source]! methods context finalState
              | throwError "native inferred type comparison rejected"
            unless equal && cleanCaches comparedState do throwError "native inference lost expected type or clean caches"
            state := finalState
            successes := successes + 1
        for expression in malformed do
          if (TypeChecker.Inner.inferType' expression inferOnly methods context {}).isOk then
            throwError "malformed native inference control unexpectedly accepted"
          failures := failures + 1
      for expression in mismatches do
        if (TypeChecker.Inner.inferType' expression false methods context {}).isOk then
          throwError "checked native inference mismatch unexpectedly accepted"
        failures := failures + 1
      if (TypeChecker.Inner.ensureSortCore natural natural methods context {}).isOk ||
          (TypeChecker.Inner.ensureForallCore natural natural methods context {}).isOk then
        throwError "native sort/forall guards unexpectedly accepted Nat"
      let .ok (proposition, propState) := TypeChecker.Inner.isProp (.const ``True []) methods context {}
        | throwError "native proposition fixture rejected"
      let .ok (nonproposition, natState) := TypeChecker.Inner.isProp natural methods context {}
        | throwError "native nonproposition fixture rejected"
      unless proposition && !nonproposition && cleanCaches propState && cleanCaches natState do
        throwError "native proposition guards lost result or caches"
      let projectionSource := .proj ``Prod 0 pair
      let dependentBinder := .forallE `field natural (.bvar 0) .default
      let invalidProjections := #[
        (fun _ => ()) <$> TypeChecker.Inner.nativeProjectionParameter environment projectionSource #[natural] 0 natural,
        (fun _ => ()) <$> TypeChecker.Inner.nativeProjectionField environment projectionSource ``Prod pair true 0 dependentBinder,
        (fun _ => ()) <$> TypeChecker.Inner.nativeProjectionFinal environment projectionSource true dependentBinder,
        (fun _ => ()) <$> TypeChecker.Inner.nativeProjectionBody ``Prod 0 pair (.const ``Prod [.zero, .zero])]
      for action in invalidProjections do
        if (action methods context {}).isOk then throwError "malformed native projection helper unexpectedly accepted"
        projectionFailures := projectionFailures + 1
      let poisoned : TypeChecker.State := { whnfCache := ({} : ExprMap Expr).insert natural (.mdata {} natural) }
      let .ok (_, poisonedFinal) := TypeChecker.Inner.inferType' literal true methods context poisoned
        | throwError "poisoned-cache precondition fixture rejected"
      unless !cleanCaches poisonedFinal do throwError "poisoned cache precondition control disappeared"
      if ((TypeChecker.Methods.withFuel 0).inferType literal false context {}).isOk then
        throwError "zero-fuel native inference unexpectedly accepted"
      for expression in [literal, .mdata {} literal, .sort .zero, natural] do
        for inferOnly in [false, true] do
          let .ok (_, finalState) := (TypeChecker.Methods.withFuel 1).inferType expression inferOnly context {}
            | throwError "positive one-fuel native inference fixture rejected"
          unless cleanCaches finalState do throwError "one-fuel native inference corrupted caches"
          oneFuelSuccesses := oneFuelSuccesses + 1
  logInfo m!"{successes} cold/warm actual inference controls preserve caches and expected types; {failures} malformed/checked mismatches and {projectionFailures} actual projection-helper guards reject; {oneFuelSuccesses} positive one-fuel entries preserve caches; both safeties, eager modes and inference modes, literals, sorts, constants, binders, local/let variables, applications, metadata and dependent/Prop projections covered; actual guards, poisoned-cache precondition and zero-fuel controls pass; no arbitrary-fuel Methods.HeadWF or semantic checker is fabricated"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.InferenceHeadFrame
    | throwError "native inference head-frame module absent"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned inference head-frame axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected inference head-frame dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned native inference head-frame declarations audited against unchanged logical/native representation foundations; no checker/metatheory admissions"
  nativeControls

end InferenceHeadFrameTest
