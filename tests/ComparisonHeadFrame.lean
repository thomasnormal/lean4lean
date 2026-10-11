import Lean4Lean.Verify.TypeChecker.ComparisonHeadFrame
import Lean.Util.CollectAxioms

namespace ComparisonHeadFrameTest
open Lean hiding Environment Exception
open Lean4Lean

private def seven : Nat := 7
private def alsoSeven : Nat := 3 + 4
private theorem firstProof : True := True.intro
private theorem secondProof : True := True.intro

example (function : Nat → Nat) : (fun value => function value) = function := rfl
example (pair : Nat × Nat) : (pair.1, pair.2) = pair := rfl
example (first second : Unit) : first = second := rfl

example (fuel : Nat) : (TypeChecker.Methods.withFuel fuel).HeadWF :=
  TypeChecker.Methods.withFuel.headWF fuel

example (expression : Expr) : (TypeChecker.whnf expression).HeadWF NativeHeadClean :=
  TypeChecker.whnf.headWF expression

example (expression : Expr) : (TypeChecker.whnfCore expression).HeadWF NativeHeadClean :=
  TypeChecker.whnfCore.headWF expression

example (expression : Expr) : (TypeChecker.checkType expression).HeadWF (fun _ => True) :=
  TypeChecker.checkType.headWF expression

example (first second : Expr) : (TypeChecker.isDefEq first second).HeadWF (fun _ => True) :=
  TypeChecker.isDefEq.headWF first second

example (environment : Kernel.Environment) (safety : DefinitionSafety) (locals : LocalContext)
    (parameters : List Name) (fuel : FuelConfig) (expression normalized : Expr)
    (accepted : (TypeChecker.whnf expression).run environment safety locals parameters fuel = .ok normalized) :
    NativeHeadClean normalized :=
  (TypeChecker.whnf.headWF expression).run environment safety locals parameters fuel accepted

private def cleanHead (expression : Expr) : Bool := !expression.isMData && !expression.isLet

private def cleanCaches (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => cleanHead entry.2) &&
    state.whnfCache.toList.all (fun entry => cleanHead entry.2)

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := .const ``Nat []
  let literal := .lit (.natVal 7)
  let function := .fvar ⟨`comparisonFunction⟩
  let pair := .fvar ⟨`comparisonPair⟩
  let firstUnit := .fvar ⟨`comparisonFirstUnit⟩
  let secondUnit := .fvar ⟨`comparisonSecondUnit⟩
  let functionType := .forallE `value natural natural .default
  let pairType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let locals := ({} : LocalContext).mkLocalDecl ⟨`comparisonFunction⟩ `function functionType .default
    |>.mkLocalDecl ⟨`comparisonPair⟩ `pair pairType .default
    |>.mkLocalDecl ⟨`comparisonFirstUnit⟩ `firstUnit (.const ``Unit []) .default
    |>.mkLocalDecl ⟨`comparisonSecondUnit⟩ `secondUnit (.const ``Unit []) .default
  let etaFunction := .lam `value natural (.app function (.bvar 0)) .default
  let etaPair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural,
    .proj ``Prod 0 pair, .proj ``Prod 1 pair]
  let identity := .lam `first natural (.bvar 0) .default
  let renamedIdentity := .lam `second natural (.bvar 0) .default
  let firstForall := .forallE `first natural natural .default
  let secondForall := .forallE `second natural natural .default
  let boolTrue := .const ``Bool.true []
  let boolExpression := mkAppN (.const ``Bool.and []) #[boolTrue, boolTrue]
  let addition := mkAppN (.const ``Nat.add []) #[.lit (.natVal 3), .lit (.natVal 4)]
  let controls : Array (Expr × Expr × Bool) := #[
    (identity, renamedIdentity, true), (firstForall, secondForall, true),
    (etaFunction, function, true), (pair, etaPair, true), (firstUnit, secondUnit, true),
    (.const ``firstProof [], .const ``secondProof [], true),
    (.const ``seven [], .const ``alsoSeven [], true), (addition, literal, true),
    (.app (.const ``Nat.succ []) (.lit (.natVal 6)), literal, true),
    (.lit (.strVal "ab"), .strLitToConstructor "ab", true),
    (boolExpression, boolTrue, true), (.mdata {} literal, literal, true),
    (.letE `value natural literal (.bvar 0) false, literal, true),
    (.proj ``Prod 0 pair, .proj ``Prod 0 pair, true),
    (literal, .lit (.natVal 8), false), (natural, .const ``Bool [], false)]
  let mut coreCount := 0
  let mut publicCount := 0
  let mut entryCount := 0
  let mut initializedCount := 0
  let mut helperCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : TypeChecker.Context :=
          { env := environment, lctx := locals, safety, eagerReduce := eager, fuel := { recDepth := fuel } }
        let methods := TypeChecker.Methods.withFuel fuel
        for source in [:controls.size] do
          let (first, second, expected) := controls[source]!
          unless (TypeChecker.checkType first context {}).isOk && (TypeChecker.checkType second context {}).isOk do
            throwError "genuinely typed comparison fixture rejected at {source}"
          for reversed in [false, true] do
            let (left, right) := if reversed then (second, first) else (first, second)
            let mut state : TypeChecker.State := {}
            for _ in [:2] do
              let .ok (equal, finalState) := methods.isDefEqCore left right context state
                | throwError "actual comparison core fixture rejected at {source}, fuel={fuel}"
              unless equal == expected && cleanCaches finalState do
                throwError "actual comparison core lost expected result or clean caches at {source}"
              state := finalState
              coreCount := coreCount + 1
            state := {}
            for _ in [:2] do
              let .ok (equal, finalState) := TypeChecker.isDefEq left right context state
                | throwError "configured public comparison fixture rejected at {source}, fuel={fuel}"
              unless equal == expected && cleanCaches finalState do
                throwError "configured public comparison lost expected result or clean caches at {source}"
              state := finalState
              publicCount := publicCount + 1
          let mut state : TypeChecker.State := {}
          for _ in [:2] do
            let .ok (_, checkedState) := TypeChecker.checkType first context state
              | throwError "configured checking entry rejected"
            let .ok (_, inferredState) := TypeChecker.inferType first context checkedState
              | throwError "configured inference entry rejected"
            let .ok (coreHead, coreState) := TypeChecker.whnfCore first context inferredState
              | throwError "configured core normalization entry rejected"
            let .ok (fullHead, finalState) := TypeChecker.whnf first context coreState
              | throwError "configured full normalization entry rejected"
            unless cleanHead coreHead && cleanHead fullHead && cleanCaches finalState do
              throwError "configured actual entries lost head/cache invariant"
            state := finalState
            entryCount := entryCount + 4
          let .ok (initializedHead) := (TypeChecker.whnf first).run environment safety locals [] { recDepth := fuel }
            | throwError "actual cold-initialized M.run normalization rejected"
          unless cleanHead initializedHead do throwError "actual cold-initialized normalization lost head invariant"
          initializedCount := initializedCount + 1
        let .ok (proofEqual, proofState) := TypeChecker.Inner.isDefEqProofIrrel
            (.const ``firstProof []) (.const ``secondProof []) methods context {}
          | throwError "actual proof irrelevance helper rejected"
        let .ok (functionEqual, functionState) := TypeChecker.Inner.tryEtaExpansion etaFunction function methods context {}
          | throwError "actual lambda eta helper rejected"
        let .ok (pairEqual, pairState) := TypeChecker.Inner.tryEtaStruct pair etaPair methods context {}
          | throwError "actual structure eta helper rejected"
        let .ok (unitEqual, unitState) := TypeChecker.Inner.isDefEqUnitLike firstUnit secondUnit methods context {}
          | throwError "actual unit-like helper rejected"
        unless proofEqual == .true && functionEqual && pairEqual && unitEqual &&
            cleanCaches proofState && cleanCaches functionState && cleanCaches pairState && cleanCaches unitState do
          throwError "actual proof/eta/unit helpers lost result or cache invariant"
        helperCount := helperCount + 4
        unless !(TypeChecker.Inner.lazyDeltaReduction.loop literal literal 0 methods context {}).isOk do
          throwError "zero lazy-delta budget unexpectedly accepted"
        let zero := TypeChecker.Methods.withFuel 0
        if (zero.isDefEqCore literal literal context {}).isOk || (zero.whnf literal context {}).isOk ||
            (zero.whnfCore literal false false context {}).isOk || (zero.inferType literal true context {}).isOk then
          throwError "zero-fuel method entry unexpectedly accepted"
        let poisoned : TypeChecker.State := { whnfCache := ({} : ExprMap Expr).insert natural (.mdata {} natural) }
        let .ok (_, poisonedFinal) := TypeChecker.isDefEq literal literal context poisoned
          | throwError "poisoned-cache precondition fixture rejected"
        unless !cleanCaches poisonedFinal do throwError "poisoned-cache initial precondition control disappeared"
  logInfo m!"{coreCount} actual comparison-core and {publicCount} configured public cold/warm bidirectional comparisons retain expected typed results and clean caches; {entryCount} configured inference/checking/core/full normalization entries, {initializedCount} actual cold-initialized M.run normalizations and {helperCount} actual proof/lambda-eta/structure-eta/unit helpers pass; both safeties, eager modes and fuels 32/128; delta, Nat, string, Bool, metadata, lets, binders and projections covered; timeout, zero-fuel and poisoned-cache controls pass; arbitrary-fuel cache/head contract is formally proved, not semantic normalization or frontend closure"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ComparisonHeadFrame
    | throwError "native comparison head-frame module absent"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned comparison head-frame axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected comparison head-frame dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned native comparison/fuel/entry declarations audited against unchanged logical/native representation foundations; no checker/metatheory admissions"
  nativeControls

end ComparisonHeadFrameTest
