import Lean4Lean.Verify.TypeChecker.ScopedComparison
import Lean.Util.CollectAxioms

namespace ScopedComparisonTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

example {context : VContext} {state : VState} {locals : MLCtx} [context.MLCWF locals]
    {first second : Expr} {substitution : Array Expr} {variables : List Expr}
    (aligned : substitution.toList.reverse = variables)
    (closed : ∀ value ∈ variables, value.looseBVarRange' = 0)
    (firstTranslation : (context.withMLC locals).TrExprS (first.instantiateList variables) firstSemantic)
    (secondTranslation : (context.withMLC locals).TrExprS (second.instantiateList variables) secondSemantic) :
    (Inner.isDefEqLambda first second substitution).ScopeWF (context.withMLC locals) state
      (fun equal _ => equal → (context.withMLC locals).IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqLambda.scopeWF aligned closed firstTranslation secondTranslation

example {context : VContext} {state : VState} {locals : MLCtx} [context.MLCWF locals]
    {first second : Expr} {substitution : Array Expr} {variables : List Expr}
    (aligned : substitution.toList.reverse = variables)
    (closed : ∀ value ∈ variables, value.looseBVarRange' = 0)
    (firstTranslation : (context.withMLC locals).TrExprS (first.instantiateList variables) firstSemantic)
    (secondTranslation : (context.withMLC locals).TrExprS (second.instantiateList variables) secondSemantic) :
    (Inner.isDefEqForall first second substitution).ScopeWF (context.withMLC locals) state
      (fun equal _ => equal → (context.withMLC locals).IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqForall.scopeWF aligned closed firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqLambda first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqLambda.scopeWF_empty firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqForall first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqForall.scopeWF_empty firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.quickIsDefEq first second useHash).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.quickIsDefEq.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState} {action : RecM Bool} {post : VState → Prop}
    (valid : action.ScopeWF context state (fun equal finalState => equal → post finalState)) :
    (toLBoolM action).ScopeWF context state (fun equal finalState => equal = .true → post finalState) :=
  valid.toLBoolM

example : ¬(∀ value ∈ [Expr.bvar 0], value.looseBVarRange' = 0) := by
  simp [Expr.looseBVarRange']

example (context : VContext) (identifier : MVarId) :
    ¬∃ semantic, context.TrExprS (.mvar identifier) semantic := by
  rintro ⟨semantic, translated⟩
  cases translated

private def stableHead (locals : LocalContext) (expression : Expr) : Bool :=
  !expression.isMData && !expression.isLet && match expression with
    | .fvar identifier => !Inner.isLetFVar locals identifier
    | _ => true

private def stableCaches (locals : LocalContext) (state : State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => stableHead locals entry.2) &&
    state.whnfCache.toList.all (fun entry => stableHead locals entry.2)

private def advanceGenerator (generator : NameGenerator) : Nat → NameGenerator
  | 0 => generator
  | count + 1 => advanceGenerator generator.next count

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let literal := Expr.lit (.natVal 7)
  let aliasIdentifier : FVarId := ⟨`scopedComparisonAlias⟩
  let locals := ({} : LocalContext).mkLetDecl aliasIdentifier `alias (.sort (.succ .zero)) natural
  let identity := Expr.lam `first natural (.bvar 0) .default
  let renamedIdentity := Expr.lam `second natural (.bvar 0) .default
  let constant := Expr.lam `first natural literal .default
  let renamedConstant := Expr.lam `second natural (.mdata {} literal) .default
  let dependent := Expr.lam `first natural (.lam `second natural (.bvar 1) .default) .default
  let renamedDependent := Expr.lam `outer natural (.lam `inner natural (.bvar 1) .default) .default
  let skippedOuter := Expr.lam `first natural (.lam `second natural (.bvar 0) .default) .default
  let renamedSkippedOuter := Expr.lam `outer natural (.lam `inner natural (.bvar 0) .default) .default
  let lambdaControls : Array (Expr × Expr × Bool × Nat) := #[
    (identity, renamedIdentity, true, 1),
    (constant, renamedConstant, true, 0),
    (dependent, renamedDependent, true, 2),
    (skippedOuter, renamedSkippedOuter, true, 1),
    (.lam `alias (.fvar aliasIdentifier) (.bvar 0) .default, renamedIdentity, true, 1),
    (constant, .lam `second natural (.lit (.natVal 8)) .default, false, 0),
    (constant, .lam `second (.const ``Bool []) (.const ``Bool.true []) .default, false, 0),
    (.sort .zero, .sort .zero, true, 0)]
  let dependentForall := Expr.forallE `type (.sort (.succ .zero))
    (.forallE `value (.bvar 0) (.bvar 1) .default) .default
  let renamedDependentForall := Expr.forallE `renamedType (.sort (.succ .zero))
    (.forallE `renamedValue (.bvar 0) (.bvar 1) .default) .default
  let skippedForall := Expr.forallE `type (.sort (.succ .zero))
    (.forallE `value natural natural .default) .default
  let renamedSkippedForall := Expr.forallE `renamedType (.sort (.succ .zero))
    (.forallE `renamedValue natural natural .default) .default
  let forallControls : Array (Expr × Expr × Bool × Nat) := #[
    (.forallE `first natural natural .default, .forallE `second natural natural .default, true, 0),
    (dependentForall, renamedDependentForall, true, 2),
    (skippedForall, renamedSkippedForall, true, 0),
    (.forallE `first (.fvar aliasIdentifier) natural .default, .forallE `second natural natural .default, true, 0),
    (.forallE `first natural natural .default,
      .forallE `second (.const ``Bool []) natural .default, false, 0),
    (.forallE `first natural natural .default,
      .forallE `second natural (.const ``Bool []) .default, false, 0),
    (.sort .zero, .sort .zero, true, 0)]
  let workers : List ((Expr → Expr → RecM Bool) × Array (Expr × Expr × Bool × Nat)) := [
    (fun first second => Inner.isDefEqLambda first second, lambdaControls),
    (fun first second => Inner.isDefEqForall first second, forallControls)]
  let addition := mkAppN (.const ``Nat.add []) #[.lit (.natVal 3), .lit (.natVal 4)]
  let quickControls : Array (Expr × Expr × LBool) := #[
    (identity, renamedIdentity, .true),
    (dependentForall, renamedDependentForall, .true),
    (.sort (.max .zero .zero), .sort .zero, .true),
    (.sort (.succ .zero), .sort .zero, .false),
    (.mdata {} addition, .mdata {} literal, .true),
    (literal, literal, .true),
    (literal, .lit (.natVal 8), .false),
    (natural, .const ``Bool [], .undef)]
  let mut telescopeCount := 0
  let mut quickCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager, fuel := { recDepth := fuel } }
        let methods := Methods.withFuel fuel
        for (worker, controls) in workers do
          for control in [:controls.size] do
            let (first, second, expected, freshCount) := controls[control]!
            unless (TypeChecker.checkType first context {}).isOk &&
                (TypeChecker.checkType second context {}).isOk do
              throwError "typed scoped telescope control rejected at {control}"
            for reversed in [false, true] do
              let (left, right) := if reversed then (second, first) else (first, second)
              let mut state : State := {}
              for _ in [:2] do
                let expectedGenerator := advanceGenerator state.ngen freshCount
                let .ok (equal, finalState) := worker left right methods context state
                  | throwError "scoped telescope worker rejected at {control}"
                unless equal == expected && stableCaches locals finalState &&
                    finalState.ngen.curr == expectedGenerator.curr do
                  throwError "scoped telescope worker loses result/cache/fresh-name frame at {control}, reverse={reversed}, expected fresh={freshCount}, expected generator={expectedGenerator.curr}, actual generator={finalState.ngen.curr}"
                state := finalState
                telescopeCount := telescopeCount + 1
        for useHash in [false, true] do
          for control in [:quickControls.size] do
            let (first, second, expected) := quickControls[control]!
            unless (TypeChecker.checkType first context {}).isOk &&
                (TypeChecker.checkType second context {}).isOk do
              throwError "typed scoped quick comparison control rejected at {control}"
            for reversed in [false, true] do
              let (left, right) := if reversed then (second, first) else (first, second)
              let mut state : State := {}
              for _ in [:2] do
                let .ok (equal, finalState) := Inner.quickIsDefEq left right useHash methods context state
                  | throwError "scoped quick comparison rejected at {control}"
                unless equal == expected && stableCaches locals finalState do
                  throwError "scoped quick comparison loses result/cache frame at {control}"
                state := finalState
                quickCount := quickCount + 1
  let context : Context := { env := environment, lctx := locals }
  let poisoned : State := { whnfCache := ({} : ExprMap Expr).insert natural (.fvar aliasIdentifier) }
  let .ok (_, poisonedFinal) := Inner.quickIsDefEq natural natural true (Methods.withFuel 32) context poisoned
    | throwError "scoped comparison poisoned-cache control rejected"
  unless !stableCaches locals poisonedFinal do throwError "scoped comparison cache premise disappeared"
  unless !(Inner.isDefEqLambda identity renamedIdentity #[] (Methods.withFuel 0) context {}).isOk do
    throwError "zero-fuel telescope callback unexpectedly succeeded"
  let .ok (equal, finalState) := Inner.quickIsDefEq literal literal true (Methods.withFuel 0) context {}
    | throwError "zero-fuel pure quick comparison rejected"
  unless equal == .true && stableCaches locals finalState do throwError "pure quick comparison loses frame"
  logInfo m!"{telescopeCount} actual cold/warm bidirectional lambda/forall comparisons preserve expected results, scoped caches and exact fresh-name counts; {quickCount} actual quick comparisons preserve true/false/undefined results and scoped caches with both hash modes; both safeties/eager modes, fuels 32/128, dependent/unused/nested binders, domain aliases, domain/body mismatches, sorts/literals/metadata covered; poisoned-cache premise and zero-fuel controls pass; no arbitrary-fuel Methods.ScopeWF or semantic checker is fabricated"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedComparison
    | throwError "scoped comparison module absent"
  let lambdaBaseline ← collectAxioms ``Inner.isDefEqLambda.WF
  let forallBaseline ← collectAxioms ``Inner.isDefEqForall.WF
  let quickBaseline ← collectAxioms ``Inner.quickIsDefEq.WF
  let normalizerBaseline ← collectAxioms ``Inner.whnf'.WF
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  logInfo m!"existing semantic lambda comparison baseline: {repr lambdaBaseline}"
  logInfo m!"existing semantic forall comparison baseline: {repr forallBaseline}"
  logInfo m!"existing semantic quick comparison baseline: {repr quickBaseline}"
  logInfo m!"existing semantic normalization baseline: {repr normalizerBaseline}"
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned scoped comparison axiom {name}"
      if let some proof := information.value? then
        if proof.hasSorry then throwError "owned scoped comparison admission {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless lambdaBaseline.contains dependency || forallBaseline.contains dependency ||
            quickBaseline.contains dependency || normalizerBaseline.contains dependency ||
            native.contains dependency do
          throwError "unexpected scoped comparison dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned scoped comparison declarations audited against existing semantic lambda/forall/quick/normalization baselines and native scope foundations; inherited admissions remain explicit; no owned axioms or proof admissions"
  nativeControls

end ScopedComparisonTest
