import Lean4Lean.Verify.TypeChecker.ScopedDelta
import Lean.Util.CollectAxioms

namespace ScopedDeltaTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private def seven : Nat := nat_lit 7
private def eight : Nat := nat_lit 8
private def ordinarySeven : Nat := 7
private def aliasSeven : Nat := seven
private def constantFunction (_value : Nat) : Nat := nat_lit 7
private def successorAlias := Nat.succ

example {context : VContext} {state : VState} {action : M Result} {post}
    (valid : action.ScopeWF context state post) :
    (liftM action : RecM Result).ScopeWF context state post := valid.lift

example {context : VContext} {state : VState} :
    (Inner.cacheFailure first second).ScopeWF context state (fun _ _ => True) :=
  Inner.cacheFailure.scopeWF

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.tryUnfoldProjApp expression).ScopeWF context state fun result _ =>
      ∀ normalized, result = some normalized →
        context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic :=
  Inner.tryUnfoldProjApp.scopeWF translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.reduceNat expression).ScopeWF context state fun result _ =>
      ∀ normalized, result = some normalized →
        context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic :=
  Inner.reduceNat.scopeWF translated

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.lazyDeltaReductionStep first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) :=
  Inner.lazyDeltaReductionStep.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.lazyDeltaReduction.loop first second budget).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic) :=
  Inner.lazyDeltaReduction.loop.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.lazyDeltaReduction first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic) :=
  Inner.lazyDeltaReduction.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqOffset first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqOffset.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryStringLitExpansionCore first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryStringLitExpansionCore.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryStringLitExpansion first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryStringLitExpansion.scopeWF firstTranslation secondTranslation

private def stableHead (locals : LocalContext) (expression : Expr) : Bool :=
  !expression.isMData && !expression.isLet && match expression with
    | .fvar identifier => !Inner.isLetFVar locals identifier
    | _ => true

private def stableCaches (locals : LocalContext) (state : State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => stableHead locals entry.2) &&
    state.whnfCache.toList.all (fun entry => stableHead locals entry.2)

private def sameStatus : ReductionStatus → ReductionStatus → Bool
  | .bool first, .bool second => first == second
  | .unknown firstLeft firstRight, .unknown secondLeft secondRight
  | .continue firstLeft firstRight, .continue secondLeft secondRight =>
    firstLeft == secondLeft && firstRight == secondRight
  | _, _ => false

private def describeStatus : ReductionStatus → MessageData
  | .bool equal => m!"Boolean {equal}"
  | .unknown first second => m!"unknown {repr first}, {repr second}"
  | .continue first second => m!"continue {repr first}, {repr second}"

private def describeAttempt : Except Kernel.Exception Result → String
  | .ok _ => "success"
  | .error .deterministicTimeout => "deterministic timeout"
  | .error .deepRecursion => "callback recursion exhausted"
  | .error (.other message) => message
  | .error _ => "non-resource kernel exception"

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let boolean := Expr.const ``Bool []
  let literal := Expr.lit (.natVal 7)
  let different := Expr.lit (.natVal 8)
  let firstDefinition := Expr.const ``seven []
  let secondDefinition := Expr.const ``eight []
  let ordinaryDefinition := Expr.const ``ordinarySeven []
  let wrappedLiteral := mkAppN (.const ``OfNat.ofNat [.zero])
    #[natural, literal, .app (.const ``instOfNatNat []) literal]
  let aliasDefinition := Expr.const ``aliasSeven []
  let constant := Expr.const ``constantFunction []
  let successor := Expr.const ``successorAlias []
  let aliasIdentifier : FVarId := ⟨`scopedDeltaAlias⟩
  let pairIdentifier : FVarId := ⟨`scopedDeltaPair⟩
  let pairType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, different]
  let projection := Expr.proj ``Prod 0 pair
  let stuckProjection := Expr.proj ``Prod 0 (.fvar pairIdentifier)
  let locals := ({} : LocalContext).mkLocalDecl pairIdentifier `pair pairType .default
    |>.mkLetDecl aliasIdentifier `alias (.sort (.succ .zero)) natural
  let steps : Array (Expr × Expr × ReductionStatus × Bool) := #[
    (natural, boolean, .unknown natural boolean, false),
    (firstDefinition, literal, .bool true, false),
    (literal, firstDefinition, .bool true, false),
    (firstDefinition, secondDefinition, .bool false, false),
    (aliasDefinition, firstDefinition, .bool true, false),
    (firstDefinition, aliasDefinition, .bool true, false),
    (aliasDefinition, literal, .continue firstDefinition literal, false),
    (firstDefinition, projection, .continue firstDefinition literal, false),
    (projection, firstDefinition, .continue literal firstDefinition, false),
    (.app constant literal, .app constant literal, .bool true, false),
    (.app constant literal, .app constant different, .bool true, true),
    (.app successor literal, .app successor different,
      .continue (.app (.const ``Nat.succ []) literal) (.app (.const ``Nat.succ []) different), true),
    (ordinaryDefinition, literal, .continue wrappedLiteral literal, false),
    (stuckProjection, stuckProjection, .unknown stuckProjection stuckProjection, false)]
  let loops : Array (Expr × Expr × ReductionStatus) := #[
    (natural, boolean, .unknown natural boolean),
    (firstDefinition, literal, .bool true),
    (literal, firstDefinition, .bool true),
    (firstDefinition, secondDefinition, .bool false),
    (aliasDefinition, literal, .bool true),
    (firstDefinition, projection, .bool true),
    (projection, firstDefinition, .bool true),
    (.app constant literal, .app constant different, .bool true),
    (.app successor literal, .app successor different, .bool false),
    (literal, literal, .bool true), (literal, different, .bool false),
    (stuckProjection, stuckProjection, .unknown stuckProjection stuckProjection)]
  let strings : List (RecM LBool × LBool) := [
    (Inner.tryStringLitExpansionCore (.lit (.strVal "ab")) (.strLitToConstructor "ab"), .true),
    (Inner.tryStringLitExpansionCore literal natural, .undef),
    (Inner.tryStringLitExpansionCore (.lit (.strVal "ab")) (.lit (.strVal "ab")), .undef),
    (Inner.tryStringLitExpansion (.lit (.strVal "ab")) (.strLitToConstructor "ab"), .true),
    (Inner.tryStringLitExpansion (.strLitToConstructor "ab") (.lit (.strVal "ab")), .true),
    (Inner.tryStringLitExpansion literal natural, .undef),
    (Inner.isDefEqOffset (.lit (.natVal 0)) .natZero, .true),
    (Inner.isDefEqOffset literal different, .false),
    (Inner.isDefEqOffset natural boolean, .undef)]
  let mismatchedStrings : List (RecM LBool) := [
    Inner.tryStringLitExpansionCore (.lit (.strVal "ab")) (.strLitToConstructor "ac"),
    Inner.tryStringLitExpansion (.strLitToConstructor "ac") (.lit (.strVal "ab"))]
  let mut stepCount := 0
  let mut loopCount := 0
  let mut stringOffsetCount := 0
  let mut mismatchCount := 0
  let mut projectionCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager,
          fuel := { recDepth := fuel, lazyDelta := 8 } }
        let methods := Methods.withFuel fuel
        for bound : control in [:steps.size] do
          let (first, second, expected, cachedFailure) := steps[control]
          unless (TypeChecker.checkType first context {}).isOk && (TypeChecker.checkType second context {}).isOk do
            throwError "typed delta step inputs rejected at {control}"
          let mut state : State := {}
          for _ in [:2] do
            let .ok (result, finalState) := Inner.lazyDeltaReductionStep first second methods context state
              | throwError "scoped delta step rejected at {control}, fuel={fuel}"
            unless sameStatus result expected && stableCaches locals finalState &&
                Inner.failedBefore finalState.failure first second == cachedFailure do
              throwError "scoped delta step lost result/frame/failure cache at {control}, fuel={fuel}: actual={describeStatus result}, expected={describeStatus expected}, scoped={stableCaches locals finalState}, cached={Inner.failedBefore finalState.failure first second}"
            state := finalState
            stepCount := stepCount + 1
        for bound : control in [:loops.size] do
          let (first, second, expected) := loops[control]
          unless (TypeChecker.checkType first context {}).isOk && (TypeChecker.checkType second context {}).isOk do
            throwError "typed delta loop inputs rejected at {control}"
          for action in [Inner.lazyDeltaReduction.loop first second 2,
              Inner.lazyDeltaReduction.loop first second 8, Inner.lazyDeltaReduction first second] do
            let mut state : State := {}
            for _ in [:2] do
              let .ok (result, finalState) := action methods context state
                | throwError "scoped delta loop rejected at {control}, fuel={fuel}"
              unless sameStatus result expected && stableCaches locals finalState do
                throwError "scoped delta loop lost terminal result/frame at {control}, fuel={fuel}: actual={describeStatus result}, expected={describeStatus expected}, scoped={stableCaches locals finalState}"
              state := finalState
              loopCount := loopCount + 1
        for ((action, expected), control) in strings.zipIdx do
          let stringContext : Context := { context with fuel := { context.fuel with lazyDelta := 1000 } }
          let mut state : State := {}
          for _ in [:2] do
            let attempted := action methods stringContext state
            let .ok (result, finalState) := attempted
              | throwError "scoped string/offset control rejected at {control}, fuel={fuel}: {describeAttempt attempted}"
            unless result == expected && stableCaches locals finalState do
              throwError "scoped string/offset control lost three-valued result/frame at {control}, fuel={fuel}"
            state := finalState
            stringOffsetCount := stringOffsetCount + 1
        for (source, expected) in [(projection, some literal), (stuckProjection, none), (natural, none)] do
          let mut state : State := {}
          for _ in [:2] do
            let .ok (result, finalState) := Inner.tryUnfoldProjApp source methods context state
              | throwError "scoped projection-app guard rejected"
            unless result == expected && stableCaches locals finalState do
              throwError "scoped projection-app guard lost optional result/frame"
            state := finalState
            projectionCount := projectionCount + 1
        unless !(Inner.lazyDeltaReduction.loop aliasDefinition literal 1 methods context {}).isOk do
          throwError "one-step lazy-delta continuation budget unexpectedly suffices"
        unless !(Inner.lazyDeltaReduction.loop literal literal 0 methods context {}).isOk do
          throwError "zero lazy-delta budget unexpectedly succeeds"
        let .ok (equal, finalState) := methods.isDefEqCore ordinaryDefinition literal context {}
          | throwError "ordinary OfNat numeral comparison rejected"
        unless equal && stableCaches locals finalState do
          throwError "ordinary OfNat numeral comparison loses result/frame"
      let mismatchContext : Context := {
        env := environment, lctx := locals, safety, eagerReduce := eager,
        fuel := { recDepth := 1024, lazyDelta := 1000 } }
      for action in mismatchedStrings do
        let mut state : State := {}
        for _ in [:2] do
          let attempted := action (Methods.withFuel 1024) mismatchContext state
          let .ok (result, finalState) := attempted
            | throwError "mismatched string control rejected at 1024: {describeAttempt attempted}"
          unless result == .false && stableCaches locals finalState do
            throwError "mismatched string control lost false result/frame"
          state := finalState
          mismatchCount := mismatchCount + 1
        match action (Methods.withFuel 32) mismatchContext {} with
        | .error .deepRecursion => pure ()
        | _ => throwError "mismatched string depth-32 resource boundary changed"
  let context : Context := { env := environment, lctx := locals }
  let .ok (result, finalState) := Inner.lazyDeltaReduction.loop (.lit (.natVal 0)) .natZero 1
      (Methods.withFuel 0) context {} | throwError "pure zero-callback-fuel offset control rejected"
  unless sameStatus result (.bool true) && stableCaches locals finalState do
    throwError "pure offset control loses result/frame"
  unless !(Inner.lazyDeltaReductionStep firstDefinition literal (Methods.withFuel 0) context {}).isOk do
    throwError "zero callback fuel delta unfolding unexpectedly succeeds"
  let zeroBudget : Context := { context with fuel := { lazyDelta := 0 } }
  unless !(Inner.lazyDeltaReduction literal literal (Methods.withFuel 32) zeroBudget {}).isOk do
    throwError "configured zero lazy-delta budget unexpectedly succeeds"
  let poisoned : State := { whnfCache := ({} : ExprMap Expr).insert natural (.fvar aliasIdentifier) }
  let .ok (_, poisonedFinal) := Inner.lazyDeltaReductionStep natural boolean (Methods.withFuel 0) context poisoned
    | throwError "delta cache-premise pure guard rejected"
  unless !stableCaches locals poisonedFinal do throwError "delta cache premise disappeared"
  logInfo m!"{stepCount} cold/warm typed actual lazy-delta steps, {loopCount} typed terminal loop/configured reductions, {stringOffsetCount} three-valued string/offset controls, {mismatchCount} false string controls at callback depth 1024 and {projectionCount} projection-app guards preserve results and scoped caches; both safeties/eager modes and ordinary callback fuels 32/128; regular same-head success, failed argument caching with equal/unequal unfolded bodies, hint ordering, raw/OfNat-wrapped numerals, actual continue/unknown/Boolean statuses, open projection and Nat paths, symmetric string expansion, explicit loop budgets 2/8, one-step exhaustion, zero loop/callback fuel, mismatched-string depth-32 exhaustion and poisoned-cache premise covered; no arbitrary-fuel scoped method instance is fabricated"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedDelta
    | throwError "scoped delta module absent"
  let mut baseline := #[]
  for theoremName in #[``Inner.lazyDeltaReductionStep.WF, ``Inner.lazyDeltaReduction.loop.WF,
      ``Inner.tryStringLitExpansion.WF, ``Inner.reduceNat.WF] do
    let dependencies ← collectAxioms theoremName
    logInfo m!"existing semantic delta/string baseline {theoremName}: {repr dependencies}"
    baseline := baseline ++ dependencies
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned scoped delta axiom {name}"
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then throwError "owned scoped delta admission {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency || native.contains dependency do
          throwError "unexpected scoped delta dependency {dependency} in {name}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned scoped delta/string declarations audited against original semantic workers and native scope foundations; inherited admissions remain explicit; no owned axioms or proof admissions"
  nativeControls

end ScopedDeltaTest
