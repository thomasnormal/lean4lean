import Lean4Lean.Verify.TypeChecker.ScopedWHNF
import Lean.Util.CollectAxioms

namespace ScopedWHNFTest
open Lean hiding Environment Exception
open Lean4Lean

private def seven : Nat := 7

private def quotientControl : Nat :=
  Quot.lift (fun value : Nat => value) (by intro first second relation; exact relation) (Quot.mk Eq 5)

private def quotientIndControl : True :=
  Quot.ind (β := fun _ => True) (fun _ : Nat => True.intro) (Quot.mk Eq 5)

private def ignoredRecursor : RecursorVal := {
  name := `IgnoredScopedRecursor
  levelParams := []
  type := .sort (.succ .zero)
  all := [`IgnoredScopedInductive]
  numParams := 0
  numIndices := 0
  numMotives := 0
  numMinors := 0
  rules := []
  k := false
  isUnsafe := true }

private theorem ignoredRecursorSupported :
    TrEnv' .safe (({} : ConstMap).insert ignoredRecursor.name (.recInfo ignoredRecursor))
      false VEnv.empty :=
  .ignoreConst (C := {}) (ci := .recInfo ignoredRecursor)
    (by simp [SMap.find?]) (by decide) .empty

example : ({} : VEnv).constants ignoredRecursor.name = none := rfl

example (valid : TrEnv safety native environment)
    (found : native.find? name = some (.recInfo header)) : ¬environment.contains name :=
  valid.recursorNotInModel found

example {monad : Type → Type} [Monad monad] {context : TypeChecker.VContext}
    (translated : context.TrExprS expression semantic)
    (normalize infer : Expr → monad Expr) (compare : Expr → Expr → monad Bool) :
    inductiveReduceRec context.env expression normalize infer compare = pure none :=
  inductiveReduceRec.eq_none translated normalize infer compare

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    (translated : context.TrExprS expression semantic) :
    (quotReduceRec expression TypeChecker.Inner.whnf).ScopeWF context state (fun _ _ => True) :=
  quotReduceRec.scopeFrame translated

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj).ScopeWF context state (fun _ _ => True) :=
  TypeChecker.Inner.reduceRecursor.scopeFrame translated

example : (TypeChecker.Methods.withFuel 0).ScopeWF := TypeChecker.Methods.withFuel.zero_scopeWF

example {context : TypeChecker.VContext} {state : TypeChecker.VState} (valid : state.WF context) :
    TypeChecker.HeadCacheNamesWF state.toState := valid.headCacheNames

example {context : TypeChecker.VContext} {state : TypeChecker.VState} (valid : state.WF context) :
    NativeLocalNamesWF context.lctx' state.ngen := valid.localNames

example {context : TypeChecker.VContext} {state : TypeChecker.VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized :=
  TypeChecker.Inner.whnfCore'.scopeWF translated

example {context : TypeChecker.VContext} {state : TypeChecker.VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.Inner.whnf' expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized :=
  TypeChecker.Inner.whnf'.scopeWF translated

private def stableHead (locals : LocalContext) (expression : Expr) : Bool :=
  !expression.isMData && !expression.isLet && match expression with
    | .fvar identifier => !TypeChecker.Inner.isLetFVar locals identifier
    | _ => true

private def stableCaches (locals : LocalContext) (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => stableHead locals entry.2) &&
    state.whnfCache.toList.all (fun entry => stableHead locals entry.2)

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let some (.defnInfo quotientInfo) := environment.find? ``quotientControl
    | throwError "scoped quotient lift fixture absent"
  let some (.defnInfo quotientIndInfo) := environment.find? ``quotientIndControl
    | throwError "scoped quotient induction fixture absent"
  let quotientConstructor := quotientInfo.value.getAppArgs[5]!
  unless quotientConstructor.isAppOfArity ``Quot.mk 3 do
    throwError "scoped quotient lift fixture lost its constructor"
  let quotientCoreExpected := quotientConstructor.appArg!
  let natural := Expr.const ``Nat []
  let literal := Expr.lit (.natVal 7)
  let localId : FVarId := ⟨`scopedNativeLocal⟩
  let letId : FVarId := ⟨`scopedNativeLet⟩
  let localHead := Expr.fvar localId
  let letHead := Expr.fvar letId
  let locals := ({} : LocalContext).mkLocalDecl localId `localValue natural .default
    |>.mkLetDecl letId `letValue natural (.mdata {} literal)
  let identity := Expr.lam `argument natural (.bvar 0) .default
  let curried := Expr.lam `first natural (.lam `second natural (.bvar 1) .default) .default
  let letExpression := Expr.letE `value natural literal (.bvar 0) false
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, localHead]
  let delta := Expr.const ``seven []
  let add := mkAppN (.const ``Nat.add []) #[.lit (.natVal 3), .lit (.natVal 4)]
  let power := mkAppN (.const ``Nat.pow []) #[.lit (.natVal 2), .lit (.natVal 3)]
  let equal := mkAppN (.const ``Nat.beq []) #[literal, literal]
  let cases : List (Expr × Expr × Expr) := [
    (.mdata {} localHead, localHead, localHead),
    (.mdata {} letHead, literal, literal),
    (letExpression, literal, literal),
    (.app identity literal, literal, literal),
    (mkAppN curried #[localHead, literal], localHead, localHead),
    (.app (.mdata {} identity) literal, literal, literal),
    (.proj ``Prod 0 pair, literal, literal),
    (.proj ``Prod 1 pair, localHead, localHead),
    (delta, delta, literal),
    (add, add, literal),
    (power, power, .lit (.natVal 8)),
    (equal, equal, .const ``Bool.true []),
    (quotientInfo.value, quotientCoreExpected, .lit (.natVal 5)),
    (.mdata {} quotientIndInfo.value, .const ``True.intro [], .const ``True.intro [])]
  let mut coreCount := 0
  let mut fullCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            let methods := TypeChecker.Methods.withFuel fuel
            let context : TypeChecker.Context := {
              env := environment, safety, lctx := locals, eagerReduce := eager, fuel := { recDepth := fuel } }
            let mut state : TypeChecker.State := {}
            for _ in [0:2] do
              for (source, coreExpected, fullExpected) in cases do
                let .ok (normalized, next) := TypeChecker.Inner.whnfCore' source cheapRec cheapProj methods context state
                  | throwError "actual scoped core worker rejected"
                unless normalized == coreExpected && stableHead locals normalized && stableCaches locals next do
                  throwError "actual scoped core worker loses expected head or cache scope: source {source}, result {repr normalized}, expected {repr coreExpected}, stable head {stableHead locals normalized}, stable caches {stableCaches locals next}, cheap recursor {cheapRec}, cheap projection {cheapProj}"
                state := next
                coreCount := coreCount + 1
                let .ok (normalized, next) := TypeChecker.Inner.whnf' source methods context state
                  | throwError "actual scoped full worker rejected"
                unless normalized == fullExpected && stableHead locals normalized && stableCaches locals next do
                  throwError "actual scoped full worker loses expected head or cache scope"
                state := next
                fullCount := fullCount + 1
            let stringProjection := Expr.proj ``String 0 (.lit (.strVal "A"))
            let stringResult := TypeChecker.Inner.whnf' stringProjection (TypeChecker.Methods.withFuel 1024)
              { context with fuel := { recDepth := 1024, whnf := 1024, whnfEager := 1024 } } state
            let .ok (characters, next) := stringResult
              | match stringResult with
                | .error .deepRecursion => throwError "actual string projection expansion exceeded callback fuel"
                | .error .deterministicTimeout => throwError "actual string projection expansion timed out"
                | .error (.other message) => throwError "actual string projection expansion rejected: {message}"
                | _ => throwError "actual string projection expansion rejected differently"
            unless characters.getAppFn == .const ``ByteArray.mk [] && stableHead locals characters &&
                stableCaches locals next do
              throwError "actual string byte-array projection expansion differs or loses scoped caches"
  let context : TypeChecker.Context := { env := environment, lctx := locals }
  let poisoned : TypeChecker.State := {
    whnfCoreCache := ({} : ExprMap Expr).insert letExpression letHead,
    whnfCache := ({} : ExprMap Expr).insert letExpression letHead }
  let .ok (badCore, _) := TypeChecker.whnfCore letExpression context poisoned
    | throwError "poisoned scoped core cache precondition control rejected"
  let .ok (badFull, _) := TypeChecker.whnf letExpression context poisoned
    | throwError "poisoned scoped full cache precondition control rejected"
  unless badCore == letHead && badFull == letHead && !badCore.isLet && !badCore.isMData &&
      !stableHead locals badCore && !stableHead locals badFull do
    throwError "conversion-only/local-let warm cache precondition control disappeared"
  let zero := TypeChecker.Methods.withFuel 0
  unless !(zero.whnfCore literal false false context {}).isOk && !(zero.whnf literal context {}).isOk do
    throwError "zero-fuel implementing normalization method unexpectedly accepted"
  let .ok (pureCore, _) := TypeChecker.Inner.whnfCore' literal false false zero context {}
    | throwError "actual zero-callback core worker easy case rejected"
  let .ok (pureFull, _) := TypeChecker.Inner.whnf' literal zero context {}
    | throwError "actual zero-callback full worker easy case rejected"
  unless pureCore == literal && pureFull == literal do throwError "zero-callback worker easy case differs"
  let timeout : TypeChecker.Context := { context with fuel := { whnf := 0, whnfEager := 0 } }
  unless !(TypeChecker.Inner.whnf' delta (TypeChecker.Methods.withFuel 32) timeout {}).isOk do
    throwError "actual zero-budget delta loop unexpectedly accepted"
  logInfo m!"{coreCount} actual core and {fullCount} actual full normalizations retain expected scoped heads and caches; cold/warm, both safeties/eager modes, fuels 32/128, all cheap flags; local/let heads, metadata, beta spines, rebuilt heads, projections, delta, Nat/Bool and quotient lift/induction reductions; 32 actual string byte-array projections at callback/WHNF budget 1024 pass; poisoned local-let caches and resource boundaries are negative controls, not model/checker receipts; actual nonzero scoped callback/fuel closure remains open"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedWHNF
    | throwError "scoped normalizer module absent"
  let baseline ← collectAxioms ``TypeChecker.Inner.whnf'.WF
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  logInfo m!"existing semantic full-normalizer baseline: {repr baseline}"
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned scoped normalizer axiom {name}"
      if let some proof := information.value? then
        if proof.hasSorry then throwError "owned scoped normalizer admission {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency || native.contains dependency do
          throwError "unexpected scoped normalizer dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  for theoremName in #[``TrEnv'.recursorLookupRejected, ``TrEnv.recursorLookupRejected,
      ``TrEnv.recursorNotInModel, ``inductiveReduceRec.eq_none, ``ignoredRecursorSupported] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "recursor scope axiom {theoremName}"
    let some proof := information.value? | throwError "recursor scope proof absent {theoremName}"
    if proof.hasSorry then throwError "recursor scope admission {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency || native.contains dependency do
        throwError "unexpected recursor scope dependency {dependency} in {theoremName}"
  logInfo m!"{owned} exhaustive owned model-aware scope/normalizer declarations audited against existing semantic WHNF baseline and native scope foundations; inherited admissions remain explicitly visible; no owned axiom or proof admission; recursor lookup exclusions and actual inductive rejection audited"
  nativeControls

end ScopedWHNFTest
