import Lean4Lean.Verify.InductiveParameterOpeningAgreement
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive
open Lean4Lean.TypeChecker (MLCtx)

namespace InductiveParameterOpeningAgreementTest

private def sourceType : Expr :=
  .forallE `sourceType (.mdata {} (.sort .zero))
    (.forallE `sourceValue (.mdata {} (.bvar 0)) (.mdata {} (.sort .zero)) .implicit) .strictImplicit

private def targetType : Expr :=
  .forallE `targetType (.sort .zero) (.forallE `targetValue (.bvar 0) (.sort .zero) .default) .default

private def originalSemantic : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.sort .zero))

private theorem environmentWF : VEnv.empty.WF := ⟨[], .empty⟩

private theorem sortTyping (context : List VExpr) :
    VEnv.empty.HasType 0 context (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF (by trivial) (by trivial) rfl

private theorem targetTranslation : TrExprS VEnv.empty [] [] targetType originalSemantic :=
  .forallE ⟨_, sortTyping []⟩
    (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩) (.sort rfl)
    (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩ (.bvar rfl) (.sort rfl))

private theorem sourceTranslation : TrExprS VEnv.empty [] [] sourceType originalSemantic :=
  .forallE ⟨_, sortTyping []⟩
    (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩) (.mdata (.sort rfl))
    (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩ (.mdata (.bvar rfl)) (.mdata (.sort rfl)))

private theorem originalTyping : VEnv.empty.IsType 0 [] originalSemantic :=
  .forallE ⟨_, sortTyping []⟩ (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩)

private theorem differentNativeInputs : sourceType ≠ targetType := by
  simp [sourceType, targetType]

private theorem actualAgreement (count : Nat) (nativeEnv : Kernel.Environment)
    (state : ElimNestedInductive.State) :
    ((do
      let source ← withParams sourceType count (fun lctx remainder params => pure (lctx, remainder, params))
      let target ← withParams targetType count (fun lctx remainder params => pure (lctx, remainder, params))
      return (source, target) : M ((LocalContext × Expr × Array Expr) × (LocalContext × Expr × Array Expr)))
        nativeEnv state).WF fun returned =>
      TypedParameterAgreement VEnv.empty [] count returned.1.1.1 returned.1.2.1
        returned.1.1.2.1 returned.1.2.2.1 returned.1.1.2.2 returned.1.2.2.2 :=
  (withParams.getTypedAgreement environmentWF sourceType targetType originalSemantic
    sourceTranslation targetTranslation originalTyping count nativeEnv state).mono fun _ receipts => receipts.2.2

private theorem rebindActualRemainder
    (agreement : TypedParameterAgreement VEnv.empty [] count sourceContext targetContext
      sourceRemainder targetRemainder sourceParams targetParams)
    (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (replaceParams targetParams sourceRemainder sourceParams nativeEnv state).WF fun returned =>
      returned.2 = state ∧ Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
      ∃ (target : MLCtx) (semantic : VExpr) (level : VLevel),
        target.WF VEnv.empty [] ∧ targetContext = target.lctx ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        TrExprS VEnv.empty [] target.vlctx returned.1 semantic ∧
        VEnv.empty.HasType 0 target.vlctx.toCtx semantic (.sort level) :=
  agreement.rebindRemainder environmentWF nativeEnv state

private theorem actualTypedRebinding (count : Nat) (nativeEnv : Kernel.Environment)
    (state : ElimNestedInductive.State) :
    ((do
      let source ← withParams sourceType count (fun lctx remainder params => pure (lctx, remainder, params))
      let target ← withParams targetType count (fun lctx remainder params => pure (lctx, remainder, params))
      let rebound ← replaceParams target.2.2 source.2.1 source.2.2
      return (target.1, rebound) : M (LocalContext × Expr)) nativeEnv state).WF fun returned =>
      Closed returned.1.2 0 ∧ returned.1.2.looseBVarRange' = 0 ∧
      ∃ (target : MLCtx) (semantic : VExpr) (level : VLevel),
        target.WF VEnv.empty [] ∧ returned.1.1 = target.lctx ∧
        returned.1.2.FVarsIn (· ∈ target.vlctx.fvars) ∧
        TrExprS VEnv.empty [] target.vlctx returned.1.2 semantic ∧
        VEnv.empty.HasType 0 target.vlctx.toCtx semantic (.sort level) :=
  withParams.rebindTypedRemainder environmentWF sourceType targetType originalSemantic
    sourceTranslation targetTranslation originalTyping count nativeEnv state

private theorem retainedBaseRecovery (base : MLCtx) (body targetBody : VExpr) :
    base.mkForall' 0 (by omega) body = base.mkForall' 0 (by omega) targetBody ↔
      base.vlctx.toCtx = base.vlctx.toCtx ∧ body = targetBody :=
  (ParameterPrefix.nil (base := base)).forall_eq_iff .nil rfl body targetBody

private def sourceIdentifier : FVarId := ⟨`source⟩
private def targetIdentifier : FVarId := ⟨`target⟩
private def sourceContext : MLCtx := .vlam sourceIdentifier `source (.sort .zero) (.sort .zero) .default .nil
private def targetContext : MLCtx :=
  .vlam targetIdentifier `target (.sort (.succ .zero)) (.sort (.succ .zero)) .default .nil

private theorem unequalDomains : sourceContext.vlctx.toCtx ≠ targetContext.vlctx.toCtx := by
  simp [sourceContext, targetContext, VLCtx.toCtx]

private theorem unequalReconstruction (body targetBody : VExpr) :
    sourceContext.mkForall' 1 (by decide) body ≠ targetContext.mkForall' 1 (by decide) targetBody := by
  intro equality
  have sourcePrefix : ParameterPrefix .nil sourceContext [sourceIdentifier] := .snoc .nil
  have targetPrefix : ParameterPrefix .nil targetContext [targetIdentifier] := .snoc .nil
  exact unequalDomains ((sourcePrefix.forall_eq_iff targetPrefix rfl body targetBody).mp equality).1

private def checkedType (nativeEnv : Kernel.Environment) (lctx : LocalContext) (expression : Expr) :
    Except Kernel.Exception Expr :=
  (monadLift (TypeChecker.checkType expression) : AddInductive.M Expr)
    { env := nativeEnv, lctx, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }

private def runtimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let mut checks := 0
  for start in [0, 19] do
    for count in [0, 1, 2] do
      let initial : ElimNestedInductive.State :=
        { ngen := { namePrefix := `OpeningAgreement, idx := start }, newTypes := #[], lvls := [] }
      let .ok ((source, sourceRemainder, sourceParams), middle) := withParams sourceType count
          (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv initial
        | throwError "actual annotated source opening failed"
      let .ok ((target, targetRemainder, targetParams), final) := withParams targetType count
          (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv middle
        | throwError "actual independent target opening failed"
      unless sourceParams.size == count && targetParams.size == count && final.ngen.idx == start + 2 * count do
        throwError "actual opening changed counts or generator advancement"
      if count > 0 then
        unless sourceParams != targetParams do throwError "the independently allocated parameters coincide"
        checks := checks + 1
      let .ok _ := checkedType nativeEnv source sourceRemainder | throwError "source remainder is not typed"
      let .ok _ := checkedType nativeEnv target targetRemainder | throwError "target remainder is not typed"
      let .ok (rebound, returned) := replaceParams targetParams sourceRemainder sourceParams nativeEnv final
        | throwError "actual remainder rebinding failed"
      let .ok _ := checkedType nativeEnv target rebound | throwError "rebound dependent remainder is not typed"
      unless rebound == (sourceRemainder.abstract sourceParams).instantiateRev targetParams &&
          !rebound.hasLooseBVars && returned.ngen.idx == final.ngen.idx &&
          returned.newTypes == final.newTypes && returned.nestedAux == final.nestedAux do
        throwError "remainder rebinding changed syntax, scope, generator, family state or cache"
      checks := checks + 6
  match withParams sourceType 3 (fun _ _ _ => pure ()) nativeEnv { newTypes := #[], lvls := [] } with
  | .error _ => checks := checks + 1
  | .ok _ => throwError "overlong source opening was accepted"
  unless checks == 41 do throwError "opening agreement runtime manifest changed: {checks}"
  logInfo m!"opening agreement runtime: {checks} independent, annotated, dependent, short-prefix, state and failure controls"

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "opening agreement unexpected dependency {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} dependencies = {repr dependencies}"

private def auditExact (name : Name) (expected : List Name) : MetaM Unit := do
  audit name expected
  let dependencies ← collectAxioms name
  unless dependencies.size == expected.length do
    throwError "opening agreement exact dependency count changed in {name}: {dependencies.size}"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := inherited ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq,
    ``Expr.instantiate1_eq]
  for name in [``ParameterPrefix.forall_eq_iff,
      ``unequalDomains, ``unequalReconstruction, ``differentNativeInputs, ``retainedBaseRecovery] do audit name logical
  for name in [``TypedParameterOpening.agreement, ``withParams.getTypedAgreement,
      ``TypedParameterAgreement.rebindRemainder,
      ``withParams.rebindTypedRemainder, ``actualAgreement, ``rebindActualRemainder,
      ``actualTypedRebinding] do audit name native
  auditExact ``ParameterPrefix.forall_eq_iff logical
  auditExact ``TypedParameterOpening.agreement (logical ++ [``sorryAx])
  auditExact ``withParams.getTypedAgreement (inherited ++ [``Expr.instantiate1_eq])
  auditExact ``TypedParameterAgreement.rebindRemainder
    (inherited ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq])
  auditExact ``withParams.rebindTypedRemainder native
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterOpeningAgreement
    | throwError "opening agreement module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new opening agreement axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless native.contains dependency do throwError "unexpected module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveParameterOpeningAgreementTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless native.contains dependency do throwError "unexpected fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"opening agreement exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 10 do throwError "opening agreement module manifest changed: {moduleCount}"
  unless fixtureCount == 33 do throwError "opening agreement fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveParameterOpeningAgreementTest
