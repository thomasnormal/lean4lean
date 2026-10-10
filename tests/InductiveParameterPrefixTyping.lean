import Lean4Lean.Verify.InductiveParameterPrefixTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive Lean4Lean.TypeChecker
open Lean.Kernel

namespace InductiveParameterPrefixTypingTest

inductive IndexedContainer (proposition : Prop) : Nat → Prop where
  | intro : proposition → IndexedContainer proposition 0

private def sourceType : FVarId := ⟨`IndependentSourceType⟩
private def sourceValue : FVarId := ⟨`IndependentSourceValue⟩
private def targetType : FVarId := ⟨`IndependentTargetType⟩
private def targetValue : FVarId := ⟨`IndependentTargetValue⟩
private def sourceFirst : MLCtx := .vlam sourceType `type (.sort .zero) (.sort .zero) .default .nil
private def source : MLCtx := .vlam sourceValue `value (.fvar sourceType) (.bvar 0) .default sourceFirst
private def targetFirst : MLCtx := .vlam targetType `type (.sort .zero) (.sort .zero) .default .nil
private def target : MLCtx := .vlam targetValue `value (.fvar targetType) (.bvar 0) .default targetFirst
private def sourceIdentifiers : List FVarId := [sourceType, sourceValue]
private def targetIdentifiers : List FVarId := [targetType, targetValue]

private theorem modelEnvironmentWF : VEnv.empty.WF := ⟨[], .empty⟩

private theorem sortTranslation (context : VLCtx) :
    TrExprS VEnv.empty [] context (.sort .zero) (.sort .zero) := .sort rfl

private theorem sortTyping (context : List VExpr) :
    VEnv.empty.HasType 0 context (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF (by trivial) (by trivial) rfl

private theorem sourceWellFormed : source.WF VEnv.empty [] := by
  have first : sourceFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      sortTranslation [], _, sortTyping []⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [sourceFirst, sourceType, sourceValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem targetWellFormed : target.WF VEnv.empty [] := by
  have first : targetFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      sortTranslation [], _, sortTyping []⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [targetFirst, targetType, targetValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem sourcePrefix : ParameterPrefix .nil source sourceIdentifiers := .snoc (.snoc .nil)
private theorem targetPrefix : ParameterPrefix .nil target targetIdentifiers := .snoc (.snoc .nil)
private theorem sameDependentDomains : source.vlctx.toCtx = target.vlctx.toCtx := rfl

private def body : Expr := .letE `proofUse (.fvar sourceType) (.fvar sourceValue)
  (.lam `argument (.fvar sourceType) (.fvar sourceType) .default) true
private def bodySemantic : VExpr := .lam (.bvar 1) (.bvar 2)
private def familyType : VExpr := .forallE (.bvar 1) (.sort .zero)

private theorem familyTranslation : TrExprS VEnv.empty [] source.vlctx body bodySemantic :=
  .letE (.bvar .zero) (.fvar rfl) (.fvar rfl)
    (.lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl) (.fvar rfl))

private theorem familyTyping : VEnv.empty.HasType 0 source.vlctx.toCtx bodySemantic familyType :=
  .lam (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))

private theorem independentArguments :
    ∃ arguments, TypedParameterArguments VEnv.empty [] target
      ((source.mkForall' sourceIdentifiers.length sourcePrefix.bound familyType).liftN 2)
      (targetIdentifiers.map Expr.fvar) arguments familyType := by
  obtain ⟨arguments, typing⟩ := targetPrefix.arguments modelEnvironmentWF targetWellFormed familyType
  exact ⟨arguments, typing⟩

private theorem freshTargetIsNotInRemovedBase (semantic : VExpr) :
    ¬TrExprS VEnv.empty [] [] (.fvar targetType) semantic := by
  intro translated
  cases translated with
  | fvar lookup => simp [VLCtx.find?] at lookup

private theorem typedIndependentFamily (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (replaceParams (targetIdentifiers.map Expr.fvar).toArray body
      (sourceIdentifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧ Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS VEnv.empty [] target.vlctx returned.1 resultSemantic ∧
          VEnv.empty.HasType 0 target.vlctx.toCtx resultSemantic familyType :=
  (replaceParams.prefix_rename_typed modelEnvironmentWF sourceWellFormed targetWellFormed
    sourcePrefix targetPrefix rfl sameDependentDomains familyTranslation familyTyping nativeEnv state).mono
      fun _ ⟨unchanged, _, closed, scope, support, resultSemantic, translated, typed⟩ =>
        ⟨unchanged, closed, scope, support, resultSemantic, translated, typed⟩

private def telescope : Expr :=
  .forallE `type (.sort .zero) (.forallE `value (.bvar 0) (.sort .zero) .default) .default
private def telescopeSemantic : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.sort .zero))

private theorem telescopeTranslation : TrExprS VEnv.empty [] [] telescope telescopeSemantic := by
  have domain : VEnv.empty.IsType 0 [] (.sort .zero) := ⟨_, sortTyping []⟩
  have valueDomain : VEnv.empty.IsType 0 [.sort .zero] (.bvar 0) := ⟨_, .bvar .zero⟩
  have result : VEnv.empty.IsType 0 [.bvar 0, .sort .zero] (.sort .zero) := ⟨_, sortTyping _⟩
  exact .forallE domain (.forallE valueDomain result) (sortTranslation [])
    (.forallE valueDomain result (.bvar rfl) (sortTranslation _))

private theorem telescopeTyping : VEnv.empty.IsType 0 [] telescopeSemantic :=
  .forallE ⟨_, sortTyping []⟩ (.forallE ⟨_, .bvar .zero⟩ ⟨_, sortTyping _⟩)

private theorem actualNativeOpening (numParams : Nat) (nativeEnv : Kernel.Environment)
    (state : ElimNestedInductive.State) :
    (withParams telescope numParams (fun lctx remainder params => pure (lctx, remainder, params))
      nativeEnv state).WF fun returned =>
        TypedParameterOpening VEnv.empty [] telescopeSemantic numParams returned.1.1 returned.1.2.1 returned.1.2.2 :=
  withParams.getTypedContext modelEnvironmentWF telescope telescopeSemantic telescopeTranslation telescopeTyping
    numParams nativeEnv state

private theorem ambientPrefixTyping :
    ∃ prefixSemantic prefixType,
      TrExprS VEnv.empty [] [(none, .vlam (.sort .zero))]
        (mkAppRange (Expr.lam `argument (.sort .zero) (.sort .zero) .default) 0 0 #[.bvar 0])
        prefixSemantic ∧ VEnv.empty.HasType 0 [.sort .zero] prefixSemantic prefixType := by
  have functionTranslated : TrExprS VEnv.empty [] [(none, .vlam (.sort .zero))]
      (.lam `argument (.sort .zero) (.sort .zero) .default) (.lam (.sort .zero) (.sort .zero)) :=
    .lam ⟨_, sortTyping _⟩ (sortTranslation _) (sortTranslation _)
  have functionTyped : VEnv.empty.HasType 0 [.sort .zero] (.lam (.sort .zero) (.sort .zero))
      (.forallE (.sort .zero) (.sort (.succ .zero))) := .lam (sortTyping _) (sortTyping _)
  have argumentTranslated : TrExprS VEnv.empty [] [(none, .vlam (.sort .zero))] (.bvar 0) (.bvar 0) :=
    .bvar (A := .sort .zero) rfl
  have argumentTyped : VEnv.empty.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  simpa [Expr.getAppArgs_eq, Expr.getAppArgsList, Expr.getAppArgsRevList] using
    nestedApp_prefixTyping (.app functionTyped argumentTyped functionTranslated argumentTranslated)
      (functionTyped.app argumentTyped) 0 (Nat.zero_le _)

private theorem openingSuppliesOwnArguments
    (opening : TypedParameterOpening VEnv.empty [] telescopeSemantic numParams lctx remainder params) :
    ∃ (context : MLCtx) (identifiers : List FVarId) (bound : identifiers.length ≤ context.length),
      context.lctx = lctx ∧ params = (identifiers.map Expr.fvar).toArray ∧
      identifiers.length = numParams ∧ ∀ resultType,
        ∃ arguments, TypedParameterArguments VEnv.empty [] context
          ((context.mkForall' identifiers.length bound resultType).liftN numParams)
          params.toList arguments resultType := by
  obtain ⟨context, identifiers, _, wellFormed, selected, length, rfl, rfl, _, _, _⟩ := opening
  refine ⟨context, identifiers, selected.bound, rfl, rfl, length, ?_⟩
  intro resultType
  simpa [length] using selected.arguments modelEnvironmentWF wellFormed resultType

private def sameState (first second : ElimNestedInductive.State) : Bool :=
  first.ngen.namePrefix == second.ngen.namePrefix && first.ngen.idx == second.ngen.idx &&
    first.nestedAux == second.nestedAux && first.newTypes == second.newTypes &&
    first.lvls == second.lvls && first.nextIdx == second.nextIdx

private def checkedType (nativeEnv : Kernel.Environment) (lctx : LocalContext) (expression : Expr) : Except Kernel.Exception Expr :=
  (monadLift (TypeChecker.checkType expression) : AddInductive.M Expr)
    { env := nativeEnv, lctx, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }

private def runtimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let mut checks := 0
  for sourceIndex in [0, 17] do
    for targetIndex in [0, 41] do
      let initial : ElimNestedInductive.State :=
        { ngen := { namePrefix := `ActualSourceParameters, idx := sourceIndex }, nextIdx := 29,
          lvls := [.zero], nestedAux := #[(.sort .zero, `PreviousAux)], newTypes := #[] }
      let targetInitial := { initial with ngen := { namePrefix := `ActualTargetParameters, idx := targetIndex } }
      let .ok ((sourceContext, _, sourceParams), sourceState) :=
          withParams telescope 2 (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv initial
        | throwError "actual source parameter opening failed"
      let .ok ((targetContext, _, targetParams), targetState) :=
          withParams telescope 2 (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv targetInitial
        | throwError "actual target parameter opening failed"
      unless sourceParams.size == 2 && targetParams.size == 2 && sourceParams != targetParams &&
          sourceState.ngen.idx == sourceIndex + 2 && targetState.ngen.idx == targetIndex + 2 do
        throwError "actual opening lost independent IDs or chronological parameter counts"
      let family := Expr.letE `proofUse sourceParams[0]! sourceParams[1]!
        (.lam `argument sourceParams[0]! sourceParams[0]! .default) true
      let .ok (rebound, returnedState) := replaceParams targetParams family sourceParams nativeEnv sourceState
        | throwError "independent family replacement failed"
      let expectedFamily := Expr.letE `proofUse targetParams[0]! targetParams[1]!
        (.lam `argument targetParams[0]! targetParams[0]! .default) true
      let .ok sourceFamilyType := checkedType nativeEnv sourceContext family
        | throwError "source family was not typed"
      let .ok targetFamilyType := checkedType nativeEnv targetContext rebound
        | throwError "target family was not typed"
      unless rebound == expectedFamily && sameState sourceState returnedState &&
          sourceFamilyType.isForall && targetFamilyType.isForall && !rebound.hasLooseBVars do
        throwError "non-sort family replacement changed type shape, syntax, scope or state"
      checks := checks + 5
      let nestedParameter := mkApp2 (.const ``And []) sourceParams[0]! (.const ``True [])
      let nested := mkApp2 (.const ``IndexedContainer []) nestedParameter (.const ``Nat.zero [])
      let nestedState := { sourceState with newTypes := #[{ name := ``And, type := .sort .zero, ctors := [] }] }
      let .ok (some info, classifiedState) := isNestedInductiveApp? nested nativeEnv nestedState
        | throwError "actual indexed nested application was not selected"
      let selected := mkAppRange nested.getAppFn 0 info.numParams nested.getAppArgs
      let .ok selectedType := checkedType nativeEnv sourceContext selected
        | throwError "selected partial container application was not typed"
      let .ok (renamedPrefix, renamedState) := replaceParams targetParams selected sourceParams nativeEnv classifiedState
        | throwError "actual selected prefix replacement failed"
      let .ok renamedType := checkedType nativeEnv targetContext renamedPrefix
        | throwError "renamed partial container application was not typed"
      unless info.numParams == 1 && nested.getAppArgs.size == 2 && selectedType.isForall &&
          renamedType.isForall && sameState nestedState renamedState && !renamedPrefix.hasLooseBVars do
        throwError "actual nested prefix included the residual index or lost family typing"
      checks := checks + 5
      let looseNested := mkApp2 (.const ``IndexedContainer []) nestedParameter (.bvar 0)
      let .ok (some looseInfo, _) := isNestedInductiveApp? looseNested nativeEnv nestedState
        | throwError "a loose residual index was incorrectly rejected by the parameter classifier"
      let loosePrefix := mkAppRange looseNested.getAppFn 0 looseInfo.numParams looseNested.getAppArgs
      let .ok _ := checkedType nativeEnv sourceContext
          (.forallE `index (.const ``Nat []) looseNested .default)
        | throwError "the actual indexed application was not typed under its ambient binder"
      unless looseNested.hasLooseBVars && loosePrefix == selected && !loosePrefix.hasLooseBVars do
        throwError "the ambient bound index escaped into the closed selected parameter prefix"
      checks := checks + 1
      let .ok (wrongOrder, _) := replaceParams targetParams.reverse family sourceParams nativeEnv sourceState
        | throwError "raw reversed argument control did not run"
      match checkedType nativeEnv targetContext wrongOrder with
      | .error _ => checks := checks + 1
      | .ok _ => throwError "reversed dependent target parameters incorrectly type-check"
  for count in [0, 1, 2] do
    let .ok ((context, remainder, params), _) := withParams telescope count
        (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv { lvls := [], newTypes := #[] }
      | throwError "short actual parameter opening failed"
    unless params.size == count do throwError "short actual parameter opening changed its prefix count"
    let .ok _ := checkedType nativeEnv context remainder | throwError "opened remainder was not typed"
    checks := checks + 2
  match withParams telescope 3 (fun _ _ _ => pure ()) nativeEnv { lvls := [], newTypes := #[] } with
  | .error _ => checks := checks + 1
  | .ok _ => throwError "too many parameters unexpectedly opened"
  unless checks == 55 do throwError "independent prefix runtime manifest changed: expected 55, got {checks}"
  logInfo m!"independent prefix typing runtime: {checks} actual opening, dependent-domain, non-sort family, selected indexed-prefix, state, order and failure controls"

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "independent prefix typing unexpected dependency {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} logical/inherited/native dependencies = {repr dependencies}"

private def auditExact (name : Name) (expected : List Name) : MetaM Unit := do
  audit name expected
  let dependencies ← collectAxioms name
  unless dependencies.size == expected.length do
    throwError "independent prefix typing exact dependency count changed for {name}: expected {expected.length}, got {dependencies.size}"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := inherited ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq,
    ``Expr.instantiate1_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  for name in [``ParameterPrefix.insertion, ``ParameterPrefix.forall_eq] do
    audit name logical
  let production := [``TypedParameterArguments.append, ``TypedParameterArguments.weakFV, ``ParameterPrefix.arguments,
    ``replaceParams.prefix_typedInto, ``replaceParams.prefix_rename_typed,
    ``withParams.typedContext, ``withParams.getTypedContext, ``nestedApp_prefixTyping,
    ``isNestedInductiveApp?.typedPrefix, ``isNestedInductiveApp?.typedRebinding]
  for name in production do audit name native
  for name in [``TypedParameterArguments.weakFV, ``ParameterPrefix.arguments] do auditExact name inherited
  let replacementInterfaces := inherited ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq]
  for name in [``replaceParams.prefix_typedInto, ``replaceParams.prefix_rename_typed,
      ``typedIndependentFamily] do auditExact name replacementInterfaces
  for name in [``withParams.typedContext, ``withParams.getTypedContext, ``actualNativeOpening] do
    auditExact name (inherited ++ [``Expr.instantiate1_eq])
  for name in [``nestedApp_prefixTyping, ``isNestedInductiveApp?.typedPrefix] do
    auditExact name (logical ++ [``sorryAx, `Lean.Expr.mkAppRangeAux.eq_def])
  auditExact ``isNestedInductiveApp?.typedRebinding
    (replacementInterfaces ++ [`Lean.Expr.mkAppRangeAux.eq_def])
  let fixtures := [``sourceWellFormed, ``targetWellFormed, ``sameDependentDomains,
    ``familyTranslation, ``familyTyping, ``independentArguments, ``freshTargetIsNotInRemovedBase,
    ``typedIndependentFamily, ``telescopeTranslation, ``telescopeTyping, ``actualNativeOpening,
    ``ambientPrefixTyping, ``openingSuppliesOwnArguments]
  for name in fixtures do audit name native
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterPrefixTyping
    | throwError "independent prefix typing module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new independent-prefix module axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless native.contains dependency do throwError "module-owned unexpected dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveParameterPrefixTypingTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless native.contains dependency do throwError "fixture-owned unexpected dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"independent prefix typing: {fixtures.length} fixture proof controls and {production.length + 2} production contracts; {moduleCount} module-owned and {fixtureCount} fixture-namespace declarations audited"
  unless moduleCount == 22 do throwError "independent prefix module manifest changed: expected 22, got {moduleCount}"
  unless fixtureCount == 58 do throwError "independent prefix fixture manifest changed: expected 58, got {fixtureCount}"
  runtimeControls

end InductiveParameterPrefixTypingTest
