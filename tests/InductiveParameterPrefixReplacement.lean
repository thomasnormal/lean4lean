import Lean4Lean.Verify.InductiveParameterPrefixReplacement
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive Lean4Lean.TypeChecker
open Lean.Kernel

namespace InductiveParameterPrefixReplacementTest

private def targetType : FVarId := ⟨`PrefixTargetType⟩
private def targetValue : FVarId := ⟨`PrefixTargetValue⟩
private def sourceType : FVarId := ⟨`PrefixSourceType⟩
private def sourceValue : FVarId := ⟨`PrefixSourceValue⟩
private def sourceExtra : FVarId := ⟨`PrefixSourceExtra⟩
private def insertedFirst : FVarId := ⟨`PrefixInsertedFirst⟩
private def insertedSecond : FVarId := ⟨`PrefixInsertedSecond⟩

private def baseType : MLCtx := .vlam targetType `targetType (.sort .zero) (.sort .zero) .default .nil
private def base : MLCtx := .vlam targetValue `targetValue (.fvar targetType) (.bvar 0) .default baseType
private def sourceFirst : MLCtx := .vlam sourceType `sourceType (.sort .zero) (.sort .zero) .default base
private def source : MLCtx := .vlam sourceValue `sourceValue (.fvar sourceType) (.bvar 0) .default sourceFirst
private def targetFirst : MLCtx := .vlam insertedFirst `insertedFirst (.sort .zero) (.sort .zero) .default base
private def target : MLCtx := .vlam insertedSecond `insertedSecond (.sort .zero) (.sort .zero) .default targetFirst
private def identifiers : List FVarId := [sourceType, sourceValue]
private def replacements : List Expr := [.fvar targetType, .fvar targetValue]
private def semantics : List VExpr := [.bvar 1, .bvar 0]

private theorem sortTranslation (context : VLCtx) :
    TrExprS VEnv.empty [] context (.sort .zero) (.sort .zero) :=
  .sort (by simp [VLevel.ofLevel])

private theorem sortTyping (context : List VExpr) :
    VEnv.empty.HasType 0 context (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF (by trivial) (by trivial) rfl

private theorem baseWellFormed : base.WF VEnv.empty [] := by
  have first : baseType.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      sortTranslation [], _, sortTyping []⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [baseType, targetType, targetValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem sourceWellFormed : source.WF VEnv.empty [] := by
  have first : sourceFirst.WF VEnv.empty [] :=
    ⟨baseWellFormed, baseWellFormed.tr.find?_eq_none.mpr
      (by simp [base, baseType, sourceType, targetType, targetValue]), sortTranslation _, _, sortTyping _⟩
  exact ⟨first, first.tr.find?_eq_none.mpr
    (by simp [sourceFirst, base, baseType, sourceValue, sourceType, targetType, targetValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem targetWellFormed : target.WF VEnv.empty [] := by
  have first : targetFirst.WF VEnv.empty [] :=
    ⟨baseWellFormed, baseWellFormed.tr.find?_eq_none.mpr
      (by simp [base, baseType, insertedFirst, targetType, targetValue]), sortTranslation _, _, sortTyping _⟩
  exact ⟨first, first.tr.find?_eq_none.mpr
    (by simp [targetFirst, base, baseType, insertedSecond, insertedFirst, targetType, targetValue]),
    sortTranslation _, _, sortTyping _⟩

private theorem actualPrefix : ParameterPrefix base source identifiers :=
  .snoc (.snoc .nil)

private theorem independentInsertion : VLCtx.FVLift' base.vlctx target.vlctx 0 (.skip (.skip .refl)) 0 :=
  .skip_fvar _ _ (.skip_fvar _ _ .refl)

private def body : Expr :=
  .forallE `formal (.fvar sourceType)
    (.letE `proofUse (.fvar sourceType) (.fvar sourceValue) (.fvar sourceType) true) .default

private def bodySemantic : VExpr := .forallE (.bvar 1) (.bvar 2)

private theorem bodyTranslation : TrExprS VEnv.empty [] source.vlctx body bodySemantic := by
  have domainTyped : VEnv.empty.HasType 0 source.vlctx.toCtx (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have resultTyped : VEnv.empty.HasType 0 (.bvar 1 :: source.vlctx.toCtx) (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  exact .forallE ⟨_, domainTyped⟩ ⟨_, resultTyped⟩ (.fvar rfl)
    (.letE (.bvar (.succ .zero)) (.fvar rfl) (.fvar rfl) (.fvar rfl))

private theorem bodyTyping : VEnv.empty.HasType 0 source.vlctx.toCtx bodySemantic (.sort .zero) := by
  have domainTyped : VEnv.empty.HasType 0 source.vlctx.toCtx (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have resultTyped : VEnv.empty.HasType 0 (.bvar 1 :: source.vlctx.toCtx) (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  exact VEnv.IsDefEq.defeq (.sortDF (by exact ⟨trivial, trivial⟩) (by trivial) VLevel.imax_zero)
    (.forallEDF domainTyped resultTyped)

private theorem dependentArguments : TypedParameterArguments VEnv.empty [] base
    (source.mkForall' identifiers.length actualPrefix.bound (.sort .zero))
    replacements semantics (.sort .zero) :=
  .cons (.fvar rfl) (.bvar (.succ .zero)) (.cons (.fvar rfl) (.bvar .zero) .nil)

private def betaReplacement : Expr :=
  .app (.lam `identity (.fvar targetType) (.bvar 0) .default) (.fvar targetValue)

private def betaSemantic : VExpr := .app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)

private theorem betaTranslationAndTyping :
    TrExprS VEnv.empty [] base.vlctx betaReplacement betaSemantic ∧
    VEnv.empty.HasType 0 base.vlctx.toCtx betaSemantic (.bvar 1) := by
  have domainTyped : VEnv.empty.HasType 0 base.vlctx.toCtx (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have identityTyped : VEnv.empty.HasType 0 base.vlctx.toCtx
      (.lam (.bvar 1) (.bvar 0)) (.forallE (.bvar 1) (.bvar 2)) :=
    .lamDF domainTyped (.bvar .zero)
  have valueTyped : VEnv.empty.HasType 0 base.vlctx.toCtx (.bvar 0) (.bvar 1) := .bvar .zero
  exact ⟨.app identityTyped valueTyped (.lam ⟨_, domainTyped⟩ (.fvar rfl) (.bvar rfl)) (.fvar rfl),
    identityTyped.app valueTyped⟩

private theorem nonliteralDependentArguments : TypedParameterArguments VEnv.empty [] base
    (source.mkForall' identifiers.length actualPrefix.bound (.sort .zero))
    [.fvar targetType, betaReplacement] [.bvar 1, betaSemantic] (.sort .zero) :=
  .cons (.fvar rfl) (.bvar (.succ .zero))
    (.cons betaTranslationAndTyping.1 betaTranslationAndTyping.2 .nil)

private def Receipt (arguments : List Expr) (state : ElimNestedInductive.State) : Prop :=
  (replaceParams arguments.toArray body (identifiers.map Expr.fvar).toArray
    (Lean.Kernel.Environment.empty `PrefixFixture) state).WF fun returned =>
      returned.2 = state ∧ returned.1 = (body.abstractList identifiers).instantiateRevList arguments ∧
      Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧ returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧
      ∃ semantic, TrExprS VEnv.empty [] base.vlctx returned.1 semantic ∧
        VEnv.empty.HasType 0 base.vlctx.toCtx semantic (.sort .zero) ∧
        TrExprS VEnv.empty [] target.vlctx returned.1 (semantic.lift' (.skip (.skip .refl))) ∧
        VEnv.empty.HasType 0 target.vlctx.toCtx (semantic.lift' (.skip (.skip .refl))) (.sort .zero)

private theorem replaceTheWholeDependentPrefix (state : ElimNestedInductive.State) : Receipt replacements state := by
  exact (replaceParams.prefix_typedRebased ⟨[], .empty⟩ sourceWellFormed actualPrefix bodyTranslation bodyTyping
    dependentArguments rfl targetWellFormed independentInsertion
    (Lean.Kernel.Environment.empty `PrefixFixture) state).mono fun returned receipts => by
      obtain ⟨unchanged, equation, closed, scope, support, semantic, translated, typed, _,
        targetTranslated, targetTyped, _⟩ := receipts
      exact ⟨unchanged, equation, closed, scope, support, semantic, translated, typed, targetTranslated, targetTyped⟩

private theorem replaceWithANonliteralDependentArgument (state : ElimNestedInductive.State) :
    Receipt [.fvar targetType, betaReplacement] state := by
  exact (replaceParams.prefix_typedRebased ⟨[], .empty⟩ sourceWellFormed actualPrefix bodyTranslation bodyTyping
    nonliteralDependentArguments rfl targetWellFormed independentInsertion
    (Lean.Kernel.Environment.empty `PrefixFixture) state).mono fun returned receipts => by
      obtain ⟨unchanged, equation, closed, scope, support, semantic, translated, typed, _,
        targetTranslated, targetTyped, _⟩ := receipts
      exact ⟨unchanged, equation, closed, scope, support, semantic, translated, typed, targetTranslated, targetTyped⟩

private theorem emptyPrefixStillSuppliesTypehood (state : ElimNestedInductive.State) :
    (replaceParams #[] (.sort .zero) #[] (Lean.Kernel.Environment.empty `PrefixFixture) state).WF
      fun returned => returned.2 = state ∧ ∃ semantic, TrExprS VEnv.empty [] base.vlctx returned.1 semantic ∧
        VEnv.empty.HasType 0 base.vlctx.toCtx semantic (.sort (.succ .zero)) := by
  exact (replaceParams.prefix_typed ⟨[], .empty⟩ baseWellFormed ParameterPrefix.nil
    (sortTranslation _) (sortTyping _) TypedParameterArguments.nil rfl
    (Lean.Kernel.Environment.empty `PrefixFixture) state).mono fun returned receipts => by
      obtain ⟨unchanged, _, _, _, _, _, semantic, translated, typed, _⟩ := receipts
      exact ⟨unchanged, semantic, translated, typed⟩

private theorem singletonPrefixStillSuppliesTypehood (state : ElimNestedInductive.State) :
    (replaceParams #[.fvar targetType] (.fvar sourceType) #[.fvar sourceType]
      (Lean.Kernel.Environment.empty `PrefixFixture) state).WF
      fun returned => returned.2 = state ∧ ∃ semantic, TrExprS VEnv.empty [] base.vlctx returned.1 semantic ∧
        VEnv.empty.HasType 0 base.vlctx.toCtx semantic (.sort .zero) := by
  have firstWF : sourceFirst.WF VEnv.empty [] := sourceWellFormed.1
  have parameters : ParameterPrefix base sourceFirst [sourceType] := .snoc .nil
  have arguments : TypedParameterArguments VEnv.empty [] base
      (sourceFirst.mkForall' 1 parameters.bound (.sort .zero)) [.fvar targetType] [.bvar 1] (.sort .zero) :=
    .cons (.fvar rfl) (.bvar (.succ .zero)) .nil
  exact (replaceParams.prefix_typed ⟨[], .empty⟩ firstWF parameters
    (TrExprS.fvar (A := .sort .zero) rfl) (.bvar .zero) arguments rfl
    (Lean.Kernel.Environment.empty `PrefixFixture) state).mono fun returned receipts => by
      obtain ⟨unchanged, _, _, _, _, _, semantic, translated, typed, _⟩ := receipts
      exact ⟨unchanged, semantic, translated, typed⟩

private theorem prefixOrderAndRetainedBaseAreExact :
    source.fvarRevList identifiers.length actualPrefix.bound = [sourceValue, sourceType] ∧
    source.dropN identifiers.length actualPrefix.bound = base ∧
    identifiers.Nodup ∧ replacements.length = semantics.length :=
  ⟨actualPrefix.fvarRevList, actualPrefix.drop, actualPrefix.nodup sourceWellFormed, dependentArguments.length⟩

private def sourceThree : MLCtx :=
  .vlam sourceExtra `sourceExtra (.fvar sourceType) (.bvar 1) .default source

private def threeIdentifiers : List FVarId := [sourceType, sourceValue, sourceExtra]

private def threeBody : Expr :=
  .letE `firstProof (.fvar sourceType) (.fvar sourceValue)
    (.letE `secondProof (.fvar sourceType) (.fvar sourceExtra) (.fvar sourceType) true) true

private theorem sourceThreeWellFormed : sourceThree.WF VEnv.empty [] :=
  ⟨sourceWellFormed, sourceWellFormed.tr.find?_eq_none.mpr
    (by simp [source, sourceFirst, base, baseType, sourceExtra, sourceType, sourceValue, targetType, targetValue]),
    .fvar rfl, _, .bvar (.succ .zero)⟩

private theorem actualThreePrefix : ParameterPrefix base sourceThree threeIdentifiers :=
  .snoc actualPrefix

private theorem threeBodyTranslation : TrExprS VEnv.empty [] sourceThree.vlctx threeBody (.bvar 2) :=
  .letE (.bvar (.succ .zero)) (.fvar rfl) (.fvar rfl)
    (.letE (.bvar .zero) (.fvar rfl) (.fvar rfl) (.fvar rfl))

private theorem threeBodyTyping : VEnv.empty.HasType 0 sourceThree.vlctx.toCtx (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ .zero))

private theorem threeDependentArguments : TypedParameterArguments VEnv.empty [] base
    (sourceThree.mkForall' threeIdentifiers.length actualThreePrefix.bound (.sort .zero))
    [.fvar targetType, .fvar targetValue, betaReplacement] [.bvar 1, .bvar 0, betaSemantic] (.sort .zero) :=
  .cons (.fvar rfl) (.bvar (.succ .zero))
    (.cons (.fvar rfl) (.bvar .zero) (.cons betaTranslationAndTyping.1 betaTranslationAndTyping.2 .nil))

private theorem replaceAllThreeDependentParameters (state : ElimNestedInductive.State) :
    (replaceParams #[.fvar targetType, .fvar targetValue, betaReplacement] threeBody
      (threeIdentifiers.map Expr.fvar).toArray (Lean.Kernel.Environment.empty `PrefixFixture) state).WF
      fun returned => returned.2 = state ∧ Closed returned.1 0 ∧ returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧
        ∃ semantic, TrExprS VEnv.empty [] base.vlctx returned.1 semantic ∧
          VEnv.empty.HasType 0 base.vlctx.toCtx semantic (.sort .zero) ∧
          TrExprS VEnv.empty [] target.vlctx returned.1 (semantic.lift' (.skip (.skip .refl))) ∧
          VEnv.empty.HasType 0 target.vlctx.toCtx (semantic.lift' (.skip (.skip .refl))) (.sort .zero) := by
  exact (replaceParams.prefix_typedRebased ⟨[], .empty⟩ sourceThreeWellFormed actualThreePrefix
    threeBodyTranslation threeBodyTyping threeDependentArguments rfl targetWellFormed independentInsertion
    (Lean.Kernel.Environment.empty `PrefixFixture) state).mono fun returned receipts => by
      obtain ⟨unchanged, _, closed, _, support, semantic, translated, typed, _,
        targetTranslated, targetTyped, _⟩ := receipts
      exact ⟨unchanged, closed, support, semantic, translated, typed, targetTranslated, targetTyped⟩

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "prefix replacement unexpected axiom {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} inherited/native dependencies"

private def auditExact (name : Name) (expected : List Name) : MetaM Unit := do
  audit name expected
  let dependencies ← collectAxioms name
  for dependency in expected do
    unless dependencies.contains dependency do throwError "prefix replacement expected dependency {dependency} absent in {name}"

private def runtimeControls : MetaM Unit := do
  let environment := Lean.Kernel.Environment.empty `PrefixFixture
  let state : ElimNestedInductive.State :=
    { ngen := { namePrefix := `PrefixState, idx := 19 }, nextIdx := 91,
      nestedAux := #[(.sort .zero, `PreviouslyRecordedAux)], lvls := [.zero], newTypes := #[] }
  let .ok (returned, returnedState) := replaceParams replacements.toArray body
      (identifiers.map Expr.fvar).toArray environment state
    | throwError "dependent prefix replacement failed"
  let .ok (returnedBeta, _) := replaceParams #[.fvar targetType, betaReplacement] body
      (identifiers.map Expr.fvar).toArray environment state
    | throwError "nonliteral dependent prefix replacement failed"
  let .ok (wrongOrder, _) := replaceParams replacements.toArray body
      #[.fvar sourceValue, .fvar sourceType] environment state
    | throwError "wrong-order raw replacement failed"
  let .ok (wrongDomain, _) := replaceParams #[.fvar targetType, .sort .zero] body
      (identifiers.map Expr.fvar).toArray environment state
    | throwError "wrong-domain raw replacement failed"
  let .ok (returnedThree, _) := replaceParams #[.fvar targetType, .fvar targetValue, betaReplacement]
      threeBody (threeIdentifiers.map Expr.fvar).toArray environment state
    | throwError "three-parameter dependent replacement failed"
  let expected := Expr.forallE `formal (.fvar targetType)
    (.letE `proofUse (.fvar targetType) (.fvar targetValue) (.fvar targetType) true) .default
  let expectedBeta := Expr.forallE `formal (.fvar targetType)
    (.letE `proofUse (.fvar targetType) betaReplacement (.fvar targetType) true) .default
  let expectedThree := Expr.letE `firstProof (.fvar targetType) (.fvar targetValue)
    (.letE `secondProof (.fvar targetType) betaReplacement (.fvar targetType) true) true
  let reader : AddInductive.Context :=
    { env := environment, lparams := [], safety := .safe, allowPrimitive := false,
      lctx := base.lctx, fuel := { recDepth := 256 } }
  let hasExpectedSort (expression : Expr) (context : LocalContext) : Bool :=
    match ((monadLift (TypeChecker.checkType expression) : AddInductive.M Expr) { reader with lctx := context }) with
    | .ok (.sort .zero) => true
    | _ => false
  let isRejected (expression : Expr) : Bool :=
    match ((monadLift (TypeChecker.checkType expression) : AddInductive.M Expr) reader) with
    | .error _ => true
    | .ok _ => false
  let controls := [
    (sourceType != targetType && sourceValue != targetValue, "source/target IDs are distinct"),
    (identifiers.length == 2 && replacements.length == 2, "both actual prefixes have two entries"),
    ((source.lctx.find? sourceValue).map LocalDecl.type == some (.fvar sourceType), "second source domain depends on first"),
    (returned == expected, "native replacement uses chronological argument order under forall/let"),
    (returnedBeta == expectedBeta, "nonliteral second argument keeps the dependent let domain"),
    (returned == (body.abstractList identifiers).instantiateRevList replacements, "native reverse substitution matches the structural result"),
    (returned.looseBVarRange' == 0 && returnedBeta.looseBVarRange' == 0, "both native outputs are scoped"),
    (!returned.fvarsList.contains sourceType && !returned.fvarsList.contains sourceValue, "whole source prefix is removed"),
    (returned.fvarsList == [targetType, targetType, targetValue, targetType], "exact target support survives in the native let"),
    (returnedState.ngen.curr == state.ngen.curr && returnedState.nextIdx == state.nextIdx, "generator/counter state is unchanged"),
    (returnedState.nestedAux == state.nestedAux && returnedState.lvls == state.lvls, "remembered auxiliaries/levels are unchanged"),
    (hasExpectedSort body source.lctx, "the original dependent native body is type-valued"),
    (hasExpectedSort returned base.lctx, "the substituted body is type-valued in the retained base"),
    (hasExpectedSort returnedBeta base.lctx, "the nonliteral result is type-valued in the retained base"),
    (hasExpectedSort returned target.lctx && hasExpectedSort returnedBeta target.lctx, "both outputs survive independent two-declaration insertion"),
    (returnedThree == expectedThree, "all three dependent parameters are substituted in chronological order"),
    (hasExpectedSort threeBody sourceThree.lctx, "the three-parameter native source is type-valued"),
    (hasExpectedSort returnedThree base.lctx && hasExpectedSort returnedThree target.lctx,
      "the three-parameter result is type-valued in base and independent insertion"),
    (returnedThree.looseBVarRange' == 0 && returnedThree.fvarsList.all
      (fun identifier => identifier != sourceType && identifier != sourceValue && identifier != sourceExtra),
      "no selected source parameter escapes the three-parameter replacement"),
    (wrongOrder != returned && isRejected wrongOrder, "reversed source arrays are not a compatible substitution"),
    (isRejected wrongDomain, "a wrongly typed dependent second argument is rejected"),
    ((body.abstract (identifiers.map Expr.fvar).toArray).instantiate replacements.toArray != returned,
      "forward instantiation is not chronological reverse instantiation")]
  for (condition, label) in controls do
    unless condition do throwError "prefix replacement runtime failed: {label}"
  logInfo m!"prefix replacement runtime: {controls.length} dependent-domain, order, scope/support, state and native type-check controls"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let rawAllowed := logical ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq]
  let typedAllowed := rawAllowed ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  auditExact ``replaceParams.prefix_eq rawAllowed
  for name in [``replaceParams.prefix_typed, ``replaceParams.prefix_typedRebased,
      ``replaceTheWholeDependentPrefix, ``replaceWithANonliteralDependentArgument,
      ``emptyPrefixStillSuppliesTypehood, ``singletonPrefixStillSuppliesTypehood,
      ``replaceAllThreeDependentParameters] do auditExact name typedAllowed
  let fixtureControls := [``baseWellFormed, ``sourceWellFormed, ``targetWellFormed, ``actualPrefix, ``independentInsertion,
      ``bodyTranslation, ``bodyTyping, ``dependentArguments, ``nonliteralDependentArguments,
      ``replaceTheWholeDependentPrefix, ``replaceWithANonliteralDependentArgument,
      ``emptyPrefixStillSuppliesTypehood, ``singletonPrefixStillSuppliesTypehood,
      ``prefixOrderAndRetainedBaseAreExact, ``betaTranslationAndTyping,
      ``sourceThreeWellFormed, ``actualThreePrefix, ``threeBodyTranslation, ``threeBodyTyping,
      ``threeDependentArguments, ``replaceAllThreeDependentParameters]
  for name in fixtureControls do audit name typedAllowed
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterPrefixReplacement
    | throwError "prefix replacement module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "prefix replacement module-owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless typedAllowed.contains dependency do throwError "prefix module unexpected axiom {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveParameterPrefixReplacementTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless typedAllowed.contains dependency do throwError "prefix fixture unexpected axiom {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  unless moduleCount == 45 do throwError "prefix replacement module manifest changed: expected 45, got {moduleCount}"
  unless fixtureCount == 69 do throwError "prefix replacement fixture manifest changed: expected 69, got {fixtureCount}"
  logInfo m!"prefix replacement: {fixtureControls.length} fixture proof controls plus three exact production contracts; {moduleCount} module-owned and {fixtureCount} fixture-namespace declarations including generated helpers audited"
  runtimeControls

end InductiveParameterPrefixReplacementTest
