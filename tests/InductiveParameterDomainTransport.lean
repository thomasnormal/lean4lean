import Lean4Lean.Verify.InductiveParameterDomainTransport
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive
open Lean4Lean.TypeChecker (MLCtx)

namespace InductiveParameterDomainTransportTest

inductive IndexedContainer (proposition : Prop) : Nat → Prop where
  | intro : proposition → IndexedContainer proposition 0

private def sourceType : FVarId := ⟨`DomainSourceType⟩
private def sourceValue : FVarId := ⟨`DomainSourceValue⟩
private def targetType : FVarId := ⟨`DomainTargetType⟩
private def targetValue : FVarId := ⟨`DomainTargetValue⟩
private def betaDomain : Expr := .app (.lam `type (.sort (.succ .zero)) (.bvar 0) .default) (.sort .zero)
private def betaSemantic : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
private def sourceFirst : MLCtx := .vlam sourceType `type (.sort .zero) (.sort .zero) .default .nil
private def source : MLCtx := .vlam sourceValue `value (.fvar sourceType) (.bvar 0) .default sourceFirst
private def targetFirst : MLCtx := .vlam targetType `type betaDomain betaSemantic .default .nil
private def target : MLCtx := .vlam targetValue `value (.fvar targetType) (.bvar 0) .default targetFirst
private def sourceIdentifiers : List FVarId := [sourceType, sourceValue]
private def targetIdentifiers : List FVarId := [targetType, targetValue]

private theorem environmentWF : VEnv.empty.WF := ⟨[], .empty⟩

private theorem sortTyping (context : List VExpr) (level : VLevel) (valid : level.WF 0) :
    VEnv.empty.HasType 0 context (.sort level) (.sort (.succ level)) := .sortDF valid valid rfl

private theorem betaTranslation : TrExprS VEnv.empty [] [] betaDomain betaSemantic :=
  .app (.lam (sortTyping [] (.succ .zero) (by trivial)) (.bvar .zero))
    (sortTyping [] .zero (by trivial))
    (.lam ⟨_, sortTyping [] (.succ .zero) (by trivial)⟩ (.sort rfl) (.bvar rfl)) (.sort rfl)

private theorem betaEquality : VEnv.empty.IsDefEq 0 [] betaSemantic (.sort .zero) (.sort (.succ .zero)) :=
  .beta (.bvar .zero) (sortTyping [] .zero (by trivial))

private theorem sourceWellFormed : source.WF VEnv.empty [] := by
  have first : sourceFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      .sort rfl, _, sortTyping [] .zero (by trivial)⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [sourceFirst, sourceType, sourceValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem targetWellFormed : target.WF VEnv.empty [] := by
  have first : targetFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      betaTranslation, _, betaEquality.hasType.1⟩
  have converted : VEnv.empty.HasType 0 targetFirst.vlctx.toCtx (.bvar 0) (.sort .zero) := by
    have equality := betaEquality.weak environmentWF.ordered (B := betaSemantic)
    simpa [betaSemantic, VExpr.lift, VExpr.liftN] using VEnv.IsDefEq.defeqDF equality (VEnv.IsDefEq.bvar Lookup.zero)
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [targetFirst, targetType, targetValue]),
    .fvar rfl, _, converted⟩

private theorem sourcePrefix : ParameterPrefix .nil source sourceIdentifiers := .snoc (.snoc .nil)
private theorem targetPrefix : ParameterPrefix .nil target targetIdentifiers := .snoc (.snoc .nil)

private theorem equivalentDependentDomains :
    VEnv.empty.IsDefEqCtx 0 [] source.vlctx.toCtx target.vlctx.toCtx :=
  .succ (.succ .zero betaEquality.symm) (VEnv.HasType.bvar Lookup.zero)

private theorem unequalDependentDomains : source.vlctx.toCtx ≠ target.vlctx.toCtx := by
  simp [source, target, sourceFirst, targetFirst, betaSemantic, VLCtx.toCtx]

private def family : Expr := .lam `argument (.fvar sourceType) (.fvar sourceType) .default
private def familySemantic : VExpr := .lam (.bvar 1) (.bvar 2)
private def familyType : VExpr := .forallE (.bvar 1) (.sort .zero)

private theorem familyTranslation : TrExprS VEnv.empty [] source.vlctx family familySemantic :=
  .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl) (.fvar rfl)

private theorem familyTyping : VEnv.empty.HasType 0 source.vlctx.toCtx familySemantic familyType :=
  .lam (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))

private theorem convertedTelescope :
    ∃ level, VEnv.empty.IsDefEq 0 []
      (source.mkForall' 2 sourcePrefix.bound familyType)
      (target.mkForall' 2 targetPrefix.bound familyType) (.sort level) := by
  obtain ⟨_, typeTyped⟩ := familyTyping.isType environmentWF.ordered sourceWellFormed.tr.wf.toCtx
  exact sourcePrefix.forall_defeq targetPrefix rfl equivalentDependentDomains typeTyped

private theorem typedNonliteralFamily (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (replaceParams (targetIdentifiers.map Expr.fvar).toArray family
      (sourceIdentifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧ Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS VEnv.empty [] target.vlctx returned.1 resultSemantic ∧
          VEnv.empty.HasType 0 target.vlctx.toCtx resultSemantic familyType :=
  (replaceParams.prefix_rename_defeq_typed environmentWF sourceWellFormed targetWellFormed
    sourcePrefix targetPrefix rfl equivalentDependentDomains familyTranslation familyTyping nativeEnv state).mono
      fun _ ⟨unchanged, _, closed, range, support, resultSemantic, translated, typed⟩ =>
        ⟨unchanged, closed, range, support, resultSemantic, translated, typed⟩

private theorem acceptedCheckExtendsContext
    {context : TypeChecker.VContext} {initial : TypeChecker.VState} {final : TypeChecker.State}
    {base target : List VExpr} {sourceDomain targetDomain : Expr}
    {sourceSemantic targetSemantic : VExpr} {level : VLevel}
    (contexts : context.venv.IsDefEqCtx context.lparams.length base context.vlctx.toCtx target)
    (sourceTranslated : context.TrExprS sourceDomain sourceSemantic)
    (targetTranslated : context.TrExprS targetDomain targetSemantic)
    (sourceTyped : context.HasType sourceSemantic (.sort level))
    (initialWF : initial.WF context)
    (accepted : TypeChecker.isDefEq sourceDomain targetDomain context.toContext initial.toState = .ok (true, final)) :
    context.venv.IsDefEqCtx context.lparams.length base
      (sourceSemantic :: context.vlctx.toCtx) (targetSemantic :: target) :=
  TypeChecker.isDefEq.acceptedParameterContextStep contexts sourceTranslated targetTranslated sourceTyped initialWF accepted

private theorem acceptedEmptyCheckCreatesContext
    (accepted : TypeChecker.M.run (Kernel.Environment.empty `DomainTransportFixture) .safe {} [] {}
      (TypeChecker.isDefEq (.sort .zero) betaDomain) = .ok true) :
    VEnv.empty.IsDefEqCtx 0 [] [.sort .zero] [betaSemantic] := by
  let nativeWF := VEnvs.WF.empty `DomainTransportFixture
  let context := TypeChecker.VContext.mk' nativeWF .safe [] {}
  have nativeAccepted : (Prod.fst <$> TypeChecker.isDefEq (.sort .zero) betaDomain
      context.toContext ({} : TypeChecker.VState).toState) = .ok true := accepted
  generalize checkEq : TypeChecker.isDefEq (.sort .zero) betaDomain
      context.toContext ({} : TypeChecker.VState).toState = result at nativeAccepted
  cases result with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨result, final⟩ := returned
    change Except.ok result = .ok true at nativeAccepted
    cases nativeAccepted
    exact TypeChecker.isDefEq.acceptedParameterContextStep (context := context) (.zero)
      (.sort rfl) betaTranslation (sortTyping [] .zero (by trivial)) TypeChecker.VState.WF.empty checkEq

private theorem convertedBodyTelescope :
    ∃ level, VEnv.empty.IsDefEq 0 []
      (sourceFirst.mkForall' 1 (by decide) (.bvar 0))
      (targetFirst.mkForall' 1 (by decide) (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))) (.sort level) := by
  have sourcePrefix : ParameterPrefix .nil sourceFirst [sourceType] := .snoc .nil
  have targetPrefix : ParameterPrefix .nil targetFirst [targetType] := .snoc .nil
  have bodyEquality : VEnv.empty.IsDefEq 0 sourceFirst.vlctx.toCtx (.bvar 0)
      (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.sort .zero) :=
    (VEnv.IsDefEq.beta (VEnv.HasType.bvar Lookup.zero) (VEnv.HasType.bvar Lookup.zero)).symm
  exact sourcePrefix.forall_defeq (universes := []) targetPrefix rfl (.succ .zero betaEquality.symm) bodyEquality

private theorem retainedBaseTransport
    {env : VEnv} {universes : List Name} {base : MLCtx} {body targetBody : VExpr} {level : VLevel}
    (equality : env.IsDefEq universes.length base.vlctx.toCtx body targetBody (.sort level)) :
    ∃ resultLevel, env.IsDefEq universes.length base.vlctx.toCtx
      (base.mkForall' 0 (by omega) body) (base.mkForall' 0 (by omega) targetBody) (.sort resultLevel) :=
  (ParameterPrefix.nil (base := base)).forall_defeq .nil rfl .zero equality

private theorem retainedBaseLength (base : MLCtx) : base.vlctx.toCtx.length = 0 + base.vlctx.toCtx.length :=
  (ParameterPrefix.nil (base := base)).toCtx_length

private def sourceTelescope : Expr :=
  .forallE `type (.sort .zero) (.forallE `value (.bvar 0) (.sort .zero) .default) .default
private def targetTelescope : Expr :=
  .forallE `type betaDomain (.forallE `value (.bvar 0) (.sort .zero) .default) .default

private def checkedType (nativeEnv : Kernel.Environment) (lctx : LocalContext) (expression : Expr) :
    Except Kernel.Exception Expr :=
  (monadLift (TypeChecker.checkType expression) : AddInductive.M Expr)
    { env := nativeEnv, lctx, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }

private def checkedEquality (nativeEnv : Kernel.Environment) (lctx : LocalContext) (first second : Expr) :
    Except Kernel.Exception Bool :=
  (monadLift (TypeChecker.isDefEq first second) : AddInductive.M Bool)
    { env := nativeEnv, lctx, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }

private def runtimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let mut checks := 0
  let .ok true := checkedEquality nativeEnv {} (.sort .zero) betaDomain
    | throwError "the actual checker did not accept beta-equivalent domains"
  unless (.sort .zero : Expr) != betaDomain do throwError "nonliteral domains accidentally coincide"
  checks := checks + 2
  let sourceName := `AcceptedDomainSource
  let constructorType := Expr.forallE `type betaDomain
    (.forallE `value (.bvar 0) (mkApp2 (.const sourceName []) (.bvar 1) (.bvar 0)) .default) .default
  let types : Array InductiveType :=
    #[{ name := sourceName, type := sourceTelescope, ctors := [{ name := `AcceptedDomainSource.mk, type := constructorType }] },
      { name := `AcceptedDomainTarget, type := targetTelescope, ctors := [] }]
  let reader : AddInductive.Context :=
    { env := nativeEnv, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }
  let .ok stats := (AddInductive.checkInductiveTypes 2 types (fun stats => do
      let staged ← AddInductive.declareInductiveTypes stats 2 types 0 false
      AddInductive.withEnv staged do
        AddInductive.checkConstructors types stats false
        pure stats) reader)
    | throwError "actual header/constructor checks rejected nonliteral matching parameter domains"
  unless stats.params.size == 2 && stats.nindices == #[0, 0] do
    throwError "actual accepted checks changed parameter or index counts"
  unless constructorType.bindingDomain! != sourceTelescope.bindingDomain! do
    throwError "constructor/header domain acceptance collapsed to literal equality"
  checks := checks + 3
  let incompatible : InductiveType :=
    { name := `RejectedDomainTarget,
      type := .forallE `type (.sort (.succ .zero))
        (.forallE `value (.bvar 0) (.sort .zero) .default) .default,
      ctors := [] }
  match AddInductive.checkInductiveTypes 2 #[types[0]!, incompatible] (fun _ => pure ()) reader with
  | .error _ => checks := checks + 1
  | .ok _ => throwError "actual header checks accepted incompatible parameter universes"
  for sourceIndex in [0, 13] do
    for targetIndex in [0, 29] do
      let initial : ElimNestedInductive.State :=
        { ngen := { namePrefix := `ActualDomainSource, idx := sourceIndex }, newTypes := #[], lvls := [] }
      let targetInitial := { initial with ngen := { namePrefix := `ActualDomainTarget, idx := targetIndex } }
      let .ok ((sourceContext, _, sourceParams), sourceState) := withParams sourceTelescope 2
          (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv initial
        | throwError "actual source opening failed"
      let .ok ((targetContext, _, targetParams), _) := withParams targetTelescope 2
          (fun lctx remainder params => pure (lctx, remainder, params)) nativeEnv targetInitial
        | throwError "actual beta-domain target opening failed"
      let some sourceDecl := sourceContext.findFVar? sourceParams[0]! | throwError "source parameter absent"
      let some targetDecl := targetContext.findFVar? targetParams[0]! | throwError "target parameter absent"
      unless sourceDecl.type != targetDecl.type && sourceParams != targetParams do
        throwError "the actual domain contexts or independent IDs accidentally coincide"
      checks := checks + 1
      let body := Expr.lam `argument sourceParams[0]! sourceParams[0]! .default
      let .ok sourceFamilyType := checkedType nativeEnv sourceContext body | throwError "source family untyped"
      let .ok (rebound, reboundState) := replaceParams targetParams body sourceParams nativeEnv sourceState
        | throwError "nonliteral-domain family rebinding failed"
      let .ok targetFamilyType := checkedType nativeEnv targetContext rebound | throwError "target family untyped"
      unless sourceFamilyType.isForall && targetFamilyType.isForall &&
          rebound == .lam `argument targetParams[0]! targetParams[0]! .default &&
          reboundState.ngen.idx == sourceState.ngen.idx && !rebound.hasLooseBVars do
        throwError "non-sort family lost its type, syntax, scope or state"
      checks := checks + 4
      let sourceDependentType := sourceContext.get! sourceParams[1]!.fvarId! |>.type
      let renamedDependentType := sourceDependentType.abstract sourceParams |>.instantiateRev targetParams
      let .ok true := checkedEquality nativeEnv targetContext renamedDependentType
          (targetContext.get! targetParams[1]!.fvarId!).type
        | throwError "the actual dependent second domains do not agree after parameter renaming"
      checks := checks + 1
      let parameter := mkApp2 (.const ``And []) sourceParams[0]! (.const ``True [])
      let nested := mkApp2 (.const ``IndexedContainer []) parameter (.const ``Nat.zero [])
      let nestedState := { sourceState with newTypes := #[{ name := ``And, type := .sort .zero, ctors := [] }] }
      let .ok (some info, classified) := isNestedInductiveApp? nested nativeEnv nestedState
        | throwError "actual nested application not selected"
      let selected := mkAppRange nested.getAppFn 0 info.numParams nested.getAppArgs
      let .ok selectedType := checkedType nativeEnv sourceContext selected | throwError "selected family untyped"
      let .ok (renamed, _) := replaceParams targetParams selected sourceParams nativeEnv classified
        | throwError "selected nested prefix rebinding failed"
      let .ok renamedType := checkedType nativeEnv targetContext renamed | throwError "renamed nested family untyped"
      unless info.numParams == 1 && selectedType.isForall && renamedType.isForall && !renamed.hasLooseBVars do
        throwError "nested prefix included an index or lost non-sort typing"
      checks := checks + 5
      let .ok (reversed, _) := replaceParams targetParams.reverse body sourceParams nativeEnv sourceState
        | throwError "reversed parameter control failed to execute"
      match checkedType nativeEnv targetContext reversed with
      | .error _ => checks := checks + 1
      | .ok _ => throwError "reversed dependent parameters incorrectly accepted"
  match checkedEquality nativeEnv {} (.sort .zero) (.sort (.succ .zero)) with
  | .ok false => checks := checks + 1
  | _ => throwError "unequal universe domains incorrectly accepted"
  unless checks == 55 do throwError "domain transport runtime manifest changed: {checks}"
  logInfo m!"domain transport runtime: {checks} beta-equivalent, independent, dependent, non-sort, nested and negative controls"

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "domain transport unexpected dependency {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} dependencies = {repr dependencies}"

private def auditExact (name : Name) (expected : List Name) : MetaM Unit := do
  audit name expected
  let dependencies ← collectAxioms name
  unless dependencies.size == expected.length do
    throwError "domain transport exact dependency count changed for {name}: {dependencies.size}"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let replacement := inherited ++ [``Expr.abstract_eq, ``Expr.instantiateRev_eq, ``Expr.instantiate_eq]
  let native := replacement ++ [`Lean.Expr.mkAppRangeAux.eq_def]
  let checker := native ++ [``Expr.eqv_eq, ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq,
    ``Lean4Lean.ptrEqExpr_eq, ``Expr.looseBVarRange_eq, ``PersistentHashMap.findAux_isSome,
    ``Expr.replace_eq, ``Level.hasParam_eq, ``Expr.hasLevelParam_eq, ``Level.hasMVar_eq,
    ``Lean4Lean.ptrEqConstantInfo_eq, ``Expr.instantiateRange_eq, ``Expr.instantiate1_eq,
    ``Expr.abstractRange_eq, ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``Expr.instantiateRevRange_eq]
  let allowed := checker
  for name in [``ParameterPrefix.toCtx_length, ``ParameterPrefix.forall_defeq,
      ``unequalDependentDomains, ``equivalentDependentDomains, ``betaEquality, ``retainedBaseLength,
      ``convertedBodyTelescope, ``retainedBaseTransport] do
    audit name logical
  for name in [``replaceParams.prefix_typedInto_defeq, ``replaceParams.prefix_rename_defeq_typed,
      ``isNestedInductiveApp?.defeqTypedRebinding, ``TypeChecker.isDefEq.acceptedParameterDomain,
      ``TypeChecker.isDefEq.acceptedParameterContextStep, ``sourceWellFormed, ``targetWellFormed,
      ``familyTranslation, ``familyTyping, ``convertedTelescope, ``typedNonliteralFamily,
      ``acceptedCheckExtendsContext, ``acceptedEmptyCheckCreatesContext] do audit name allowed
  auditExact ``ParameterPrefix.toCtx_length [``propext]
  auditExact ``ParameterPrefix.forall_defeq logical
  for name in [``replaceParams.prefix_typedInto_defeq, ``replaceParams.prefix_rename_defeq_typed,
      ``typedNonliteralFamily] do auditExact name replacement
  auditExact ``isNestedInductiveApp?.defeqTypedRebinding native
  for name in [``TypeChecker.isDefEq.WF, ``TypeChecker.isDefEq.acceptedParameterDomain,
      ``TypeChecker.isDefEq.acceptedParameterContextStep, ``acceptedCheckExtendsContext,
      ``acceptedEmptyCheckCreatesContext] do auditExact name checker
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterDomainTransport
    | throwError "domain transport module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new domain transport axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveParameterDomainTransportTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"domain transport exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 13 do throwError "domain transport module manifest changed: {moduleCount}"
  unless fixtureCount == 71 do throwError "domain transport fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveParameterDomainTransportTest
