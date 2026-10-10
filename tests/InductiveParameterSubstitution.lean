import Lean4Lean.Verify.InductiveParameterSubstitution
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterSubstitutionTest

private theorem coreProjectsTheDependentValueAndTypeCongruences
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic resultType : VExpr}
    (translated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic resultType)
    (supported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ argument argumentType level,
      source.find? (.inr identifier) = some (argument, argumentType) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (bodySemantic.inst (argument.lift' lift))
        (resultType.inst originalArgument) ∧
      env.IsDefEq universes.length original.toCtx
        (resultType.inst originalArgument) (resultType.inst (argument.lift' lift)) (.sort level) := by
  obtain ⟨argument, argumentType, level, lookup, _, _, _, _, _, _, valueEquality, typeEquality⟩ :=
    receipt.instantiateCore envWF originalWF position identifier selected originalLookup
      translated typed supported
  exact ⟨argument, argumentType, level, lookup, valueEquality, typeEquality⟩

private theorem nativeProjectsSupportedTranslationAndTyping
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic resultType : VExpr}
    (translated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic resultType)
    (supported : body.FVarsIn (· ∈ source.fvars)) :
    (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length original.toCtx
        (bodySemantic.inst originalArgument) (resultType.inst originalArgument) := by
  obtain ⟨_, _, _, _, _, _, support, translation, typing, _, _, _⟩ :=
    receipt.instantiate envWF originalWF position identifier selected originalLookup
      translated typed supported
  exact ⟨support, translation, typing⟩

private def carrier : FVarId := ⟨`ParameterSubstitutionCarrier⟩
private def aliasIdentifier : FVarId := ⟨`ParameterSubstitutionAlias⟩
private def insertedOne : FVarId := ⟨`ParameterSubstitutionInsertedOne⟩
private def insertedTwo : FVarId := ⟨`ParameterSubstitutionInsertedTwo⟩
private def insertedThree : FVarId := ⟨`ParameterSubstitutionInsertedThree⟩
private def selectedIdentifier : FVarId := ⟨`ParameterSubstitutionSelected⟩
private def absentIdentifier : FVarId := ⟨`ParameterSubstitutionAbsent⟩
private def parameterType : VExpr := .sort (.succ .zero)
private def betaValue : VExpr := .app (.lam parameterType (.bvar 0)) (.bvar 0)

private def sourceContext : VLCtx :=
  [(some (aliasIdentifier, [carrier]), .vlet parameterType (.bvar 0)),
    (some (carrier, []), .vlam parameterType)]

private def originalContext : VLCtx :=
  [(some (aliasIdentifier, [carrier]), .vlet parameterType betaValue),
    (some (carrier, []), .vlam parameterType)]

private def insertLambda (identifier : FVarId) (context : VLCtx) : VLCtx :=
  (some (identifier, []), .vlam (.sort .zero)) :: context

private def insertThree (context : VLCtx) : VLCtx :=
  insertLambda insertedThree (insertLambda insertedTwo (insertLambda insertedOne context))

private theorem contextsAgreeByNonLiteralBeta (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes originalContext sourceContext := by
  apply VLCtx.IsDefEq.cons
  · apply VLCtx.IsDefEq.cons .nil
    · rintro identifier dependencies equality
      cases equality
      simp [VLCtx.fvars]
    · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, carrier, aliasIdentifier]
  · exact .vlet (.beta (.bvar .zero) (.bvar .zero)) (.sortDF (by trivial) (by trivial) rfl)

private theorem insertionPreservesContextAgreement
    {env : VEnv} {universes : Nat} {original aligned : VLCtx}
    (contexts : VLCtx.IsDefEq env universes original aligned)
    (identifier : FVarId) (fresh : identifier ∉ original.fvars) :
    VLCtx.IsDefEq env universes (insertLambda identifier original) (insertLambda identifier aligned) := by
  apply VLCtx.IsDefEq.cons contexts
  · rintro selected dependencies equality
    cases equality
    exact ⟨fresh, by simp⟩
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem oneInsertedContextsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertLambda insertedOne originalContext)
      (insertLambda insertedOne sourceContext) :=
  insertionPreservesContextAgreement (contextsAgreeByNonLiteralBeta env universes) insertedOne (by decide)

private theorem threeInsertedContextsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertThree originalContext) (insertThree sourceContext) := by
  apply insertionPreservesContextAgreement
  · apply insertionPreservesContextAgreement
    · exact oneInsertedContextsAgree env universes
    · decide
  · decide

private theorem oneInsertedWeakening :
    VLCtx.FVLift' sourceContext (insertLambda insertedOne sourceContext) 0 (.skip .refl) 0 :=
  .skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl

private theorem threeInsertedWeakening :
    VLCtx.FVLift' sourceContext (insertThree sourceContext) 0 (.skipN .refl 3) 0 :=
  .skip_fvar (insertedThree, []) (.vlam (.sort .zero))
    (.skip_fvar (insertedTwo, []) (.vlam (.sort .zero))
      (.skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl))

private def nestedBody : Expr :=
  .lam `outer (.bvar 0) (.lam `inner (.bvar 1) (.bvar 1) .default) .default

private def nestedSemantic : VExpr := .lam (.bvar 0) (.lam (.bvar 1) (.bvar 1))
private def nestedType : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))

private theorem nestedBodyTranslated (env : VEnv) (universes : List Name) (context : VLCtx) :
    TrExprS env universes ((none, .vlam parameterType) :: context) nestedBody nestedSemantic := by
  apply TrExprS.lam
  · exact ⟨.succ .zero, .bvar .zero⟩
  · exact .bvar rfl
  · apply TrExprS.lam
    · exact ⟨.succ .zero, .bvar (.succ .zero)⟩
    · exact .bvar rfl
    · exact .bvar rfl

private theorem nestedBodyTyped (env : VEnv) (universes : Nat) (context : List VExpr) :
    env.HasType universes (parameterType :: context) nestedSemantic nestedType :=
  .lam (.bvar .zero) (.lam (.bvar (.succ .zero)) (.bvar (.succ .zero)))

private def NestedOutcome (env : VEnv) (universes : List Name) (source original : VLCtx)
    (originalArgument reducedArgument : VExpr) : Prop :=
  ∃ level,
    (nestedBody.instantiate1' (.fvar aliasIdentifier)).FVarsIn (· ∈ source.fvars) ∧
    TrExprS env universes original (nestedBody.instantiate1' (.fvar aliasIdentifier))
      (nestedSemantic.inst originalArgument) ∧
    env.HasType universes.length original.toCtx
      (nestedSemantic.inst originalArgument) (nestedType.inst originalArgument) ∧
    env.HasType universes.length original.toCtx
      (nestedSemantic.inst reducedArgument) (nestedType.inst reducedArgument) ∧
    env.IsDefEq universes.length original.toCtx
      (nestedSemantic.inst originalArgument) (nestedSemantic.inst reducedArgument)
      (nestedType.inst originalArgument) ∧
    env.IsDefEq universes.length original.toCtx
      (nestedType.inst originalArgument) (nestedType.inst reducedArgument) (.sort level)

private theorem agreementSubstitutesTheDependentNestedBody
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx} {lift : Lift}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift [carrier, aliasIdentifier])
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    {originalArgument reducedArgument : VExpr}
    (originalLookup : original.find? (.inr aliasIdentifier) = some (originalArgument, parameterType))
    (sourceLookup : source.find? (.inr aliasIdentifier) = some (reducedArgument, parameterType)) :
    NestedOutcome env universes source original originalArgument (reducedArgument.lift' lift) := by
  obtain ⟨argument, argumentType, level, lookup, _, _, support, translation, typing,
    reducedTyping, valueEquality, typeEquality⟩ :=
    receipt.instantiateCore envWF originalWF 1 aliasIdentifier rfl originalLookup
      (nestedBodyTranslated env universes original)
      (nestedBodyTyped env universes.length original.toCtx) (by simp [nestedBody, FVarsIn])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lookup.symm.trans sourceLookup))
  exact ⟨level, support, translation, typing, reducedTyping, valueEquality, typeEquality⟩

private theorem zeroInsertionSubstitutesNonLiteralBeta
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    NestedOutcome env universes sourceContext originalContext betaValue (.bvar 0) := by
  have contexts := contextsAgreeByNonLiteralBeta env universes.length
  have sourceWF := (contexts.symm envWF.ordered).wf
  have receipt := ((VLCtx.FVLift'.refl (Δ := sourceContext)).retainedPrefix envWF sourceWF
    sourceWF (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simpa [sourceContext, VLCtx.fvars, or_comm] using member)).agreesWithOriginal
      envWF contexts
  exact agreementSubstitutesTheDependentNestedBody receipt envWF contexts.wf rfl rfl

private theorem oneInsertionSubstitutesNonLiteralBeta
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    NestedOutcome env universes sourceContext (insertLambda insertedOne originalContext)
      (betaValue.lift' (.skip .refl)) (.bvar 1) := by
  have contexts := oneInsertedContextsAgree env universes.length
  have sourceWF := (contextsAgreeByNonLiteralBeta env universes.length).symm envWF.ordered
  have alignedWF := (contexts.symm envWF.ordered).wf
  have receipt := (oneInsertedWeakening.retainedPrefix envWF sourceWF.wf alignedWF
    (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simpa [sourceContext, VLCtx.fvars, or_comm] using member)).agreesWithOriginal
      envWF contexts
  exact agreementSubstitutesTheDependentNestedBody receipt envWF contexts.wf rfl rfl

private theorem threeInsertionsSubstituteNonLiteralBeta
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    NestedOutcome env universes sourceContext (insertThree originalContext)
      (betaValue.lift' (.skipN .refl 3)) (.bvar 3) := by
  have contexts := threeInsertedContextsAgree env universes.length
  have sourceWF := (contextsAgreeByNonLiteralBeta env universes.length).symm envWF.ordered
  have alignedWF := (contexts.symm envWF.ordered).wf
  have receipt := (threeInsertedWeakening.retainedPrefix envWF sourceWF.wf alignedWF
    (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simpa [sourceContext, VLCtx.fvars, or_comm] using member)).agreesWithOriginal
      envWF contexts
  exact agreementSubstitutesTheDependentNestedBody receipt envWF contexts.wf rfl rfl

private def selectedSource : VLCtx :=
  (some (selectedIdentifier, []), .vlam (.sort .zero)) :: sourceContext

private def selectedOriginal : VLCtx :=
  (some (selectedIdentifier, []), .vlam (.sort .zero)) :: insertLambda insertedOne originalContext

private def selectedAligned : VLCtx :=
  (some (selectedIdentifier, []), .vlam (.sort .zero)) :: insertLambda insertedOne sourceContext

private theorem selectedEndpointsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes selectedOriginal selectedAligned :=
  insertionPreservesContextAgreement (oneInsertedContextsAgree env universes) selectedIdentifier (by decide)

private theorem selectedEndpointWeakening :
    VLCtx.FVLift' selectedSource selectedAligned 0 (.consN (.skip .refl) 1) 0 :=
  .cons_fvar (selectedIdentifier, []) (.vlam (.sort .zero)) (by simp) oneInsertedWeakening

private theorem selectedEndpointSubstitutionUsesTheRetainedCutoff
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    NestedOutcome env universes selectedSource selectedOriginal
      (betaValue.lift' (.skipN .refl 2)) (.bvar 2) := by
  have contexts := selectedEndpointsAgree env universes.length
  have alignedWF := (contexts.symm envWF.ordered).wf
  have sourceWF := selectedEndpointWeakening.wf envWF alignedWF
  have receipt := (selectedEndpointWeakening.retainedPrefix envWF sourceWF alignedWF
    (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simp [selectedSource, sourceContext, VLCtx.fvars] at member ⊢
        grind)).agreesWithOriginal envWF contexts
  exact agreementSubstitutesTheDependentNestedBody receipt envWF contexts.wf rfl rfl

private theorem nestedNativeSubstitutionPreservesBothBinders :
    nestedBody.instantiate1' (.fvar aliasIdentifier) =
      .lam `outer (.fvar aliasIdentifier)
        (.lam `inner (.fvar aliasIdentifier) (.bvar 1) .default) .default := rfl

private theorem nestedSemanticSubstitutionRaisesTheArgumentUnderBinders :
    nestedSemantic.inst (.bvar 2) = .lam (.bvar 2) (.lam (.bvar 3) (.bvar 1)) ∧
      nestedType.inst (.bvar 2) = .forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4)) := ⟨rfl, rfl⟩

private theorem originalBetaIsNotItsReducedArgument : betaValue ≠ .bvar 0 := by
  intro equality
  cases equality

private theorem omittedParameterCannotProvideSubstitutionAgreement
    {env : VEnv} {universes : List Name} {original aligned : VLCtx} {lift : Lift} :
    ¬ RetainedFVarPrefixAgreement env universes [] original aligned lift [aliasIdentifier] := by
  intro receipt
  have member : aliasIdentifier ∈ VLCtx.fvars [] := receipt.transported.sourceRetained (by simp)
  simp at member

private theorem unsupportedBodyFailsItsPremise :
    ¬ (Expr.app nestedBody (.fvar absentIdentifier)).FVarsIn (· ∈ sourceContext.fvars) := by
  simp [nestedBody, FVarsIn, sourceContext, VLCtx.fvars, absentIdentifier, carrier, aliasIdentifier]

private theorem wrongRequestedPositionCannotSelectTheParameter :
    [carrier, aliasIdentifier][0]? ≠ some aliasIdentifier ∧
      [carrier, aliasIdentifier][2]? = none := by simp [carrier, aliasIdentifier]

private theorem droppedOriginalContextCannotProvideAgreement
    {env : VEnv} {universes : List Name} {aligned : VLCtx} {lift : Lift} :
    ¬ RetainedFVarPrefixAgreement env universes sourceContext [] aligned lift [aliasIdentifier] := by
  intro receipt
  have member : aliasIdentifier ∈ VLCtx.fvars [] := receipt.originalRetained (by simp)
  simp at member

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .const _ _ => [2]
  | .app function argument => [3] ++ semanticShape function ++ semanticShape argument
  | .lam type body => [4] ++ semanticShape type ++ semanticShape body
  | .forallE type body => [5] ++ semanticShape type ++ semanticShape body

private def runtimeSubstitutions : MetaM Unit := do
  let expectedNative := Expr.lam `outer (.fvar aliasIdentifier)
    (.lam `inner (.fvar aliasIdentifier) (.bvar 1) .default) .default
  for (source, original, aligned, lift, expectedPosition) in
      [(sourceContext, originalContext, sourceContext, Lift.refl, 0),
        (sourceContext, insertLambda insertedOne originalContext,
          insertLambda insertedOne sourceContext, Lift.skip .refl, 1),
        (sourceContext, insertThree originalContext, insertThree sourceContext, Lift.skipN .refl 3, 3),
        (selectedSource, selectedOriginal, selectedAligned, Lift.consN (.skip .refl) 1, 2)] do
    let some (sourceArgument, _) := source.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution source argument absent"
    let some (originalArgument, _) := original.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution original argument absent"
    let some (alignedArgument, _) := aligned.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution aligned argument absent"
    let liftedArgument := sourceArgument.lift' lift
    unless semanticShape liftedArgument == semanticShape alignedArgument do
      throwError "parameter-substitution source lift differs from aligned lookup"
    unless semanticShape alignedArgument == [0, expectedPosition] do
      throwError "parameter-substitution aligned lookup lost its selected binder cutoff"
    unless semanticShape originalArgument != semanticShape liftedArgument do
      throwError "parameter-substitution original beta unexpectedly became literal equality"
    let core := nestedBody.instantiate1' (.fvar aliasIdentifier)
    let native := nestedBody.instantiate1 (.fvar aliasIdentifier)
    unless core == expectedNative && native == expectedNative do
      throwError "parameter-substitution native/core replacement captured a nested bound variable"
    for argument in [originalArgument, liftedArgument] do
      let expectedBody := VExpr.lam argument (.lam argument.lift (.bvar 1))
      let expectedType := VExpr.forallE argument (.forallE argument.lift (argument.liftN 2))
      unless semanticShape (nestedSemantic.inst argument) == semanticShape expectedBody do
        throwError "parameter-substitution dependent lambda body shifted the argument incorrectly"
      unless semanticShape (nestedType.inst argument) == semanticShape expectedType do
        throwError "parameter-substitution dependent result type shifted the argument incorrectly"
  logInfo "parameter-substitution runtime: 36 lookup/substitution checks across zero/one/three inserts and selected consN endpoint; original beta and lifted reduced arguments; both nested binder cutoffs"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-substitution declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "parameter-substitution unexpected axiom {axiomName} in {name}"

private def auditModule (coreAllowed nativeAllowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterSubstitution
    | throwError "parameter-substitution module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-substitution module-owned axiom {name}"
      let allowed := if name == ``RetainedFVarPrefixAgreement.instantiate then nativeAllowed else coreAllowed
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"parameter-substitution module: {declarations} declarations audited; core forbids all native/container/range/abstraction interfaces"

private def rejectedNativeInterface (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.instantiate1_eq (logical ++ [``sorryAx])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "parameter-substitution core audit accepted native instantiation"
  match exception with
  | .error _ message =>
    let expected := m!"parameter-substitution unexpected axiom {``Expr.instantiate1_eq} in {``Expr.instantiate1_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let nativeAllowed := inherited ++ [``Expr.instantiate1_eq]
  for name in [``coreProjectsTheDependentValueAndTypeCongruences, ``nestedBodyTranslated,
      ``agreementSubstitutesTheDependentNestedBody, ``zeroInsertionSubstitutesNonLiteralBeta,
      ``oneInsertionSubstitutesNonLiteralBeta, ``threeInsertionsSubstituteNonLiteralBeta,
      ``selectedEndpointSubstitutionUsesTheRetainedCutoff,
      ``omittedParameterCannotProvideSubstitutionAgreement,
      ``droppedOriginalContextCannotProvideAgreement] do
    auditDeclaration name inherited
  auditDeclaration ``nativeProjectsSupportedTranslationAndTyping nativeAllowed
  for name in [``contextsAgreeByNonLiteralBeta, ``insertionPreservesContextAgreement,
      ``oneInsertedContextsAgree, ``threeInsertedContextsAgree, ``oneInsertedWeakening,
      ``threeInsertedWeakening, ``nestedBodyTyped,
      ``selectedEndpointsAgree, ``selectedEndpointWeakening,
      ``nestedNativeSubstitutionPreservesBothBinders,
      ``nestedSemanticSubstitutionRaisesTheArgumentUnderBinders,
      ``originalBetaIsNotItsReducedArgument,
      ``unsupportedBodyFailsItsPremise, ``wrongRequestedPositionCannotSelectTheParameter] do
    auditDeclaration name logical
  auditModule inherited nativeAllowed
  rejectedNativeInterface logical
  runtimeSubstitutions
  logInfo "parameter-substitution tests: 24 proof controls; generic core/native projections; nonliteral beta arguments; dependent nested lambda bodies/types; zero/one/three insertions; selected consN cutoff; omitted/dropped/unsupported/wrong-position negatives"

end InductiveParameterSubstitutionTest
