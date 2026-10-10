import Lean4Lean.Verify.InductiveParameterSubstitutionChain
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterSubstitutionPairTest

private theorem coreProjectsInnerEqualityAndFinalOuterAgreements
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0) (targetWF : target.WF env universes.length)
    (outerPosition : Nat) (outerIdentifier : FVarId) (outerSelected : identifiers[outerPosition]? = some outerIdentifier)
    (innerPosition : Nat) (innerIdentifier : FVarId) (innerSelected : identifiers[innerPosition]? = some innerIdentifier)
    {originalOuterArgument originalOuterArgumentType originalInnerArgument originalInnerArgumentType : VExpr}
    (outerLookup : original.find? (.inr outerIdentifier) = some (originalOuterArgument, originalOuterArgumentType))
    (innerLookup : original.find? (.inr innerIdentifier) = some (originalInnerArgument, originalInnerArgumentType))
    {innerDomain : VExpr}
    (raisedInnerArgumentTyped : env.HasType universes.length
      (originalOuterArgumentType :: original.toCtx) originalInnerArgument.lift innerDomain)
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes
      ((none, .vlam innerDomain) :: (none, .vlam originalOuterArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 2) (supported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ (innerArgument innerType outerArgument outerType semantic : VExpr),
      source.find? (.inr innerIdentifier) = some (innerArgument, innerType) ∧
      source.find? (.inr outerIdentifier) = some (outerArgument, outerType) ∧
      env.IsDefEq universes.length original.toCtx originalInnerArgument
        (innerArgument.lift' removalLift) originalInnerArgumentType ∧
      TrExprS env universes ((none, .vlam originalOuterArgumentType) :: original)
        (body.instantiate1' (.fvar innerIdentifier)) (bodySemantic.inst originalInnerArgument.lift) ∧
      env.HasType universes.length (originalOuterArgumentType :: original.toCtx)
        (bodySemantic.inst originalInnerArgument.lift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst originalInnerArgument.lift).inst (outerArgument.lift' removalLift)) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        (semantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst (outerArgument.lift' removalLift))
        (semantic.lift' removalLift) (.sort level) ∧
      env.HasType universes.length original.toCtx
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift)) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift)) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift))
        (semantic.lift' removalLift) (.sort level) := by
  obtain ⟨innerArgument, innerType, outerArgument, outerType, semantic, sourceInnerLookup, _, _,
    innerEquality, _, _, intermediateTranslation, intermediateTyping, sourceOuterLookup, _, _, _, _,
    _, _, outerEquality, _, _, rebaseEquality, alternativeEquality, _, _, simultaneousTyped,
    simultaneousEquality, simultaneousRebaseEquality⟩ :=
    receipt.instantiatePairIsTypeRebasedCore envWF removal contexts insertion targetWF outerPosition
      outerIdentifier outerSelected innerPosition innerIdentifier innerSelected outerLookup innerLookup
      raisedInnerArgumentTyped translated typed closed supported
  exact ⟨innerArgument, innerType, outerArgument, outerType, semantic, sourceInnerLookup, sourceOuterLookup,
    innerEquality, intermediateTranslation, intermediateTyping, outerEquality, rebaseEquality,
    alternativeEquality, simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩

private theorem semanticHelperProjectsOuterChainAndResidualWithoutAnExpression
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {removalLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (outerPosition : Nat) (outerIdentifier : FVarId)
    (outerSelected : identifiers[outerPosition]? = some outerIdentifier)
    (innerPosition : Nat) (innerIdentifier : FVarId)
    (innerSelected : identifiers[innerPosition]? = some innerIdentifier)
    {originalOuterArgument originalOuterArgumentType originalInnerArgument originalInnerArgumentType : VExpr}
    (outerLookup : original.find? (.inr outerIdentifier) =
      some (originalOuterArgument, originalOuterArgumentType))
    (innerLookup : original.find? (.inr innerIdentifier) =
      some (originalInnerArgument, originalInnerArgumentType))
    {innerDomain : VExpr}
    (raisedInnerArgumentTyped : env.HasType universes.length
      (originalOuterArgumentType :: original.toCtx) originalInnerArgument.lift innerDomain)
    {bodySemantic : VExpr} {level : VLevel}
    (bodyTyped : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level)) :
    ∃ innerArgument innerType outerArgument outerType,
      source.find? (.inr innerIdentifier) = some (innerArgument, innerType) ∧
      source.find? (.inr outerIdentifier) = some (outerArgument, outerType) ∧
      env.IsDefEq universes.length (originalOuterArgumentType :: original.toCtx)
        originalInnerArgument.lift (innerArgument.lift' removalLift).lift innerDomain ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst
          (outerArgument.lift' removalLift)) (.sort level) ∧
      SemanticSubstitutionChain env universes.length original.toCtx level
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst originalInnerArgument.lift).inst (outerArgument.lift' removalLift)) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst (outerArgument.lift' removalLift))
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst
          (outerArgument.lift' removalLift)) (.sort level) :=
  receipt.instantiatePairOuterChain envWF originalWF outerPosition outerIdentifier outerSelected
    innerPosition innerIdentifier innerSelected outerLookup innerLookup raisedInnerArgumentTyped bodyTyped

private theorem nativeProjectsBothStagesClosureSupportAndTargetTyping
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0) (targetWF : target.WF env universes.length)
    (outerPosition : Nat) (outerIdentifier : FVarId) (outerSelected : identifiers[outerPosition]? = some outerIdentifier)
    (innerPosition : Nat) (innerIdentifier : FVarId) (innerSelected : identifiers[innerPosition]? = some innerIdentifier)
    {originalOuterArgument originalOuterArgumentType originalInnerArgument originalInnerArgumentType : VExpr}
    (outerLookup : original.find? (.inr outerIdentifier) = some (originalOuterArgument, originalOuterArgumentType))
    (innerLookup : original.find? (.inr innerIdentifier) = some (originalInnerArgument, originalInnerArgumentType))
    {innerDomain : VExpr}
    (raisedInnerArgumentTyped : env.HasType universes.length
      (originalOuterArgumentType :: original.toCtx) originalInnerArgument.lift innerDomain)
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes
      ((none, .vlam innerDomain) :: (none, .vlam originalOuterArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 2) (supported : body.FVarsIn (· ∈ source.fvars)) :
    Closed (body.instantiate1 (.fvar innerIdentifier)) 1 ∧
      (body.instantiate1 (.fvar innerIdentifier)).FVarsIn (· ∈ source.fvars) ∧
      Closed ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)) 0 ∧
      ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)).FVarsIn (· ∈ source.fvars) ∧
      ∃ (innerArgument outerArgument semantic : VExpr),
        TrExprS env universes target
          ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)) (semantic.lift' insertionLift) ∧
        env.HasType universes.length target.toCtx (semantic.lift' insertionLift) (.sort level) ∧
        env.HasType universes.length original.toCtx
          ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift)) (.sort level) ∧
        env.IsDefEq universes.length original.toCtx
          ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
          ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift)) (.sort level) ∧
        env.IsDefEq universes.length original.toCtx
          ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift))
          (semantic.lift' removalLift) (.sort level) := by
  obtain ⟨innerArgument, _, outerArgument, _, semantic, _, _, _, _, intermediateClosed, intermediateSupported,
    _, _, _, _, _, finalClosed, finalSupported, _, _, _, _, _, _, _, targetTranslation, targetTyping,
    simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩ :=
    receipt.instantiatePairIsTypeRebased envWF removal contexts insertion targetWF outerPosition
      outerIdentifier outerSelected innerPosition innerIdentifier innerSelected outerLookup innerLookup
      raisedInnerArgumentTyped translated typed closed supported
  exact ⟨intermediateClosed, intermediateSupported, finalClosed, finalSupported, innerArgument, outerArgument,
    semantic, targetTranslation, targetTyping, simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩

private theorem semanticHelperProjectsBothArgumentCongruenceWithoutAnExpression
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {removalLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (outerPosition : Nat) (outerIdentifier : FVarId) (outerSelected : identifiers[outerPosition]? = some outerIdentifier)
    (innerPosition : Nat) (innerIdentifier : FVarId) (innerSelected : identifiers[innerPosition]? = some innerIdentifier)
    {originalOuterArgument originalOuterArgumentType originalInnerArgument originalInnerArgumentType : VExpr}
    (outerLookup : original.find? (.inr outerIdentifier) = some (originalOuterArgument, originalOuterArgumentType))
    (innerLookup : original.find? (.inr innerIdentifier) = some (originalInnerArgument, originalInnerArgumentType))
    {innerDomain : VExpr}
    (raisedInnerArgumentTyped : env.HasType universes.length
      (originalOuterArgumentType :: original.toCtx) originalInnerArgument.lift innerDomain)
    {bodySemantic : VExpr} {level : VLevel}
    (typed : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level)) :
    ∃ innerArgument innerType outerArgument outerType,
      source.find? (.inr innerIdentifier) = some (innerArgument, innerType) ∧
      source.find? (.inr outerIdentifier) = some (outerArgument, outerType) ∧
      env.IsDefEq universes.length (originalOuterArgumentType :: original.toCtx)
        originalInnerArgument.lift (innerArgument.lift' removalLift).lift innerDomain ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst (innerArgument.lift' removalLift).lift).inst (outerArgument.lift' removalLift)) (.sort level) := by
  exact receipt.instantiatePairIsDefEq envWF originalWF outerPosition outerIdentifier outerSelected
    innerPosition innerIdentifier innerSelected outerLookup innerLookup raisedInnerArgumentTyped typed

private def outerIdentifier : FVarId := ⟨`ParameterSubstitutionPairOuter⟩
private def innerIdentifier : FVarId := ⟨`ParameterSubstitutionPairInner⟩
private def insertedOne : FVarId := ⟨`ParameterSubstitutionPairInsertedOne⟩
private def insertedTwo : FVarId := ⟨`ParameterSubstitutionPairInsertedTwo⟩
private def insertedThree : FVarId := ⟨`ParameterSubstitutionPairInsertedThree⟩
private def absentIdentifier : FVarId := ⟨`ParameterSubstitutionPairAbsent⟩
private def parameterType : VExpr := .sort (.succ .zero)

private def sourceContext : VLCtx :=
  [(some (innerIdentifier, []), .vlam parameterType),
    (some (outerIdentifier, []), .vlam parameterType)]

private def insertLambda (identifier : FVarId) (context : VLCtx) : VLCtx :=
  (some (identifier, []), .vlam (.sort .zero)) :: context

private def originalContext : VLCtx := insertLambda insertedOne sourceContext
private def targetContext : VLCtx :=
  insertLambda insertedThree (insertLambda insertedTwo originalContext)

private theorem sourceContextWF (env : VEnv) (universes : Nat) : sourceContext.WF env universes := by
  refine ⟨⟨trivial, ?_, ⟨.succ (.succ .zero), .sort (by trivial)⟩⟩,
    ?_, ⟨.succ (.succ .zero), .sort (by trivial)⟩⟩
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars]
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, innerIdentifier, outerIdentifier]

private theorem insertedContextWF {env : VEnv} {universes : Nat} {context : VLCtx}
    (contextWF : context.WF env universes) (identifier : FVarId) (fresh : identifier ∉ context.fvars) :
    (insertLambda identifier context).WF env universes := by
  refine ⟨contextWF, ?_, ⟨.succ .zero, .sort (by trivial)⟩⟩
  rintro selected dependencies equality
  cases equality
  exact ⟨fresh, by simp⟩

private theorem originalContextWF (env : VEnv) (universes : Nat) : originalContext.WF env universes :=
  insertedContextWF (sourceContextWF env universes) insertedOne (by decide)

private theorem targetContextWF (env : VEnv) (universes : Nat) : targetContext.WF env universes :=
  insertedContextWF
    (insertedContextWF (originalContextWF env universes) insertedTwo (by decide)) insertedThree (by decide)

private theorem oneInsertedWeakening :
    VLCtx.FVLift' sourceContext originalContext 0 (.skip .refl) 0 :=
  .skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl

private theorem threeInsertedWeakening :
    VLCtx.FVLift' sourceContext targetContext 0 (.skipN .refl 3) 0 :=
  .skip_fvar (insertedThree, []) (.vlam (.sort .zero))
    (.skip_fvar (insertedTwo, []) (.vlam (.sort .zero))
      (.skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl))

private def pairedBody : Expr :=
  .forallE `localType (.sort (.succ .zero))
    (.forallE `outerElement (.bvar 2)
      (.forallE `innerElement (.bvar 2) (.bvar 2) .default) .default) .default

private def pairedSemantic : VExpr :=
  .forallE parameterType (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 2)))

private def pairedLevel : VLevel :=
  .imax (.succ (.succ .zero)) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))

private def intermediateBody : Expr :=
  .forallE `localType (.sort (.succ .zero))
    (.forallE `outerElement (.bvar 1)
      (.forallE `innerElement (.fvar innerIdentifier) (.bvar 2) .default) .default) .default

private def finalBody : Expr :=
  .forallE `localType (.sort (.succ .zero))
    (.forallE `outerElement (.fvar outerIdentifier)
      (.forallE `innerElement (.fvar innerIdentifier) (.bvar 2) .default) .default) .default

private theorem pairedBodyTyped (env : VEnv) (universes : Nat) (context : List VExpr) :
    env.HasType universes (parameterType :: parameterType :: context) pairedSemantic (.sort pairedLevel) :=
  VEnv.HasType.forallE (.sort (by trivial))
    (VEnv.HasType.forallE (.bvar (.succ (.succ .zero)))
      (VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero)))))

private theorem pairedBodyTranslated (env : VEnv) (universes : List Name) (context : VLCtx) :
    TrExprS env universes ((none, .vlam parameterType) :: (none, .vlam parameterType) :: context)
      pairedBody pairedSemantic := by
  apply TrExprS.forallE
  · exact ⟨.succ (.succ .zero), .sort (by trivial)⟩
  · exact ⟨.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)),
      VEnv.HasType.forallE (.bvar (.succ (.succ .zero)))
        (VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero))))⟩
  · exact .sort (by simp [VLevel.ofLevel])
  · apply TrExprS.forallE
    · exact ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩
    · exact ⟨.imax (.succ .zero) (.succ .zero),
        VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero)))⟩
    · exact .bvar rfl
    · exact .forallE ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩
        ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩ (.bvar rfl) (.bvar rfl)

private theorem bothAnonymousBindersAreActuallyUsed :
    pairedBody.instantiate1' (.fvar innerIdentifier) = intermediateBody ∧
      (pairedBody.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier) = finalBody := ⟨rfl, rfl⟩

private theorem genuineIntermediateBodyRetainsOnlyItsOuterFormal :
    Closed pairedBody 2 ∧ ¬ Closed pairedBody 1 ∧
      Closed intermediateBody 1 ∧ ¬ Closed intermediateBody 0 ∧ Closed finalBody 0 := by
  simp [pairedBody, intermediateBody, finalBody, Closed]

private theorem innerBeforeOuterIsNotTheSwappedOrder :
    (pairedBody.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier) ≠
      (pairedBody.instantiate1' (.fvar outerIdentifier)).instantiate1' (.fvar innerIdentifier) := by
  simp [pairedBody, Expr.instantiate1', Expr.liftLooseBVars', outerIdentifier, innerIdentifier]

private theorem sourceSupportsBothSelectedArgumentsAndBody :
    [outerIdentifier, innerIdentifier] ⊆ sourceContext.fvars ∧
      pairedBody.FVarsIn (· ∈ sourceContext.fvars) ∧
      intermediateBody.FVarsIn (· ∈ sourceContext.fvars) ∧ finalBody.FVarsIn (· ∈ sourceContext.fvars) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro identifier member
    simpa [sourceContext, VLCtx.fvars, or_comm] using member
  all_goals simp [pairedBody, intermediateBody, finalBody, FVarsIn, sourceContext, VLCtx.fvars,
    parameterType, Level.hasMVar']

private theorem unsupportedIntermediateCannotSatisfyTheSupportPremise :
    ¬ (Expr.app intermediateBody (.fvar absentIdentifier)).FVarsIn (· ∈ sourceContext.fvars) := by
  simp [intermediateBody, FVarsIn, sourceContext, VLCtx.fvars, absentIdentifier, innerIdentifier,
    outerIdentifier, Level.hasMVar']

private theorem thirdAnonymousBinderFailsTheClosurePremise : ¬ Closed (Expr.bvar 2) 2 := by
  simp [Closed]

private theorem selectedPositionsCannotBeSwappedOrOutOfRange :
    [outerIdentifier, innerIdentifier][0]? = some outerIdentifier ∧
      [outerIdentifier, innerIdentifier][1]? = some innerIdentifier ∧
      [outerIdentifier, innerIdentifier][0]? ≠ some innerIdentifier ∧
      [outerIdentifier, innerIdentifier][2]? = none := by
  simp [outerIdentifier, innerIdentifier]

private theorem duplicateRequestedPositionIsStillAValidSelection :
    [outerIdentifier][0]? = some outerIdentifier ∧
      [outerIdentifier][0]? = some outerIdentifier := ⟨rfl, rfl⟩

private theorem distinctRemovalAndInsertionMoveBothActualParameters :
    (VExpr.bvar 0).lift' (.skip .refl) = .bvar 1 ∧
      (VExpr.bvar 1).lift' (.skip .refl) = .bvar 2 ∧
      (VExpr.bvar 0).lift' (.skipN .refl 3) = .bvar 3 ∧
      (VExpr.bvar 1).lift' (.skipN .refl 3) = .bvar 4 := ⟨rfl, rfl, rfl, rfl⟩

private theorem concreteAgreement {env : VEnv} {universes : List Name} {identifiers : List FVarId}
    (envWF : env.WF) (retained : identifiers ⊆ sourceContext.fvars) :
    RetainedFVarPrefixAgreement env universes sourceContext originalContext originalContext
      (.skip .refl) identifiers :=
  (oneInsertedWeakening.retainedPrefix envWF (sourceContextWF env universes.length)
    (originalContextWF env universes.length) retained).agreesWithOriginal envWF
      (.refl envWF.ordered (originalContextWF env universes.length))

private theorem genuinePairRebasesThroughDistinctInsertions
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    Closed intermediateBody 1 ∧ Closed finalBody 0 ∧
      TrExprS env universes ((none, .vlam parameterType) :: originalContext) intermediateBody
        (pairedSemantic.inst (VExpr.bvar 1).lift) ∧
      ∃ semantic,
        TrExprS env universes sourceContext finalBody semantic ∧
        env.HasType universes.length sourceContext.toCtx semantic (.sort pairedLevel) ∧
        env.IsDefEq universes.length originalContext.toCtx
          ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (semantic.lift' (.skip .refl)) (.sort pairedLevel) ∧
        TrExprS env universes targetContext finalBody (semantic.lift' (.skipN .refl 3)) ∧
        env.HasType universes.length targetContext.toCtx (semantic.lift' (.skipN .refl 3)) (.sort pairedLevel) := by
  have receipt := concreteAgreement (universes := universes) envWF sourceSupportsBothSelectedArgumentsAndBody.1
  obtain ⟨_, _, _, _, semantic, _, _, _, _, intermediateClosed, _, intermediateTranslation, _,
    _, _, _, finalClosed, _, _, _, _, sourceTranslation, sourceTyping, rebaseEquality, _,
    targetTranslation, targetTyping, _, _, _⟩ :=
    receipt.instantiatePairIsTypeRebasedCore envWF oneInsertedWeakening
      (.refl envWF.ordered (originalContextWF env universes.length)) threeInsertedWeakening
      (targetContextWF env universes.length) 0 outerIdentifier rfl 1 innerIdentifier rfl
      (originalOuterArgument := .bvar 2) (originalOuterArgumentType := parameterType)
      (originalInnerArgument := .bvar 1) (originalInnerArgumentType := parameterType)
      rfl rfl (innerDomain := parameterType) (.bvar (.succ (.succ .zero)))
      (pairedBodyTranslated env universes originalContext)
      (pairedBodyTyped env universes.length originalContext.toCtx)
      genuineIntermediateBodyRetainsOnlyItsOuterFormal.1 sourceSupportsBothSelectedArgumentsAndBody.2.1
  exact ⟨intermediateClosed, finalClosed, intermediateTranslation, semantic,
    sourceTranslation, sourceTyping, rebaseEquality, targetTranslation, targetTyping⟩

private theorem repeatedSelectedParameterDoesNotRequireDistinctPositions
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    Closed ((pairedBody.instantiate1' (.fvar outerIdentifier)).instantiate1' (.fvar outerIdentifier)) 0 ∧
      ∃ (semantic : VExpr),
        TrExprS env universes targetContext
          ((pairedBody.instantiate1' (.fvar outerIdentifier)).instantiate1' (.fvar outerIdentifier))
          (semantic.lift' (.skipN .refl 3)) ∧
        env.HasType universes.length targetContext.toCtx (semantic.lift' (.skipN .refl 3)) (.sort pairedLevel) := by
  have retained : [outerIdentifier] ⊆ sourceContext.fvars := by
    intro identifier member
    have equality : identifier = outerIdentifier := by simpa using member
    simp [equality, sourceContext, VLCtx.fvars]
  have receipt := concreteAgreement (universes := universes) envWF retained
  obtain ⟨_, _, _, _, semantic, _, _, _, _, _, _, _, _, _, _, _, closed, _, _, _, _, _, _, _, _,
    targetTranslation, targetTyping, _, _, _⟩ :=
    receipt.instantiatePairIsTypeRebasedCore envWF oneInsertedWeakening
      (.refl envWF.ordered (originalContextWF env universes.length)) threeInsertedWeakening
      (targetContextWF env universes.length) 0 outerIdentifier rfl 0 outerIdentifier rfl
      (originalOuterArgument := .bvar 2) (originalOuterArgumentType := parameterType)
      (originalInnerArgument := .bvar 2) (originalInnerArgumentType := parameterType)
      rfl rfl (innerDomain := parameterType) (.bvar (.succ (.succ (.succ .zero))))
      (pairedBodyTranslated env universes originalContext)
      (pairedBodyTyped env universes.length originalContext.toCtx)
      genuineIntermediateBodyRetainsOnlyItsOuterFormal.1 sourceSupportsBothSelectedArgumentsAndBody.2.1
  exact ⟨closed, semantic, targetTranslation, targetTyping⟩

private def equivalentInnerUniverse : VLevel := .max (.succ .zero) .zero
private def equivalentInnerDomain : VExpr := .sort equivalentInnerUniverse
private def equivalentPairLevel : VLevel :=
  .imax (.succ (.succ .zero)) (.imax (.succ .zero) (.imax equivalentInnerUniverse (.succ .zero)))

private theorem explicitRaisedTypingDoesNotRequireLiteralDomainEquality
    (env : VEnv) (universes : Nat) :
    equivalentInnerDomain ≠ parameterType.lift ∧
      env.HasType universes (parameterType :: originalContext.toCtx)
        (VExpr.bvar 1).lift equivalentInnerDomain := by
  refine ⟨?_, ?_⟩
  · intro equality
    cases equality
  · have equality : env.IsDefEq universes (parameterType :: originalContext.toCtx)
        parameterType equivalentInnerDomain (.sort (.succ (.succ .zero))) :=
      .sortDF (by trivial) (by trivial)
        (by simp [VLevel.equiv_def, VLevel.eval, equivalentInnerUniverse])
    exact VEnv.IsDefEq.defeq equality (.bvar (.succ (.succ .zero)))

private theorem nonliteralInnerDomainStillRebasesTheGenuinePair
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    ∃ (semantic : VExpr),
      TrExprS env universes targetContext finalBody (semantic.lift' (.skipN .refl 3)) ∧
      env.HasType universes.length targetContext.toCtx (semantic.lift' (.skipN .refl 3)) (.sort equivalentPairLevel) ∧
      env.HasType universes.length originalContext.toCtx
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (.sort equivalentPairLevel) ∧
      env.IsDefEq universes.length originalContext.toCtx
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2))
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (.sort equivalentPairLevel) ∧
      env.IsDefEq universes.length originalContext.toCtx
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2))
        (semantic.lift' (.skip .refl)) (.sort equivalentPairLevel) := by
  have typed : env.HasType universes.length
      (equivalentInnerDomain :: parameterType :: originalContext.toCtx) pairedSemantic (.sort equivalentPairLevel) :=
    VEnv.HasType.forallE (.sort (by trivial))
      (VEnv.HasType.forallE (.bvar (.succ (.succ .zero)))
        (VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero)))))
  have translated : TrExprS env universes
      ((none, .vlam equivalentInnerDomain) :: (none, .vlam parameterType) :: originalContext)
      pairedBody pairedSemantic := by
    apply TrExprS.forallE
    · exact ⟨.succ (.succ .zero), .sort (by trivial)⟩
    · exact ⟨.imax (.succ .zero) (.imax equivalentInnerUniverse (.succ .zero)),
        VEnv.HasType.forallE (.bvar (.succ (.succ .zero)))
          (VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero))))⟩
    · exact .sort (by simp [VLevel.ofLevel])
    · apply TrExprS.forallE
      · exact ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩
      · exact ⟨.imax equivalentInnerUniverse (.succ .zero),
          VEnv.HasType.forallE (.bvar (.succ (.succ .zero))) (.bvar (.succ (.succ .zero)))⟩
      · exact .bvar rfl
      · exact .forallE ⟨equivalentInnerUniverse, .bvar (.succ (.succ .zero))⟩
          ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩ (.bvar rfl) (.bvar rfl)
  have receipt := concreteAgreement (universes := universes) envWF sourceSupportsBothSelectedArgumentsAndBody.1
  obtain ⟨innerArgument, innerType, outerArgument, outerType, semantic, innerLookup, _, _, _, _, _, _, _,
    outerLookup, _, _, _, _, _, _, _, _, _, _, _, targetTranslation, targetTyping,
    simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩ :=
    receipt.instantiatePairIsTypeRebasedCore envWF oneInsertedWeakening
      (.refl envWF.ordered (originalContextWF env universes.length)) threeInsertedWeakening
      (targetContextWF env universes.length) 0 outerIdentifier rfl 1 innerIdentifier rfl
      (originalOuterArgument := .bvar 2) (originalOuterArgumentType := parameterType)
      (originalInnerArgument := .bvar 1) (originalInnerArgumentType := parameterType) rfl rfl
      (explicitRaisedTypingDoesNotRequireLiteralDomainEquality env universes.length).2 translated typed
      genuineIntermediateBodyRetainsOnlyItsOuterFormal.1 sourceSupportsBothSelectedArgumentsAndBody.2.1
  have innerSourceLookup : sourceContext.find? (.inr innerIdentifier) = some (.bvar 0, parameterType) := rfl
  have outerSourceLookup : sourceContext.find? (.inr outerIdentifier) = some (.bvar 1, parameterType) := rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (innerLookup.symm.trans innerSourceLookup))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (outerLookup.symm.trans outerSourceLookup))
  exact ⟨semantic, targetTranslation, targetTyping, simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩

private def betaOuterCarrier : FVarId := ⟨`ParameterSubstitutionPairBetaOuterCarrier⟩
private def betaInnerCarrier : FVarId := ⟨`ParameterSubstitutionPairBetaInnerCarrier⟩
private def betaArgument (position : Nat) : VExpr :=
  .app (.lam parameterType (.bvar 0)) (.bvar position)

private def betaSourceContext : VLCtx :=
  [(some (innerIdentifier, [betaInnerCarrier]), .vlet parameterType (.bvar 0)),
    (some (outerIdentifier, [betaOuterCarrier]), .vlet parameterType (.bvar 1)),
    (some (betaInnerCarrier, []), .vlam parameterType),
    (some (betaOuterCarrier, []), .vlam parameterType)]

private def betaOriginalBase : VLCtx :=
  [(some (innerIdentifier, [betaInnerCarrier]), .vlet parameterType (betaArgument 0)),
    (some (outerIdentifier, [betaOuterCarrier]), .vlet parameterType (betaArgument 1)),
    (some (betaInnerCarrier, []), .vlam parameterType),
    (some (betaOuterCarrier, []), .vlam parameterType)]

private def betaOriginalContext : VLCtx := insertLambda insertedOne betaOriginalBase
private def betaAlignedContext : VLCtx := insertLambda insertedOne betaSourceContext
private def betaTargetContext : VLCtx :=
  insertLambda insertedThree (insertLambda insertedTwo betaAlignedContext)

private theorem bothBetaContextsAgreeWithoutLiteralValueEquality (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes betaOriginalBase betaSourceContext := by
  apply VLCtx.IsDefEq.cons
  · apply VLCtx.IsDefEq.cons
    · apply VLCtx.IsDefEq.cons
      · apply VLCtx.IsDefEq.cons .nil
        · rintro identifier dependencies equality
          cases equality
          simp [VLCtx.fvars]
        · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
      · rintro identifier dependencies equality
        cases equality
        simp [VLCtx.fvars, betaInnerCarrier, betaOuterCarrier]
      · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
    · rintro identifier dependencies equality
      cases equality
      simp [VLCtx.fvars, betaInnerCarrier, betaOuterCarrier, outerIdentifier]
    · exact .vlet (.beta (.bvar .zero) (.bvar (.succ .zero))) (.sortDF (by trivial) (by trivial) rfl)
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, betaInnerCarrier, betaOuterCarrier, outerIdentifier, innerIdentifier]
  · exact .vlet (.beta (.bvar .zero) (.bvar .zero)) (.sortDF (by trivial) (by trivial) rfl)

private theorem insertedBetaContextsStillAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes betaOriginalContext betaAlignedContext := by
  apply VLCtx.IsDefEq.cons (bothBetaContextsAgreeWithoutLiteralValueEquality env universes)
  · rintro identifier dependencies equality
    cases equality
    simp [betaOriginalBase, VLCtx.fvars, insertedOne, betaInnerCarrier, betaOuterCarrier,
      outerIdentifier, innerIdentifier]
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem bothOriginalArgumentsAreNonliteralBetaValues :
    betaOriginalContext.find? (.inr innerIdentifier) =
      some ((betaArgument 0).lift' (.skip .refl), parameterType) ∧
    betaOriginalContext.find? (.inr outerIdentifier) =
      some ((betaArgument 1).lift' (.skip .refl), parameterType) ∧
      (betaArgument 0).lift' (.skip .refl) ≠ .bvar 1 ∧
      (betaArgument 1).lift' (.skip .refl) ≠ .bvar 2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem simultaneousCongruenceReplacesBothNonliteralBetaArguments
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    ∃ (semantic : VExpr),
      env.HasType universes.length betaOriginalContext.toCtx
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (.sort pairedLevel) ∧
      env.IsDefEq universes.length betaOriginalContext.toCtx
        ((pairedSemantic.inst ((betaArgument 0).lift' (.skip .refl)).lift).inst
          ((betaArgument 1).lift' (.skip .refl)))
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (.sort pairedLevel) ∧
      env.IsDefEq universes.length betaOriginalContext.toCtx
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (semantic.lift' (.skip .refl)) (.sort pairedLevel) ∧
      TrExprS env universes betaTargetContext finalBody (semantic.lift' (.skipN .refl 3)) ∧
      env.HasType universes.length betaTargetContext.toCtx (semantic.lift' (.skipN .refl 3)) (.sort pairedLevel) ∧
      SemanticSubstitutionChain env universes.length betaOriginalContext.toCtx pairedLevel
        ((pairedSemantic.inst ((betaArgument 0).lift' (.skip .refl)).lift).inst
          ((betaArgument 1).lift' (.skip .refl)))
        ((pairedSemantic.inst ((betaArgument 0).lift' (.skip .refl)).lift).inst (.bvar 2)) ∧
      env.IsDefEq universes.length betaOriginalContext.toCtx
        ((pairedSemantic.inst ((betaArgument 0).lift' (.skip .refl)).lift).inst (.bvar 2))
        ((pairedSemantic.inst (VExpr.bvar 1).lift).inst (.bvar 2)) (.sort pairedLevel) ∧
      env.IsDefEq universes.length betaOriginalContext.toCtx
        ((pairedSemantic.inst ((betaArgument 0).lift' (.skip .refl)).lift).inst (.bvar 2))
        (semantic.lift' (.skip .refl)) (.sort pairedLevel) := by
  have contexts := insertedBetaContextsStillAgree env universes.length
  have sourceWF := ((bothBetaContextsAgreeWithoutLiteralValueEquality env universes.length).symm envWF.ordered).wf
  have alignedWF := (contexts.symm envWF.ordered).wf
  have targetWF := insertedContextWF
    (insertedContextWF alignedWF insertedTwo (by decide)) insertedThree (by decide)
  have removal : VLCtx.FVLift' betaSourceContext betaAlignedContext 0 (.skip .refl) 0 :=
    .skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl
  have insertion : VLCtx.FVLift' betaSourceContext betaTargetContext 0 (.skipN .refl 3) 0 :=
    .skip_fvar (insertedThree, []) (.vlam (.sort .zero))
      (.skip_fvar (insertedTwo, []) (.vlam (.sort .zero)) removal)
  have retained : [outerIdentifier, innerIdentifier] ⊆ betaSourceContext.fvars := by
    intro identifier member
    simp [betaSourceContext, VLCtx.fvars] at member ⊢
    grind
  have receipt := (removal.retainedPrefix envWF sourceWF alignedWF retained).agreesWithOriginal envWF contexts
  have raisedTyped : env.HasType universes.length (parameterType :: betaOriginalContext.toCtx)
      ((betaArgument 0).lift' (.skip .refl)).lift parameterType :=
    VEnv.HasType.app (VEnv.HasType.lam (.sort (by trivial)) (.bvar .zero)) (.bvar (.succ (.succ .zero)))
  obtain ⟨innerArgument, innerType, outerArgument, outerType, semantic, innerLookup, _, _, _, _, _, _, _,
    outerLookup, _, _, _, _, _, _, _, _, _, rebaseEquality, _, targetTranslation, targetTyping,
    simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality⟩ :=
    receipt.instantiatePairIsTypeRebasedCore envWF removal contexts insertion targetWF
      0 outerIdentifier rfl 1 innerIdentifier rfl
      (originalOuterArgument := (betaArgument 1).lift' (.skip .refl)) (originalOuterArgumentType := parameterType)
      (originalInnerArgument := (betaArgument 0).lift' (.skip .refl)) (originalInnerArgumentType := parameterType)
      rfl rfl raisedTyped (pairedBodyTranslated env universes betaOriginalContext)
      (pairedBodyTyped env universes.length betaOriginalContext.toCtx)
      genuineIntermediateBodyRetainsOnlyItsOuterFormal.1
      (by simp [pairedBody, FVarsIn, Level.hasMVar'])
  have innerSourceLookup : betaSourceContext.find? (.inr innerIdentifier) = some (.bvar 0, parameterType) := rfl
  have outerSourceLookup : betaSourceContext.find? (.inr outerIdentifier) = some (.bvar 1, parameterType) := rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (innerLookup.symm.trans innerSourceLookup))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (outerLookup.symm.trans outerSourceLookup))
  obtain ⟨chainInnerArgument, chainInnerType, chainOuterArgument, chainOuterType,
    chainInnerLookup, chainOuterLookup, _, _, outerChain, residualBoth⟩ :=
    receipt.instantiatePairOuterChain envWF contexts.wf 0 outerIdentifier rfl 1 innerIdentifier rfl
      (originalOuterArgument := (betaArgument 1).lift' (.skip .refl)) (originalOuterArgumentType := parameterType)
      (originalInnerArgument := (betaArgument 0).lift' (.skip .refl)) (originalInnerArgumentType := parameterType)
      rfl rfl raisedTyped (pairedBodyTyped env universes.length betaOriginalContext.toCtx)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (chainInnerLookup.symm.trans innerSourceLookup))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (chainOuterLookup.symm.trans outerSourceLookup))
  have residualCommon := outerChain.cancelLeft rebaseEquality envWF contexts.wf.toCtx
  exact ⟨semantic, simultaneousTyped, simultaneousEquality, simultaneousRebaseEquality, targetTranslation,
    targetTyping, outerChain, residualBoth, residualCommon⟩

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .const _ _ => [2]
  | .app function argument => [3] ++ semanticShape function ++ semanticShape argument
  | .lam type body => [4] ++ semanticShape type ++ semanticShape body
  | .forallE type body => [5] ++ semanticShape type ++ semanticShape body

private def expectedSemantic (outerArgument innerArgument : VExpr) : VExpr :=
  .forallE parameterType
    (.forallE outerArgument.lift (.forallE (innerArgument.liftN 2) (.bvar 2)))

private def runtimePairs : MetaM Unit := do
  let some (sourceOuter, _) := sourceContext.find? (.inr outerIdentifier)
    | throwError "parameter-substitution-pair source outer absent"
  let some (sourceInner, _) := sourceContext.find? (.inr innerIdentifier)
    | throwError "parameter-substitution-pair source inner absent"
  let some (originalOuter, _) := originalContext.find? (.inr outerIdentifier)
    | throwError "parameter-substitution-pair original outer absent"
  let some (originalInner, _) := originalContext.find? (.inr innerIdentifier)
    | throwError "parameter-substitution-pair original inner absent"
  let some (targetOuter, _) := targetContext.find? (.inr outerIdentifier)
    | throwError "parameter-substitution-pair target outer absent"
  let some (targetInner, _) := targetContext.find? (.inr innerIdentifier)
    | throwError "parameter-substitution-pair target inner absent"
  let originalSemantic := (pairedSemantic.inst originalInner.lift).inst originalOuter
  let reducedSemantic := (pairedSemantic.inst sourceInner.lift).inst sourceOuter
  let targetSemantic := (pairedSemantic.inst targetInner.lift).inst targetOuter
  let conditions := [
    (pairedBody.instantiate1' (.fvar innerIdentifier) == intermediateBody, "core inner stage"),
    (pairedBody.instantiate1 (.fvar innerIdentifier) == intermediateBody, "native inner stage"),
    ((pairedBody.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier) == finalBody, "core two stages"),
    ((pairedBody.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier) == finalBody, "native two stages"),
    ((pairedBody.instantiate1' (.fvar outerIdentifier)).instantiate1' (.fvar innerIdentifier) != finalBody, "wrong core order"),
    ((pairedBody.instantiate1 (.fvar outerIdentifier)).instantiate1 (.fvar innerIdentifier) != finalBody, "wrong native order"),
    (semanticShape originalSemantic == semanticShape (expectedSemantic originalOuter originalInner), "original semantic order"),
    (semanticShape reducedSemantic == semanticShape (expectedSemantic sourceOuter sourceInner), "reduced semantic order"),
    (semanticShape targetSemantic == semanticShape (expectedSemantic targetOuter targetInner), "target semantic order"),
    (semanticShape originalSemantic == semanticShape (reducedSemantic.lift' (.skip .refl)), "one-binder removal"),
    (semanticShape targetSemantic == semanticShape (reducedSemantic.lift' (.skipN .refl 3)), "three-binder insertion"),
    (semanticShape originalSemantic != semanticShape targetSemantic, "distinct removal/insertion"),
    (semanticShape ((pairedSemantic.inst originalInner).inst originalOuter) != semanticShape originalSemantic, "inner argument must lift"),
    (semanticShape sourceOuter == [0, 1] && semanticShape sourceInner == [0, 0], "source pair positions"),
    (semanticShape originalOuter == [0, 2] && semanticShape originalInner == [0, 1], "original pair positions"),
    (semanticShape targetOuter == [0, 4] && semanticShape targetInner == [0, 3], "target pair positions"),
    ([outerIdentifier][0]? == some outerIdentifier, "duplicate selected position remains selectable")]
  for (condition, label) in conditions do
    unless condition do throwError "parameter-substitution-pair runtime failed: {label}"
  logInfo m!"parameter-substitution-pair runtime: {conditions.length} genuine intermediate/final/order/shift controls; both anonymous formal binders used and local binder protected"

private def runtimeSimultaneousBetaPairs : MetaM Unit := do
  let originalInner := (betaArgument 0).lift' (.skip .refl)
  let originalOuter := (betaArgument 1).lift' (.skip .refl)
  let raisedInner := (VExpr.bvar 0).lift' (.skip .refl)
  let raisedOuter := (VExpr.bvar 1).lift' (.skip .refl)
  let originalFinal := (pairedSemantic.inst originalInner.lift).inst originalOuter
  let outerOnly := (pairedSemantic.inst originalInner.lift).inst raisedOuter
  let bothReduced := (pairedSemantic.inst raisedInner.lift).inst raisedOuter
  let sourceFinal := (pairedSemantic.inst (VExpr.bvar 0).lift).inst (.bvar 1)
  let targetFinal := sourceFinal.lift' (.skipN .refl 3)
  let conditions := [
    (semanticShape originalInner != semanticShape raisedInner, "nonliteral inner beta"),
    (semanticShape originalOuter != semanticShape raisedOuter, "nonliteral outer beta"),
    (semanticShape originalFinal != semanticShape bothReduced, "simultaneous equality is not literal equality"),
    (semanticShape originalFinal != semanticShape outerOnly, "outer chain is not literal equality"),
    (semanticShape outerOnly != semanticShape bothReduced, "residual inner equality is not literal equality"),
    (semanticShape outerOnly == semanticShape (expectedSemantic raisedOuter originalInner), "outer chain retains original inner argument"),
    (semanticShape originalFinal == semanticShape (expectedSemantic originalOuter originalInner), "both original beta shifts"),
    (semanticShape bothReduced == semanticShape (expectedSemantic raisedOuter raisedInner), "both reduced argument shifts"),
    (semanticShape bothReduced == semanticShape (sourceFinal.lift' (.skip .refl)), "common removal semantic"),
    (semanticShape ((pairedSemantic.inst raisedInner).inst raisedOuter) != semanticShape bothReduced, "both-reduced inner lift required"),
    (semanticShape ((pairedSemantic.inst raisedOuter.lift).inst raisedInner) != semanticShape bothReduced, "both-reduced order required"),
    (semanticShape targetFinal == semanticShape (expectedSemantic (.bvar 4) (.bvar 3)), "common insertion semantic"),
    (semanticShape bothReduced != semanticShape targetFinal, "removal/insertion receipts distinct")]
  for (condition, label) in conditions do
    unless condition do throwError "parameter-substitution-pair simultaneous runtime failed: {label}"
  logInfo m!"parameter-substitution-pair simultaneous runtime: {conditions.length} two-nonliteral-beta/common-semantic/order/lift controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-substitution-pair declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "parameter-substitution-pair unexpected axiom {axiomName} in {name}"

private def auditModule (coreAllowed nativeAllowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterSubstitutionPair
    | throwError "parameter-substitution-pair module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-substitution-pair module-owned axiom {name}"
      let allowed := if name == ``RetainedFVarPrefixAgreement.instantiatePairIsTypeRebased then nativeAllowed else coreAllowed
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == 3 do throwError "parameter-substitution-pair module declaration manifest changed"
  logInfo m!"parameter-substitution-pair module: {declarations} declarations audited; core forbids native/container/range/abstraction interfaces"

private def rejectedNativeInterface (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.instantiate1_eq (logical ++ [``sorryAx])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "parameter-substitution-pair core audit accepted native instantiation"
  match exception with
  | .error _ message =>
    let expected := m!"parameter-substitution-pair unexpected axiom {``Expr.instantiate1_eq} in {``Expr.instantiate1_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let nativeAllowed := inherited ++ [``Expr.instantiate1_eq]
  let inheritedControls := [``coreProjectsInnerEqualityAndFinalOuterAgreements, ``pairedBodyTranslated,
    ``semanticHelperProjectsOuterChainAndResidualWithoutAnExpression,
    ``concreteAgreement, ``genuinePairRebasesThroughDistinctInsertions,
    ``repeatedSelectedParameterDoesNotRequireDistinctPositions, ``nonliteralInnerDomainStillRebasesTheGenuinePair,
    ``semanticHelperProjectsBothArgumentCongruenceWithoutAnExpression,
    ``simultaneousCongruenceReplacesBothNonliteralBetaArguments]
  let logicalControls := [``sourceContextWF, ``insertedContextWF, ``originalContextWF, ``targetContextWF,
    ``oneInsertedWeakening, ``threeInsertedWeakening, ``pairedBodyTyped,
    ``bothAnonymousBindersAreActuallyUsed, ``genuineIntermediateBodyRetainsOnlyItsOuterFormal,
    ``innerBeforeOuterIsNotTheSwappedOrder, ``sourceSupportsBothSelectedArgumentsAndBody,
    ``unsupportedIntermediateCannotSatisfyTheSupportPremise, ``thirdAnonymousBinderFailsTheClosurePremise,
    ``selectedPositionsCannotBeSwappedOrOutOfRange, ``duplicateRequestedPositionIsStillAValidSelection,
    ``distinctRemovalAndInsertionMoveBothActualParameters, ``explicitRaisedTypingDoesNotRequireLiteralDomainEquality,
    ``bothBetaContextsAgreeWithoutLiteralValueEquality, ``insertedBetaContextsStillAgree,
    ``bothOriginalArgumentsAreNonliteralBetaValues]
  for name in inheritedControls do auditDeclaration name inherited
  for name in logicalControls do auditDeclaration name logical
  auditDeclaration ``nativeProjectsBothStagesClosureSupportAndTargetTyping nativeAllowed
  auditDeclaration ``RetainedFVarPrefixAgreement.instantiatePairIsDefEq inherited
  auditDeclaration ``RetainedFVarPrefixAgreement.instantiatePairOuterChain inherited
  auditDeclaration ``Closed.instantiate1_offset logical
  auditModule inherited nativeAllowed
  rejectedNativeInterface logical
  runtimePairs
  runtimeSimultaneousBetaPairs
  logInfo m!"parameter-substitution-pair tests: {inheritedControls.length + logicalControls.length + 1} proof controls; simultaneous inner/outer congruence; semantic outer chain and same-context residual cancellation; both original beta arguments nonliteral; genuine two-formal body and typed intermediate; inner-before-outer substitution; nested local binder protected; explicit arbitrary innerDomain typing premise; distinct removal/insertion; duplicate position accepted; closure/support/selection negatives"

end InductiveParameterSubstitutionPairTest
