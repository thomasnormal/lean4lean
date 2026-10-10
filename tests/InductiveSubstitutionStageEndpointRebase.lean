import Lean4Lean.Verify.InductiveSubstitutionStageEndpointRebase
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveSubstitutionStageEndpointRebaseTest

private def EndpointRebaseReceipt (env : VEnv) (universes : List Name)
    (smaller original aligned target : VLCtx) (removalLift insertionLift : Lift)
    (originalDomain reducedDomain : VExpr) (body : Expr) (bodySemantic : VExpr)
    (domainLevel level : VLevel) (originalArgument reducedArgument : VExpr) : Prop :=
  ∃ reducedBody,
    VLCtx.FVLift' ((none, .vlam reducedDomain) :: smaller)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) 1 removalLift 1 ∧
    VLCtx.IsDefEq env universes.length ((none, .vlam originalDomain) :: original)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) ∧
    env.HasType universes.length smaller.toCtx reducedDomain (.sort domainLevel) ∧
    TrExprS env universes ((none, .vlam reducedDomain) :: smaller) body reducedBody ∧
    env.HasType universes.length (reducedDomain :: smaller.toCtx) reducedBody (.sort level) ∧
    env.IsDefEq universes.length (originalDomain :: original.toCtx)
      bodySemantic (reducedBody.lift' removalLift.cons) (.sort level) ∧
    env.HasType universes.length smaller.toCtx reducedArgument reducedDomain ∧
    env.HasType universes.length smaller.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
    env.IsDefEq universes.length original.toCtx (bodySemantic.inst originalArgument)
      ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) ∧
    TrExprS env universes ((none, .vlam (reducedDomain.lift' insertionLift)) :: target)
      body (reducedBody.lift' insertionLift.cons) ∧
    env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
      (reducedBody.lift' insertionLift.cons) (.sort level) ∧
    env.HasType universes.length target.toCtx (reducedArgument.lift' insertionLift)
      (reducedDomain.lift' insertionLift) ∧
    env.HasType universes.length target.toCtx
      ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level)

private theorem endpointForwardsEveryReceipt
    {env : VEnv} {universes : List Name} {smaller original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
    {body : Expr} {domainLevel level : VLevel} {originalArgument reducedArgument : VExpr}
    (envWF : env.WF) (removal : VLCtx.FVLift' smaller aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' removalLift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ smaller.fvars))
    (argumentEquality : env.IsDefEq universes.length original.toCtx
      originalArgument (reducedArgument.lift' removalLift) originalDomain)
    (insertion : VLCtx.FVLift' smaller target 0 insertionLift 0)
    (targetWF : target.WF env universes.length) :
    EndpointRebaseReceipt env universes smaller original aligned target removalLift insertionLift originalDomain reducedDomain
      body bodySemantic domainLevel level originalArgument reducedArgument :=
  translated.strengthenSubstitutionStageEndpointRebased envWF removal contexts domainEquality typed closed
    supported argumentEquality insertion targetWF

private theorem semanticHistoricalArgumentNeedsOnlyActualDomainEquality
    {env : VEnv} {universes : List Name} {smaller original aligned target : VLCtx}
    {removalLift insertionLift : Lift}
    {originalDomain reducedDomain bodySemantic historicalArgument reducedArgument : VExpr}
    {body : Expr} {domainLevel level : VLevel}
    (envWF : env.WF) (removal : VLCtx.FVLift' smaller aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' removalLift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ smaller.fvars))
    (argumentEquality : env.IsDefEq universes.length original.toCtx
      historicalArgument (reducedArgument.lift' removalLift) originalDomain)
    (insertion : VLCtx.FVLift' smaller target 0 insertionLift 0)
    (targetWF : target.WF env universes.length) :
    ∃ reducedBody : VExpr,
      env.HasType universes.length smaller.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
      env.HasType universes.length original.toCtx (bodySemantic.inst historicalArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx (bodySemantic.inst historicalArgument)
        ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) ∧
      env.HasType universes.length target.toCtx
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) := by
  obtain ⟨reducedBody, _, _, _, _, _, _, _, reducedType, endpointEquality, _, _, _, targetType⟩ :=
    translated.strengthenSubstitutionStageEndpointRebased envWF removal contexts domainEquality typed closed
      supported argumentEquality insertion targetWF
  exact ⟨reducedBody, reducedType, endpointEquality.hasType.1, endpointEquality, targetType⟩

private theorem argumentEqualityKeepsTheActualDeclaredDomain
    {env : VEnv} {universes : List Name} {original : VLCtx}
    {originalDomain originalArgument reducedArgument : VExpr} {removalLift : Lift}
    (equality : env.IsDefEq universes.length original.toCtx
      originalArgument (reducedArgument.lift' removalLift) originalDomain) :
    env.HasType universes.length original.toCtx originalArgument originalDomain ∧
    env.HasType universes.length original.toCtx (reducedArgument.lift' removalLift) originalDomain :=
  equality.hasType

private theorem historicalEqualityIsConvertedToTheActualDomain
    {env : VEnv} {universes : List Name} {smaller original aligned target : VLCtx}
    {removalLift insertionLift : Lift}
    {originalDomain reducedDomain bodySemantic historicalArgument reducedArgument historicalDomain : VExpr}
    {body : Expr} {domainLevel level : VLevel}
    (envWF : env.WF) (removal : VLCtx.FVLift' smaller aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' removalLift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ smaller.fvars))
    (historicalEquality : env.IsDefEq universes.length original.toCtx
      historicalArgument (reducedArgument.lift' removalLift) historicalDomain)
    (historicalArgumentType : env.HasType universes.length original.toCtx historicalArgument originalDomain)
    (insertion : VLCtx.FVLift' smaller target 0 insertionLift 0)
    (targetWF : target.WF env universes.length) :
    EndpointRebaseReceipt env universes smaller original aligned target removalLift insertionLift originalDomain reducedDomain
      body bodySemantic domainLevel level historicalArgument reducedArgument := by
  have argumentEquality := historicalEquality.toU.of_l envWF contexts.wf.toCtx historicalArgumentType
  exact translated.strengthenSubstitutionStageEndpointRebased envWF removal contexts domainEquality typed closed
    supported argumentEquality insertion targetWF

private def retained : FVarId := ⟨`StageEndpointRebaseRetained⟩
private def suffix : FVarId := ⟨`StageEndpointRebaseSuffix⟩
private def discarded : FVarId := ⟨`StageEndpointRebaseDiscarded⟩
private def insertedFirst : FVarId := ⟨`StageEndpointRebaseInsertedFirst⟩
private def insertedSecond : FVarId := ⟨`StageEndpointRebaseInsertedSecond⟩
private def absent : FVarId := ⟨`StageEndpointRebaseAbsent⟩
private def domain : VExpr := .sort .zero
private def domainLevel : VLevel := .succ .zero
private def stageLevel : VLevel := .imax .zero (.imax .zero .zero)
private def base : VLCtx := [(some (retained, []), .vlam domain)]
private def smaller : VLCtx := (some (suffix, []), .vlam domain) :: base
private def aligned : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (discarded, []), .vlam domain) :: base
private def target : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (insertedFirst, []), .vlam domain) ::
    (some (insertedSecond, []), .vlam domain) :: base
private def removalLift : Lift := .cons (.skip .refl)
private def insertionLift : Lift := .cons (.skip (.skip .refl))
private def nativeBody : Expr :=
  .forallE `formalUse (.bvar 0)
    (.forallE `suffixUse (.fvar suffix) (.fvar retained) .default) .default
private def originalBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 5))
private def reducedBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 4))
private def nonliteralDomain : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) domain
private def originalArgument : VExpr := .app (.lam domain (.bvar 3)) (.bvar 1)
private def reducedArgument : VExpr := .bvar 1

private theorem extendDomainWF (env : VEnv) (context : VLCtx) (identifier : FVarId)
    (contextWF : context.WF env 0) (fresh : identifier ∉ context.fvars) :
    VLCtx.WF env 0 ((some (identifier, []), .vlam domain) :: context) := by
  refine ⟨contextWF, ?_, domainLevel, .sortDF (by trivial) (by trivial) rfl⟩
  rintro selected dependencies equality
  cases equality
  exact ⟨fresh, by simp⟩

private theorem baseWF (env : VEnv) : base.WF env 0 :=
  extendDomainWF env [] retained (by trivial) (by simp [VLCtx.fvars])

private theorem smallerWF (env : VEnv) : smaller.WF env 0 :=
  extendDomainWF env base suffix (baseWF env) (by simp [base, VLCtx.fvars, suffix, retained])

private theorem alignedWF (env : VEnv) : aligned.WF env 0 := by
  have middleWF := extendDomainWF env base discarded (baseWF env)
    (by simp [base, VLCtx.fvars, discarded, retained])
  exact extendDomainWF env _ suffix middleWF
    (by simp [base, VLCtx.fvars, suffix, discarded, retained])

private theorem selectedSuffixRemoval : VLCtx.FVLift' smaller aligned 0 removalLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (discarded, []) (.vlam domain) .refl)

private theorem targetWF (env : VEnv) : target.WF env 0 := by
  have secondWF := extendDomainWF env base insertedSecond (baseWF env)
    (by simp [base, VLCtx.fvars, insertedSecond, retained])
  have firstWF := extendDomainWF env _ insertedFirst secondWF
    (by simp [base, VLCtx.fvars, insertedFirst, insertedSecond, retained])
  exact extendDomainWF env _ suffix firstWF
    (by simp [base, VLCtx.fvars, suffix, insertedFirst, insertedSecond, retained])

private theorem selectedSuffixInsertion : VLCtx.FVLift' smaller target 0 insertionLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (insertedFirst, []) (.vlam domain)
      (.skip_fvar (insertedSecond, []) (.vlam domain) .refl))

private theorem actualDomainEquality (env : VEnv) :
    env.IsDefEq 0 aligned.toCtx nonliteralDomain domain (.sort domainLevel) :=
  .beta (.bvar .zero) (.sortDF (by trivial) (by trivial) rfl)

private theorem formalTypedUnderTheActualDomain (env : VEnv) (envWF : env.WF) :
    env.HasType 0 (nonliteralDomain :: aligned.toCtx) (.bvar 0) domain :=
  .defeqDF ((actualDomainEquality env).weak envWF.ordered) (.bvar .zero)

private theorem originalNestedBodyTyped (env : VEnv) (envWF : env.WF) :
    env.HasType 0 (nonliteralDomain :: aligned.toCtx) originalBody (.sort stageLevel) :=
  .forallEDF (formalTypedUnderTheActualDomain env envWF)
    (.forallEDF (.bvar (.succ (.succ .zero)))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))

private theorem originalNestedBodyTranslated (env : VEnv) (envWF : env.WF) :
    TrExprS env [] ((none, .vlam nonliteralDomain) :: aligned) nativeBody originalBody :=
  .forallE ⟨.zero, formalTypedUnderTheActualDomain env envWF⟩
    ⟨.imax .zero .zero, .forallEDF (.bvar (.succ (.succ .zero)))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))⟩
    (.bvar rfl)
    (.forallE ⟨.zero, .bvar (.succ (.succ .zero))⟩
      ⟨.zero, .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))⟩ (.fvar rfl) (.fvar rfl))

private theorem stageBodyClosedAndSupported :
    Closed nativeBody 1 ∧ nativeBody.FVarsIn (· ∈ smaller.fvars) := by
  constructor
  · change (0 < 1) ∧ True ∧ True
    decide
  · simp [nativeBody, FVarsIn, smaller, base, VLCtx.fvars]

private theorem nonliteralHistoricalArgumentEquality (env : VEnv) :
    env.IsDefEq 0 aligned.toCtx originalArgument (reducedArgument.lift' removalLift) nonliteralDomain :=
  .defeqDF (actualDomainEquality env).symm
    (.beta (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ .zero)))

private theorem genuineRemovalAndIndependentInsertion (env : VEnv) (envWF : env.WF) :
    EndpointRebaseReceipt env [] smaller aligned aligned target removalLift insertionLift nonliteralDomain domain
      nativeBody originalBody domainLevel stageLevel originalArgument reducedArgument :=
  TrExprS.strengthenSubstitutionStageEndpointRebased envWF selectedSuffixRemoval
    (VLCtx.IsDefEq.refl envWF.ordered (alignedWF env)) (actualDomainEquality env)
    (originalNestedBodyTranslated env envWF) (originalNestedBodyTyped env envWF)
    stageBodyClosedAndSupported.1 stageBodyClosedAndSupported.2
    (nonliteralHistoricalArgumentEquality env) selectedSuffixInsertion (targetWF env)

private theorem genuineEndpointRebaseProjectsTypesAndEquality (env : VEnv) (envWF : env.WF) :
    ∃ reduced : VExpr,
      env.HasType 0 smaller.toCtx reducedArgument domain ∧
      env.HasType 0 smaller.toCtx (reduced.inst reducedArgument) (.sort stageLevel) ∧
      env.HasType 0 aligned.toCtx (originalBody.inst originalArgument) (.sort stageLevel) ∧
      env.HasType 0 aligned.toCtx ((reduced.inst reducedArgument).lift' removalLift) (.sort stageLevel) ∧
      env.IsDefEq 0 aligned.toCtx (originalBody.inst originalArgument)
        ((reduced.inst reducedArgument).lift' removalLift) (.sort stageLevel) ∧
      TrExprS env [] ((none, .vlam (domain.lift' insertionLift)) :: target)
        nativeBody (reduced.lift' insertionLift.cons) ∧
      env.HasType 0 ((domain.lift' insertionLift) :: target.toCtx)
        (reduced.lift' insertionLift.cons) (.sort stageLevel) ∧
      env.HasType 0 target.toCtx (reducedArgument.lift' insertionLift) (domain.lift' insertionLift) ∧
      env.HasType 0 target.toCtx
        ((reduced.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort stageLevel) ∧
      env.HasType 0 target.toCtx ((reduced.inst reducedArgument).lift' insertionLift) (.sort stageLevel) := by
  obtain ⟨reduced, _, _, _, _, _, _, reducedArgumentType, reducedType, endpointEquality,
    targetTranslation, targetBodyType, targetArgumentType, targetEndpointType⟩ :=
    genuineRemovalAndIndependentInsertion env envWF
  have targetLiftedType : env.HasType 0 target.toCtx
      ((reduced.inst reducedArgument).lift' insertionLift) (.sort stageLevel) := by
    simpa only [VExpr.lift'_inst_hi] using targetEndpointType
  exact ⟨reduced, reducedArgumentType, reducedType, endpointEquality.hasType.1,
    endpointEquality.hasType.2, endpointEquality, targetTranslation, targetBodyType,
    targetArgumentType, targetEndpointType, targetLiftedType⟩

private theorem nonliteralDomainAndArgumentAreNotLiftedEndpointRebases :
    nonliteralDomain ≠ domain.lift' removalLift ∧
    originalArgument ≠ reducedArgument.lift' removalLift := by
  constructor <;> intro equality <;> cases equality

private theorem removedCoordinateHasNoLiftedPreimage (expression : VExpr) :
    expression.lift' removalLift ≠ .bvar 1 := by
  cases expression <;> simp [removalLift, VExpr.lift']
  case bvar position => cases position <;> simp [Lift.liftVar]

private theorem historicalArgumentHasNoLiteralStagePreimage (expression : VExpr) :
    expression.lift' removalLift ≠ originalArgument := by
  cases expression with
  | app function argument =>
    intro equality
    exact removedCoordinateHasNoLiftedPreimage argument (VExpr.app.inj equality).2
  | bvar | sort | const | lam | forallE => intro equality; cases equality

private theorem removalMustProtectTheSelectedSuffix :
    (VExpr.bvar 0).lift' removalLift = .bvar 0 ∧
    (VExpr.bvar 1).lift' removalLift = .bvar 2 ∧
    reducedBody.lift' removalLift.cons ≠ reducedBody.lift' (Lift.skip .refl).cons := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem protectedBodyHasDistinctFormalSuffixAndBaseCoordinates :
    reducedBody.lift' removalLift.cons = originalBody ∧
    reducedArgument.lift' removalLift = .bvar 2 := ⟨rfl, rfl⟩

private theorem bodyLiftMustProtectTheStageFormal :
    reducedBody.lift' removalLift.cons ≠ reducedBody.lift' removalLift := by
  intro equality
  cases equality

private theorem argumentsMustNotReceiveTheBodyConsLift :
    reducedArgument.lift' removalLift ≠ reducedArgument.lift' removalLift.cons := by
  intro equality
  cases equality

private theorem endpointNormalizationUsesPlainRemovalLift :
    (reducedBody.inst reducedArgument).lift' removalLift =
      (reducedBody.lift' removalLift.cons).inst (reducedArgument.lift' removalLift) ∧
    (reducedBody.inst reducedArgument).lift' removalLift =
      .forallE (.bvar 2) (.forallE (.bvar 1) (.bvar 4)) ∧
    originalBody.inst originalArgument ≠ (reducedBody.inst reducedArgument).lift' removalLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem independentRemovalAndInsertionCoordinates :
    (VExpr.bvar 1).lift' removalLift = .bvar 2 ∧
    (VExpr.bvar 1).lift' insertionLift = .bvar 3 ∧ removalLift ≠ insertionLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem targetBodyProtectsFormalSuffixAndBaseCoordinates :
    reducedBody.lift' insertionLift.cons = .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6)) ∧
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' insertionLift := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private theorem targetArgumentsDomainsAndEndpointsUsePlainContextLift :
    reducedArgument.lift' insertionLift = .bvar 3 ∧
    reducedArgument.lift' insertionLift ≠ reducedArgument.lift' insertionLift.cons ∧
    (VExpr.bvar 1).lift' insertionLift ≠ (VExpr.bvar 1).lift' insertionLift.cons ∧
    (reducedBody.inst reducedArgument).lift' insertionLift ≠
      (reducedBody.inst reducedArgument).lift' insertionLift.cons := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem targetInsertionMustProtectTheSelectedSuffix :
    (VExpr.bvar 0).lift' insertionLift = .bvar 0 ∧
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' (Lift.skip (.skip .refl)).cons := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private theorem endpointNormalizationUsesPlainInsertionLift :
    (reducedBody.inst reducedArgument).lift' insertionLift =
      (reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift) ∧
    (reducedBody.inst reducedArgument).lift' insertionLift =
      .forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5)) ∧
    (reducedBody.inst reducedArgument).lift' insertionLift ≠
      (reducedBody.inst reducedArgument).lift' removalLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem targetContextIsIndependentOfTheOriginalContext :
    target.toCtx.length = 4 ∧ aligned.toCtx.length = 3 ∧ smaller.toCtx.length = 2 ∧
    target.toCtx ≠ aligned.toCtx := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem originalAndReducedContextsAreNotInterchangeable :
    aligned.toCtx.length = 3 ∧ smaller.toCtx.length = 2 ∧ aligned.toCtx ≠ smaller.toCtx := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem droppedAndMissingFVarsCannotSupplyBodySupport :
    ¬(Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) ∧
    ¬(Expr.fvar absent).FVarsIn (· ∈ smaller.fvars) := by
  simp [FVarsIn, smaller, base, VLCtx.fvars, discarded, absent, suffix, retained]

private theorem originalTranslationDoesNotReplaceSmallerSupport (env : VEnv) :
    TrExprS env [] ((none, .vlam nonliteralDomain) :: aligned) (.fvar discarded) (.bvar 2) ∧
    ¬(Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) :=
  ⟨.fvar rfl, droppedAndMissingFVarsCannotSupplyBodySupport.1⟩

private theorem formalBinderNeedsClosedOneRatherThanClosedZero :
    Closed nativeBody 1 ∧ ¬Closed nativeBody 0 ∧ ¬Closed (.bvar 1) 1 := by
  refine ⟨stageBodyClosedAndSupported.1, ?_, ?_⟩
  · simp [nativeBody, Closed]
  · change ¬1 < 1
    decide

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .const _ _ => [2]
  | .app function argument => 3 :: (semanticShape function ++ semanticShape argument)
  | .lam binder body => 4 :: (semanticShape binder ++ semanticShape body)
  | .forallE binder body => 5 :: (semanticShape binder ++ semanticShape body)

private def sourceClosedAt : Expr → Nat → Bool
  | .bvar position, depth => position < depth
  | .fvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => true
  | .mvar _, _ => false
  | .app function argument, depth => sourceClosedAt function depth && sourceClosedAt argument depth
  | .lam _ binder body _, depth | .forallE _ binder body _, depth =>
    sourceClosedAt binder depth && sourceClosedAt body (depth + 1)
  | .letE _ binder value body _, depth =>
    sourceClosedAt binder depth && sourceClosedAt value depth && sourceClosedAt body (depth + 1)
  | .proj _ _ body, depth | .mdata _ body, depth => sourceClosedAt body depth

private def runtimeControls : MetaM Unit := do
  let conditions := [
    (sourceClosedAt nativeBody 1, "nested stage body is Closed 1"),
    (!sourceClosedAt nativeBody 0, "stage formal is not Closed 0"),
    (!sourceClosedAt (.bvar 1) 1, "second loose formal is not Closed 1"),
    (nativeBody.fvarsList == [suffix, retained], "body uses retained suffix and base"),
    (smaller.fvars.contains suffix, "selected suffix remains supported"),
    (smaller.fvars.contains retained, "retained base remains supported"),
    (!smaller.fvars.contains discarded, "removed fvar lacks support"),
    (!smaller.fvars.contains absent, "absent fvar lacks support"),
    (aligned.fvars.contains discarded, "removed fvar existed in source"),
    (target.fvars.contains insertedFirst && target.fvars.contains insertedSecond, "target has two distinct inserted declarations"),
    (target.toCtx.length == 4, "target context is not the original chronology context"),
    (aligned.toCtx.length == 3 && smaller.toCtx.length == 2, "original and reduced contexts differ"),
    (semanticShape nonliteralDomain != semanticShape (domain.lift' removalLift), "actual domain is nonliteral beta syntax"),
    (semanticShape originalArgument != semanticShape (reducedArgument.lift' removalLift), "historical argument is not literal lift syntax"),
    (semanticShape originalArgument == semanticShape (.app (.lam domain (.bvar 3)) (.bvar 1)),
      "historical beta argument mentions the removed coordinate"),
    (semanticShape ((VExpr.bvar 0).lift' removalLift) == [0, 0], "removal protects selected suffix"),
    (semanticShape ((VExpr.bvar 1).lift' removalLift) == [0, 2], "removal coordinate skips one"),
    (semanticShape (reducedBody.lift' removalLift.cons) == semanticShape originalBody, "removal rebuilds original body"),
    (semanticShape (reducedBody.lift' removalLift.cons) != semanticShape (reducedBody.lift' removalLift),
      "missing formal cons changes nested suffix"),
    (semanticShape (reducedArgument.lift' removalLift) != semanticShape (reducedArgument.lift' removalLift.cons),
      "body cons lift is wrong for reduced argument"),
    (semanticShape (reducedBody.lift' removalLift.cons) !=
      semanticShape (reducedBody.lift' (Lift.skip .refl).cons), "wrong suffix cutoff changes body"),
    (semanticShape ((reducedBody.inst reducedArgument).lift' removalLift) ==
      semanticShape ((reducedBody.lift' removalLift.cons).inst (reducedArgument.lift' removalLift)),
      "lifted reduced endpoint agrees with protected body instantiation"),
    (semanticShape ((reducedBody.inst reducedArgument).lift' removalLift) ==
      semanticShape (.forallE (.bvar 2) (.forallE (.bvar 1) (.bvar 4))), "reduced endpoint coordinates are exact"),
    (semanticShape (originalBody.inst originalArgument) !=
      semanticShape ((reducedBody.inst reducedArgument).lift' removalLift), "endpoint agreement is not literal syntax equality"),
    (semanticShape (reducedBody.lift' insertionLift.cons) ==
      semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6))), "target protects formal and nested suffix"),
    (semanticShape (reducedBody.lift' insertionLift.cons) != semanticShape (reducedBody.lift' insertionLift),
      "target body requires the formal cons lift"),
    (semanticShape (reducedArgument.lift' insertionLift) == [0, 3], "target argument uses plain insertion lift"),
    (semanticShape ((VExpr.bvar 1).lift' insertionLift) != semanticShape ((VExpr.bvar 1).lift' insertionLift.cons),
      "target domain syntax must use its context coordinates"),
    (semanticShape ((reducedBody.inst reducedArgument).lift' insertionLift) ==
      semanticShape ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)),
      "target endpoint commutes with reduced instantiation"),
    (semanticShape ((reducedBody.inst reducedArgument).lift' insertionLift) ==
      semanticShape (.forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5))), "target endpoint has exact independent coordinates"),
    (semanticShape ((reducedBody.inst reducedArgument).lift' insertionLift) !=
      semanticShape ((reducedBody.inst reducedArgument).lift' removalLift), "target insertion does not reuse original removal"),
    (semanticShape (reducedBody.lift' insertionLift.cons) !=
      semanticShape (reducedBody.lift' (Lift.skip (.skip .refl)).cons), "target insertion protects selected suffix cutoff")]
  for (condition, label) in conditions do
    unless condition do throwError "endpoint-rebase runtime failed: {label}"
  logInfo m!"endpoint-rebase runtime: {conditions.length} independent removal/insertion, formal/nested/suffix coordinates, nonliteral actual domain, historical argument without stage preimage, target endpoint normalization, support and closure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "endpoint-rebase audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do throwError "endpoint-rebase unexpected axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (expected : Nat) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "endpoint-rebase audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "endpoint-rebase module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == expected do
    throwError "endpoint-rebase module declaration manifest changed: {moduleName}; expected {expected}, got {declarations}"
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditExactInheritedDependencies (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "endpoint-rebase exact inherited dependency manifest changed: {name}"
  logInfo m!"{name}: exact four inherited logical/typing axioms; no native/container/range/abstraction interfaces"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let proofControls := [``endpointForwardsEveryReceipt, ``semanticHistoricalArgumentNeedsOnlyActualDomainEquality,
    ``argumentEqualityKeepsTheActualDeclaredDomain, ``historicalEqualityIsConvertedToTheActualDomain,
    ``extendDomainWF, ``baseWF, ``smallerWF, ``alignedWF, ``targetWF,
    ``selectedSuffixRemoval, ``selectedSuffixInsertion, ``actualDomainEquality, ``formalTypedUnderTheActualDomain,
    ``originalNestedBodyTyped, ``originalNestedBodyTranslated, ``stageBodyClosedAndSupported,
    ``nonliteralHistoricalArgumentEquality, ``genuineRemovalAndIndependentInsertion, ``genuineEndpointRebaseProjectsTypesAndEquality,
    ``nonliteralDomainAndArgumentAreNotLiftedEndpointRebases, ``removedCoordinateHasNoLiftedPreimage,
    ``historicalArgumentHasNoLiteralStagePreimage, ``removalMustProtectTheSelectedSuffix,
    ``protectedBodyHasDistinctFormalSuffixAndBaseCoordinates, ``bodyLiftMustProtectTheStageFormal,
    ``argumentsMustNotReceiveTheBodyConsLift, ``endpointNormalizationUsesPlainRemovalLift,
    ``independentRemovalAndInsertionCoordinates, ``targetBodyProtectsFormalSuffixAndBaseCoordinates,
    ``targetArgumentsDomainsAndEndpointsUsePlainContextLift, ``targetInsertionMustProtectTheSelectedSuffix,
    ``endpointNormalizationUsesPlainInsertionLift, ``targetContextIsIndependentOfTheOriginalContext,
    ``originalAndReducedContextsAreNotInterchangeable, ``droppedAndMissingFVarsCannotSupplyBodySupport,
    ``originalTranslationDoesNotReplaceSmallerSupport, ``formalBinderNeedsClosedOneRatherThanClosedZero]
  for name in proofControls do auditDeclaration name inherited
  auditDeclaration ``EndpointRebaseReceipt inherited
  for name in [``retained, ``suffix, ``discarded, ``insertedFirst, ``insertedSecond, ``absent, ``domain, ``domainLevel, ``stageLevel,
      ``base, ``smaller, ``aligned, ``target, ``removalLift, ``insertionLift, ``nativeBody, ``originalBody, ``reducedBody,
      ``nonliteralDomain, ``originalArgument, ``reducedArgument, ``semanticShape, ``sourceClosedAt,
      ``runtimeControls, ``auditDeclaration, ``auditModule, ``auditExactInheritedDependencies] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveSubstitutionStageEndpointRebase 2 inherited
  auditExactInheritedDependencies ``TrExprS.strengthenSubstitutionStageEndpointRebased inherited
  runtimeControls
  logInfo m!"endpoint-rebase tests: {proofControls.length} proof controls; all thirteen receipts forwarded; nonliteral actual domain and historical argument with no literal stage preimage; retained formal/base/suffix under nested binders; original endpoint equality retained in its original context; target body translation and body/argument/endpoint type projections; independent removal/insertion, support, closure, context and plain-versus-cons lift negatives"

end InductiveSubstitutionStageEndpointRebaseTest
