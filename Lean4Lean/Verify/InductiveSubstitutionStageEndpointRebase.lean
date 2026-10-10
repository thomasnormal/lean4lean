import Lean4Lean.Verify.InductiveSubstitutionStageEndpoint

namespace Lean4Lean
open Lean hiding Environment Exception
open VEnv

theorem TrExprS.strengthenSubstitutionStageEndpointRebased
    {env : VEnv} {universes : List Name} {smaller original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
    {originalArgument reducedArgument : VExpr} {body : Expr} {domainLevel level : VLevel}
    (envWF : env.WF)
    (removal : VLCtx.FVLift' smaller aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' removalLift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1)
    (supported : body.FVarsIn (· ∈ smaller.fvars))
    (argumentEquality : env.IsDefEq universes.length original.toCtx
      originalArgument (reducedArgument.lift' removalLift) originalDomain)
    (insertion : VLCtx.FVLift' smaller target 0 insertionLift 0)
    (targetWF : target.WF env universes.length) :
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
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) := by
  obtain ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality⟩ :=
    TrExprS.strengthenSubstitutionStageEndpoint envWF removal contexts domainEquality translated typed
      closed supported argumentEquality
  have targetDomainTyped : env.HasType universes.length target.toCtx
      (reducedDomain.lift' insertionLift) (.sort domainLevel) := by
    simpa only [VExpr.lift'] using reducedDomainTyped.weak' envWF.ordered insertion.toCtx
  have targetBodyWF : VLCtx.WF env universes.length
      ((none, .vlam (reducedDomain.lift' insertionLift)) :: target) :=
    ⟨targetWF, nofun, domainLevel, targetDomainTyped⟩
  have targetBodyTranslation := reducedBodyTranslation.weakFV' envWF.ordered
    (insertion.cons_bvar (.vlam reducedDomain)) targetBodyWF
  have targetBodyTyped : env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
      (reducedBody.lift' insertionLift.cons) (.sort level) := by
    simpa only [VExpr.lift'] using reducedBodyTyped.weak' envWF.ordered insertion.toCtx.cons
  have targetArgumentTyped := reducedArgumentTyped.weak' envWF.ordered insertion.toCtx
  have targetEndpointTyped : env.HasType universes.length target.toCtx
      ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) := by
    simpa only [VExpr.lift'_inst_hi, VExpr.lift'] using reducedEndpointTyped.weak' envWF.ordered insertion.toCtx
  exact ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality,
    targetBodyTranslation, targetBodyTyped, targetArgumentTyped, targetEndpointTyped⟩

end Lean4Lean
