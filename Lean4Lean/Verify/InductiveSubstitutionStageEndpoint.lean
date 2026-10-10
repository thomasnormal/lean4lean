import Lean4Lean.Verify.InductiveSubstitutionStageBody

namespace Lean4Lean
open Lean hiding Environment Exception
open VEnv

theorem TrExprS.strengthenSubstitutionStageEndpoint
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {removalLift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
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
      originalArgument (reducedArgument.lift' removalLift) originalDomain) :
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
        ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) := by
  obtain ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality⟩ :=
    TrExprS.strengthenSubstitutionBodyIsType envWF removal contexts domainEquality translated typed closed supported
  have alignedWF := (contexts.symm envWF.ordered).wf
  have smallerWF := removal.wf envWF alignedWF
  have liftedArgumentTyped : env.HasType universes.length aligned.toCtx
      (reducedArgument.lift' removalLift) (reducedDomain.lift' removalLift) :=
    (VEnv.IsDefEq.defeqDF domainEquality argumentEquality.hasType.2).defeqDFC envWF.ordered contexts.defeqCtx
  have reducedArgumentTyped : env.HasType universes.length smaller.toCtx reducedArgument reducedDomain :=
    (HasType.weak'_iff envWF alignedWF.toCtx removal.toCtx).mp liftedArgumentTyped
  have reducedEndpointTyped : env.HasType universes.length smaller.toCtx
      (reducedBody.inst reducedArgument) (.sort level) := by
    simpa only [VExpr.inst] using
      VEnv.IsDefEq.instDF envWF.ordered smallerWF.toCtx reducedBodyTyped reducedArgumentTyped
  have endpointEquality : env.IsDefEq universes.length original.toCtx
      (bodySemantic.inst originalArgument) ((reducedBody.inst reducedArgument).lift' removalLift)
      (.sort level) := by
    simpa only [VExpr.lift'_inst_hi, VExpr.inst] using
      VEnv.IsDefEq.instDF envWF.ordered contexts.wf.toCtx bodyEquality argumentEquality
  exact ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality⟩

end Lean4Lean
