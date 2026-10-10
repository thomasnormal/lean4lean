import Lean4Lean.Verify.InductiveIndexDomainStrengthening

namespace Lean4Lean
open Lean hiding Environment Exception
open VEnv

theorem TrExprS.strengthenSubstitutionBodyIsType
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {lift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
    {body : Expr} {domainLevel level : VLevel}
    (envWF : env.WF)
    (weakening : VLCtx.FVLift' smaller aligned 0 lift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' lift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1)
    (supported : body.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reducedBody,
      VLCtx.FVLift' ((none, .vlam reducedDomain) :: smaller)
        ((none, .vlam (reducedDomain.lift' lift)) :: aligned) 1 lift 1 ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam originalDomain) :: original)
        ((none, .vlam (reducedDomain.lift' lift)) :: aligned) ∧
      env.HasType universes.length smaller.toCtx reducedDomain (.sort domainLevel) ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: smaller) body reducedBody ∧
      env.HasType universes.length (reducedDomain :: smaller.toCtx) reducedBody (.sort level) ∧
      env.IsDefEq universes.length (originalDomain :: original.toCtx)
        bodySemantic (reducedBody.lift' lift.cons) (.sort level) := by
  have bodyWeakening : VLCtx.FVLift' ((none, .vlam reducedDomain) :: smaller)
      ((none, .vlam (reducedDomain.lift' lift)) :: aligned) 1 lift 1 :=
    weakening.cons_bvar (.vlam reducedDomain)
  have bodyContexts : VLCtx.IsDefEq env universes.length
      ((none, .vlam originalDomain) :: original)
      ((none, .vlam (reducedDomain.lift' lift)) :: aligned) :=
    contexts.cons nofun (.vlam domainEquality)
  have alignedWF := (contexts.symm envWF.ordered).wf
  have liftedDomainTyped := domainEquality.hasType.2.defeqDFC envWF.ordered contexts.defeqCtx
  have reducedDomainTyped : env.HasType universes.length smaller.toCtx reducedDomain (.sort domainLevel) :=
    (HasType.weak'_iff envWF alignedWF.toCtx weakening.toCtx).mp liftedDomainTyped
  obtain ⟨reducedBody, reducedTranslation, reducedType, bodyEquality⟩ :=
    TrExprS.strengthenIsTypeAt envWF bodyWeakening bodyContexts translated typed closed
      (by simpa only [VLCtx.fvars_cons_none] using supported)
  exact ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped,
    reducedTranslation, reducedType, bodyEquality⟩

end Lean4Lean
