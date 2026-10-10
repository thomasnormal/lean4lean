import Lean4Lean.Verify.InductiveParameterPrefixAgreement
import Lean4Lean.Verify.InductiveSubstitutionStageEndpointRebase
import Lean4Lean.Verify.InductiveAnnotationModelClosed

namespace Lean4Lean
open Lean hiding Environment Exception

theorem RetainedFVarPrefixAgreement.instantiateStageIsTypeRebasedCore
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 1) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedDomain domainLevel reducedBody,
      source.find? (.inr identifier) = some (reducedArgument, reducedDomain) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.IsDefEq universes.length original.toCtx
        originalArgumentType (reducedDomain.lift' removalLift) (.sort domainLevel) ∧
      env.IsDefEq universes.length original.toCtx
        originalArgument (reducedArgument.lift' removalLift) originalArgumentType ∧
      VLCtx.FVLift' ((none, .vlam reducedDomain) :: source)
        ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) 1 removalLift 1 ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam originalArgumentType) :: original)
        ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) ∧
      env.HasType universes.length source.toCtx reducedDomain (.sort domainLevel) ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: source) body reducedBody ∧
      env.HasType universes.length (reducedDomain :: source.toCtx) reducedBody (.sort level) ∧
      env.IsDefEq universes.length (originalArgumentType :: original.toCtx)
        bodySemantic (reducedBody.lift' removalLift.cons) (.sort level) ∧
      env.HasType universes.length source.toCtx reducedArgument reducedDomain ∧
      env.HasType universes.length source.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx (bodySemantic.inst originalArgument)
        ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) ∧
      TrExprS env universes ((none, .vlam (reducedDomain.lift' insertionLift)) :: target)
        body (reducedBody.lift' insertionLift.cons) ∧
      env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
        (reducedBody.lift' insertionLift.cons) (.sort level) ∧
      env.HasType universes.length target.toCtx (reducedArgument.lift' insertionLift)
        (reducedDomain.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) ∧
      Closed (body.instantiate1' (.fvar identifier)) 0 ∧
      (body.instantiate1' (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1' (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      TrExprS env universes source (body.instantiate1' (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      TrExprS env universes target (.fvar identifier) (reducedArgument.lift' insertionLift) ∧
      TrExprS env universes target (body.instantiate1' (.fvar identifier))
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) := by
  obtain ⟨reducedArgument, reducedDomain, receiptArgument, receiptArgumentType, domainLevel,
    reducedLookup, reducedArgumentTranslation, _, receiptLookup, originalArgumentTranslation,
    originalArgumentTyped, domainEquality, argumentEquality⟩ := receipt.lookups position identifier selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (receiptLookup.symm.trans originalLookup))
  obtain ⟨reducedBody, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality,
    targetBodyTranslation, targetBodyTyped, targetArgumentTyped, targetEndpointTyped⟩ :=
    TrExprS.strengthenSubstitutionStageEndpointRebased envWF removal contexts domainEquality bodyTranslated
      bodyTyped bodyClosed bodySupported argumentEquality insertion targetWF
  have argumentSupported : (Expr.fvar identifier).FVarsIn (· ∈ source.fvars) :=
    receipt.transported.sourceRetained (List.mem_of_getElem? selected)
  have substitutedClosed : Closed (body.instantiate1' (.fvar identifier)) 0 :=
    bodyClosed.instantiate1_offset (replacementClosed := (show Closed (.fvar identifier) 0 from trivial))
      (Nat.zero_le 0)
  have substitutedSupport := bodySupported.instantiate1 argumentSupported
  have originalInstantiatedTranslation := bodyTranslated.inst envWF.ordered originalArgumentTyped
    originalArgumentTranslation
  have reducedInstantiatedTranslation := reducedBodyTranslation.inst envWF.ordered reducedArgumentTyped
    reducedArgumentTranslation
  have targetArgumentTranslation := reducedArgumentTranslation.weakFV' envWF.ordered insertion targetWF
  have targetInstantiatedTranslation := targetBodyTranslation.inst envWF.ordered targetArgumentTyped
    targetArgumentTranslation
  exact ⟨reducedArgument, reducedDomain, domainLevel, reducedBody, reducedLookup, reducedArgumentTranslation,
    domainEquality, argumentEquality, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality,
    targetBodyTranslation, targetBodyTyped, targetArgumentTyped, targetEndpointTyped, substitutedClosed,
    substitutedSupport, originalInstantiatedTranslation, reducedInstantiatedTranslation,
    targetArgumentTranslation, targetInstantiatedTranslation⟩

theorem RetainedFVarPrefixAgreement.instantiateStageIsTypeRebased
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 1) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedDomain domainLevel reducedBody,
      source.find? (.inr identifier) = some (reducedArgument, reducedDomain) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.IsDefEq universes.length original.toCtx
        originalArgumentType (reducedDomain.lift' removalLift) (.sort domainLevel) ∧
      env.IsDefEq universes.length original.toCtx
        originalArgument (reducedArgument.lift' removalLift) originalArgumentType ∧
      VLCtx.FVLift' ((none, .vlam reducedDomain) :: source)
        ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) 1 removalLift 1 ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam originalArgumentType) :: original)
        ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) ∧
      env.HasType universes.length source.toCtx reducedDomain (.sort domainLevel) ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: source) body reducedBody ∧
      env.HasType universes.length (reducedDomain :: source.toCtx) reducedBody (.sort level) ∧
      env.IsDefEq universes.length (originalArgumentType :: original.toCtx)
        bodySemantic (reducedBody.lift' removalLift.cons) (.sort level) ∧
      env.HasType universes.length source.toCtx reducedArgument reducedDomain ∧
      env.HasType universes.length source.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx (bodySemantic.inst originalArgument)
        ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) ∧
      TrExprS env universes ((none, .vlam (reducedDomain.lift' insertionLift)) :: target)
        body (reducedBody.lift' insertionLift.cons) ∧
      env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
        (reducedBody.lift' insertionLift.cons) (.sort level) ∧
      env.HasType universes.length target.toCtx (reducedArgument.lift' insertionLift)
        (reducedDomain.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) ∧
      Closed (body.instantiate1 (.fvar identifier)) 0 ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      TrExprS env universes source (body.instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      TrExprS env universes target (.fvar identifier) (reducedArgument.lift' insertionLift) ∧
      TrExprS env universes target (body.instantiate1 (.fvar identifier))
        ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) := by
  simpa only [Expr.instantiate1_eq] using receipt.instantiateStageIsTypeRebasedCore envWF removal
    contexts insertion targetWF position identifier selected originalLookup bodyTranslated bodyTyped
    bodyClosed bodySupported

end Lean4Lean
