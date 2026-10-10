import Lean4Lean.Verify.InductiveParameterSubstitutionRebase

namespace Lean4Lean
open Lean hiding Environment Exception

theorem RetainedFVarPrefixAgreement.instantiatePairIsTypeRebasedCore
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
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
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes
      ((none, .vlam innerDomain) :: (none, .vlam originalOuterArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 2) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedInnerArgument reducedInnerArgumentType reducedOuterArgument reducedOuterArgumentType reducedSemantic,
      source.find? (.inr innerIdentifier) = some (reducedInnerArgument, reducedInnerArgumentType) ∧
      TrExprS env universes source (.fvar innerIdentifier) reducedInnerArgument ∧
      env.HasType universes.length source.toCtx reducedInnerArgument reducedInnerArgumentType ∧
      env.IsDefEq universes.length original.toCtx originalInnerArgument
        (reducedInnerArgument.lift' removalLift) originalInnerArgumentType ∧
      Closed (body.instantiate1' (.fvar innerIdentifier)) 1 ∧
      (body.instantiate1' (.fvar innerIdentifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes ((none, .vlam originalOuterArgumentType) :: original)
        (body.instantiate1' (.fvar innerIdentifier)) (bodySemantic.inst originalInnerArgument.lift) ∧
      env.HasType universes.length (originalOuterArgumentType :: original.toCtx)
        (bodySemantic.inst originalInnerArgument.lift) (.sort level) ∧
      source.find? (.inr outerIdentifier) = some (reducedOuterArgument, reducedOuterArgumentType) ∧
      TrExprS env universes source (.fvar outerIdentifier) reducedOuterArgument ∧
      env.HasType universes.length source.toCtx reducedOuterArgument reducedOuterArgumentType ∧
      Closed ((body.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier)) 0 ∧
      ((body.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier)).FVarsIn
        (· ∈ source.fvars) ∧
      TrExprS env universes original
        ((body.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier))
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument) ∧
      env.HasType universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift))
        (.sort level) ∧
      TrExprS env universes source
        ((body.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier)) reducedSemantic ∧
      env.HasType universes.length source.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift))
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      TrExprS env universes target
        ((body.instantiate1' (.fvar innerIdentifier)).instantiate1' (.fvar outerIdentifier))
        (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        (reducedSemantic.lift' insertionLift) (.sort level) := by
  obtain ⟨reducedInnerArgument, reducedInnerArgumentType, receiptInnerArgument, receiptInnerType, _,
    reducedInnerLookup, reducedInnerTranslation, reducedInnerTyped, receiptInnerLookup, _, _, _,
    innerEquality⟩ := receipt.lookups innerPosition innerIdentifier innerSelected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (receiptInnerLookup.symm.trans innerLookup))
  have raisedInnerLookup :
      VLCtx.find? ((none, .vlam originalOuterArgumentType) :: original) (.inr innerIdentifier) =
        some (receiptInnerArgument.lift, receiptInnerType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, innerLookup]
  have raisedInnerTranslation : TrExprS env universes
      ((none, .vlam originalOuterArgumentType) :: original)
      (.fvar innerIdentifier) receiptInnerArgument.lift := .fvar raisedInnerLookup
  have intermediateTranslation :=
    bodyTranslated.inst envWF.ordered raisedInnerArgumentTyped raisedInnerTranslation
  have intermediateTyped : env.HasType universes.length
      (originalOuterArgumentType :: original.toCtx)
      (bodySemantic.inst receiptInnerArgument.lift) (.sort level) := by
    simpa only [VExpr.inst] using bodyTyped.instN envWF.ordered .zero raisedInnerArgumentTyped
  have intermediateClosed : Closed (body.instantiate1' (.fvar innerIdentifier)) 1 :=
    bodyClosed.instantiate1_offset
      (replacementClosed := (show Closed (.fvar innerIdentifier) 0 from trivial)) (Nat.zero_le 1)
  have innerSupported : (Expr.fvar innerIdentifier).FVarsIn (· ∈ source.fvars) :=
    receipt.transported.sourceRetained (List.mem_of_getElem? innerSelected)
  have intermediateSupported := bodySupported.instantiate1 innerSupported
  obtain ⟨reducedOuterArgument, reducedOuterArgumentType, reducedSemantic, reducedOuterLookup,
    reducedOuterTranslation, reducedOuterTyped, substitutedClosed, substitutedSupported,
    substitutedTranslation, substitutedTyped, outerEquality, reducedTranslation, reducedType,
    rebaseEquality, alternativeEquality, targetTranslation, targetType⟩ :=
    receipt.instantiateIsTypeRebasedCore envWF removal contexts insertion targetWF
      outerPosition outerIdentifier outerSelected outerLookup intermediateTranslation
      intermediateTyped intermediateClosed intermediateSupported
  exact ⟨reducedInnerArgument, reducedInnerArgumentType, reducedOuterArgument, reducedOuterArgumentType,
    reducedSemantic, reducedInnerLookup, reducedInnerTranslation, reducedInnerTyped, innerEquality,
    intermediateClosed, intermediateSupported, intermediateTranslation, intermediateTyped,
    reducedOuterLookup, reducedOuterTranslation, reducedOuterTyped, substitutedClosed,
    substitutedSupported, substitutedTranslation, substitutedTyped, outerEquality,
    reducedTranslation, reducedType, rebaseEquality, alternativeEquality, targetTranslation, targetType⟩

theorem RetainedFVarPrefixAgreement.instantiatePairIsTypeRebased
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
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
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes
      ((none, .vlam innerDomain) :: (none, .vlam originalOuterArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: original.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 2) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedInnerArgument reducedInnerArgumentType reducedOuterArgument reducedOuterArgumentType reducedSemantic,
      source.find? (.inr innerIdentifier) = some (reducedInnerArgument, reducedInnerArgumentType) ∧
      TrExprS env universes source (.fvar innerIdentifier) reducedInnerArgument ∧
      env.HasType universes.length source.toCtx reducedInnerArgument reducedInnerArgumentType ∧
      env.IsDefEq universes.length original.toCtx originalInnerArgument
        (reducedInnerArgument.lift' removalLift) originalInnerArgumentType ∧
      Closed (body.instantiate1 (.fvar innerIdentifier)) 1 ∧
      (body.instantiate1 (.fvar innerIdentifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes ((none, .vlam originalOuterArgumentType) :: original)
        (body.instantiate1 (.fvar innerIdentifier)) (bodySemantic.inst originalInnerArgument.lift) ∧
      env.HasType universes.length (originalOuterArgumentType :: original.toCtx)
        (bodySemantic.inst originalInnerArgument.lift) (.sort level) ∧
      source.find? (.inr outerIdentifier) = some (reducedOuterArgument, reducedOuterArgumentType) ∧
      TrExprS env universes source (.fvar outerIdentifier) reducedOuterArgument ∧
      env.HasType universes.length source.toCtx reducedOuterArgument reducedOuterArgumentType ∧
      Closed ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)) 0 ∧
      ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)).FVarsIn
        (· ∈ source.fvars) ∧
      TrExprS env universes original
        ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier))
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument) ∧
      env.HasType universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift))
        (.sort level) ∧
      TrExprS env universes source
        ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)) reducedSemantic ∧
      env.HasType universes.length source.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift))
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      TrExprS env universes target
        ((body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier))
        (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        (reducedSemantic.lift' insertionLift) (.sort level) := by
  simpa only [Expr.instantiate1_eq] using receipt.instantiatePairIsTypeRebasedCore envWF removal
    contexts insertion targetWF outerPosition outerIdentifier outerSelected innerPosition
    innerIdentifier innerSelected outerLookup innerLookup raisedInnerArgumentTyped bodyTranslated
    bodyTyped bodyClosed bodySupported

end Lean4Lean
