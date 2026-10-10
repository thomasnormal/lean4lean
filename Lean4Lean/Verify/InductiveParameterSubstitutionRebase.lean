import Lean4Lean.Verify.InductiveParameterSubstitution
import Lean4Lean.Verify.InductiveIndexRebaseTyping
import Lean4Lean.Verify.InductiveAnnotationModelClosed

namespace Lean4Lean
open Lean hiding Environment Exception

theorem RetainedFVarPrefixAgreement.instantiateIsTypeRebasedCore
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
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx)
      bodySemantic (.sort level))
    (bodyClosed : Closed body 1) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedArgumentType reducedSemantic,
      source.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.HasType universes.length source.toCtx reducedArgument reducedArgumentType ∧
      Closed (body.instantiate1' (.fvar identifier)) 0 ∧
      (body.instantiate1' (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1' (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length original.toCtx (bodySemantic.inst originalArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument)
        (bodySemantic.inst (reducedArgument.lift' removalLift)) (.sort level) ∧
      TrExprS env universes source (body.instantiate1' (.fvar identifier)) reducedSemantic ∧
      env.HasType universes.length source.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (reducedSemantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst (reducedArgument.lift' removalLift))
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      TrExprS env universes target (body.instantiate1' (.fvar identifier))
        (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        (reducedSemantic.lift' insertionLift) (.sort level) := by
  obtain ⟨reducedArgument, reducedArgumentType, _, reducedLookup, reducedArgumentTranslation,
    reducedArgumentTyped, substitutedSupport, substitutedTranslation, substitutedTyped, _,
    argumentEquality, _⟩ := receipt.instantiateCore envWF contexts.wf position identifier selected
      originalLookup bodyTranslated bodyTyped bodySupported
  have substitutedClosed : Closed (body.instantiate1' (.fvar identifier)) 0 :=
    bodyClosed.instantiate1_offset (replacementClosed := (show Closed (.fvar identifier) 0 from trivial))
      (Nat.zero_le 0)
  have substitutedType : env.HasType universes.length original.toCtx
      (bodySemantic.inst originalArgument) (.sort level) := by
    simpa only [VExpr.inst] using substitutedTyped
  have substitutedArgumentEquality : env.IsDefEq universes.length original.toCtx
      (bodySemantic.inst originalArgument)
      (bodySemantic.inst (reducedArgument.lift' removalLift)) (.sort level) := by
    simpa only [VExpr.inst] using argumentEquality
  obtain ⟨reducedSemantic, reducedTranslation, reducedType, rebasedEquality,
    targetTranslation, targetType⟩ := TrExprS.rebaseIsType envWF removal contexts insertion targetWF
      substitutedTranslation substitutedType substitutedClosed substitutedSupport
  have alternativeEquality := substitutedArgumentEquality.symm.trans rebasedEquality
  exact ⟨reducedArgument, reducedArgumentType, reducedSemantic, reducedLookup,
    reducedArgumentTranslation, reducedArgumentTyped, substitutedClosed, substitutedSupport,
    substitutedTranslation, substitutedType, substitutedArgumentEquality, reducedTranslation,
    reducedType, rebasedEquality, alternativeEquality, targetTranslation, targetType⟩

theorem RetainedFVarPrefixAgreement.instantiateIsTypeRebased
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
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx)
      bodySemantic (.sort level))
    (bodyClosed : Closed body 1) (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedArgumentType reducedSemantic,
      source.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.HasType universes.length source.toCtx reducedArgument reducedArgumentType ∧
      Closed (body.instantiate1 (.fvar identifier)) 0 ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length original.toCtx (bodySemantic.inst originalArgument) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument)
        (bodySemantic.inst (reducedArgument.lift' removalLift)) (.sort level) ∧
      TrExprS env universes source (body.instantiate1 (.fvar identifier)) reducedSemantic ∧
      env.HasType universes.length source.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (reducedSemantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst (reducedArgument.lift' removalLift))
        (reducedSemantic.lift' removalLift) (.sort level) ∧
      TrExprS env universes target (body.instantiate1 (.fvar identifier))
        (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        (reducedSemantic.lift' insertionLift) (.sort level) := by
  simpa only [Expr.instantiate1_eq] using receipt.instantiateIsTypeRebasedCore envWF removal
    contexts insertion targetWF position identifier selected originalLookup bodyTranslated bodyTyped
    bodyClosed bodySupported

end Lean4Lean
