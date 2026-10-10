import Lean4Lean.Verify.InductiveParameterPrefixAgreement

namespace Lean4Lean
open Lean hiding Environment Exception

theorem RetainedFVarPrefixAgreement.instantiateCore
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic resultType : VExpr}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx)
      bodySemantic resultType)
    (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedArgumentType level,
      source.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.HasType universes.length source.toCtx reducedArgument reducedArgumentType ∧
      (body.instantiate1' (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1' (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length original.toCtx
        (bodySemantic.inst originalArgument) (resultType.inst originalArgument) ∧
      env.HasType universes.length original.toCtx
        (bodySemantic.inst (reducedArgument.lift' lift))
        (resultType.inst (reducedArgument.lift' lift)) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (bodySemantic.inst (reducedArgument.lift' lift))
        (resultType.inst originalArgument) ∧
      env.IsDefEq universes.length original.toCtx
        (resultType.inst originalArgument) (resultType.inst (reducedArgument.lift' lift))
        (.sort level) := by
  obtain ⟨reducedArgument, reducedArgumentType, receiptArgument, receiptArgumentType, _,
    reducedLookup, reducedTranslation, reducedTyped, receiptLookup, argumentTranslation,
    argumentTyped, _, argumentEquality⟩ := receipt.lookups position identifier selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (receiptLookup.symm.trans originalLookup))
  obtain ⟨argumentLevel, argumentTypeTyped⟩ :=
    argumentTyped.isType envWF.ordered originalWF.toCtx
  have binderWF : OnCtx (receiptArgumentType :: original.toCtx) (env.IsType universes.length) :=
    ⟨originalWF.toCtx, argumentLevel, argumentTypeTyped⟩
  obtain ⟨level, resultTypeTyped⟩ := bodyTyped.isType envWF.ordered binderWF
  have resultTranslation := bodyTranslated.inst envWF.ordered argumentTyped argumentTranslation
  have resultTyped := bodyTyped.instN envWF.ordered .zero argumentTyped
  have liftedResultTyped := bodyTyped.instN envWF.ordered .zero argumentEquality.hasType.2
  have resultEquality := VEnv.IsDefEq.instDF envWF.ordered originalWF.toCtx
    bodyTyped argumentEquality
  have resultTypeEquality := VEnv.IsDefEq.instDF envWF.ordered originalWF.toCtx
    resultTypeTyped argumentEquality
  have argumentSupported : (Expr.fvar identifier).FVarsIn (· ∈ source.fvars) :=
    receipt.transported.sourceRetained (List.mem_of_getElem? selected)
  exact ⟨reducedArgument, reducedArgumentType, level, reducedLookup, reducedTranslation,
    reducedTyped, bodySupported.instantiate1 argumentSupported, resultTranslation, resultTyped,
    liftedResultTyped, resultEquality, resultTypeEquality⟩

theorem RetainedFVarPrefixAgreement.instantiate
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers)
    (envWF : env.WF) (originalWF : original.WF env universes.length)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic resultType : VExpr}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: original)
      body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: original.toCtx)
      bodySemantic resultType)
    (bodySupported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ reducedArgument reducedArgumentType level,
      source.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      TrExprS env universes source (.fvar identifier) reducedArgument ∧
      env.HasType universes.length source.toCtx reducedArgument reducedArgumentType ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      TrExprS env universes original (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length original.toCtx
        (bodySemantic.inst originalArgument) (resultType.inst originalArgument) ∧
      env.HasType universes.length original.toCtx
        (bodySemantic.inst (reducedArgument.lift' lift))
        (resultType.inst (reducedArgument.lift' lift)) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (bodySemantic.inst (reducedArgument.lift' lift))
        (resultType.inst originalArgument) ∧
      env.IsDefEq universes.length original.toCtx
        (resultType.inst originalArgument) (resultType.inst (reducedArgument.lift' lift))
        (.sort level) := by
  simpa only [Expr.instantiate1_eq] using receipt.instantiateCore envWF originalWF position
    identifier selected originalLookup bodyTranslated bodyTyped bodySupported

end Lean4Lean
