import Lean4Lean.Verify.InductiveParameterSubstitutionPair

namespace Lean4Lean
open Lean hiding Environment Exception

inductive SemanticSubstitutionChain (env : VEnv) (universes : Nat) (context : List VExpr)
    (level : VLevel) : VExpr → VExpr → Prop where
  | nil (expression : VExpr)
      (typed : env.HasType universes context expression (.sort level)) :
      SemanticSubstitutionChain env universes context level expression expression
  | cons {before after final body original reduced domain : VExpr}
      (beforeEq : before = body.inst original)
      (afterEq : after = body.inst reduced)
      (bodyTyped : env.HasType universes (domain :: context) body (.sort level))
      (argumentEquality : env.IsDefEq universes context original reduced domain)
      (tail : SemanticSubstitutionChain env universes context level after final) :
      SemanticSubstitutionChain env universes context level before final

theorem SemanticSubstitutionChain.single
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced domain : VExpr}
    (bodyTyped : env.HasType universes (domain :: context) body (.sort level))
    (argumentEquality : env.IsDefEq universes context original reduced domain)
    (reducedTyped : env.HasType universes context (body.inst reduced) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original) (body.inst reduced) :=
  .cons rfl rfl bodyTyped argumentEquality (.nil _ reducedTyped)

theorem SemanticSubstitutionChain.isDefEq
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before final)
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.IsDefEq universes context before final (.sort level) := by
  induction chain with
  | nil expression typed => exact typed
  | cons beforeEq afterEq bodyTyped argumentEquality tail ih =>
    rw [beforeEq]
    rw [afterEq] at ih
    have stage := VEnv.IsDefEq.instDF envWF.ordered contextWF bodyTyped argumentEquality
    simpa only [VExpr.inst] using stage.trans ih

theorem SemanticSubstitutionChain.append
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before middle final : VExpr}
    (first : SemanticSubstitutionChain env universes context level before middle)
    (second : SemanticSubstitutionChain env universes context level middle final) :
    SemanticSubstitutionChain env universes context level before final := by
  induction first with
  | nil expression typed => exact second
  | cons beforeEq afterEq bodyTyped argumentEquality tail ih =>
    exact .cons beforeEq afterEq bodyTyped argumentEquality (ih second)

theorem SemanticSubstitutionChain.cancelLeft
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before middle final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before middle)
    (direct : env.IsDefEq universes context before final (.sort level))
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.IsDefEq universes context middle final (.sort level) :=
  (chain.isDefEq envWF contextWF).symm.trans direct

theorem SemanticSubstitutionChain.hasType
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before final)
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.HasType universes context before (.sort level) ∧
      env.HasType universes context final (.sort level) := by
  have equality := chain.isDefEq envWF contextWF
  exact ⟨equality.hasType.1, equality.hasType.2⟩

theorem RetainedFVarPrefixAgreement.instantiatePairOuterChain
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
    ∃ reducedInnerArgument reducedInnerArgumentType reducedOuterArgument reducedOuterArgumentType,
      source.find? (.inr innerIdentifier) = some (reducedInnerArgument, reducedInnerArgumentType) ∧
      source.find? (.inr outerIdentifier) = some (reducedOuterArgument, reducedOuterArgumentType) ∧
      env.IsDefEq universes.length (originalOuterArgumentType :: original.toCtx)
        originalInnerArgument.lift (reducedInnerArgument.lift' removalLift).lift innerDomain ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst (reducedInnerArgument.lift' removalLift).lift).inst
          (reducedOuterArgument.lift' removalLift)) (.sort level) ∧
      SemanticSubstitutionChain env universes.length original.toCtx level
        ((bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument)
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift)) ∧
      env.IsDefEq universes.length original.toCtx
        ((bodySemantic.inst originalInnerArgument.lift).inst (reducedOuterArgument.lift' removalLift))
        ((bodySemantic.inst (reducedInnerArgument.lift' removalLift).lift).inst
          (reducedOuterArgument.lift' removalLift)) (.sort level) := by
  obtain ⟨reducedInnerArgument, reducedInnerArgumentType, reducedOuterArgument, reducedOuterArgumentType,
    reducedInnerLookup, reducedOuterLookup, actualInnerEquality, simultaneousEquality⟩ :=
    receipt.instantiatePairIsDefEq envWF originalWF outerPosition outerIdentifier outerSelected
      innerPosition innerIdentifier innerSelected outerLookup innerLookup raisedInnerArgumentTyped bodyTyped
  obtain ⟨lookupOuterArgument, lookupOuterType, lookupOriginalArgument, lookupOriginalType, _,
    sourceOuterLookup, _, _, originalOuterLookup, _, _, _, outerArgumentEquality⟩ :=
    receipt.lookups outerPosition outerIdentifier outerSelected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (sourceOuterLookup.symm.trans reducedOuterLookup))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (originalOuterLookup.symm.trans outerLookup))
  have intermediateTyped : env.HasType universes.length
      (lookupOriginalType :: original.toCtx)
      (bodySemantic.inst originalInnerArgument.lift) (.sort level) := by
    simpa only [VExpr.inst] using bodyTyped.instN envWF.ordered .zero raisedInnerArgumentTyped
  have outerStageEquality : env.IsDefEq universes.length original.toCtx
      ((bodySemantic.inst originalInnerArgument.lift).inst lookupOriginalArgument)
      ((bodySemantic.inst originalInnerArgument.lift).inst (lookupOuterArgument.lift' removalLift))
      (.sort level) := by
    simpa only [VExpr.inst] using VEnv.IsDefEq.instDF envWF.ordered originalWF.toCtx
      intermediateTyped outerArgumentEquality
  have outerChain := SemanticSubstitutionChain.single intermediateTyped outerArgumentEquality
    outerStageEquality.hasType.2
  exact ⟨reducedInnerArgument, reducedInnerArgumentType, lookupOuterArgument, lookupOuterType,
    reducedInnerLookup, reducedOuterLookup, actualInnerEquality, simultaneousEquality, outerChain,
    outerChain.cancelLeft simultaneousEquality envWF originalWF.toCtx⟩

end Lean4Lean
