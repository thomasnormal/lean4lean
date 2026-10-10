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

theorem SemanticSubstitutionChain.hasType
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before final)
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.HasType universes context before (.sort level) ∧
      env.HasType universes context final (.sort level) := by
  have equality := chain.isDefEq envWF contextWF
  exact ⟨equality.hasType.1, equality.hasType.2⟩

end Lean4Lean
