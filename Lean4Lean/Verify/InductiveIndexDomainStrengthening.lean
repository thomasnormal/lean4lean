import Lean4Lean.Verify.InductiveIndexBaseInsertion

namespace Lean4Lean
open Lean hiding Environment Exception
open VEnv

theorem TrExprS.strengthenIsTypeAt
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {binderDepth protectedDepth : Nat} {lift : Lift}
    {domain : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF)
    (weakening : VLCtx.FVLift' smaller aligned binderDepth lift protectedDepth)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (translated : TrExprS env universes original domain semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed domain binderDepth)
    (supported : domain.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reduced,
      TrExprS env universes smaller domain reduced ∧
      env.HasType universes.length smaller.toCtx reduced (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        semantic (reduced.lift' (lift.consN protectedDepth)) (.sort level) := by
  obtain ⟨reduced, reducedTranslation⟩ :=
    translated.weakFV'_inv envWF weakening contexts closed supported
  have alignedWF := (contexts.symm envWF.ordered).wf
  have liftedTranslation := reducedTranslation.weakFV' envWF.ordered weakening alignedWF
  have equality := (translated.uniq envWF contexts liftedTranslation).of_l
    envWF contexts.wf.toCtx typed
  have liftedType := equality.hasType.2.defeqDFC envWF.ordered contexts.defeqCtx
  have reducedType : env.HasType universes.length smaller.toCtx reduced (.sort level) :=
    (HasType.weak'_iff envWF alignedWF.toCtx weakening.toCtx).mp liftedType
  exact ⟨reduced, reducedTranslation, reducedType, equality⟩

theorem TrExprS.strengthenIsType
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {lift : Lift} {domain : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF)
    (weakening : VLCtx.FVLift' smaller aligned 0 lift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (translated : TrExprS env universes original domain semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed domain 0)
    (supported : domain.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reduced,
      TrExprS env universes smaller domain reduced ∧
      env.HasType universes.length smaller.toCtx reduced (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        semantic (reduced.lift' lift) (.sort level) :=
  TrExprS.strengthenIsTypeAt envWF weakening contexts translated typed closed supported

end Lean4Lean
