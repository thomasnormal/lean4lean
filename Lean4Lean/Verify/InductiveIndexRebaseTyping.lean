import Lean4Lean.Verify.InductiveIndexDomainStrengthening

namespace Lean4Lean
open Lean hiding Environment Exception
open VEnv

theorem TrExprS.rebaseIsType
    {env : VEnv} {universes : List Name} {reduced original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {domain : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF)
    (removal : VLCtx.FVLift' reduced aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' reduced target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (translated : TrExprS env universes original domain semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed domain 0)
    (supported : domain.FVarsIn (· ∈ reduced.fvars)) :
    ∃ reducedSemantic,
      TrExprS env universes reduced domain reducedSemantic ∧
      env.HasType universes.length reduced.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        semantic (reducedSemantic.lift' removalLift) (.sort level) ∧
      TrExprS env universes target domain (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx
        (reducedSemantic.lift' insertionLift) (.sort level) := by
  obtain ⟨reducedSemantic, reducedTranslation, reducedType, equality⟩ :=
    TrExprS.strengthenIsType envWF removal contexts translated typed closed supported
  have targetTranslation := reducedTranslation.weakFV' envWF.ordered insertion targetWF
  have targetType : env.HasType universes.length target.toCtx
      (reducedSemantic.lift' insertionLift) (.sort level) :=
    reducedType.weak' envWF.ordered insertion.toCtx
  exact ⟨reducedSemantic, reducedTranslation, reducedType, equality, targetTranslation, targetType⟩

end Lean4Lean
