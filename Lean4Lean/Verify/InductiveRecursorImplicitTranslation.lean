import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean
open Lean

theorem TrExprS.inferImplicit {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {expression : Expr} {semantic : VExpr}
    (translated : TrExprS env universes virtual expression semantic)
    (count : Nat) (considerRange : Bool) :
    TrExprS env universes virtual (expression.inferImplicit count considerRange) semantic := by
  induction count generalizing virtual expression semantic with
  | zero => cases expression <;> exact translated
  | succ count tailInduction =>
    cases expression <;> try exact translated
    case forallE name domain body binderInfo =>
      cases translated with
      | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
        exact .forallE domainTyped bodyTyped domainTranslated (tailInduction bodyTranslated)

theorem TrExpr.inferImplicit {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {expression : Expr} {semantic : VExpr}
    (translated : TrExpr env universes virtual expression semantic)
    (count : Nat) (considerRange : Bool) :
    TrExpr env universes virtual (expression.inferImplicit count considerRange) semantic := by
  obtain ⟨strictSemantic, strictTranslated, equality⟩ := translated
  exact ⟨strictSemantic, strictTranslated.inferImplicit count considerRange, equality⟩

end Lean4Lean
