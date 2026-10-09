import Lean4Lean.Verify.InductiveAnnotationModel
import Lean4Lean.Verify.InductiveIndexLookup

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem indexRenameExpr_isAppOfArity (pairs : List (FVarId × FVarId)) (value : Expr)
    (name : Name) (arity : Nat) :
    (indexRenameExpr pairs value).isAppOfArity name arity = value.isAppOfArity name arity := by
  induction value generalizing arity with
  | app function argument ihFn ihArg =>
    cases arity with
    | zero => rfl
    | succ arity => exact ihFn arity
  | _ => cases arity <;> rfl

private theorem renamedBinaryNonConstant (pairs : List (FVarId × FVarId))
    (function carrier extra : Expr)
    (notConstant : ∀ name levels, function = .const name levels → False) :
    peelTypeAnnotations (.app (.app (indexRenameExpr pairs function) (indexRenameExpr pairs carrier))
      (indexRenameExpr pairs extra)) =
      .app (.app (indexRenameExpr pairs function) (indexRenameExpr pairs carrier))
        (indexRenameExpr pairs extra) := by
  cases function with
  | const name levels => exact False.elim (notConstant name levels rfl)
  | _ => rfl

private theorem renamedAppNoAnnotationHead (pairs : List (FVarId × FVarId))
    (function argument : Expr)
    (notUnary : ∀ name levels carrier, Expr.app function argument = .app (.const name levels) carrier → False)
    (notBinary : ∀ name levels carrier extra,
      Expr.app function argument = .app (.app (.const name levels) carrier) extra → False) :
    peelTypeAnnotations (.app (indexRenameExpr pairs function) (indexRenameExpr pairs argument)) =
      .app (indexRenameExpr pairs function) (indexRenameExpr pairs argument) := by
  cases function with
  | const name levels => exact False.elim (notUnary name levels argument rfl)
  | app head carrier =>
    exact renamedBinaryNonConstant pairs head carrier argument
      (fun name levels heq => notBinary name levels carrier argument (by rw [heq]))
  | _ => rfl

private theorem renamedNoAnnotationHead (pairs : List (FVarId × FVarId)) (value : Expr)
    (notUnary : ∀ name levels carrier, value = .app (.const name levels) carrier → False)
    (notBinary : ∀ name levels carrier extra, value = .app (.app (.const name levels) carrier) extra → False) :
    peelTypeAnnotations (indexRenameExpr pairs value) = indexRenameExpr pairs value := by
  cases value with
  | app function argument => exact renamedAppNoAnnotationHead pairs function argument notUnary notBinary
  | _ => rfl

theorem indexRenameExpr_peelTypeAnnotations (pairs : List (FVarId × FVarId)) (value : Expr) :
    indexRenameExpr pairs (peelTypeAnnotations value) = peelTypeAnnotations (indexRenameExpr pairs value) := by
  induction value using peelTypeAnnotations.induct with
  | case1 name levels carrier hannotation ih =>
    simp only [peelTypeAnnotations, hannotation, ↓reduceIte, indexRenameExpr, ih]
  | case2 name levels carrier hother =>
    simp only [peelTypeAnnotations, hother, ↓reduceIte, indexRenameExpr]
  | case3 name levels carrier extra hannotation ih =>
    simp only [peelTypeAnnotations, hannotation, ↓reduceIte, indexRenameExpr, ih]
  | case4 name levels carrier extra hother =>
    simp only [peelTypeAnnotations, hother, ↓reduceIte, indexRenameExpr]
  | case5 value notUnary notBinary =>
    rw [renamedNoAnnotationHead pairs value notUnary notBinary]
    have hself := renamedNoAnnotationHead [] value notUnary notBinary
    have hinitial : indexRenameExpr [] value = value := indexRenameExpr_fixedParameters
      (params := value.fvarsList) (by intro id _ hmem; cases hmem) (IndexFVarsWithin.of_subset (.refl _))
    rw [hinitial] at hself
    rw [hself]

theorem IndexLookupRenaming.peelTypeAnnotations {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) :
    IndexLookupRenaming pairs (Lean4Lean.AddInductive.peelTypeAnnotations left)
      (Lean4Lean.AddInductive.peelTypeAnnotations right) := by
  change indexRenameExpr pairs (Lean4Lean.AddInductive.peelTypeAnnotations left) =
    Lean4Lean.AddInductive.peelTypeAnnotations right
  rw [indexRenameExpr_peelTypeAnnotations, related]

end Lean4Lean.AddInductive
