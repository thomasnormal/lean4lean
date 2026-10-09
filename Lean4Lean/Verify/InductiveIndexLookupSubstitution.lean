import Lean4Lean.Verify.InductiveIndexLookup

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem indexRenameExpr_liftLooseBVars' (pairs : List (FVarId × FVarId)) (value : Expr)
    (start amount : Nat) :
    indexRenameExpr pairs (value.liftLooseBVars' start amount) =
      (indexRenameExpr pairs value).liftLooseBVars' start amount := by
  induction value generalizing start with
  | bvar index => rfl
  | sort level => rfl
  | const name levels => rfl
  | lit literal => rfl
  | mvar id => rfl
  | fvar id => rfl
  | app function argument ihFn ihArg =>
    simp only [Expr.liftLooseBVars', indexRenameExpr, ihFn, ihArg]
  | lam name domain body bi ihDomain ihBody =>
    simp only [Expr.liftLooseBVars', indexRenameExpr, ihDomain, ihBody]
  | forallE name domain body bi ihDomain ihBody =>
    simp only [Expr.liftLooseBVars', indexRenameExpr, ihDomain, ihBody]
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    simp only [Expr.liftLooseBVars', indexRenameExpr, ihDomain, ihValue, ihBody]
  | mdata data body ih => simp only [Expr.liftLooseBVars', indexRenameExpr, ih]
  | proj name index body ih => simp only [Expr.liftLooseBVars', indexRenameExpr, ih]

theorem indexRenameExpr_instantiate1' (pairs : List (FVarId × FVarId))
    (value replacement : Expr) (depth : Nat) :
    indexRenameExpr pairs (value.instantiate1' replacement depth) =
      (indexRenameExpr pairs value).instantiate1' (indexRenameExpr pairs replacement) depth := by
  induction value generalizing depth with
  | bvar index =>
    simp only [Expr.instantiate1', indexRenameExpr]
    split
    · rfl
    · split
      · exact indexRenameExpr_liftLooseBVars' pairs replacement 0 depth
      · rfl
  | sort level => rfl
  | const name levels => rfl
  | lit literal => rfl
  | mvar id => rfl
  | fvar id => rfl
  | app function argument ihFn ihArg =>
    simp only [Expr.instantiate1', indexRenameExpr, ihFn, ihArg]
  | lam name domain body bi ihDomain ihBody =>
    simp only [Expr.instantiate1', indexRenameExpr, ihDomain, ihBody]
  | forallE name domain body bi ihDomain ihBody =>
    simp only [Expr.instantiate1', indexRenameExpr, ihDomain, ihBody]
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    simp only [Expr.instantiate1', indexRenameExpr, ihDomain, ihValue, ihBody]
  | mdata data body ih => simp only [Expr.instantiate1', indexRenameExpr, ih]
  | proj name index body ih => simp only [Expr.instantiate1', indexRenameExpr, ih]

theorem indexRenameExpr_instantiate1 (pairs : List (FVarId × FVarId)) (value replacement : Expr) :
    indexRenameExpr pairs (value.instantiate1 replacement) =
      (indexRenameExpr pairs value).instantiate1 (indexRenameExpr pairs replacement) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  exact indexRenameExpr_instantiate1' pairs value replacement 0

theorem indexRenameExpr_binderSignature (pairs : List (FVarId × FVarId)) (value : Expr) :
    Expr.binderSignature (indexRenameExpr pairs value) = Expr.binderSignature value := by
  induction value with
  | forallE name domain body bi ihDomain ihBody => exact congrArg ((name, bi) :: ·) ihBody
  | _ => rfl

theorem IndexLookupRenaming.liftLooseBVars' {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) (start amount : Nat) :
    IndexLookupRenaming pairs (left.liftLooseBVars' start amount) (right.liftLooseBVars' start amount) := by
  change indexRenameExpr pairs (left.liftLooseBVars' start amount) = right.liftLooseBVars' start amount
  rw [indexRenameExpr_liftLooseBVars', related]

theorem IndexLookupRenaming.instantiate1' {pairs : List (FVarId × FVarId)}
    {left right leftValue rightValue : Expr} (related : IndexLookupRenaming pairs left right)
    (values : IndexLookupRenaming pairs leftValue rightValue) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' leftValue depth) (right.instantiate1' rightValue depth) := by
  change indexRenameExpr pairs (left.instantiate1' leftValue depth) = right.instantiate1' rightValue depth
  rw [indexRenameExpr_instantiate1', related, values]

theorem IndexLookupRenaming.instantiate1 {pairs : List (FVarId × FVarId)}
    {left right leftValue rightValue : Expr} (related : IndexLookupRenaming pairs left right)
    (values : IndexLookupRenaming pairs leftValue rightValue) :
    IndexLookupRenaming pairs (left.instantiate1 leftValue) (right.instantiate1 rightValue) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  exact related.instantiate1' values 0

theorem IndexLookupRenaming.binderSignature {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) : Expr.binderSignature left = Expr.binderSignature right := by
  rw [← related, indexRenameExpr_binderSignature]

end Lean4Lean.AddInductive
