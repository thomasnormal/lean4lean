import Lean4Lean.Verify.InductiveIndexLookupSupport

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def peelTypeAnnotations (expression : Expr) : Expr :=
  match expression with
  | .app (.const name levels) carrier =>
    if name = ``_root_.outParam ∨ name = ``_root_.semiOutParam then peelTypeAnnotations carrier
    else .app (.const name levels) carrier
  | .app (.app (.const name levels) carrier) extra =>
    if name = ``_root_.optParam ∨ name = ``_root_.autoParam then peelTypeAnnotations carrier
    else .app (.app (.const name levels) carrier) extra
  | expression => expression
termination_by structural expression

theorem peelTypeAnnotations.outParam (levels : List Level) (carrier : Expr) :
    peelTypeAnnotations (.app (.const ``_root_.outParam levels) carrier) = peelTypeAnnotations carrier := by
  simp only [peelTypeAnnotations, true_or, ↓reduceIte]

theorem peelTypeAnnotations.semiOutParam (levels : List Level) (carrier : Expr) :
    peelTypeAnnotations (.app (.const ``_root_.semiOutParam levels) carrier) = peelTypeAnnotations carrier := by
  simp only [peelTypeAnnotations, or_true, ↓reduceIte]

theorem peelTypeAnnotations.optParam (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (.app (.app (.const ``_root_.optParam levels) carrier) extra) =
      peelTypeAnnotations carrier := by
  simp only [peelTypeAnnotations, true_or, ↓reduceIte]

theorem peelTypeAnnotations.autoParam (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (.app (.app (.const ``_root_.autoParam levels) carrier) extra) =
      peelTypeAnnotations carrier := by
  simp only [peelTypeAnnotations, or_true, ↓reduceIte]

theorem peelTypeAnnotations.unaryOther (name : Name) (levels : List Level) (carrier : Expr)
    (hout : name ≠ ``_root_.outParam) (hsemi : name ≠ ``_root_.semiOutParam) :
    peelTypeAnnotations (.app (.const name levels) carrier) = .app (.const name levels) carrier := by
  simp only [peelTypeAnnotations, hout, hsemi, false_or, ↓reduceIte]

theorem peelTypeAnnotations.binaryOther (name : Name) (levels : List Level) (carrier extra : Expr)
    (hopt : name ≠ ``_root_.optParam) (hauto : name ≠ ``_root_.autoParam) :
    peelTypeAnnotations (.app (.app (.const name levels) carrier) extra) =
      .app (.app (.const name levels) carrier) extra := by
  simp only [peelTypeAnnotations, hopt, hauto, false_or, ↓reduceIte]

theorem peelTypeAnnotations.forallE (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (.forallE name domain body bi) = .forallE name domain body bi := rfl

theorem peelTypeAnnotations.lam (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (.lam name domain body bi) = .lam name domain body bi := rfl

theorem peelTypeAnnotations.letE (name : Name) (domain value body : Expr) (nondep : Bool) :
    peelTypeAnnotations (.letE name domain value body nondep) = .letE name domain value body nondep := rfl

theorem peelTypeAnnotations.mdata (data : MData) (body : Expr) :
    peelTypeAnnotations (.mdata data body) = .mdata data body := rfl

theorem peelTypeAnnotations.proj (name : Name) (position : Nat) (body : Expr) :
    peelTypeAnnotations (.proj name position body) = .proj name position body := rfl

end Lean4Lean.AddInductive
