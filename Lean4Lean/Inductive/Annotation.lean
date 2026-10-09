import Lean.Expr

namespace Lean4Lean.AddInductive
open Lean

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

end Lean4Lean.AddInductive
