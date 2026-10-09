import Lean4Lean.Verify.InductiveAnnotationModelFVarsIn

namespace Lean4Lean
open Lean AddInductive

theorem Closed.peelTypeAnnotations {value : Expr} {depth : Nat}
    (closed : value.Closed depth) : (peelTypeAnnotations value).Closed depth := by
  induction value using AddInductive.peelTypeAnnotations.induct <;>
    simp_all [AddInductive.peelTypeAnnotations, Closed]

theorem Closed.instantiate1_offset {value replacement : Expr} {depth offset : Nat}
    (closed : value.Closed (depth + 1)) (replacementClosed : replacement.Closed 0)
    (offsetWithin : offset ≤ depth) : (value.instantiate1' replacement offset).Closed depth := by
  induction value generalizing depth offset with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · simp only [Closed] at closed ⊢
      omega
    · split
      · rw [Expr.liftLooseBVars_eq_self replacementClosed.looseBVarRange_le]
        exact replacementClosed.mono (Nat.zero_le depth)
      · simp only [Closed] at closed ⊢
        omega
  | fvar | sort | const | lit => trivial
  | mvar => exact closed.elim
  | app function argument functionIH argumentIH =>
    exact ⟨functionIH closed.1 offsetWithin, argumentIH closed.2 offsetWithin⟩
  | lam name domain body binderInfo domainIH bodyIH =>
    exact ⟨domainIH closed.1 offsetWithin, bodyIH closed.2 (Nat.succ_le_succ offsetWithin)⟩
  | forallE name domain body binderInfo domainIH bodyIH =>
    exact ⟨domainIH closed.1 offsetWithin, bodyIH closed.2 (Nat.succ_le_succ offsetWithin)⟩
  | letE name domain value body nondep domainIH valueIH bodyIH =>
    exact ⟨domainIH closed.1 offsetWithin, valueIH closed.2.1 offsetWithin,
      bodyIH closed.2.2 (Nat.succ_le_succ offsetWithin)⟩
  | mdata metadata value valueIH => exact valueIH closed offsetWithin
  | proj name index value valueIH => exact valueIH closed offsetWithin

theorem Closed.instantiate1_native {value replacement : Expr} {depth : Nat}
    (closed : value.Closed (depth + 1)) (replacementClosed : replacement.Closed 0) :
    (value.instantiate1 replacement).Closed depth := by
  rw [Expr.instantiate1_eq]
  exact closed.instantiate1_offset replacementClosed (Nat.zero_le depth)

end Lean4Lean
