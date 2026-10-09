import Lean4Lean.Verify.ExprBoundedRange
import Lean4Lean.Verify.InductiveAnnotationModelClosed

namespace Lean4Lean
open Lean AddInductive

theorem BVarRangeFits.peelTypeAnnotations {value : Expr} (fits : BVarRangeFits value) :
    BVarRangeFits (peelTypeAnnotations value) := by
  induction value using AddInductive.peelTypeAnnotations.induct <;>
    simp_all [AddInductive.peelTypeAnnotations, BVarRangeFits]

theorem BVarRangeFits.instantiate1_offset {value replacement : Expr} {offset : Nat}
    (fits : BVarRangeFits value) (replacementFits : BVarRangeFits replacement)
    (replacementClosed : replacement.Closed 0) :
    BVarRangeFits (value.instantiate1' replacement offset) := by
  induction value generalizing offset with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · exact fits
    · split
      · rw [Expr.liftLooseBVars_eq_self replacementClosed.looseBVarRange_le]
        exact replacementFits
      · simp only [BVarRangeFits] at fits ⊢
        omega
  | fvar | mvar | sort | const | lit => trivial
  | app function argument functionIH argumentIH =>
    exact ⟨functionIH fits.1, argumentIH fits.2⟩
  | lam name domain body binderInfo domainIH bodyIH =>
    exact ⟨domainIH fits.1, bodyIH fits.2⟩
  | forallE name domain body binderInfo domainIH bodyIH =>
    exact ⟨domainIH fits.1, bodyIH fits.2⟩
  | letE name domain value body nondep domainIH valueIH bodyIH =>
    exact ⟨domainIH fits.1, valueIH fits.2.1, bodyIH fits.2.2⟩
  | mdata metadata value valueIH => exact valueIH fits
  | proj name index value valueIH => exact valueIH fits

theorem BVarRangeFits.instantiate1_native {value replacement : Expr}
    (fits : BVarRangeFits value) (replacementFits : BVarRangeFits replacement)
    (replacementClosed : replacement.Closed 0) : BVarRangeFits (value.instantiate1 replacement) := by
  rw [Expr.instantiate1_eq]
  exact fits.instantiate1_offset replacementFits replacementClosed

end Lean4Lean
