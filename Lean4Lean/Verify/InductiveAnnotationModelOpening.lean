import Lean4Lean.Verify.InductiveAnnotationOpeningShape

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem peelTypeAnnotations_instantiate1'_fvar (expression : Expr) (id : FVarId) (depth : Nat) :
    peelTypeAnnotations (expression.instantiate1' (.fvar id) depth) =
      (peelTypeAnnotations expression).instantiate1' (.fvar id) depth := by
  induction expression using peelTypeAnnotations.induct generalizing depth with
  | case1 name levels carrier hannotation ih =>
    simp only [Expr.instantiate1', peelTypeAnnotations, hannotation, ↓reduceIte, ih]
  | case2 name levels carrier hother =>
    simp only [Expr.instantiate1', peelTypeAnnotations, hother, ↓reduceIte]
  | case3 name levels carrier extra hannotation ih =>
    simp only [Expr.instantiate1', peelTypeAnnotations, hannotation, ↓reduceIte, ih]
  | case4 name levels carrier extra hother =>
    simp only [Expr.instantiate1', peelTypeAnnotations, hother, ↓reduceIte]
  | case5 value notUnary notBinary =>
    have hopened : peelTypeAnnotations (value.instantiate1' (.fvar id) depth) =
        value.instantiate1' (.fvar id) depth := by
      apply peelTypeAnnotations.eq_3
      · intro name levels carrier hhead
        obtain ⟨originalCarrier, horiginal, _⟩ := instantiate1'_fvar_preservesUnaryHead hhead
        exact notUnary name levels originalCarrier horiginal
      · intro name levels carrier extra hhead
        obtain ⟨originalCarrier, originalExtra, horiginal, _, _⟩ :=
          instantiate1'_fvar_preservesBinaryHead hhead
        exact notBinary name levels originalCarrier originalExtra horiginal
    rw [hopened, peelTypeAnnotations.eq_3 value notUnary notBinary]

theorem peelTypeAnnotations_instantiate1_fvar (expression : Expr) (id : FVarId) :
    peelTypeAnnotations (expression.instantiate1 (.fvar id)) =
      (peelTypeAnnotations expression).instantiate1 (.fvar id) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  exact peelTypeAnnotations_instantiate1'_fvar expression id 0

end Lean4Lean.AddInductive
