import Lean4Lean.Theory.VLevel

/-! Constructive detection of levels equivalent to zero, independent of reduction. -/

namespace Lean4Lean.VEnv.QuotPropReduction

def zeroLike : VLevel → Bool
  | .zero => true
  | .succ _ | .param _ => false
  | .max first second => zeroLike first && zeroLike second
  | .imax _ second => zeroLike second

theorem zeroLike_iff (level : VLevel) : zeroLike level = true ↔ level ≈ .zero := by
  induction level with
  | zero => simp [zeroLike, VLevel.equiv_def]
  | succ level => simp [zeroLike, VLevel.equiv_def, VLevel.eval]
  | param index =>
    simp only [zeroLike, Bool.false_eq_true, false_iff]
    intro equal
    have evaluated := VLevel.equiv_def.mp equal (List.replicate (index + 1) 1)
    simp [VLevel.eval] at evaluated
  | max first second firstIH secondIH =>
    simp only [zeroLike, Bool.and_eq_true, firstIH, secondIH, VLevel.equiv_def, VLevel.eval]
    constructor
    · rintro ⟨firstZero, secondZero⟩ values
      rw [firstZero values, secondZero values]
      rfl
    · intro equal
      exact ⟨fun values => Nat.eq_zero_of_le_zero
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq (equal values))),
        fun values => Nat.eq_zero_of_le_zero
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq (equal values)))⟩
  | imax first second _ secondIH =>
    constructor
    · intro checked
      have secondZero := secondIH.mp checked
      exact VLevel.equiv_def.mpr fun values => by
        simp [VLevel.eval, Lean.Nat.imax, VLevel.equiv_def.mp secondZero values]
    · intro equal
      apply secondIH.mpr
      apply VLevel.equiv_def.mpr
      intro values
      have evaluated := VLevel.equiv_def.mp equal values
      change Lean.Nat.imax (first.eval values) (second.eval values) = 0 at evaluated
      cases secondValue : second.eval values with
      | zero => rfl
      | succ value =>
        simp only [Lean.Nat.imax, secondValue, Nat.succ_ne_zero, if_false] at evaluated
        exact Nat.noConfusion (Nat.eq_zero_of_le_zero
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq evaluated)))

end Lean4Lean.VEnv.QuotPropReduction
