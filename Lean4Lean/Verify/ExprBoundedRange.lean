import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Typing.Expr

namespace Lean4Lean
open Lean

def BVarRangeFits : Expr → Prop
  | .bvar index => index + 1 ≤ 2^20 - 1
  | .app function argument => BVarRangeFits function ∧ BVarRangeFits argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
    BVarRangeFits domain ∧ BVarRangeFits body
  | .letE _ domain value body _ =>
    BVarRangeFits domain ∧ BVarRangeFits value ∧ BVarRangeFits body
  | .mdata _ value | .proj _ _ value => BVarRangeFits value
  | _ => True

theorem BVarRangeFits.rangeAccurate {value : Expr} (fits : BVarRangeFits value) :
    value.looseBVarRange = value.looseBVarRange' := by
  induction value with
  | bvar index =>
    exact Expr.mkData_looseBVarRange fits
  | fvar | mvar | sort | const | lit =>
    exact Expr.mkData_looseBVarRange (by decide)
  | app function argument ihFunction ihArgument =>
    change (Expr.mkAppData function.data argument.data).looseBVarRange.toNat = _
    rw [Expr.mkAppData_looseBVarRange, UInt32.max_toNat]
    change max function.looseBVarRange argument.looseBVarRange = _
    rw [ihFunction fits.1, ihArgument fits.2]
    rfl
  | mdata data value ih =>
    change (Expr.mkData _ value.looseBVarRange _ _ _ _ _).looseBVarRange.toNat = _
    rw [Expr.mkData_looseBVarRange Expr.looseBVarRange_le]
    exact ih fits
  | proj name index value ih =>
    change (Expr.mkData _ value.looseBVarRange _ _ _ _ _).looseBVarRange.toNat = _
    rw [Expr.mkData_looseBVarRange Expr.looseBVarRange_le]
    exact ih fits
  | lam name domain body info ihDomain ihBody | forallE name domain body info ihDomain ihBody =>
    change (Expr.mkData _ (max domain.looseBVarRange (body.looseBVarRange - 1))
      _ _ _ _ _).looseBVarRange.toNat = _
    have bound : max domain.looseBVarRange (body.looseBVarRange - 1) ≤ 2^20 - 1 := by
      have domainBound := Expr.looseBVarRange_le (e := domain)
      have bodyBound := Expr.looseBVarRange_le (e := body)
      omega
    rw [Expr.mkData_looseBVarRange bound]
    rw [ihDomain fits.1, ihBody fits.2]
    rfl
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    change (Expr.mkData _ (max (max domain.looseBVarRange value.looseBVarRange)
      (body.looseBVarRange - 1)) _ _ _ _ _).looseBVarRange.toNat = _
    have bound : max (max domain.looseBVarRange value.looseBVarRange)
        (body.looseBVarRange - 1) ≤ 2^20 - 1 := by
      have domainBound := Expr.looseBVarRange_le (e := domain)
      have valueBound := Expr.looseBVarRange_le (e := value)
      have bodyBound := Expr.looseBVarRange_le (e := body)
      omega
    rw [Expr.mkData_looseBVarRange bound]
    rw [ihDomain fits.1, ihValue fits.2.1, ihBody fits.2.2]
    rfl

theorem BVarRangeFits.rangeZeroReflects {value : Expr} (fits : BVarRangeFits value)
    (zero : value.looseBVarRange = 0) : value.looseBVarRange' = 0 :=
  fits.rangeAccurate.symm.trans zero

theorem BVarRangeFits.hasLooseBVars_eq_false_iff {value : Expr} (fits : BVarRangeFits value) :
    value.hasLooseBVars = false ↔ value.looseBVarRange' = 0 := by
  rw [Expr.hasLooseBVars, fits.rangeAccurate]
  simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]

private theorem closed_iff_structuralRange {value : Expr} {depth : Nat} :
    value.Closed depth ↔ value.looseBVarRange' ≤ depth ∧ value.hasExprMVar' = false := by
  induction value generalizing depth <;>
    simp_all [Closed, Expr.looseBVarRange', Expr.hasExprMVar', Nat.max_le,
      Nat.sub_le_iff_le_add, and_assoc, and_left_comm, and_comm]
  all_goals omega

theorem BVarRangeFits.closed_iff_nativeRange {value : Expr} {depth : Nat}
    (fits : BVarRangeFits value) :
    value.Closed depth ↔ value.looseBVarRange ≤ depth ∧ value.hasExprMVar = false := by
  rw [fits.rangeAccurate, Expr.hasExprMVar_eq]
  exact closed_iff_structuralRange

theorem BVarRangeFits.closed_iff {value : Expr} (fits : BVarRangeFits value) :
    value.Closed ↔ value.hasLooseBVars = false ∧ value.hasExprMVar = false := by
  rw [fits.closed_iff_nativeRange]
  simp only [Expr.hasLooseBVars, decide_eq_false_iff_not, Nat.not_lt]

theorem FVarsIn.closed_of_bvarRangeFits_atDepth {predicate : FVarId → Prop}
    {value : Expr} {depth : Nat} (within : value.FVarsIn predicate)
    (fits : BVarRangeFits value) (range : value.looseBVarRange ≤ depth) :
    value.Closed depth := by
  refine fits.closed_iff_nativeRange.mpr ⟨range, ?_⟩
  rw [Expr.hasExprMVar_eq]
  clear fits range
  induction value <;> simp_all [FVarsIn, Expr.hasExprMVar']

theorem FVarsIn.closed_of_bvarRangeFits {predicate : FVarId → Prop} {value : Expr}
    (within : value.FVarsIn predicate) (fits : BVarRangeFits value)
    (zero : value.looseBVarRange = 0) : value.Closed :=
  within.closed_of_bvarRangeFits_atDepth fits (Nat.le_of_eq zero)

end Lean4Lean
