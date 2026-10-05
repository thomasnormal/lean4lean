import Lean4Lean.Primitive

-- Run with: lake env lean tests/Primitive.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let addZero := mkApp2 q(Nat.add) (.bvar 0) q(Nat.zero)
  let andFalse := mkApp2 q(Bool.and) q(false) (.bvar 0)
  let cases := [
    ("Nat forall wrapper", Expr.arrow q(Nat) addZero, false),
    ("Nat lambda wrapper", Expr.lam0 q(Nat) addZero, true),
    ("Bool lambda with Nat domain", Expr.lam0 q(Nat) andFalse, false),
    ("Bool lambda with Bool domain", Expr.lam0 q(Bool) andFalse, true)]
  for (name, e, expected) in cases do
    let accepted := ((TypeChecker.checkType e).run env).isOk
    unless accepted == expected do
      throwError "{name}: expected accepted={expected}, got {accepted}"
