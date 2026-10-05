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

  -- These bounds are too small to compute the large examples by unary unfolding.
  let fuel : FuelConfig := { recDepth := 16, whnf := 8, lazyDelta := 8 }
  for (a, b) in [(0, 0), (17, 0), (0, 23), (1000000, 2000000),
      (1208925819614629174706177, 1208925819614629174706179)] do
    let e := mkApp2 q(Nat.add) (mkNatLit a) (mkNatLit b)
    match (TypeChecker.whnf e).run env (fuel := fuel) with
    | .ok r =>
      unless r.rawNatLit? == some (a + b) do
        throwError "Nat.add {a} {b}: expected literal {a + b}"
    | .error _ => throwError "Nat.add {a} {b}: reduction failed"

  let some (.defnInfo add) := env.find? ``Nat.add | throwError "missing Nat.add"
  let badAdd := { add with value := q(fun a (_ : Nat) => a) }
  if ((Lean4Lean.Environment.checkPrimitiveDef badAdd).run env).isOk then
    throwError "accepted a Nat.add implementation that ignores its second argument"

  for (a, b) in [(0, 0), (17, 0), (0, 23), (1, 29), (31, 1), (1000000, 2000000),
      (1208925819614629174706177, 1208925819614629174706179)] do
    let e := mkApp2 q(Nat.mul) (mkNatLit a) (mkNatLit b)
    match (TypeChecker.whnf e).run env (fuel := fuel) with
    | .ok r =>
      unless r.rawNatLit? == some (a * b) do
        throwError "Nat.mul {a} {b}: expected literal {a * b}"
    | .error _ => throwError "Nat.mul {a} {b}: reduction failed"

  let some (.defnInfo mul) := env.find? ``Nat.mul | throwError "missing Nat.mul"
  for badMul in [{ mul with value := q(fun (_ _ : Nat) => Nat.zero) },
      { mul with value := q(Nat.add) }] do
    if ((Lean4Lean.Environment.checkPrimitiveDef badMul).run env).isOk then
      throwError "accepted an incorrect Nat.mul implementation"

  for (a, b) in [(0, 0), (17, 0), (0, 23), (1, 29), (31, 1), (2, 80), (3, 40)] do
    let e := mkApp2 q(Nat.pow) (mkNatLit a) (mkNatLit b)
    match (TypeChecker.whnf e).run env (fuel := fuel) with
    | .ok r =>
      unless r.rawNatLit? == some (a ^ b) do
        throwError "Nat.pow {a} {b}: expected literal {a ^ b}"
    | .error _ => throwError "Nat.pow {a} {b}: reduction failed"

  -- Check the native exponent guard directly, without falling back to unfolding.
  let limit : Nat := 2 ^ 24
  let boundaryCases : List (Nat × Option Nat) := [(limit, some 1), (limit + 1, none)]
  for (exponent, expected) in boundaryCases do
    let action := TypeChecker.RecM.run <|
      TypeChecker.Inner.reducePow (mkNatLit 1) (mkNatLit exponent)
    match action.run env (fuel := fuel) with
    | .ok r =>
      unless r == expected.map (fun n => Expr.lit (.natVal n)) do
        throwError "Nat.pow exponent guard at {exponent}: expected {repr expected}, got {repr r}"
    | .error _ => throwError "Nat.pow exponent guard failed at {exponent}"

  let some (.defnInfo pow) := env.find? ``Nat.pow | throwError "missing Nat.pow"
  for badPow in [{ pow with value := q(fun (_ _ : Nat) => Nat.succ Nat.zero) },
      { pow with value := q(Nat.mul) }] do
    if ((Lean4Lean.Environment.checkPrimitiveDef badPow).run env).isOk then
      throwError "accepted an incorrect Nat.pow implementation"
