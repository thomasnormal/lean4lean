import Lean4Lean.Primitive

-- Run with: lake env lean tests/Division.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let some (.defnInfo div) := env.find? ``Nat.div | throwError "missing Nat.div"
  match (Environment.checkPrimitiveDef div).run env with
  | .ok _ => pure ()
  | .error e => throwError "rejected the reference Nat.div implementation: {e.toMessageData {}}"
  for value in [q(fun (_ _ : Nat) => Nat.zero), q(fun (a : Nat) (_ : Nat) => a)] do
    if ((Environment.checkPrimitiveDef { div with value }).run env).isOk then
      throwError "accepted an incorrect Nat.div implementation"

  -- Large quotients cannot be computed by repeated subtraction with this fuel.
  let fuel : FuelConfig := { recDepth := 16, whnf := 8, lazyDelta := 8 }
  for (a, b) in [(0, 0), (17, 0), (0, 17), (17, 1), (17, 17), (31, 7), (7, 31),
      (1208925819614629174706177, 3),
      (1208925819614629174706177, 1208925819614629174706175)] do
    let e := mkApp2 q(Nat.div) (mkNatLit a) (mkNatLit b)
    match (TypeChecker.whnf e).run env (fuel := fuel) with
    | .ok r =>
      unless r.rawNatLit? == some (a / b) do
        throwError "Nat.div {a} {b}: expected literal {a / b}"
    | .error _ => throwError "Nat.div {a} {b}: reduction failed"
