import Lean4Lean.Verify.Primitive

-- Run with: lake env lean tests/GcdAndBitwise.lean
-- Native GCD and bitwise reductions remain disabled; these exercise unfolding.
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let some (.defnInfo gcd) := env.find? ``Nat.gcd | throwError "missing Nat.gcd"
  match (Environment.checkPrimitiveDef gcd).run env with
  | .ok true => pure ()
  | _ => throwError "rejected the reference Nat.gcd implementation"
  for value in [q(fun (_ _ : Nat) => Nat.zero), q(fun (_ : Nat) (n : Nat) => n), q(Nat.mod)] do
    if ((Environment.checkPrimitiveDef { gcd with value }).run env).isOk then
      throwError "accepted an incorrect Nat.gcd implementation"
  for (a, b) in [(0, 0), (0, 17), (17, 0), (1, 23), (17, 17), (6, 9), (1000, 3000),
      (8589934591, 6442450943)] do
    match (TypeChecker.whnf (mkApp2 q(Nat.gcd) (mkNatLit a) (mkNatLit b))).run env with
    | .ok result =>
      unless TypeChecker.Inner.rawNatLitExt? result == some (Nat.gcd a b) do
        throwError "Nat.gcd {a} {b}: incorrect unfolded result"
    | .error e => throwError "Nat.gcd {a} {b}: {e.toMessageData {}}"

  let some (.defnInfo bitwise) := env.find? ``Nat.bitwise | throwError "missing Nat.bitwise"
  match (Environment.checkPrimitiveDef bitwise).run env with
  | .ok true => pure ()
  | _ => throwError "rejected the reference Nat.bitwise implementation"
  for value in [q(fun (_ : Bool → Bool → Bool) (_ _ : Nat) => Nat.zero),
      q(fun (_ : Bool → Bool → Bool) (n : Nat) (_ : Nat) => n),
      q(fun (_ : Bool → Bool → Bool) (n m : Nat) => Nat.bitwise Bool.and n m)] do
    if ((Environment.checkPrimitiveDef { bitwise with value }).run env).isOk then
      throwError "accepted an incorrect Nat.bitwise implementation"
  let ops : List (Expr × (Bool → Bool → Bool)) := [
    (q(Bool.and), Bool.and), (q(Bool.or), Bool.or), (q(Bool.xor), Bool.xor),
    (q(fun (_ _ : Bool) => false), fun _ _ => false),
    (q(fun (_ _ : Bool) => true), fun _ _ => true)]
  for (n, m) in [(0, 0), (0, 17), (17, 0), (17, 17), (6, 9), (31, 7), (7, 31),
      (1208925819614629174706177, 1208925819614629174706179)] do
    for (f, g) in ops do
      let e := mkApp3 q(Nat.bitwise) f (mkNatLit n) (mkNatLit m)
      match (TypeChecker.whnf e).run env with
      | .ok result =>
        unless TypeChecker.Inner.rawNatLitExt? result == some (Nat.bitwise g n m) do
          throwError "Nat.bitwise {n} {m}: incorrect unfolded result for {f}"
      | .error e => throwError "Nat.bitwise {n} {m}: {e.toMessageData {}}"
