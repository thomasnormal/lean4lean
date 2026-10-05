import Lean4Lean.Primitive

-- Run with: lake env lean tests/Modulo.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let some (.defnInfo mod) := env.find? ``Nat.mod | throwError "missing Nat.mod"
  match (Environment.checkPrimitiveDef mod).run env with
  | .ok _ => pure ()
  | .error e => throwError "rejected the reference Nat.mod implementation: {e.toMessageData {}}"
  for value in [q(fun (_ _ : Nat) => Nat.zero), q(fun (a : Nat) (_ : Nat) => a)] do
    if ((Environment.checkPrimitiveDef { mod with value }).run env).isOk then
      throwError "accepted an incorrect Nat.mod implementation"
