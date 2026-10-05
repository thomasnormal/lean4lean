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
