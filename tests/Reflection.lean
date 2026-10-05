import Lean4Lean.Verify.Primitive

-- Run with: lake env lean tests/Reflection.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let fail {α} : TypeChecker.M α := throw (.other "invalid reflection")
  for r in [Environment.Reflection.defn₁, Environment.Reflection.defn₂] do
    unless ((r.check fail).run env).isOk do
      throwError "rejected a reflection-family type"
    unless ((r.checkNatDITE fail).run env).isOk do
      throwError "rejected a supported dependent conditional"
    for bad in [{ r with ofTrue := r.ofFalse }, { r with ofFalse := r.ofTrue }] do
      if ((bad.checkNatDITETypes fail).run env).isOk then
        throwError "accepted swapped proof converters in the type-checking prefix"
      if ((bad.checkNatDITE fail).run env).isOk then
        throwError "accepted a reflection with swapped proof converters"

  -- Both proof converters are well typed, but a selector that ignores the
  -- Boolean argument must fail one of the two checked computation equations.
  let r : Environment.Reflection := {
    type := q(fun p (_ : Bool) => p ∧ ¬p)
    ofTrue := q(fun p (h : p ∧ ¬p) => h.1)
    ofFalse := q(fun p (h : p ∧ ¬p) => h.2)
    toDec := q(fun p (_ : Bool) (h : p ∧ ¬p) => Decidable.isTrue h.1) }
  for bad in [r,
      { r with toDec := q(fun p (_ : Bool) (h : p ∧ ¬p) => Decidable.isFalse h.2) }] do
    unless ((bad.check fail).run env).isOk do
      throwError "malformed test: the reflection family should be well typed"
    unless ((bad.checkNatDITETypes fail).run env).isOk do
      throwError "malformed test: the conditional and proof converters should be well typed"
    if ((bad.checkNatDITE fail).run env).isOk then
      throwError "accepted a dependent conditional that ignores its Boolean argument"
