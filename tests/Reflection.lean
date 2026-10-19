import Lean4Lean.Verify.Primitive
import Lean4Lean.Primitive

-- Run with: lake env lean tests/Reflection.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let fail {α} : TypeChecker.M α := throw (.other "invalid reflection")
  for r in [Primitive.Reflection.defn₁, Primitive.Reflection.defn₂] do
    unless ((r.check fail).run env).isOk do
      throwError "rejected a reflection-family type"
    unless ((r.checkITE fail).run env).isOk do
      throwError "rejected a supported polymorphic conditional"
    unless ((r.checkNatDITE fail).run env).isOk do
      throwError "rejected a supported dependent conditional"
    for bad in [{ r with ofTrue := r.ofFalse }, { r with ofFalse := r.ofTrue }] do
      if ((bad.checkNatDITE fail).run env).isOk then
        throwError "accepted a reflection with swapped proof converters"

  -- Both proof converters are well typed, but a selector that ignores the
  -- Boolean argument must fail one of the two checked computation equations.
  let r : Primitive.Reflection := {
    type := q(fun p (_ : Bool) => p ∧ ¬p)
    ofTrue := q(fun p (h : p ∧ ¬p) => h.1)
    ofFalse := q(fun p (h : p ∧ ¬p) => h.2)
    toDec := q(fun p (_ : Bool) (h : p ∧ ¬p) => Decidable.isTrue h.1) }
  for bad in [r,
      { r with toDec := q(fun p (_ : Bool) (h : p ∧ ¬p) => Decidable.isFalse h.2) }] do
    unless ((bad.check fail).run env).isOk do
      throwError "malformed test: the reflection family should be well typed"
    unless ((TypeChecker.checkType bad.natDITE).run env).isOk do
      throwError "malformed test: the dependent conditional should be well typed"
    unless ((TypeChecker.checkType bad.ite).run env).isOk do
      throwError "malformed test: the polymorphic conditional should be well typed"
    if ((bad.checkITE fail).run env).isOk then
      throwError "accepted a polymorphic conditional that ignores its Boolean argument"
    if ((bad.checkNatDITE fail).run env).isOk then
      throwError "accepted a dependent conditional that ignores its Boolean argument"

  for cond in [Primitive.Condition.natLE, Primitive.Condition.natEq] do
    for ite in [false, true] do
      unless ((cond.check fail (ite := ite) (dite := true)).run env).isOk do
        throwError "rejected a supported reflected natural-number condition"
      let .reflectNatNat asBool reflect proof := cond.impl
        | throwError "malformed test: expected a reflected condition"
      for bad in [
          { cond with dec := q(fun (_ _ : Nat) => true) },
          { cond with impl := .reflectNatNat q(fun (_ _ : Nat) => true) reflect proof },
          { cond with impl := .reflectNatNat asBool reflect q(fun (_ _ : Nat) => Nat.zero) }] do
        if ((bad.check fail (ite := ite) (dite := true)).run env).isOk then
          throwError "accepted an invalid reflected decision function, Boolean function, or proof"
