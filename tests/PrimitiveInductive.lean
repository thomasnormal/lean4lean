import Lean4Lean.Verify.PrimitiveInductive
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace PrimitiveInductiveTest

private def boolType : InductiveType := {
  name := ``Bool
  type := .sort (.succ .zero)
  ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩]
}

private def natType (binderName : Name := `value)
    (binderInfo : BinderInfo := .default) : InductiveType := {
  name := ``Nat
  type := .sort (.succ .zero)
  ctors := [⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]
}

private def check (env : Kernel.Environment) (label : String)
    (types : List InductiveType) (expected : Option Bool)
    (lparams : List Name := []) (nparams : Nat := 0) (isUnsafe : Bool := false) : MetaM Unit := do
  let observed := (Environment.checkPrimitiveInductive env lparams nparams types isUnsafe).toOption
  unless observed == expected do
    throwError "{label}: expected {repr expected}, got {repr observed}"

run_meta
  for env in [Kernel.Environment.empty `PrimitiveInductiveTest, (← Lean.getEnv).toKernelEnv] do
    check env "Bool" [boolType] (some true)
    for binderInfo in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
      for binderName in [Name.anonymous, `value, `nested.binder] do
        check env "Nat binder variation" [natType binderName binderInfo] (some true)
    for type in [boolType, natType] do
      check env "unsafe primitive" [type] (some false) (isUnsafe := true)
      check env "universe-polymorphic primitive" [type] (some false) (lparams := [`universe])
      check env "parameterized primitive" [type] (some false) (nparams := 1)
      check env "primitive in Prop" [{ type with type := .sort .zero }] (some false)
      check env "primitive in Type 1" [{ type with type := .sort (.succ (.succ .zero)) }]
        (some false)
      check env "missing constructors" [{ type with ctors := [] }] none
      check env "swapped constructors" [{ type with ctors := type.ctors.reverse }] none
      check env "duplicate constructor" [{ type with ctors := type.ctors ++ [type.ctors.head!] }]
        none
      check env "wrong first constructor" [{ type with ctors :=
        { name := `Wrong, type := .const type.name [] } :: type.ctors.tail }] none
      check env "constructor universe mismatch" [{ type with ctors :=
        { name := type.ctors.head!.name, type := .const type.name [.zero] } :: type.ctors.tail }]
        none
    check env "empty declaration" [] (some false)
    check env "mutual declaration" [boolType, natType] (some false)
    check env "ordinary inductive" [{ boolType with name := `Ordinary }] (some false)
    check env "Nat.succ wrong domain" [{ natType with ctors := [natType.ctors.head!,
      ⟨``Nat.succ, .forallE `value (.const ``Bool []) (.const ``Nat []) .default⟩] }] none
    check env "Nat.succ dependent result" [{ natType with ctors := [natType.ctors.head!,
      ⟨``Nat.succ, .forallE `value (.const ``Nat []) (.bvar 0) .default⟩] }] none
    check env "Nat.succ lambda" [{ natType with ctors := [natType.ctors.head!,
      ⟨``Nat.succ, .lam `value (.const ``Nat []) (.const ``Nat []) .default⟩] }] none

  for theoremName in [``Environment.checkPrimitiveInductive.eq_true_iff,
      ``Environment.checkPrimitiveInductive.WF] do
    let axioms ← collectAxioms theoremName
    logInfo m!"{theoremName}: axioms = {repr axioms}"
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound, ``Lean.Expr.eqv_eq,
          ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq].contains axiomName do
        throwError "{theoremName}: unexpected axiom {axiomName}"

end PrimitiveInductiveTest
