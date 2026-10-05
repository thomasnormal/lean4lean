import Lean4Lean.Verify.Primitive
import Lean.Util.CollectAxioms

namespace RebasedNatAddTest
open Lean hiding Environment Exception
open Lean4Lean

example {environment : VEnv} {function : VExpr} (specification : VEnv.NatAddSpec environment function)
    (wellOrdered : environment.Ordered) (primitives : environment.HasPrimitives)
    (hasNat : environment.contains ``Nat) (first second : Nat) :
    environment.IsDefEq 0 []
      (.app (.app function (.natLit first)) (.natLit second))
      (.natLit (first + second)) .nat :=
  specification.eval wellOrdered primitives hasNat first second

example {environment : VEnv} {function : VExpr} {functionName : Name}
    (specification : VEnv.NatAddSpec environment function)
    (wellOrdered : environment.Ordered) (primitives : environment.HasPrimitives)
    (hasNat : environment.contains ``Nat)
    (definitionEquality : environment.IsDefEq 0 [] (.const functionName []) function
      (.forallE .nat (.forallE .nat .nat))) :
    environment.ReflectsNatNatNat functionName Nat.add :=
  specification.reflects wellOrdered primitives hasNat definitionEquality

run_meta
  let allowed := #[``propext, ``Quot.sound, ``sorryAx, ``Classical.choice]
  for theoremName in #[``VEnv.HasPrimitives.natSucc_type, ``VEnv.HasPrimitives.natLit_type,
      ``VEnv.NatAddSpec.mono, ``VEnv.NatAddSpec.eval, ``VEnv.NatAddSpec.reflects] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "Nat.add contract is an axiom"
    let some proof := information.value? (allowOpaque := true)
      | throwError "Nat.add contract proof absent"
    if proof.hasSorry then throwError "Nat.add contract direct admission: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Nat.add contract dependency outside the existing checker baseline: {dependency}"
    logInfo m!"{theoremName}: {repr dependencies}"

end RebasedNatAddTest
