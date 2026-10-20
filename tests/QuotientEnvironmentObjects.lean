import Lean4Lean.Verify.TypeChecker.ScopedMethods
import Lean.Util.CollectAxioms

namespace QuotientEnvironmentObjectsTest
open Lean hiding Environment Exception
open Lean4Lean

example (valid : TrEnv' safety constants true environment) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] :=
  TrEnv'.quotientObjects valid

example (valid : TrEnv safety native environment) (initialized : native.quotInit = true) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] :=
  TrEnv.quotientObjects valid initialized

run_meta
  let _environment ← getEnv
  for theoremName in #[``TrEnv'.quotientObjects, ``TrEnv.quotientObjects] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "quotient object theorem is an axiom"
    let some proof := information.value? (allowOpaque := true)
      | throwError "quotient object theorem proof is missing"
    if proof.hasSorry then throwError "quotient object theorem has a direct admission"
    logInfo m!"{theoremName}: inherited axioms = {repr (← collectAxioms theoremName)}"
  logInfo m!"quotient object availability wrappers have inspected theorem proofs with no direct admissions"

end QuotientEnvironmentObjectsTest
