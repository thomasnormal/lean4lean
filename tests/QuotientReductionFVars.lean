import Lean4Lean.Verify.TypeChecker.WHNF
import Lean.Util.CollectAxioms

namespace QuotientReductionFVarsTest
open Lean hiding Environment Exception
open Lean4Lean

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    (translated : context.TrExprS expression semantic) :
    (quotReduceRec expression TypeChecker.Inner.whnf).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced → context.FVarsBelow expression reduced) :=
  TypeChecker.Inner.quotReduceRec.fvarsBelow translated

run_meta
  let theoremName := ``TypeChecker.Inner.quotReduceRec.fvarsBelow
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "quotient FVarsBelow theorem is an axiom"
  let some proof := information.value? (allowOpaque := true)
    | throwError "quotient FVarsBelow theorem proof is missing"
  if proof.hasSorry then throwError "quotient FVarsBelow theorem has a direct admission"
  logInfo m!"quotient FVarsBelow: inspected theorem proof has no direct admission; inherited axioms = {repr (← collectAxioms theoremName)}"

end QuotientReductionFVarsTest
