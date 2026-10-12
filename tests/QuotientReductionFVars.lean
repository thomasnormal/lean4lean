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
  if let some proof := information.value? then
    if proof.hasSorry then throwError "quotient FVarsBelow theorem has an admission"
  logInfo m!"quotient reduction FVarsBelow theorem is theorem-backed and admission-free"

end QuotientReductionFVarsTest
