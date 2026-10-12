import Lean4Lean.Verify.TypeChecker.WHNF
import Lean.Util.CollectAxioms

namespace QuotientDefEqTest
open Lean hiding Environment Exception
open Lean4Lean

example {context : TypeChecker.VContext} (initialized : context.env.quotInit = true)
    (levels : List VLevel) (levelsWF : ∀ level ∈ levels, level.WF context.lparams.length) :
    context.IsDefEqU (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) :=
  context.quotientDefEq initialized levels levelsWF

run_meta
  let theoremName := ``TypeChecker.VContext.quotientDefEq
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "quotient defeq theorem is an axiom"
  if let some proof := information.value? then
    if proof.hasSorry then throwError "quotient defeq theorem has an admission"
  logInfo m!"quotient defeq theorem is theorem-backed and admission-free"

end QuotientDefEqTest
