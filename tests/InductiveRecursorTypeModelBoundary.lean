import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRecursorTypeModelBoundaryTest

#check RecursorInfoModelEndpoint.declaredRecursorFromDomains

run_meta
  let theoremName := ``RecursorInfoModelEndpoint.declaredRecursorFromDomains
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "declared recursor type/model boundary is not theorem-backed"
  let some proof := information.value? (allowOpaque := true) |
    throwError "declared recursor type/model boundary proof missing"
  if proof.hasSorry then
    throwError "declared recursor type/model boundary has an admission"
  let typeAxioms ← collectAxioms ``RecursorInfoModelEndpoint.recursorTypeFromDomains
  let modelAxioms ← collectAxioms ``RecursorTypeModelReceipt.existsDeclaredRecursor
  let axioms ← collectAxioms theoremName
  for axiomName in axioms do
    unless typeAxioms.contains axiomName || modelAxioms.contains axiomName do
      throwError "declared recursor type/model boundary has an unexpected dependency: {axiomName}"
  logInfo m!"{theoremName}: explicit selected-domain receipt and declared model constant"

end InductiveRecursorTypeModelBoundaryTest
