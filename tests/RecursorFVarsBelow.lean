import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.RecursorFVarsBelow

open Lean Lean4Lean Lean4Lean.TypeChecker Lean4Lean.TypeChecker.Inner

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (reduceRecursor expression).WF context state fun outcome _ =>
      ∀ reduced, outcome = some reduced → context.FVarsBelow expression reduced :=
  reduceRecursor.fvarsBelow translated

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  let theoremName := ``Inner.reduceRecursor.fvarsBelow
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "recursor free-variable theorem is an axiom"
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless baseline.contains dependency do
      throwError "unexpected recursor free-variable dependency: {dependency}"
  logInfo m!"recursor free-variable preservation compiles without a direct admission; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.RecursorFVarsBelow
