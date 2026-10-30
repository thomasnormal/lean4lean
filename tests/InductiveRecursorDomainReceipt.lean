import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRecursorDomainReceiptTest

#check SelectedRecursorTelescope.domainReceipt
#check RecursorSelectedDomainSupport.domainReceipts

example {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext} {initial : TypeChecker.MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent full initial) :
    ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
      ∃ projected, SelectedRecursorTelescope env universes full initial ids projected ∧
        ∀ identifier, identifier ∈ ids →
          ∃ preIds suffix model physicalIndex name domain binder semantic,
            ids = preIds ++ identifier :: suffix ∧
            SelectedRecursorTelescope env universes full initial preIds model ∧
            full.find? identifier =
              some (.cdecl physicalIndex identifier name domain binder .default) ∧
            model.lctx.find? identifier = none ∧
            TrExprS env universes model.vlctx domain semantic ∧
            env.IsType universes.length model.vlctx.toCtx semantic :=
  support.domainReceipts

run_meta
  let theoremName := ``RecursorSelectedDomainSupport.domainReceipts
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "selected-domain receipt eliminator is not theorem-backed"
  let some proof := information.value? (allowOpaque := true) |
    throwError "selected-domain receipt eliminator proof missing"
  if proof.hasSorry then
    throwError "selected-domain receipt eliminator has an admission"
  let sourceAxioms ← collectAxioms ``SelectedRecursorTelescope.domainReceipt
  let axioms ← collectAxioms theoremName
  for axiomName in axioms do
    unless sourceAxioms.contains axiomName do
      throwError "selected-domain receipt eliminator has an unexpected dependency: {axiomName}"
  logInfo m!"{theoremName}: every selected binder retains prefix model, cdecl provenance, translation, and typehood"

end InductiveRecursorDomainReceiptTest
