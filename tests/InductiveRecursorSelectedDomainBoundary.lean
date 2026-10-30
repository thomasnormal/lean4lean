import Lean4Lean.Verify.InductiveIndexDomainSupport
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRecursorSelectedDomainBoundaryTest

/-- Binder integrity proves the native index-domain free-variable boundary.  This is
    the strongest selected-domain fact available before a semantic model is supplied. -/
example {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo} {base : List FVarId}
    (integrity : RecursorBinderIntegrity stats types checkedRoot current infos)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    ∀ parent, parent < types.size →
      SelectedRecursorDomainFVars current.lctx base (infos[parent]!.indices.toList.map Expr.fvarId!) :=
  integrity.selectedIndexDomains parameters

/-- A selected-domain support receipt is strictly semantic: it supplies the
    chronological prefix model, translated domain, and typehood for each selected
    binder.  Native cdecl/index integrity alone does not contain these fields. -/
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
            env.IsType universes.length model.vlctx.toCtx semantic := by
  exact support.domainReceipts

run_meta
  let fvarTheorem := ``RecursorBinderIntegrity.selectedIndexDomains
  let fvarAxioms ← collectAxioms fvarTheorem
  if fvarAxioms.contains ``sorryAx then
    throwError "index-domain integrity boundary depends on sorryAx"
  let semanticTheorem := ``RecursorSelectedDomainSupport.domainReceipts
  let semanticInfo ← getConstInfo semanticTheorem
  if semanticInfo matches .axiomInfo _ then
    throwError "semantic selected-domain boundary is not theorem-backed"
  let some semanticProof := semanticInfo.value? (allowOpaque := true) |
    throwError "semantic selected-domain boundary proof missing"
  if semanticProof.hasSorry then
    throwError "semantic selected-domain boundary has an admission"
  logInfo "integrity supplies index-domain FVar support; semantic selected-domain support remains an explicit model/pass premise"

end InductiveRecursorSelectedDomainBoundaryTest
