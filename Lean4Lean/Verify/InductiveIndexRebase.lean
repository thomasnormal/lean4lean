import Lean4Lean.Verify.InductiveIndexBaseInsertion
import Lean4Lean.Verify.InductiveIndexBaseStrengthening
import Lean4Lean.Verify.InductiveIndexRebaseTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem SelectedRecursorTelescope.rebase
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller larger : MLCtx} {ids removedIds : List FVarId}
    {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (removal : IndexMLCtxExtension smaller removedIds initial)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids)
    (largerWF : larger.WF env universes)
    (insertion : VLCtx.FVLift smaller.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ reduced aligned target,
      SelectedRecursorTelescope env universes full smaller ids reduced ∧
      reduced.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx aligned 0
        (.consN (.skipN .refl removedIds.length) ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned ∧
      SelectedRecursorTelescope env universes full larger ids target ∧
      target.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 := by
  obtain ⟨reduced, aligned, reducedTelescope, reducedWF, contraction, contexts⟩ :=
    telescope.strengthenExtension envWF initialWF removal supported
  have smallerWF : smaller.WF env universes := by
    simpa only [removal.drop_eq] using MLCtx.WF.dropN removedIds.length removal.bound initialWF
  obtain ⟨target, targetTelescope, targetWF, insertionWeakening⟩ :=
    reducedTelescope.insertBase envWF smallerWF largerWF insertion freshBase
  exact ⟨reduced, aligned, target, reducedTelescope, reducedWF, contraction, contexts,
    targetTelescope, targetWF, insertionWeakening⟩

end Lean4Lean.AddInductive
