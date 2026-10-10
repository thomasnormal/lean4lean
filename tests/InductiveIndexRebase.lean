import Lean4Lean.Verify.InductiveIndexRebase

namespace InductiveIndexRebaseTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

private theorem rebaseReceiptComposes
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
  exact telescope.rebase envWF initialWF removal supported largerWF insertion freshBase

end InductiveIndexRebaseTest
