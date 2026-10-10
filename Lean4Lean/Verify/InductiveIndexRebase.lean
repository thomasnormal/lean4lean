import Lean4Lean.Verify.InductiveIndexBaseInsertion
import Lean4Lean.Verify.InductiveIndexBaseStrengthening
import Lean4Lean.Verify.InductiveIndexDomainSupport
import Lean4Lean.Verify.InductiveIndexRebaseTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

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

theorem TranslatedRecursorIndexTrace.selectedTelescopeRebasedOfStoredDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (smaller : MLCtx) (smallerWF : smaller.WF env universes) (baseLift : Lift)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx model.vlctx 0 baseLift 0)
    {params : List FVarId} {steps : List BinderStep}
    (stored : BinderStoredIndexTypeFVarsIn params current steps)
    (values : BinderStep.indexValues steps = finalIndices.toList)
    (parameters : params ⊆ smaller.vlctx.fvars)
    (prefixRetained : indices.toList.map Expr.fvarId! ⊆ smaller.vlctx.fvars)
    (larger : MLCtx) (largerWF : larger.WF env universes) (inserted : Nat)
    (insertion : VLCtx.FVLift smaller.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier,
      Expr.fvar identifier ∈ finalIndices.toList.drop indices.size →
      identifier ∉ larger.vlctx.fvars) :
    ∃ chronological ids reduced aligned target,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids reduced ∧
      reduced.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned ∧
      SelectedRecursorTelescope env universes current.lctx larger ids target ∧
      target.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 := by
  obtain ⟨chronological, ids, reduced, aligned, chronologicalWF, chronologicalNative,
    chronologicalVirtual, extension, array, reducedTelescope, reducedWF, contraction, contexts⟩ :=
    history.selectedTelescopeStrengthenedOfStoredDomains model modelWF native
      converted reserved current frame envWF smaller smallerWF baseLift baseWeakening stored
      values parameters prefixRetained
  have selectedFresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars := by
    intro identifier member
    apply freshBase identifier
    rw [array, ← Array.length_toList, List.drop_left]
    exact List.mem_map.mpr ⟨identifier, member, rfl⟩
  obtain ⟨target, targetTelescope, targetWF, insertionWeakening⟩ :=
    reducedTelescope.insertBase envWF smallerWF largerWF insertion selectedFresh
  exact ⟨chronological, ids, reduced, aligned, target, chronologicalWF, chronologicalNative,
    chronologicalVirtual, extension, array, reducedTelescope, reducedWF, contraction, contexts,
    targetTelescope, targetWF, insertionWeakening⟩

end Lean4Lean.AddInductive
