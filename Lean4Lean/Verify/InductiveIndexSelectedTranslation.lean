import Lean4Lean.Verify.InductiveRecursorTypeTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem SelectedRecursorTelescope.monoFull
    {env : VEnv} {universes : List Name} {left right : LocalContext}
    {initial final : MLCtx} {ids : List FVarId}
    (telescope : SelectedRecursorTelescope env universes left initial ids final)
    (lookups : ∀ identifier ∈ ids, left.find? identifier = right.find? identifier) :
    SelectedRecursorTelescope env universes right initial ids final := by
  revert lookups
  induction telescope with
  | nil => intro _; exact .nil
  | @push ids model earlier identifier physicalIndex name domain binder semantic
      lookup fresh translated typed tailInduction =>
    intro lookups
    have earlierLookups : ∀ selected ∈ ids, left.find? selected = right.find? selected := by
      intro selected member
      exact lookups selected (List.mem_append_left _ member)
    exact .push (tailInduction earlierLookups) identifier physicalIndex name domain binder semantic
      ((lookups identifier (by simp only [List.mem_append, List.mem_singleton, or_true])).symm.trans lookup)
      fresh translated typed

theorem IndexMLCtxExtension.selectedTelescope
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (finalWF : final.WF env universes) :
    SelectedRecursorTelescope env universes final.lctx initial ids final := by
  revert finalWF
  induction extension with
  | nil => intro _; exact .nil
  | @push ids model earlier identifier name domain semantic binder tailInduction =>
    intro finalWF
    have modelWF := finalWF.1
    have fresh := finalWF.2.1
    have translated := finalWF.2.2.1
    have typed := finalWF.2.2.2
    have initialWF : initial.WF env universes := by
      simpa only [earlier.drop_eq] using MLCtx.WF.dropN ids.length earlier.bound modelWF
    have earlierTelescope := tailInduction modelWF
    have retained : ∀ selected ∈ ids,
        model.lctx.find? selected =
          (MLCtx.vlam identifier name domain semantic binder model).lctx.find? selected := by
      intro selected member
      obtain ⟨_, _, _, _, _, _, projectedLookup⟩ :=
        earlierTelescope.lookups initialWF selected member
      have different : selected ≠ identifier := by
        intro equality
        subst selected
        rw [fresh] at projectedLookup
        cases projectedLookup
      rw [finalWF.find?_eq, modelWF.find?_eq]
      simp only [MLCtx.decls, List.find?_cons, LocalDecl.fvarId,
        beq_eq_false_iff_ne.mpr different]
    refine .push (earlierTelescope.monoFull retained) identifier model.length name domain binder
      semantic ?_ fresh translated typed
    rw [finalWF.find?_eq]
    simp only [MLCtx.decls, List.find?_cons, LocalDecl.fvarId, beq_self_eq_true]

theorem TranslatedRecursorIndexTrace.selectedTelescope
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes finalReader.lctx model ids finalModel := by
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
    history.mixedContext model modelWF native converted reserved
  refine ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array, ?_⟩
  simpa only [finalNative] using extension.selectedTelescope finalWF

theorem TranslatedRecursorIndexTrace.selectedTelescopeAt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx model ids finalModel := by
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array, telescope⟩ :=
    history.selectedTelescope model modelWF native converted reserved
  refine ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array, ?_⟩
  apply telescope.monoFull
  intro identifier member
  obtain ⟨_, _, _, _, _, lookup, _⟩ := telescope.lookups modelWF identifier member
  exact lookup.trans (frame.oldLookup (finalNative ▸ finalWF.tr.1) lookup).symm

end Lean4Lean.AddInductive
