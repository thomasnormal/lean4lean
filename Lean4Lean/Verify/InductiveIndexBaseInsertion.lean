import Lean4Lean.Verify.InductiveIndexSelectedTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem IndexMLCtxExtension.virtualFVars
    {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.vlctx.fvars = ids.reverse ++ initial.vlctx.fvars := by
  induction extension with
  | nil => rfl
  | @push ids model earlier identifier name domain semantic binder tailInduction =>
    change identifier :: model.vlctx.fvars = (ids ++ [identifier]).reverse ++ initial.vlctx.fvars
    simp only [tailInduction, List.reverse_append, List.reverse_singleton,
      List.cons_append, List.nil_append]

theorem SelectedRecursorTelescope.insertBase
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids : List FVarId} {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (largerWF : larger.WF env universes)
    (baseWeakening : VLCtx.FVLift initial.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ transported,
      SelectedRecursorTelescope env universes full larger ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' final.vlctx transported.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 := by
  revert freshBase
  induction telescope with
  | nil =>
    intro _
    exact ⟨larger, .nil, largerWF, baseWeakening.toFVLift'⟩
  | @push ids model earlier identifier physicalIndex name domain binder semantic
      lookup fresh translated typed tailInduction =>
    intro freshBase
    have earlierFresh : ∀ selected ∈ ids, selected ∉ larger.vlctx.fvars := by
      intro selected member
      exact freshBase selected (List.mem_append_left _ member)
    obtain ⟨transported, transportedTelescope, transportedWF, weakening⟩ := tailInduction earlierFresh
    have notEarlier : identifier ∉ ids := by
      intro member
      obtain ⟨_, _, _, _, _, _, earlierLookup⟩ := earlier.lookups initialWF identifier member
      rw [fresh] at earlierLookup
      cases earlierLookup
    have transportedFresh : transported.lctx.find? identifier = none := by
      apply transportedWF.tr.find?_eq_none.mpr
      rw [transportedTelescope.extension.virtualFVars]
      simp only [List.mem_append, List.mem_reverse, not_or]
      exact ⟨notEarlier, freshBase identifier (by simp only [List.mem_append, List.mem_singleton, or_true])⟩
    have transportedTranslation : TrExprS env universes transported.vlctx domain
        (semantic.liftN inserted ids.length) := by
      simpa only [Lift.consN, VExpr.lift'_consN_skipN] using
        translated.weakFV' envWF.ordered weakening transportedWF.tr.wf
    have transportedType : env.IsType universes.length transported.vlctx.toCtx
        (semantic.liftN inserted ids.length) := by
      simpa only [Lift.consN, VExpr.lift'_consN_skipN] using
        typed.weak' envWF.ordered weakening.toCtx
    let nextModel := MLCtx.vlam identifier name domain
      (semantic.liftN inserted ids.length) binder transported
    refine ⟨nextModel, .push transportedTelescope identifier physicalIndex name domain binder
      (semantic.liftN inserted ids.length) lookup transportedFresh transportedTranslation transportedType,
      ⟨transportedWF, transportedFresh, transportedTranslation, transportedType⟩, ?_⟩
    simpa only [nextModel, MLCtx.vlctx, VLocalDecl.lift', VLocalDecl.depth,
      VExpr.lift'_consN_skipN, Lift.consN_consN, List.length_append, List.length_singleton] using
      VLCtx.FVLift'.cons_fvar (identifier, domain.fvarsList) (.vlam semantic)
        translated.fvarsList weakening

theorem SelectedRecursorTelescope.insertExtension
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids insertedIds : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (insertion : IndexMLCtxExtension initial insertedIds larger)
    (largerWF : larger.WF env universes)
    (freshBase : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ transported,
      SelectedRecursorTelescope env universes full larger ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' final.vlctx transported.vlctx 0
        (.consN (.skipN .refl insertedIds.length) ids.length) 0 := by
  have initialWF : initial.WF env universes := by
    simpa only [insertion.drop_eq] using MLCtx.WF.dropN insertedIds.length insertion.bound largerWF
  exact telescope.insertBase envWF initialWF largerWF insertion.weakening freshBase

theorem TranslatedRecursorIndexTrace.selectedTelescopeInserted
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (larger : MLCtx) (largerWF : larger.WF env universes) (inserted : Nat)
    (baseWeakening : VLCtx.FVLift model.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier, Expr.fvar identifier ∈ finalIndices.toList.drop indices.size →
      identifier ∉ larger.vlctx.fvars) :
    ∃ chronological ids transported,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx larger ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' chronological.vlctx transported.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 := by
  obtain ⟨chronological, ids, chronologicalWF, chronologicalNative, chronologicalVirtual,
    extension, array, telescope⟩ :=
      history.selectedTelescopeAt model modelWF native converted reserved current frame
  have selectedFresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars := by
    intro identifier member
    apply freshBase identifier
    rw [array, ← Array.length_toList, List.drop_left]
    exact List.mem_map.mpr ⟨identifier, member, rfl⟩
  obtain ⟨transported, transportedTelescope, transportedWF, weakening⟩ :=
    telescope.insertBase envWF modelWF largerWF baseWeakening selectedFresh
  exact ⟨chronological, ids, transported, chronologicalWF, chronologicalNative, chronologicalVirtual,
    extension, array, transportedTelescope, transportedWF, weakening⟩

end Lean4Lean.AddInductive
