import Lean4Lean.Verify.InductiveIndexDomainStrengthening

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def SelectedRecursorDomainFVars (full : LocalContext) (base ids : List FVarId) : Prop :=
  ∀ selectedPrefix identifier suffix, ids = selectedPrefix ++ identifier :: suffix →
    ∀ physicalIndex name domain binder,
      full.find? identifier = some (.cdecl physicalIndex identifier name domain binder .default) →
      domain.fvarsList ⊆ selectedPrefix ++ base

theorem SelectedRecursorDomainFVars.appendLeft
    {full : LocalContext} {base ids tail : List FVarId}
    (supported : SelectedRecursorDomainFVars full base (ids ++ tail)) :
    SelectedRecursorDomainFVars full base ids := by
  intro selectedPrefix identifier suffix split physicalIndex name domain binder lookup
  exact supported selectedPrefix identifier (suffix ++ tail)
    (by simp only [split, List.append_assoc, List.cons_append])
    physicalIndex name domain binder lookup

theorem SelectedRecursorDomainFVars.last
    {full : LocalContext} {base ids : List FVarId} {identifier : FVarId}
    (supported : SelectedRecursorDomainFVars full base (ids ++ [identifier]))
    {physicalIndex : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (lookup : full.find? identifier =
      some (.cdecl physicalIndex identifier name domain binder .default)) :
    domain.fvarsList ⊆ ids ++ base :=
  supported ids identifier [] rfl physicalIndex name domain binder lookup

theorem SelectedRecursorTelescope.strengthenBase
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller : MLCtx} {ids : List FVarId} {baseLift : Lift}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (smallerWF : smaller.WF env universes)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx initial.vlctx 0 baseLift 0)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids) :
    ∃ transported aligned,
      SelectedRecursorTelescope env universes full smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned := by
  revert supported
  induction telescope with
  | nil =>
    intro _
    exact ⟨smaller, initial.vlctx, .nil, smallerWF, baseWeakening,
      .refl envWF.ordered initialWF.tr.wf⟩
  | @push ids model earlier identifier physicalIndex name domain binder semantic
      lookup fresh translated typed tailInduction =>
    intro supported
    obtain ⟨transported, aligned, transportedTelescope, transportedWF, weakening, contexts⟩ :=
      tailInduction supported.appendLeft
    have modelWF := earlier.context initialWF
    have closedDomain : Closed domain 0 := by
      simpa only [model.noBV] using translated.closed
    have supportedDomain : domain.FVarsIn (· ∈ transported.vlctx.fvars) := by
      apply fvarsIn_iff.mpr
      refine ⟨?_, (fvarsIn_iff.mp translated.fvarsIn).2⟩
      intro selected member
      rw [transportedTelescope.extension.virtualFVars]
      simpa only [List.mem_append, List.mem_reverse] using supported.last lookup member
    obtain ⟨level, domainTyped⟩ := typed
    obtain ⟨reduced, reducedTranslation, reducedType, domainEquality⟩ :=
      TrExprS.strengthenIsType envWF weakening contexts translated domainTyped closedDomain supportedDomain
    have transportedFresh : transported.lctx.find? identifier = none := by
      apply transportedWF.tr.find?_eq_none.mpr
      intro member
      have alignedMember := weakening.fvars_sublist.subset member
      rw [← contexts.fvars] at alignedMember
      exact modelWF.tr.find?_eq_none.mp fresh alignedMember
    let nextModel := MLCtx.vlam identifier name domain reduced binder transported
    let nextAligned := (some (identifier, domain.fvarsList),
      VLocalDecl.vlam (reduced.lift' (.consN baseLift ids.length))) :: aligned
    refine ⟨nextModel, nextAligned,
      .push transportedTelescope identifier physicalIndex name domain binder reduced
        lookup transportedFresh reducedTranslation ⟨level, reducedType⟩,
      ⟨transportedWF, transportedFresh, reducedTranslation, level, reducedType⟩, ?_, ?_⟩
    · simpa only [nextModel, nextAligned, MLCtx.vlctx, VLocalDecl.lift', VLocalDecl.depth,
        Lift.consN_consN, List.length_append, List.length_singleton] using
        VLCtx.FVLift'.cons_fvar (identifier, domain.fvarsList) (.vlam reduced)
          reducedTranslation.fvarsList weakening
    · refine contexts.cons ?_ (.vlam domainEquality)
      intro selected dependencies equality
      cases equality
      exact ⟨modelWF.tr.find?_eq_none.mp fresh, translated.fvarsList⟩

theorem SelectedRecursorTelescope.strengthenExtension
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller : MLCtx} {ids removedIds : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (removal : IndexMLCtxExtension smaller removedIds initial)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids) :
    ∃ transported aligned,
      SelectedRecursorTelescope env universes full smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0
        (.consN (.skipN .refl removedIds.length) ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned := by
  have smallerWF : smaller.WF env universes := by
    simpa only [removal.drop_eq] using MLCtx.WF.dropN removedIds.length removal.bound initialWF
  exact telescope.strengthenBase envWF initialWF smallerWF removal.weakening.toFVLift' supported

theorem TranslatedRecursorIndexTrace.selectedTelescopeStrengthened
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
    (supported : SelectedRecursorDomainFVars current.lctx smaller.vlctx.fvars
      ((finalIndices.toList.drop indices.size).map Expr.fvarId!)) :
    ∃ chronological ids transported aligned,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned := by
  obtain ⟨chronological, ids, chronologicalWF, chronologicalNative, chronologicalVirtual,
    extension, array, telescope⟩ :=
      history.selectedTelescopeAt model modelWF native converted reserved current frame
  have suffix : finalIndices.toList.drop indices.size = ids.map Expr.fvar := by
    rw [array, ← Array.length_toList, List.drop_left]
  have selectedSupport : SelectedRecursorDomainFVars current.lctx smaller.vlctx.fvars ids := by
    simpa only [suffix, List.map_map, Function.comp_def, Expr.fvarId!, List.map_id'] using supported
  obtain ⟨transported, aligned, transportedTelescope, transportedWF, weakening, contexts⟩ :=
    telescope.strengthenBase envWF modelWF smallerWF baseWeakening selectedSupport
  exact ⟨chronological, ids, transported, aligned, chronologicalWF, chronologicalNative,
    chronologicalVirtual, extension, array, transportedTelescope, transportedWF, weakening, contexts⟩

end Lean4Lean.AddInductive
