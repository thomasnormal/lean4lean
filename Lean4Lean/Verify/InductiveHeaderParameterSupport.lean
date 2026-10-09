import Lean4Lean.Verify.InductiveBinderSupport

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def CheckedHeaderSupportSources (nparams : Nat) (types : Array InductiveType) (original : Context)
    (stats : InductiveStats) (current : Context) : Prop :=
  stats.HeaderSizes types.size ∧ ∀ parent, parent < types.size →
    CheckedHeaderSupportSource nparams types parent original stats.params stats.nindices[parent]! current

theorem CheckedHeaderSupportSources.toSources {nparams : Nat} {types : Array InductiveType}
    {original current : Context} {stats : InductiveStats}
    (sources : CheckedHeaderSupportSources nparams types original stats current) :
    CheckedHeaderSources nparams types original stats current :=
  ⟨sources.1, fun parent hparent => (sources.2 parent hparent).toSource⟩

private def SupportedHeaderTracePrefix (nparams : Nat) (types : Array InductiveType) (processed : Nat)
    (original : Context) (stats : InductiveStats) (current : Context) : Prop :=
  ∀ parent, parent < processed →
    CheckedHeaderSupportSource nparams types parent original stats.params stats.nindices[parent]! current

private theorem SupportedHeaderTracePrefix.push {nparams processed : Nat} {types : Array InductiveType}
    {original current next : Context} {stats updated : InductiveStats} {count : Nat}
    (hprefix : SupportedHeaderTracePrefix nparams types processed original stats current)
    (hsize : stats.nindices.size = processed) (hindices : updated.nindices = stats.nindices.push count)
    (hparams : processed ≠ 0 → updated.params = stats.params)
    (frame : current.RecursorScopeFrame next)
    (source : CheckedHeaderSupportSource nparams types processed original updated.params count next) :
    SupportedHeaderTracePrefix nparams types (processed + 1) original updated next := by
  intro parent hparent
  by_cases hprevious : parent < processed
  · have hvalid : parent < stats.nindices.size := by omega
    have hpush : parent < (stats.nindices.push count).size := by simp; omega
    simpa only [hparams (by omega), hindices, getElem!_pos (stats.nindices.push count) parent hpush,
      Array.getElem_push_lt hvalid, getElem!_pos stats.nindices parent hvalid] using
      (hprefix parent hprevious).mono frame
  · have heq : parent = processed := by omega
    subst parent
    simpa [hindices, getElem!_pos, Array.getElem_push, hsize] using source

private structure SupportedHeaderTraceSizes (stats : InductiveStats) (processed nparams : Nat)
    (ctx : Context) : Prop where
  indices : stats.nindices.size = processed
  constants : stats.indConsts.size = processed
  levels : stats.levels.length = ctx.lparams.length
  params : stats.params.size = if processed = 0 then 0 else nparams

private theorem checkedHeader_loopInd_support (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (original ctx : Context) (post : α → Prop) (hbound : processed ≤ types.size)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hsizes : SupportedHeaderTraceSizes stats processed nparams ctx)
    (hframe : original.RecursorScopeFrame ctx)
    (hprefix : SupportedHeaderTracePrefix nparams types processed original stats ctx)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (hnext : ∀ stats current, CheckedHeaderSupportSources nparams types original stats current →
      original.RecursorScopeFrame current →
      BinderValuesBefore current current.lctx.decls.size stats.params.toList →
      (next stats current).WF post) :
    (checkInductiveTypes.loopInd nparams types next processed stats ctx).WF post := by
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i hprocessed
    apply Lean4Lean.AddInductive.readWF
    apply bindHeaderResultWF
    intro checkedUnit hguard
    cases checkedUnit
    apply bindHeaderResultWF
    intro inferred hinferred
    apply Lean4Lean.AddInductive.readWF
    apply bindHeaderResultWF
    intro normalized hnormalized
    apply checkInductiveTypes.loopInd.loop.scopedTrace
    · exact hwf
    · exact hreserved
    intro terminal finalStats count current htrace hcurrent
    obtain ⟨hindices, hconstants, hlevels⟩ := htrace.headerFields
    have hparams : finalStats.params.size = nparams := by
      apply htrace.paramsCount
      simpa [Array.isEmpty, hsizes.constants] using hsizes.params
    have hcurrentSupport : BinderValuesBefore current current.lctx.decls.size finalStats.params.toList :=
      (htrace.paramsBefore hwf hreserved support).weaken htrace.parameterBase_le_size
    apply bindHeaderResultWF
    intro sorted hsort
    have hshared : processed ≠ 0 → finalStats.params = stats.params := by
      intro hnonzero
      apply htrace.paramsUnchanged
      simpa [Array.isEmpty, hsizes.constants] using hnonzero
    have hsource : CheckedHeaderSupportSource nparams types processed original finalStats.params count current := by
      refine ⟨ctx, stats, inferred, normalized, terminal, finalStats, current, sorted,
        hframe, ?_, ?_, ?_, hsizes.indices, hsizes.constants, hsizes.params, htrace, rfl, hsort,
        .refl current hcurrent.wf hcurrent.reserved, support⟩
      · simpa only [getElem!_pos types processed hprocessed] using hguard
      · simpa only [getElem!_pos types processed hprocessed] using hinferred
      · simpa only [getElem!_pos types processed hprocessed] using hnormalized
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      apply checkedHeader_loopInd_support nparams types next (processed + 1) _ original current post
      · omega
      · exact hcurrent.wf
      · exact hcurrent.reserved
      · exact ⟨by simpa [hindices] using hsizes.indices,
          by simpa [hconstants] using hsizes.constants,
          by simpa [hlevels, hcurrent.lparams] using hsizes.levels,
          by simpa using hparams⟩
      · exact hframe.trans hcurrent
      · apply hprefix.push (count := count) hsizes.indices
        · simp [hindices]
        · exact hshared
        · exact hcurrent
        · exact hsource
      · exact hcurrentSupport
      · exact hnext
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        apply checkedHeader_loopInd_support nparams types next (processed + 1) _ original current post
        · omega
        · exact hcurrent.wf
        · exact hcurrent.reserved
        · exact ⟨by simpa [hindices] using hsizes.indices,
            by simpa [hconstants] using hsizes.constants,
            by simpa [hlevels, hcurrent.lparams] using hsizes.levels,
            by simpa using hparams⟩
        · exact hframe.trans hcurrent
        · apply hprefix.push (count := count) hsizes.indices
          · simp [hindices]
          · exact hshared
          · exact hcurrent
          · exact hsource
        · exact hcurrentSupport
        · exact hnext
  · apply Lean4Lean.AddInductive.readWF
    have hcount : processed = types.size := by omega
    simp only [hsizes.levels, hsizes.indices, hsizes.constants, hcount,
      beq_self_eq_true, ite_true]
    split
    · apply hnext _ ctx
      · exact ⟨⟨hsizes.indices.trans hcount, hsizes.constants.trans hcount⟩,
          fun parent hparent => hprefix parent (by omega)⟩
      · exact hframe
      · exact support
    · have hzero : types.size = 0 := by
        by_contra hnonzero
        have hparams : stats.params.size = nparams := by simpa [hcount, hnonzero] using hsizes.params
        simp [hparams] at ‹¬(stats.params.size == nparams) = true›
      simp only [panicWithPosWithDecl, panic, panicCore]
      apply hnext _ ctx
      · refine ⟨?_, fun parent hparent => by omega⟩
        change 0 = types.size ∧ 0 = types.size
        simp [hzero]
      · exact hframe
      · intro value hvalue; cases hvalue
termination_by types.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.scopedHeaderSupportTraces (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      ctx.RecursorScopeFrame current →
      BinderValuesBefore current current.lctx.decls.size stats.params.toList →
      (next stats current).WF post) :
    (checkInductiveTypes nparams types next ctx).WF post := by
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  apply checkedHeader_loopInd_support nparams types next 0 _ ctx ctx post
  · omega
  · exact hwf
  · exact hreserved
  · exact ⟨rfl, rfl, by simp, rfl⟩
  · exact .refl ctx hwf hreserved
  · intro parent hparent; omega
  · intro value hvalue; cases hvalue
  · exact hnext

end Lean4Lean.AddInductive
