import Lean4Lean.Verify.InductiveHeaderScope
import Lean4Lean.Verify.RecursorInfoIndices

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

private theorem bindHeaderResultWF {action : M α} {next : α → M β} {ctx : Context} {post : β → Prop}
    (hnext : ∀ result, action ctx = .ok result → (next result ctx).WF post) :
    ((action >>= next) ctx).WF post :=
  (show (action ctx).WF (fun result => action ctx = .ok result) from fun _ hresult => hresult).bind hnext

private theorem withHeaderDeclWF {ctx : Context} {name : Name} {bi : BinderInfo} {domain : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : (next (.fvar ⟨ctx.ngen.curr⟩) (recursorIndexContext ctx name bi domain)).WF post) :
    (withLocalDecl name bi domain next ctx).WF post := hnext

inductive CheckedHeaderTrace (nparams : Nat) :
    InductiveStats → Expr → Nat → Nat → Context → Expr → InductiveStats → Nat → Context → Prop where
  | stop {stats : InductiveStats} {type : Expr} {index nindices : Nat} {ctx : Context}
      (hnot : ∀ name domain body bi, type ≠ .forallE name domain body bi) (hparams : index = nparams) :
      CheckedHeaderTrace nparams stats type index nindices ctx type stats nindices ctx
  | freshParameter {stats : InductiveStats} {name : Name} {domain body : Expr} {bi : BinderInfo}
      {index nindices : Nat} {ctx : Context} {normalized terminal : Expr}
      {finalStats : InductiveStats} {finalIndices : Nat} {finalCtx : Context}
      (hparam : index < nparams) (hfirst : stats.indConsts.isEmpty = true)
      (hnormalized : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩))) : M Expr)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)) = .ok normalized)
      (tail : CheckedHeaderTrace nparams { stats with params := stats.params.push (.fvar ⟨ctx.ngen.curr⟩) }
        normalized (index + 1) nindices (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)
        terminal finalStats finalIndices finalCtx) :
      CheckedHeaderTrace nparams stats (.forallE name domain body bi) index nindices ctx
        terminal finalStats finalIndices finalCtx
  | reusedParameter {stats : InductiveStats} {name : Name} {domain body : Expr} {bi : BinderInfo}
      {index nindices : Nat} {ctx : Context} {paramType normalized terminal : Expr}
      {finalStats : InductiveStats} {finalIndices : Nat} {finalCtx : Context}
      (hparam : index < nparams) (hfirst : ¬ stats.indConsts.isEmpty = true)
      (htype : getType stats.params[index]! ctx = .ok paramType)
      (hequal : ((monadLift (TypeChecker.isDefEq domain paramType) : M Bool) ctx) = .ok true)
      (hnormalized : ((monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr) ctx) = .ok normalized)
      (tail : CheckedHeaderTrace nparams stats normalized (index + 1) nindices ctx
        terminal finalStats finalIndices finalCtx) :
      CheckedHeaderTrace nparams stats (.forallE name domain body bi) index nindices ctx
        terminal finalStats finalIndices finalCtx
  | index {stats : InductiveStats} {name : Name} {domain body : Expr} {bi : BinderInfo}
      {index nindices : Nat} {ctx : Context} {normalized terminal : Expr}
      {finalStats : InductiveStats} {finalIndices : Nat} {finalCtx : Context}
      (hparam : ¬ index < nparams)
      (hnormalized : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩))) : M Expr)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)) = .ok normalized)
      (tail : CheckedHeaderTrace nparams stats normalized index (nindices + 1)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)
        terminal finalStats finalIndices finalCtx) :
      CheckedHeaderTrace nparams stats (.forallE name domain body bi) index nindices ctx
        terminal finalStats finalIndices finalCtx

theorem checkInductiveTypes.loopInd.loop.scopedTrace (nparams fuel : Nat) (stats : InductiveStats)
    (type : Expr) (index nindices : Nat) (next : Expr → InductiveStats → Nat → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ terminal finalStats finalIndices current,
      CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices current →
      ctx.RecursorScopeFrame current → (next terminal finalStats finalIndices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next ctx).WF post := by
  induction fuel generalizing stats type index nindices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [checkInductiveTypes.loopInd.loop.eq_def]
    dsimp only
    split
    · rename_i name domain body bi
      split
      · rename_i hparam
        split
        · rename_i hfirst
          apply withHeaderDeclWF
          have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
          apply bindHeaderResultWF
          intro normalized hnormalized
          apply ih
          · exact hpush.wf
          · exact hpush.reserved
          intro terminal finalStats finalIndices current htrace hframe
          exact hnext terminal finalStats finalIndices current
            (.freshParameter hparam hfirst hnormalized htrace) (hpush.trans hframe)
        · rename_i hfirst
          apply bindHeaderResultWF
          intro paramType htype
          apply bindHeaderResultWF
          intro equal hequal
          split
          · apply Lean4Lean.AddInductive.bindWF
            intro _
            have heq : equal = true := by simpa using ‹equal = true›
            subst equal
            apply bindHeaderResultWF
            intro normalized hnormalized
            apply ih
            · exact hwf
            · exact hreserved
            intro terminal finalStats finalIndices current htrace hframe
            exact hnext terminal finalStats finalIndices current
              (.reusedParameter hparam hfirst htype hequal hnormalized htrace) hframe
          · exact Except.WF.throw
      · rename_i hparam
        apply withHeaderDeclWF
        have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
        apply bindHeaderResultWF
        intro normalized hnormalized
        apply ih
        · exact hpush.wf
        · exact hpush.reserved
        intro terminal finalStats finalIndices current htrace hframe
        exact hnext terminal finalStats finalIndices current
          (.index hparam hnormalized htrace) (hpush.trans hframe)
    · rename_i hnot
      split
      · exact Except.WF.throw
      · have hparams : index = nparams := by simpa using ‹¬(index != nparams) = true›
        exact hnext type stats nindices ctx (.stop hnot hparams) (.refl ctx hwf hreserved)

theorem CheckedHeaderTrace.terminal {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    ∀ name domain body bi, terminal ≠ .forallE name domain body bi := by
  induction trace with
  | stop hnot _ => exact hnot
  | freshParameter _ _ _ _ ih => exact ih
  | reusedParameter _ _ _ _ _ _ ih => exact ih
  | index _ _ _ ih => exact ih

theorem CheckedHeaderTrace.countBounds {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    index ≤ nparams ∧ nindices ≤ finalIndices := by
  induction trace with
  | stop _ hparams => exact ⟨Nat.le_of_eq hparams, Nat.le_refl _⟩
  | freshParameter _ _ _ _ ih => omega
  | reusedParameter _ _ _ _ _ _ ih => omega
  | index _ _ _ ih => omega

theorem CheckedHeaderTrace.headerFields {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    finalStats.nindices = stats.nindices ∧ finalStats.indConsts = stats.indConsts ∧ finalStats.levels = stats.levels := by
  induction trace with
  | stop _ _ => exact ⟨rfl, rfl, rfl⟩
  | freshParameter _ _ _ _ ih => exact ih
  | reusedParameter _ _ _ _ _ _ ih => exact ih
  | index _ _ _ ih => exact ih

theorem CheckedHeaderTrace.paramsCount {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams) :
    finalStats.params.size = nparams := by
  induction trace with
  | stop _ hindex => simpa [hindex] using hparams
  | freshParameter hparam hfirst hnormalized tail ih =>
    apply ih
    simpa [hfirst] using hparams
  | reusedParameter hparam hfirst htype hequal hnormalized tail ih =>
    apply ih
    simpa [hfirst] using hparams
  | index hparam hnormalized tail ih => exact ih hparams

theorem CheckedHeaderTrace.paramsUnchanged {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hfirst : ¬ stats.indConsts.isEmpty = true) : finalStats.params = stats.params := by
  induction trace with
  | stop _ _ => rfl
  | freshParameter _ hfirst' _ _ _ => exact False.elim (hfirst hfirst')
  | reusedParameter _ _ _ _ _ _ ih => exact ih hfirst
  | index _ _ _ ih => exact ih hfirst

theorem CheckedHeaderTrace.paramsSublist {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    stats.params.toList.Sublist finalStats.params.toList := by
  induction trace with
  | stop _ _ => exact .refl _
  | freshParameter _ _ _ _ ih =>
    refine List.Sublist.trans ?_ ih
    simp only [Array.toList_push]
    exact List.sublist_append_left _ _
  | reusedParameter _ _ _ _ _ _ ih => exact ih
  | index _ _ _ ih => exact ih

theorem CheckedHeaderTrace.scope {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) : ctx.RecursorScopeFrame finalCtx := by
  revert hwf hreserved
  induction trace with
  | stop _ _ => intro hwf hreserved; exact .refl _ hwf hreserved
  | @freshParameter stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hnormalized tail ih =>
    intro hwf hreserved
    have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
    exact hpush.trans (ih hpush.wf hpush.reserved)
  | reusedParameter _ _ _ _ _ _ ih => exact ih
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro hwf hreserved
    have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
    exact hpush.trans (ih hpush.wf hpush.reserved)

def CheckedHeaderSource (nparams : Nat) (types : Array InductiveType) (parent : Nat)
    (original : Context) (params : Array Expr) (count : Nat) (current : Context) : Prop :=
  ∃ (entry : Context) (stats : InductiveStats) (inferred normalized terminal : Expr)
    (finalStats : InductiveStats) (binderCtx : Context) (sorted : Expr),
    original.RecursorScopeFrame entry ∧
    entry.env.checkNoMVarNoFVar types[parent]!.name types[parent]!.type = .ok () ∧
    ((monadLift (TypeChecker.checkType types[parent]!.type) : M Expr) entry) = .ok inferred ∧
    ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
    stats.nindices.size = parent ∧ stats.indConsts.size = parent ∧
    stats.params.size = (if parent = 0 then 0 else nparams) ∧
    CheckedHeaderTrace nparams stats normalized 0 0 entry terminal finalStats count binderCtx ∧
    finalStats.params = params ∧
    ((monadLift (TypeChecker.ensureSort terminal) : M Expr) binderCtx) = .ok sorted ∧
    binderCtx.RecursorScopeFrame current

def CheckedHeaderSources (nparams : Nat) (types : Array InductiveType) (original : Context)
    (stats : InductiveStats) (current : Context) : Prop :=
  stats.HeaderSizes types.size ∧ ∀ parent, parent < types.size →
    CheckedHeaderSource nparams types parent original stats.params stats.nindices[parent]! current

theorem CheckedHeaderSource.mono {nparams parent count : Nat} {types : Array InductiveType}
    {original current next : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (frame : current.RecursorScopeFrame next) : CheckedHeaderSource nparams types parent original params count next := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent⟩ := source
  exact ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent.trans frame⟩

theorem CheckedHeaderSource.guarded {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    original.env.checkNoMVarNoFVar types[parent]!.name types[parent]!.type = .ok () := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent⟩ := source
  simpa only [hentry.env] using hguard

theorem CheckedHeaderSource.paramsCount {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) : params.size = nparams := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent⟩ := source
  rw [← hparams]
  apply htrace.paramsCount
  simpa [Array.isEmpty, hconst] using hparamCount

theorem CheckedHeaderSource.scope {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    original.RecursorScopeFrame current := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent⟩ := source
  exact hentry.trans ((htrace.scope hentry.wf hentry.reserved).trans hcurrent)

private def HeaderTracePrefix (nparams : Nat) (types : Array InductiveType) (processed : Nat)
    (original : Context) (stats : InductiveStats) (current : Context) : Prop :=
  ∀ parent, parent < processed →
    CheckedHeaderSource nparams types parent original stats.params stats.nindices[parent]! current

private theorem HeaderTracePrefix.push {nparams processed : Nat} {types : Array InductiveType}
    {original current next : Context} {stats updated : InductiveStats} {count : Nat}
    (hprefix : HeaderTracePrefix nparams types processed original stats current)
    (hsize : stats.nindices.size = processed) (hindices : updated.nindices = stats.nindices.push count)
    (hparams : processed ≠ 0 → updated.params = stats.params)
    (frame : current.RecursorScopeFrame next)
    (source : CheckedHeaderSource nparams types processed original updated.params count next) :
    HeaderTracePrefix nparams types (processed + 1) original updated next := by
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

private structure HeaderTraceSizes (stats : InductiveStats) (processed nparams : Nat) (ctx : Context) : Prop where
  indices : stats.nindices.size = processed
  constants : stats.indConsts.size = processed
  levels : stats.levels.length = ctx.lparams.length
  params : stats.params.size = if processed = 0 then 0 else nparams

private theorem checkedHeader_loopInd_traces (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (original ctx : Context) (post : α → Prop) (hbound : processed ≤ types.size)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hsizes : HeaderTraceSizes stats processed nparams ctx)
    (hframe : original.RecursorScopeFrame ctx)
    (hprefix : HeaderTracePrefix nparams types processed original stats ctx)
    (hnext : ∀ stats current, CheckedHeaderSources nparams types original stats current →
      original.RecursorScopeFrame current → (next stats current).WF post) :
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
    apply bindHeaderResultWF
    intro sorted hsort
    have hshared : processed ≠ 0 → finalStats.params = stats.params := by
      intro hnonzero
      apply htrace.paramsUnchanged
      simpa [Array.isEmpty, hsizes.constants] using hnonzero
    have hsource : CheckedHeaderSource nparams types processed original finalStats.params count current := by
      refine ⟨ctx, stats, inferred, normalized, terminal, finalStats, current, sorted,
        hframe, ?_, ?_, ?_, hsizes.indices, hsizes.constants, hsizes.params, htrace, rfl, hsort,
        .refl current hcurrent.wf hcurrent.reserved⟩
      · simpa only [getElem!_pos types processed hprocessed] using hguard
      · simpa only [getElem!_pos types processed hprocessed] using hinferred
      · simpa only [getElem!_pos types processed hprocessed] using hnormalized
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      apply checkedHeader_loopInd_traces nparams types next (processed + 1) _ original current post
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
      · exact hnext
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        apply checkedHeader_loopInd_traces nparams types next (processed + 1) _ original current post
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
termination_by types.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.scopedHeaderTraces (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, CheckedHeaderSources nparams types ctx stats current →
      ctx.RecursorScopeFrame current → (next stats current).WF post) :
    (checkInductiveTypes nparams types next ctx).WF post := by
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  apply checkedHeader_loopInd_traces nparams types next 0 _ ctx ctx post
  · omega
  · exact hwf
  · exact hreserved
  · exact ⟨rfl, rfl, by simp, rfl⟩
  · exact .refl ctx hwf hreserved
  · intro parent hparent; omega
  · exact hnext

theorem checkInductiveTypes.getHeaderTraces (nparams : Nat) (types : Array InductiveType)
    (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx).WF
      fun result => CheckedHeaderSources nparams types ctx result.1 result.2 ∧
        ctx.RecursorScopeFrame result.2 ∧ result.1.ParamsCount nparams types.size ∧
        result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup := by
  have htraces : (checkInductiveTypes nparams types (fun stats => do
      return (stats, ← readThe Context)) ctx).WF fun result =>
        CheckedHeaderSources nparams types ctx result.1 result.2 ∧ ctx.RecursorScopeFrame result.2 := by
    apply checkInductiveTypes.scopedHeaderTraces
    · exact hwf
    · exact hreserved
    intro stats current htraces hframe
    exact .pure ⟨htraces, hframe⟩
  intro result hresult
  obtain ⟨hframe, hsizes, hcount, hfvars, hnodup⟩ :=
    checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved result hresult
  exact ⟨(htraces result hresult).1, hframe, hcount, hfvars, hnodup⟩

end Lean4Lean.AddInductive
