import Lean4Lean.Verify.InductiveBinderPrefixes
import Lean4Lean.Verify.InductiveIndexPositions

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private newlyAllocatedBinderDeclared parameterDeclared indexDeclared
  from Lean4Lean.Verify.InductiveBinderDomains

private theorem recursorIndexSize (ctx : Context) (name : Name) (bi : BinderInfo) (domain : Expr) :
    (recursorIndexContext ctx name bi domain).lctx.decls.size = ctx.lctx.decls.size + 1 := by
  simp only [recursorIndexContext, LocalContext.mkLocalDecl, PersistentArray.push]
  split
  · rfl
  · unfold PersistentArray.mkNewTail
    split <;> rfl

theorem CheckedHeaderTrace.openedAllocations {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams) :
    ∃ steps, OpenedTelescope type steps terminal ∧ BinderStepsIndexDeclared finalCtx steps ∧
      (BinderStep.indexValues steps).length + nindices = finalIndices ∧
      (stats.indConsts.isEmpty = true →
        finalStats.params.toList = stats.params.toList ++ BinderStep.parameterValues steps) ∧
      (¬ stats.indConsts.isEmpty = true →
        stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop nparams) ∧
      steps.map BinderStep.role = List.replicate (nparams - index) .parameter ++
        List.replicate (finalIndices - nindices) .index ∧
      BinderIndexAllocations finalCtx
        (ctx.lctx.decls.size + if stats.indConsts.isEmpty then nparams - index else 0) steps := by
  revert htype hwf hreserved hparams
  induction trace with
  | stop hnot hparams =>
    intro htype hwf hreserved hsize
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro step hstep
      cases hstep
    · simp only [BinderStep.indexValues, List.length_nil, Nat.zero_add]
    · intro _
      simp only [BinderStep.parameterValues, List.append_nil]
    · intro _
      simp only [hparams, BinderStep.parameterValues, List.nil_append]
    · simp only [hparams, Nat.sub_self, List.replicate_zero, List.nil_append, List.map_nil]
    · trivial
  | @freshParameter stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
      have hnext : (stats.params.push (.fvar ⟨ctx.ngen.curr⟩)).size =
          if stats.indConsts.isEmpty then index + 1 else nparams := by
        simpa only [hfirst, ↓reduceIte, Array.size_push] using congrArg (· + 1) hsize
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hnext
      refine ⟨_, .bind .parameter name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        parameterDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩), ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro _
        simpa only [BinderStep.parameterValues, ↓reduceIte, Array.toList_push,
          List.append_assoc, List.singleton_append] using hfresh hfirst
      · intro hnot
        exact False.elim (hnot hfirst)
      · have hsucc : nparams - index = (nparams - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
      · have hstart : (recursorIndexContext ctx name bi domain.consumeTypeAnnotations).lctx.decls.size +
            (if stats.indConsts.isEmpty then nparams - (index + 1) else 0) =
            ctx.lctx.decls.size + (if stats.indConsts.isEmpty then nparams - index else 0) := by
          simp only [recursorIndexSize, hfirst, ↓reduceIte]
          omega
        simpa only [BinderIndexAllocations, hstart] using halloc
  | @reusedParameter stats name domain body bi index nindices ctx paramType normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hlookup hequal hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 stats.params[index]!).whnf ctx normalized hnormalized
      subst normalized
      have hparamSize : stats.params.size = nparams := by simpa only [if_neg hfirst] using hsize
      have hnext : stats.params.size = if stats.indConsts.isEmpty then index + 1 else nparams := by
        simpa only [if_neg hfirst] using hparamSize
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc⟩ := ih
        (hbody.instantiate1 stats.params[index]!) hwf hreserved hnext
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened,
        parameterDeclared declared name domain bi stats.params[index]!, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro _
        rw [List.drop_eq_getElem_cons (by simpa [hparamSize] using hparam), hreused hfirst]
        simp only [BinderStep.parameterValues, ↓reduceIte, List.cons_append,
          Array.getElem_toList, getElem!_pos stats.params index (by omega)]
      · have hsucc : nparams - index = (nparams - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
      · simpa only [BinderIndexAllocations, if_neg hfirst] using halloc
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hsize
      have hvalue := (newlyAllocatedBinderDeclared ctx name domain bi hwf hreserved).mono hpush.wf
        (tail.scope hpush.wf hpush.reserved)
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        indexDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩) hvalue, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [BinderStep.indexValues, ↓reduceIte, List.length_cons]
        omega
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hfresh
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hreused
      · have hbounds := tail.countBounds
        have hzero : nparams - index = 0 := by omega
        have hsucc : finalIndices - nindices = (finalIndices - (nindices + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hzero, List.replicate_zero, List.nil_append,
          hsucc, List.replicate_succ]
      · have hzero : nparams - index = 0 := by omega
        simp only [BinderIndexAllocations, hzero, ite_self, Nat.add_zero]
        refine ⟨?_, ?_⟩
        · exact (newlyAllocatedBinderPositioned ctx name domain bi hwf hreserved).mono hpush.wf
            (tail.scope hpush.wf hpush.reserved)
        · simpa only [recursorIndexSize, hzero, ite_self, Nat.add_zero] using halloc

private theorem parameterDrop (params : Array Expr) (index : Nat) (hindex : index < params.size) :
    params.toList.drop index = params[index]! :: params.toList.drop (index + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hindex)]
  simp only [Array.getElem_toList, getElem!_pos params index hindex]

theorem RecursorIndexTrace.openedAllocations {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ∃ steps, OpenedTelescope type steps terminal ∧
      stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      finalIndices.toList = indices.toList ++ BinderStep.indexValues steps ∧
      BinderStepsIndexDeclared finalCtx steps ∧
      steps.map BinderStep.role = List.replicate (finalIndex - index) .parameter ++
        List.replicate (finalIndices.size - indices.size) .index ∧
      BinderIndexAllocations finalCtx ctx.lctx.decls.size steps := by
  revert htype hwf hreserved
  induction trace with
  | stop hnot =>
    intro htype hwf hreserved
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact (List.append_nil _).symm
    · intro step hstep; cases hstep
    · simp only [Nat.sub_self, List.replicate_zero, List.nil_append, List.map_nil]
    · trivial
  | @parameter name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 stats.params[index]!).whnf ctx normalized hnormalized
      subst normalized
      obtain ⟨steps, opened, hparams, hindices, declared, hroles, halloc⟩ := ih
        (hbody.instantiate1 stats.params[index]!) hwf hreserved
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [BinderStep.parameterValues, ↓reduceIte]
        rw [parameterDrop stats.params index hparam, hparams]
        rfl
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hindices
      · exact parameterDeclared declared name domain bi stats.params[index]!
      · have hbound := tail.parameterRange.1
        have hsucc : finalIndex - index = (finalIndex - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
      · exact halloc
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
      obtain ⟨steps, opened, hparams, hindices, declared, hroles, halloc⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hparams
      · simpa only [BinderStep.indexValues, ↓reduceIte, Array.toList_push, List.append_assoc,
          List.singleton_append] using hindices
      · have hvalue := (newlyAllocatedBinderDeclared ctx name domain bi hwf hreserved).mono hpush.wf
          (tail.scope hpush.wf hpush.reserved)
        exact indexDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩) hvalue
      · have hbounds := tail.parameterRange
        have hsize := tail.indexSize
        simp only [Array.size_push] at hsize
        have hzero : finalIndex - index = 0 := by omega
        have hsucc : finalIndices.size - indices.size =
            (finalIndices.size - (indices.size + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hzero, List.replicate_zero, List.nil_append,
          Array.size_push, hsucc, List.replicate_succ]
      · refine ⟨?_, ?_⟩
        · exact (newlyAllocatedBinderPositioned ctx name domain bi hwf hreserved).mono hpush.wf
            (tail.scope hpush.wf hpush.reserved)
        · simpa only [recursorIndexSize] using halloc

theorem CheckedHeaderSource.openedAllocations_of_normalized {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal, OpenedTelescope normalized steps terminal ∧
      BinderStep.parameterValues steps = params.toList ∧
      (BinderStep.indexValues steps).length = count ∧ BinderStepsIndexDeclared current steps ∧
      steps.map BinderStep.role = List.replicate params.size .parameter ++ List.replicate count .index ∧
      ∃ start, BinderIndexAllocations current start steps := by
  have hparamsCount := source.paramsCount
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hstart : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams := by
    simpa [Array.isEmpty, hconst] using hprefixParams
  obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc⟩ :=
    htrace.openedAllocations hnormalized.1 hentry.wf hentry.reserved hstart
  refine ⟨steps, terminal, opened, ?_, hcount,
    declared.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent, ?_,
    ⟨_, halloc.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent⟩⟩
  · by_cases hfirst : stats.indConsts.isEmpty = true
    · have hsize : stats.params.size = 0 := by simpa only [hfirst, ↓reduceIte] using hstart
      have hempty : stats.params.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsize)
      have hhistory := hfresh hfirst
      rw [hempty, List.nil_append, hparams] at hhistory
      exact hhistory.symm
    · have hsize : stats.params.size = nparams := by simpa only [if_neg hfirst] using hstart
      have hdrop : stats.params.toList.drop nparams = [] :=
        List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_eq hsize)
      have hhistory := hreused hfirst
      simp only [List.drop_zero, hdrop, List.append_nil] at hhistory
      rw [← htrace.paramsUnchanged hfirst, hparams] at hhistory
      exact hhistory.symm
  · simpa only [Nat.sub_zero, hparamsCount] using hroles

theorem RecursorInfoIndexSource.openedAllocations_of_normalized
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo} {normalized : Expr}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal finalIndex, OpenedTelescope normalized steps terminal ∧
      stats.params.toList = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      info.indices.toList = BinderStep.indexValues steps ∧
      finalIndex = min (declareConstructors.arity 0 normalized) stats.params.size ∧
      BinderStepsIndexDeclared current steps ∧
      steps.map BinderStep.role = List.replicate finalIndex .parameter ++
        List.replicate info.indices.size .index ∧
      ∃ start, BinderIndexAllocations current start steps := by
  obtain ⟨entry, sourceNormalized, terminal, finalIndex, indexCtx, hentry, hsourceNormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hposition := (htrace.telescopeCounts hnormalized.1 (Nat.zero_le _)).1
  obtain ⟨steps, opened, hparams, hindices, declared, hroles, halloc⟩ :=
    htrace.openedAllocations hnormalized.1 hentry.wf hentry.reserved
  have htraceScope := htrace.scope hentry.wf hentry.reserved
  have hmajorFrame := Context.RecursorScopeFrame.push indexCtx htraceScope.wf htraceScope.reserved
    `t .default (recursorMajorDomain stats parent info.indices)
  have hmotiveFrame := Context.RecursorScopeFrame.push
    (recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices))
    hmajorFrame.wf hmajorFrame.reserved (recursorMotiveName types parent) .default
    (recursorMotiveDomain elimLevel info.indices info.major
      (recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices)))
  exact ⟨steps, terminal, finalIndex, opened, hparams, hindices, by simpa only [Nat.zero_add] using hposition,
    declared.mono htraceScope.wf (hmajorFrame.trans (hmotiveFrame.trans hcurrent)),
    by simpa only [Nat.sub_zero, Array.size_empty] using hroles,
    ⟨_, halloc.mono htraceScope.wf (hmajorFrame.trans (hmotiveFrame.trans hcurrent))⟩⟩

end Lean4Lean.AddInductive
