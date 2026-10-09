import Lean4Lean.Verify.InductiveBinderOpening

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private newlyAllocatedBinderDeclared parameterDeclared indexDeclared
  from Lean4Lean.Verify.InductiveBinderDomains

private theorem indexRolesParameterValues (steps : List BinderStep) (count : Nat)
    (hroles : steps.map BinderStep.role = List.replicate count .index) :
    BinderStep.parameterValues steps = [] := by
  induction steps generalizing count with
  | nil => rfl
  | cons step steps ih =>
    cases count with
    | zero => simp only [List.map_cons, List.replicate_zero, List.cons_ne_nil] at hroles
    | succ count =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at hroles
      simp only [BinderStep.parameterValues, hroles.1]
      exact ih count hroles.2

theorem BinderStep.parameterPrefix (steps : List BinderStep) (count indices : Nat)
    (hroles : steps.map BinderStep.role =
      List.replicate count .parameter ++ List.replicate indices .index) :
    (steps.take count).map BinderStep.value = BinderStep.parameterValues steps ∧
      (steps.take count).map BinderStep.role = List.replicate count .parameter := by
  induction count generalizing steps with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hroles
    exact ⟨(indexRolesParameterValues steps indices hroles).symm, rfl⟩
  | succ count ih =>
    cases steps with
    | nil =>
      simp only [List.map_nil, List.replicate_succ, List.cons_append] at hroles
      cases hroles
    | cons step steps =>
      simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at hroles
      obtain ⟨hvalues, hprefixRoles⟩ := ih steps hroles.2
      simp only [List.take_succ_cons, List.map_cons, BinderStep.parameterValues, hroles.1,
        ↓reduceIte, hvalues, hprefixRoles, List.replicate_succ, and_self]

theorem OpenedTelescope.sameParameterPrefix {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} {count leftIndices rightIndices : Nat}
    (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal)
    (leftRoles : left.map BinderStep.role =
      List.replicate count .parameter ++ List.replicate leftIndices .index)
    (rightRoles : right.map BinderStep.role =
      List.replicate count .parameter ++ List.replicate rightIndices .index)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right) :
    left.take count = right.take count ∧
      ((left.drop count).head?).map BinderStep.domain =
        ((right.drop count).head?).map BinderStep.domain := by
  have hleft := BinderStep.parameterPrefix left count leftIndices leftRoles
  have hright := BinderStep.parameterPrefix right count rightIndices rightRoles
  exact leftOpened.samePrefixAndNextDomain rightOpened count
    (hleft.1.trans (hparams.trans hright.1.symm)) (hleft.2.trans hright.2.symm)

theorem CheckedHeaderTrace.openedPrefix {nparams : Nat} {stats finalStats : InductiveStats}
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
        List.replicate (finalIndices - nindices) .index := by
  revert htype hwf hreserved hparams
  induction trace with
  | stop hnot hparams =>
    intro htype hwf hreserved hsize
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_, ?_, ?_⟩
    · intro step hstep
      cases hstep
    · simp only [BinderStep.indexValues, List.length_nil, Nat.zero_add]
    · intro _
      simp only [BinderStep.parameterValues, List.append_nil]
    · intro _
      simp only [hparams, BinderStep.parameterValues, List.nil_append]
    · simp only [hparams, Nat.sub_self, List.replicate_zero, List.nil_append, List.map_nil]
  | @freshParameter stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi (peelTypeAnnotations domain)) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
      have hnext : (stats.params.push (.fvar ⟨ctx.ngen.curr⟩)).size =
          if stats.indConsts.isEmpty then index + 1 else nparams := by
        simpa only [hfirst, ↓reduceIte, Array.size_push] using congrArg (· + 1) hsize
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hnext
      refine ⟨_, .bind .parameter name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        parameterDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩), ?_, ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro _
        simpa only [BinderStep.parameterValues, ↓reduceIte, Array.toList_push,
          List.append_assoc, List.singleton_append] using hfresh hfirst
      · intro hnot
        exact False.elim (hnot hfirst)
      · have hsucc : nparams - index = (nparams - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
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
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles⟩ := ih
        (hbody.instantiate1 stats.params[index]!) hwf hreserved hnext
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened,
        parameterDeclared declared name domain bi stats.params[index]!, ?_, ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro _
        rw [List.drop_eq_getElem_cons (by simpa [hparamSize] using hparam), hreused hfirst]
        simp only [BinderStep.parameterValues, ↓reduceIte, List.cons_append,
          Array.getElem_toList, getElem!_pos stats.params index (by omega)]
      · have hsucc : nparams - index = (nparams - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi (peelTypeAnnotations domain)) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hsize
      have hvalue := (newlyAllocatedBinderDeclared ctx name domain bi hwf hreserved).mono hpush.wf
        (tail.scope hpush.wf hpush.reserved)
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        indexDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩) hvalue, ?_, ?_, ?_, ?_⟩
      · simp only [BinderStep.indexValues, ↓reduceIte, List.length_cons]
        omega
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hfresh
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hreused
      · have hbounds := tail.countBounds
        have hzero : nparams - index = 0 := by omega
        have hsucc : finalIndices - nindices = (finalIndices - (nindices + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hzero, List.replicate_zero, List.nil_append,
          hsucc, List.replicate_succ]

private theorem parameterDrop (params : Array Expr) (index : Nat) (hindex : index < params.size) :
    params.toList.drop index = params[index]! :: params.toList.drop (index + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hindex)]
  simp only [Array.getElem_toList, getElem!_pos params index hindex]

theorem RecursorIndexTrace.openedPrefix {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ∃ steps, OpenedTelescope type steps terminal ∧
      stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      finalIndices.toList = indices.toList ++ BinderStep.indexValues steps ∧
      BinderStepsIndexDeclared finalCtx steps ∧
      steps.map BinderStep.role = List.replicate (finalIndex - index) .parameter ++
        List.replicate (finalIndices.size - indices.size) .index := by
  revert htype hwf hreserved
  induction trace with
  | stop hnot =>
    intro htype hwf hreserved
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact (List.append_nil _).symm
    · intro step hstep; cases hstep
    · simp only [Nat.sub_self, List.replicate_zero, List.nil_append, List.map_nil]
  | @parameter name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 stats.params[index]!).whnf ctx normalized hnormalized
      subst normalized
      obtain ⟨steps, opened, hparams, hindices, declared, hroles⟩ := ih
        (hbody.instantiate1 stats.params[index]!) hwf hreserved
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened, ?_, ?_, ?_, ?_⟩
      · simp only [BinderStep.parameterValues, ↓reduceIte]
        rw [parameterDrop stats.params index hparam, hparams]
        rfl
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hindices
      · exact parameterDeclared declared name domain bi stats.params[index]!
      · have hbound := tail.parameterRange.1
        have hsucc : finalIndex - index = (finalIndex - (index + 1)) + 1 := by omega
        simp only [List.map_cons, hroles, hsucc, List.replicate_succ, List.cons_append]
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi (peelTypeAnnotations domain)) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
      obtain ⟨steps, opened, hparams, hindices, declared, hroles⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened, ?_, ?_, ?_, ?_⟩
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

theorem CheckedHeaderSource.openedPrefix_of_normalized {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal, OpenedTelescope normalized steps terminal ∧
      BinderStep.parameterValues steps = params.toList ∧
      (BinderStep.indexValues steps).length = count ∧ BinderStepsIndexDeclared current steps ∧
      steps.map BinderStep.role = List.replicate params.size .parameter ++ List.replicate count .index := by
  have hparamsCount := source.paramsCount
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hstart : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams := by
    simpa [Array.isEmpty, hconst] using hprefixParams
  obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles⟩ :=
    htrace.openedPrefix hnormalized.1 hentry.wf hentry.reserved hstart
  refine ⟨steps, terminal, opened, ?_, hcount,
    declared.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent, ?_⟩
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

theorem RecursorInfoIndexSource.openedPrefix_of_normalized
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
        List.replicate info.indices.size .index := by
  obtain ⟨entry, sourceNormalized, terminal, finalIndex, indexCtx, hentry, hsourceNormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hposition := (htrace.telescopeCounts hnormalized.1 (Nat.zero_le _)).1
  obtain ⟨steps, opened, hparams, hindices, declared, hroles⟩ :=
    htrace.openedPrefix hnormalized.1 hentry.wf hentry.reserved
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
    by simpa only [Nat.sub_zero, Array.size_empty] using hroles⟩

end Lean4Lean.AddInductive
