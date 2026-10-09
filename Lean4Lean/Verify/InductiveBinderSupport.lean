import Lean4Lean.Verify.InductiveBinderAllocations

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private context_indices from Lean4Lean.Verify.InductiveParamValidity
open private recursorIndexSize from Lean4Lean.Verify.InductiveBinderAllocations

def BinderParameterIndexDisjoint (steps : List BinderStep) : Prop :=
  List.Disjoint ((BinderStep.parameterValues steps).map Expr.fvarId!)
    ((BinderStep.indexValues steps).map Expr.fvarId!)

def BinderValuesBefore (ctx : Context) (bound : Nat) (values : List Expr) : Prop :=
  ∀ value ∈ values, ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧
    decl.toExpr = value ∧ decl.index < bound

theorem BinderValuesBefore.mono {original current : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore original bound values) (hwf : original.lctx.WF)
    (frame : original.RecursorScopeFrame current) : BinderValuesBefore current bound values := by
  intro value hvalue
  obtain ⟨decl, hlookup, hexpr, hindex⟩ := support value hvalue
  exact ⟨decl, frame.oldLookup hwf hlookup, hexpr, hindex⟩

theorem BinderValuesBefore.weaken {ctx : Context} {bound next : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) (hbound : bound ≤ next) :
    BinderValuesBefore ctx next values := by
  intro value hvalue
  obtain ⟨decl, hlookup, hexpr, hindex⟩ := support value hvalue
  exact ⟨decl, hlookup, hexpr, Nat.lt_of_lt_of_le hindex hbound⟩

theorem BinderValuesBefore.push {ctx : Context} {values : Array Expr} {name : Name}
    {domain : Expr} {bi : BinderInfo}
    (support : BinderValuesBefore ctx ctx.lctx.decls.size values.toList)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    BinderValuesBefore (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)
      (recursorIndexContext ctx name bi domain.consumeTypeAnnotations).lctx.decls.size
      (values.push (.fvar ⟨ctx.ngen.curr⟩)).toList := by
  intro value hvalue
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hvalue
  have frame := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
  obtain hvalue | rfl := hvalue
  · exact (support.mono hwf frame).weaken (by rw [recursorIndexSize]; omega) value hvalue
  · obtain ⟨decl, hlookup, hexpr, _, _, _, hindex⟩ :=
      newlyAllocatedBinderPositioned ctx name domain bi hwf hreserved
    exact ⟨decl, hlookup, hexpr, by rw [hindex, recursorIndexSize]; omega⟩

theorem BinderValuesBefore.of_fieldsDeclared {ctx : Context} {values : Array Expr}
    (declared : RecursorFieldsDeclared ctx.lctx values) (hwf : ctx.lctx.WF) :
    BinderValuesBefore ctx ctx.lctx.decls.size values.toList := by
  intro value hvalue
  obtain ⟨decl, hdecl, rfl, _, _⟩ := declared value (by simpa using hvalue)
  have hindex : decl.index ∈ List.range ctx.lctx.numIndices := by
    rw [← context_indices hwf]
    exact List.mem_map.mpr ⟨decl, List.mem_reverse.mpr hdecl, rfl⟩
  refine ⟨decl, ?_, rfl, ?_⟩
  · simpa only [LocalDecl.toExpr, Expr.fvarId!] using hwf.find?_of_mem hdecl
  · simpa only [LocalContext.numIndices] using List.mem_range.mp hindex

theorem BinderValuesBefore.atSize {ctx : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) (hwf : ctx.lctx.WF) :
    BinderValuesBefore ctx ctx.lctx.decls.size values := by
  intro value hvalue
  obtain ⟨decl, hlookup, hexpr, _⟩ := support value hvalue
  have hmem := List.mem_of_find?_eq_some (hwf.find?_eq_find?_toList ▸ hlookup)
  have hindex : decl.index ∈ List.range ctx.lctx.numIndices := by
    rw [← context_indices hwf]
    exact List.mem_map.mpr ⟨decl, List.mem_reverse.mpr hmem, rfl⟩
  exact ⟨decl, hlookup, hexpr, by simpa only [LocalContext.numIndices] using List.mem_range.mp hindex⟩

theorem BinderIndexAllocations.parameterDisjoint {ctx : Context} {start : Nat}
    {steps : List BinderStep} (allocated : BinderIndexAllocations ctx start steps)
    (support : BinderValuesBefore ctx start (BinderStep.parameterValues steps)) :
    BinderParameterIndexDisjoint steps := by
  intro fvar hparam hindex
  obtain ⟨param, hparam, hparamId⟩ := List.mem_map.mp hparam
  obtain ⟨value, hvalue, hvalueId⟩ := List.mem_map.mp hindex
  obtain ⟨ordinal, hordinal⟩ := List.mem_iff_getElem?.mp hvalue
  obtain ⟨step, _, _, hstepValue, positioned⟩ := allocated.positioned hordinal
  obtain ⟨paramDecl, hlookup, _, hbefore⟩ := support param hparam
  obtain ⟨indexDecl, hindexLookup, _, _, _, _, hposition⟩ := positioned
  have hids : param.fvarId! = step.value.fvarId! := by rw [hstepValue, hvalueId, hparamId]
  rw [hids, hindexLookup] at hlookup
  obtain rfl := Option.some.inj hlookup
  omega

theorem CheckedHeaderTrace.paramsUnchanged_of_complete {nparams : Nat}
    {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hcomplete : nparams ≤ index) : finalStats.params = stats.params := by
  induction trace with
  | stop _ _ => rfl
  | freshParameter hparam _ _ _ _ => omega
  | reusedParameter hparam _ _ _ _ _ _ => omega
  | index _ _ _ ih => exact ih hcomplete

theorem CheckedHeaderTrace.paramsBefore {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList) :
    BinderValuesBefore finalCtx
      (ctx.lctx.decls.size + if stats.indConsts.isEmpty then nparams - index else 0)
      finalStats.params.toList := by
  revert hwf hreserved support
  induction trace with
  | stop _ hcomplete =>
    intro hwf hreserved support
    simpa only [hcomplete, Nat.sub_self, ite_self, Nat.add_zero] using support
  | @freshParameter stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hnormalized tail ih =>
    intro hwf hreserved support
    have frame := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
    have hsupported := ih frame.wf frame.reserved (support.push hwf hreserved)
    have hstart : (recursorIndexContext ctx name bi domain.consumeTypeAnnotations).lctx.decls.size +
        (if stats.indConsts.isEmpty then nparams - (index + 1) else 0) =
        ctx.lctx.decls.size + (if stats.indConsts.isEmpty then nparams - index else 0) := by
      rw [recursorIndexSize]
      simp only [hfirst, ↓reduceIte]
      omega
    simpa only [hstart] using hsupported
  | reusedParameter _ hfirst _ _ _ _ ih =>
    intro hwf hreserved support
    simpa only [if_neg hfirst] using ih hwf hreserved support
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro hwf hreserved support
    have frame := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
    have hcomplete : nparams ≤ index := Nat.le_of_not_gt hparam
    have hunchanged := tail.paramsUnchanged_of_complete hcomplete
    have hsupported := support.mono hwf (frame.trans (tail.scope frame.wf frame.reserved))
    simpa only [hunchanged, Nat.sub_eq_zero_of_le hcomplete, ite_self, Nat.add_zero] using hsupported

theorem CheckedHeaderTrace.parameterBase_le_size {nparams : Nat}
    {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    ctx.lctx.decls.size + (if stats.indConsts.isEmpty then nparams - index else 0) ≤
      finalCtx.lctx.decls.size := by
  induction trace with
  | stop _ hcomplete => simp only [hcomplete, Nat.sub_self, ite_self, Nat.add_zero, Nat.le_refl]
  | freshParameter hparam hfirst _ _ ih =>
    simp only [recursorIndexSize, hfirst, ↓reduceIte] at ih ⊢
    omega
  | reusedParameter _ hfirst _ _ _ _ ih => simpa only [if_neg hfirst] using ih
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    have hcomplete : nparams ≤ index := Nat.le_of_not_gt hparam
    simp only [Nat.sub_eq_zero_of_le hcomplete, ite_self, Nat.add_zero, recursorIndexSize] at ih ⊢
    omega

theorem CheckedHeaderTrace.openedSupport {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList) :
    ∃ steps, OpenedTelescope type steps terminal ∧ BinderStepsIndexDeclared finalCtx steps ∧
      (BinderStep.indexValues steps).length + nindices = finalIndices ∧
      (stats.indConsts.isEmpty = true →
        finalStats.params.toList = stats.params.toList ++ BinderStep.parameterValues steps) ∧
      (¬ stats.indConsts.isEmpty = true →
        stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop nparams) ∧
      steps.map BinderStep.role = List.replicate (nparams - index) .parameter ++
        List.replicate (finalIndices - nindices) .index ∧
      BinderIndexAllocations finalCtx
        (ctx.lctx.decls.size + if stats.indConsts.isEmpty then nparams - index else 0) steps ∧
      BinderParameterIndexDisjoint steps := by
  obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc⟩ :=
    trace.openedAllocations htype hwf hreserved hparams
  have hfinal := trace.paramsBefore hwf hreserved support
  refine ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc,
    halloc.parameterDisjoint ?_⟩
  intro value hvalue
  apply hfinal value
  by_cases hfirst : stats.indConsts.isEmpty = true
  · rw [hfresh hfirst]
    exact List.mem_append_right _ hvalue
  · apply trace.paramsSublist.subset
    have hdrop : value ∈ stats.params.toList.drop index := by
      rw [hreused hfirst]
      exact List.mem_append_left _ hvalue
    exact List.mem_of_mem_drop hdrop

theorem RecursorIndexTrace.openedSupport {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList) :
    ∃ steps, OpenedTelescope type steps terminal ∧
      stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      finalIndices.toList = indices.toList ++ BinderStep.indexValues steps ∧
      BinderStepsIndexDeclared finalCtx steps ∧
      steps.map BinderStep.role = List.replicate (finalIndex - index) .parameter ++
        List.replicate (finalIndices.size - indices.size) .index ∧
      BinderIndexAllocations finalCtx ctx.lctx.decls.size steps ∧
      BinderParameterIndexDisjoint steps := by
  obtain ⟨steps, opened, hparams, hindices, declared, hroles, halloc⟩ :=
    trace.openedAllocations htype hwf hreserved
  refine ⟨steps, opened, hparams, hindices, declared, hroles, halloc,
    halloc.parameterDisjoint ?_⟩
  intro value hvalue
  apply (support.mono hwf (trace.scope hwf hreserved)) value
  have hdrop : value ∈ stats.params.toList.drop index := by
    rw [hparams]
    exact List.mem_append_left _ hvalue
  exact List.mem_of_mem_drop hdrop

def CheckedHeaderSupportSource (nparams : Nat) (types : Array InductiveType) (parent : Nat)
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
    binderCtx.RecursorScopeFrame current ∧
    BinderValuesBefore entry entry.lctx.decls.size stats.params.toList

theorem CheckedHeaderSupportSource.toSource {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current) :
    CheckedHeaderSource nparams types parent original params count current := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent, _⟩ := source
  exact ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent⟩

theorem CheckedHeaderSupportSource.mono {nparams parent count : Nat} {types : Array InductiveType}
    {original current next : Context} {params : Array Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current)
    (frame : current.RecursorScopeFrame next) :
    CheckedHeaderSupportSource nparams types parent original params count next := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort, hcurrent, support⟩ := source
  exact ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams, hsort,
    hcurrent.trans frame, support⟩

theorem CheckedHeaderSupportSource.openedSupport_of_normalized {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal, OpenedTelescope normalized steps terminal ∧
      BinderStep.parameterValues steps = params.toList ∧
      (BinderStep.indexValues steps).length = count ∧ BinderStepsIndexDeclared current steps ∧
      steps.map BinderStep.role = List.replicate params.size .parameter ++ List.replicate count .index ∧
      ∃ start, BinderIndexAllocations current start steps ∧ BinderParameterIndexDisjoint steps := by
  have hparamsCount := source.toSource.paramsCount
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent, support⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hstart : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams := by
    simpa [Array.isEmpty, hconst] using hprefixParams
  obtain ⟨steps, opened, declared, hcount, hfresh, hreused, hroles, halloc, hdisjoint⟩ :=
    htrace.openedSupport hnormalized.1 hentry.wf hentry.reserved hstart support
  refine ⟨steps, terminal, opened, ?_, hcount,
    declared.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent, ?_,
    ⟨_, halloc.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent, hdisjoint⟩⟩
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

theorem RecursorInfoIndexSource.openedSupport_of_normalized
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo} {normalized : Expr}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized)
    (support : BinderValuesBefore original original.lctx.decls.size stats.params.toList)
    (hwf : original.lctx.WF) :
    ∃ steps terminal finalIndex, OpenedTelescope normalized steps terminal ∧
      stats.params.toList = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      info.indices.toList = BinderStep.indexValues steps ∧
      finalIndex = min (declareConstructors.arity 0 normalized) stats.params.size ∧
      BinderStepsIndexDeclared current steps ∧
      steps.map BinderStep.role = List.replicate finalIndex .parameter ++
        List.replicate info.indices.size .index ∧
      ∃ start, BinderIndexAllocations current start steps ∧ BinderParameterIndexDisjoint steps := by
  obtain ⟨entry, sourceNormalized, terminal, finalIndex, indexCtx, hentry, hsourceNormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hposition := (htrace.telescopeCounts hnormalized.1 (Nat.zero_le _)).1
  have hscope := (support.mono hwf hentry).atSize hentry.wf
  obtain ⟨steps, opened, hparams, hindices, declared, hroles, halloc, hdisjoint⟩ :=
    htrace.openedSupport hnormalized.1 hentry.wf hentry.reserved hscope
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
    ⟨_, halloc.mono htraceScope.wf (hmajorFrame.trans (hmotiveFrame.trans hcurrent)), hdisjoint⟩⟩

end Lean4Lean.AddInductive
