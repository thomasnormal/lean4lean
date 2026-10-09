import Lean4Lean.Verify.InductiveNormalizedHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

inductive BinderRole where
  | parameter
  | index
  deriving DecidableEq

structure BinderStep where
  role : BinderRole
  name : Name
  domain : Expr
  bi : BinderInfo
  value : Expr

def BinderStep.localDomain (step : BinderStep) : Expr := step.domain.consumeTypeAnnotations

def BinderStep.signature (step : BinderStep) : Name × BinderInfo := (step.name, step.bi)

def BinderStep.parameterValues : List BinderStep → List Expr
  | [] => []
  | step :: steps =>
      if step.role = .parameter then step.value :: parameterValues steps else parameterValues steps

def BinderStep.indexValues : List BinderStep → List Expr
  | [] => []
  | step :: steps =>
      if step.role = .index then step.value :: indexValues steps else indexValues steps

def BinderDeclaredAt (ctx : Context) (value : Expr) (name : Name) (domain : Expr)
    (bi : BinderInfo) : Prop :=
  ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
    decl.type = domain ∧ decl.userName = name ∧ decl.binderInfo = bi

theorem BinderDeclaredAt.mono {original current : Context} {value domain : Expr}
    {name : Name} {bi : BinderInfo} (hdeclared : BinderDeclaredAt original value name domain bi)
    (hwf : original.lctx.WF) (hframe : original.RecursorScopeFrame current) :
    BinderDeclaredAt current value name domain bi := by
  obtain ⟨decl, hlookup, hexpr, htype, hname, hbi⟩ := hdeclared
  exact ⟨decl, hframe.oldLookup hwf hlookup, hexpr, htype, hname, hbi⟩

private theorem newlyAllocatedBinderDeclared (ctx : Context) (name : Name) (domain : Expr)
    (bi : BinderInfo) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    BinderDeclaredAt (recursorIndexContext ctx name bi domain.consumeTypeAnnotations)
      (.fvar ⟨ctx.ngen.curr⟩) name domain.consumeTypeAnnotations bi := by
  have hframe := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
  let decl := LocalDecl.cdecl ctx.lctx.decls.size ⟨ctx.ngen.curr⟩ name
    domain.consumeTypeAnnotations bi .default
  have hmem : decl ∈ (recursorIndexContext ctx name bi domain.consumeTypeAnnotations).lctx.toList := by
    simp only [recursorIndexContext, LocalContext.mkLocalDecl_toList, List.mem_cons]
    exact .inl rfl
  refine ⟨decl, ?_, rfl, rfl, rfl, rfl⟩
  exact hframe.wf.find?_of_mem hmem

def BinderStep.IndexDomainsDeclared (ctx : Context) (steps : List BinderStep) : Prop :=
  ∀ step ∈ steps, step.role = .index → BinderDeclaredAt ctx step.value step.name step.localDomain step.bi

abbrev BinderStepsIndexDeclared := BinderStep.IndexDomainsDeclared

theorem BinderStep.IndexDomainsDeclared.mono {original current : Context} {steps : List BinderStep}
    (hdeclared : IndexDomainsDeclared original steps) (hwf : original.lctx.WF)
    (hframe : original.RecursorScopeFrame current) : IndexDomainsDeclared current steps :=
  fun step hstep hrole => (hdeclared step hstep hrole).mono hwf hframe

private theorem parameterDeclared {ctx : Context} {steps : List BinderStep}
    (hdeclared : BinderStep.IndexDomainsDeclared ctx steps)
    (name : Name) (domain : Expr) (bi : BinderInfo) (value : Expr) :
    BinderStep.IndexDomainsDeclared ctx ({ role := .parameter, name, domain, bi, value } :: steps) := by
  intro step hstep hrole
  simp only [List.mem_cons] at hstep
  obtain rfl | hstep := hstep
  · cases hrole
  · exact hdeclared step hstep hrole

private theorem indexDeclared {ctx : Context} {steps : List BinderStep}
    (hdeclared : BinderStep.IndexDomainsDeclared ctx steps)
    (name : Name) (domain : Expr) (bi : BinderInfo) (value : Expr)
    (hvalue : BinderDeclaredAt ctx value name domain.consumeTypeAnnotations bi) :
    BinderStep.IndexDomainsDeclared ctx ({ role := .index, name, domain, bi, value } :: steps) := by
  intro step hstep hrole
  simp only [List.mem_cons] at hstep
  obtain rfl | hstep := hstep
  · exact hvalue
  · exact hdeclared step hstep hrole

inductive OpenedTelescope : Expr → List BinderStep → Expr → Prop where
  | sort (level : Level) : OpenedTelescope (.sort level) [] (.sort level)
  | bind (role : BinderRole) (name : Name) (domain : Expr) (bi : BinderInfo) (value : Expr)
      {body terminal : Expr} {steps : List BinderStep}
      (tail : OpenedTelescope (body.instantiate1 value) steps terminal) :
      OpenedTelescope (.forallE name domain body bi)
        ({ role, name, domain, bi, value } :: steps) terminal

def Expr.binderSignature : Expr → List (Name × BinderInfo)
  | .forallE name _ body bi => (name, bi) :: binderSignature body
  | _ => []

theorem SortTelescope.binderSignature_instantiate1' {type : Expr} (htype : SortTelescope type)
    (value : Expr) (depth : Nat) :
    Expr.binderSignature (type.instantiate1' value depth) = Expr.binderSignature type := by
  induction htype generalizing depth with
  | sort level => rfl
  | forallE name domain bi tail ih =>
    change (name, bi) :: Expr.binderSignature _ = (name, bi) :: Expr.binderSignature _
    rw [ih (depth + 1)]

theorem SortTelescope.binderSignature_instantiate1 {type : Expr} (htype : SortTelescope type)
    (value : Expr) :
    Expr.binderSignature (type.instantiate1 value) = Expr.binderSignature type := by
  rw [Expr.instantiate1_eq]
  exact htype.binderSignature_instantiate1' value 0

theorem OpenedTelescope.signature {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (htype : SortTelescope type) :
    steps.map BinderStep.signature = Expr.binderSignature type := by
  induction opened with
  | sort level => rfl
  | @bind role name domain bi value body terminal steps tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      simp only [List.map_cons, BinderStep.signature, Expr.binderSignature]
      rw [ih (hbody.instantiate1 value), hbody.binderSignature_instantiate1 value]

theorem OpenedTelescope.sameSignature {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal) (htype : SortTelescope type) :
    left.map BinderStep.signature = right.map BinderStep.signature :=
  (leftOpened.signature htype).trans (rightOpened.signature htype).symm

theorem CheckedHeaderTrace.openedTelescope {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams) :
    ∃ steps, OpenedTelescope type steps terminal ∧ BinderStepsIndexDeclared finalCtx steps ∧
      (BinderStep.indexValues steps).length + nindices = finalIndices ∧
      (stats.indConsts.isEmpty = true →
        finalStats.params.toList = stats.params.toList ++ BinderStep.parameterValues steps) ∧
      (¬ stats.indConsts.isEmpty = true →
        stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop nparams) := by
  revert htype hwf hreserved hparams
  induction trace with
  | stop hnot hparams =>
    intro htype hwf hreserved hsize
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_, ?_⟩
    · intro step hstep
      cases hstep
    · simp only [BinderStep.indexValues, List.length_nil, Nat.zero_add]
    · intro _
      simp only [BinderStep.parameterValues, List.append_nil]
    · intro _
      simp only [hparams, BinderStep.parameterValues, List.nil_append]
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
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hnext
      refine ⟨_, .bind .parameter name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        parameterDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩), ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro _
        simpa only [BinderStep.parameterValues, ↓reduceIte, Array.toList_push,
          List.append_assoc, List.singleton_append] using hfresh hfirst
      · intro hnot
        exact False.elim (hnot hfirst)
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
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused⟩ := ih
        (hbody.instantiate1 stats.params[index]!) hwf hreserved hnext
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened,
        parameterDeclared declared name domain bi stats.params[index]!, ?_, ?_, ?_⟩
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hcount
      · intro hyes
        exact False.elim (hfirst hyes)
      · intro _
        rw [List.drop_eq_getElem_cons (by simpa [hparamSize] using hparam), hreused hfirst]
        simp only [BinderStep.parameterValues, ↓reduceIte, List.cons_append,
          Array.getElem_toList, getElem!_pos stats.params index (by omega)]
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved hsize
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
      obtain ⟨steps, opened, declared, hcount, hfresh, hreused⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved hsize
      have hvalue := (newlyAllocatedBinderDeclared ctx name domain bi hwf hreserved).mono hpush.wf
        (tail.scope hpush.wf hpush.reserved)
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened,
        indexDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩) hvalue, ?_, ?_, ?_⟩
      · simp only [BinderStep.indexValues, ↓reduceIte, List.length_cons]
        omega
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hfresh
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hreused

private theorem parameterDrop (params : Array Expr) (index : Nat) (hindex : index < params.size) :
    params.toList.drop index = params[index]! :: params.toList.drop (index + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hindex)]
  simp only [Array.getElem_toList, getElem!_pos params index hindex]

theorem RecursorIndexTrace.openedTelescope {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ∃ steps, OpenedTelescope type steps terminal ∧
      stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      finalIndices.toList = indices.toList ++ BinderStep.indexValues steps ∧
      BinderStepsIndexDeclared finalCtx steps := by
  revert htype hwf hreserved
  induction trace with
  | stop hnot =>
    intro htype hwf hreserved
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    refine ⟨[], .sort level, ?_, ?_, ?_⟩
    · rfl
    · exact (List.append_nil _).symm
    · intro step hstep; cases hstep
  | @parameter name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 stats.params[index]!).whnf ctx normalized hnormalized
      subst normalized
      obtain ⟨steps, opened, hparams, hindices, declared⟩ := ih (hbody.instantiate1 stats.params[index]!) hwf hreserved
      refine ⟨_, .bind .parameter name domain bi stats.params[index]! opened, ?_, ?_, ?_⟩
      · simp only [BinderStep.parameterValues, ↓reduceIte]
        rw [parameterDrop stats.params index hparam, hparams]
        rfl
      · simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hindices
      · exact parameterDeclared declared name domain bi stats.params[index]!
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro htype hwf hreserved
    cases htype with
    | forallE _ _ _ hbody =>
      have heq := (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)).whnf
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      subst normalized
      have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
      obtain ⟨steps, opened, hparams, hindices, declared⟩ := ih
        (hbody.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) hpush.wf hpush.reserved
      refine ⟨_, .bind .index name domain bi (.fvar ⟨ctx.ngen.curr⟩) opened, ?_, ?_, ?_⟩
      · simpa only [BinderStep.parameterValues, BinderRole.noConfusion, ↓reduceIte] using hparams
      · simpa only [BinderStep.indexValues, ↓reduceIte, Array.toList_push, List.append_assoc,
          List.singleton_append] using hindices
      · have hvalue := (newlyAllocatedBinderDeclared ctx name domain bi hwf hreserved).mono hpush.wf
          (tail.scope hpush.wf hpush.reserved)
        exact indexDeclared declared name domain bi (.fvar ⟨ctx.ngen.curr⟩) hvalue

theorem CheckedHeaderSource.opened_of_normalized {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal, OpenedTelescope normalized steps terminal ∧
      BinderStep.parameterValues steps = params.toList ∧
      (BinderStep.indexValues steps).length = count ∧ BinderStepsIndexDeclared current steps := by
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hstart : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams := by
    simpa [Array.isEmpty, hconst] using hprefixParams
  obtain ⟨steps, opened, declared, hcount, hfresh, hreused⟩ :=
    htrace.openedTelescope hnormalized.1 hentry.wf hentry.reserved hstart
  refine ⟨steps, terminal, opened, ?_, hcount,
    declared.mono (htrace.scope hentry.wf hentry.reserved).wf hcurrent⟩
  by_cases hfirst : stats.indConsts.isEmpty = true
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

theorem RecursorInfoIndexSource.opened_of_normalized
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo} {normalized : Expr}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    ∃ steps terminal finalIndex, OpenedTelescope normalized steps terminal ∧
      stats.params.toList = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      info.indices.toList = BinderStep.indexValues steps ∧
      finalIndex = min (declareConstructors.arity 0 normalized) stats.params.size ∧
      BinderStepsIndexDeclared current steps := by
  obtain ⟨entry, sourceNormalized, terminal, finalIndex, indexCtx, hentry, hsourceNormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hposition := (htrace.telescopeCounts hnormalized.1 (Nat.zero_le _)).1
  obtain ⟨steps, opened, hparams, hindices, declared⟩ := htrace.openedTelescope hnormalized.1 hentry.wf hentry.reserved
  have htraceScope := htrace.scope hentry.wf hentry.reserved
  have hmajorFrame := Context.RecursorScopeFrame.push indexCtx htraceScope.wf htraceScope.reserved
    `t .default (recursorMajorDomain stats parent info.indices)
  have hmotiveFrame := Context.RecursorScopeFrame.push
    (recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices))
    hmajorFrame.wf hmajorFrame.reserved (recursorMotiveName types parent) .default
    (recursorMotiveDomain elimLevel info.indices info.major
      (recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices)))
  exact ⟨steps, terminal, finalIndex, opened, hparams, hindices, by simpa only [Nat.zero_add] using hposition,
    declared.mono htraceScope.wf (hmajorFrame.trans (hmotiveFrame.trans hcurrent))⟩

end Lean4Lean.AddInductive
