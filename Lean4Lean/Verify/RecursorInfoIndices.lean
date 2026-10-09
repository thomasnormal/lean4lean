import Lean4Lean.Verify.RecursorInfoScope
import Lean4Lean.Verify.ConstructorArity

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.readWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata
open private Lean4Lean.AddInductive.loopU_scope Lean4Lean.AddInductive.withLocalDecl_scope
  from Lean4Lean.Verify.RecursorInfoScope
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats

def recursorIndexContext (ctx : Context) (name : Name) (bi : BinderInfo) (domain : Expr) : Context :=
  { ctx with ngen := ctx.ngen.next, lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name domain bi }

inductive RecursorIndexTrace (stats : InductiveStats) :
    Expr → Nat → Array Expr → Context → Expr → Nat → Array Expr → Context → Prop where
  | stop {type : Expr} {index : Nat} {indices : Array Expr} {ctx : Context}
      (hnot : ∀ name domain body bi, type ≠ .forallE name domain body bi) :
      RecursorIndexTrace stats type index indices ctx type index indices ctx
  | parameter {name : Name} {domain body : Expr} {bi : BinderInfo} {index : Nat} {indices : Array Expr}
      {ctx : Context} {normalized terminal : Expr} {finalIndex : Nat} {finalIndices : Array Expr} {finalCtx : Context}
      (hparam : index < stats.params.size)
      (hnormalized : ((monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr) ctx) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized (index + 1) indices ctx terminal finalIndex finalIndices finalCtx) :
      RecursorIndexTrace stats (.forallE name domain body bi) index indices ctx terminal finalIndex finalIndices finalCtx
  | index {name : Name} {domain body : Expr} {bi : BinderInfo} {index : Nat} {indices : Array Expr}
      {ctx : Context} {normalized terminal : Expr} {finalIndex : Nat} {finalIndices : Array Expr} {finalCtx : Context}
      (hparam : ¬ index < stats.params.size)
      (hnormalized : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩))) : M Expr)
        (recursorIndexContext ctx name bi (peelTypeAnnotations domain))) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized index (indices.push (.fvar ⟨ctx.ngen.curr⟩))
        (recursorIndexContext ctx name bi (peelTypeAnnotations domain)) terminal finalIndex finalIndices finalCtx) :
      RecursorIndexTrace stats (.forallE name domain body bi) index indices ctx terminal finalIndex finalIndices finalCtx

private theorem bindResultWF {action : M α} {next : α → M β} {ctx : Context} {post : β → Prop}
    (hnext : ∀ result, action ctx = .ok result → (next result ctx).WF post) :
    ((action >>= next) ctx).WF post :=
  (show (action ctx).WF (fun result => action ctx = .ok result) from fun _ hresult => hresult).bind hnext

private theorem withIndexDeclWF {ctx : Context} {name : Name} {bi : BinderInfo} {domain : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : (next (.fvar ⟨ctx.ngen.curr⟩) (recursorIndexContext ctx name bi domain)).WF post) :
    (withLocalDecl name bi domain next ctx).WF post := hnext

theorem mkRecInfos.loopArgs1.scopedTrace (stats : InductiveStats) (type : Expr) (index : Nat)
    (indices : Array Expr) (fuel : Nat) (next : Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ terminal finalIndex finalIndices current,
      RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices current →
      ctx.RecursorScopeFrame current → (next finalIndices current).WF post) :
    (mkRecInfos.loopArgs1 stats type index indices fuel next ctx).WF post := by
  induction fuel generalizing type index indices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopArgs1.eq_def]
    split
    · rename_i name domain body bi
      split
      · rename_i hparam
        apply bindResultWF
        intro normalized hnormalized
        apply ih
        · exact hwf
        · exact hreserved
        intro terminal finalIndex finalIndices current htrace hframe
        exact hnext terminal finalIndex finalIndices current (.parameter hparam hnormalized htrace) hframe
      · rename_i hparam
        apply withIndexDeclWF
        have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
        apply bindResultWF
        intro normalized hnormalized
        apply ih
        · exact hpush.wf
        · exact hpush.reserved
        intro terminal finalIndex finalIndices current htrace hframe
        exact hnext terminal finalIndex finalIndices current (.index hparam hnormalized htrace) (hpush.trans hframe)
    · rename_i hnot
      exact hnext type index indices ctx (.stop hnot) (.refl ctx hwf hreserved)

theorem RecursorIndexTrace.terminal {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    ∀ name domain body bi, terminal ≠ .forallE name domain body bi := by
  induction trace with
  | stop hnot => exact hnot
  | parameter _ _ _ ih => exact ih
  | index _ _ _ ih => exact ih

theorem RecursorIndexTrace.indexSize {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    indices.size ≤ finalIndices.size := by
  induction trace with
  | stop _ => exact Nat.le_refl _
  | parameter _ _ _ ih => exact ih
  | index _ _ _ ih => simp only [Array.size_push] at ih; omega

theorem RecursorIndexTrace.parameterRange {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    index ≤ finalIndex ∧ finalIndex ≤ max index stats.params.size := by
  induction trace with
  | stop _ => exact ⟨Nat.le_refl _, Nat.le_max_left _ _⟩
  | parameter hparam _ _ ih => constructor <;> omega
  | index _ _ _ ih => exact ih

theorem RecursorIndexTrace.rawArity {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hparams : stats.ParamsAreFVars) :
    index + indices.size + declareConstructors.arity 0 type ≤ finalIndex + finalIndices.size := by
  induction trace with
  | @stop type index indices ctx hnot =>
    have hzero : declareConstructors.arity 0 type = 0 := by
      cases type <;> try rfl
      exact False.elim (hnot _ _ _ _ rfl)
    simp only [hzero, Nat.add_zero]
    exact Nat.le_refl _
  | @parameter name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    have hfvar : stats.params[index]!.isFVar = true := by
      simpa only [getElem!_pos, hparam] using hparams _ (Array.getElem_mem hparam)
    have hbound := whnf_instantiate_arity name domain body bi _ ctx hfvar normalized hnormalized
    omega
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    have hbound := whnf_instantiate_arity name domain body bi (.fvar ⟨ctx.ngen.curr⟩)
      (recursorIndexContext ctx name bi (peelTypeAnnotations domain)) rfl normalized hnormalized
    simp only [Array.size_push] at ih
    omega

theorem RecursorIndexTrace.scope {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) : ctx.RecursorScopeFrame finalCtx := by
  revert hwf hreserved
  induction trace with
  | stop _ => intro hwf hreserved; exact .refl _ hwf hreserved
  | parameter _ _ _ ih => exact ih
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro hwf hreserved
    have hpush := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
    exact hpush.trans (ih hpush.wf hpush.reserved)

theorem RecursorIndexTrace.declared {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hdeclared : RecursorFieldsDeclared ctx.lctx indices) : RecursorFieldsDeclared finalCtx.lctx finalIndices := by
  revert hdeclared
  induction trace with
  | stop _ => exact id
  | parameter _ _ _ ih => exact ih
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    intro hdeclared
    exact ih (hdeclared.push ⟨ctx.ngen.curr⟩ name (peelTypeAnnotations domain) bi)

def recursorMajorDomain (stats : InductiveStats) (parent : Nat) (indices : Array Expr) : Expr :=
  peelTypeAnnotations (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices)

def recursorMotiveDomain (elimLevel : Level) (indices : Array Expr) (major : Expr) (ctx : Context) : Expr :=
  peelTypeAnnotations (ctx.lctx.mkForall indices (ctx.lctx.mkForall #[major] (.sort elimLevel)))

def recursorMotiveName (types : Array InductiveType) (parent : Nat) : Name :=
  if types.size > 1 then (`motive).appendIndexAfter (parent + 1) else `motive

def RecursorInfoIndexSource (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (original : Context) (info : RecInfo) (current : Context) : Prop :=
  ∃ (entry : Context) (normalized terminal : Expr) (finalIndex : Nat) (indexCtx : Context),
    original.RecursorScopeFrame entry ∧
    ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
    RecursorIndexTrace stats normalized 0 #[] entry terminal finalIndex info.indices indexCtx ∧
    info.major = .fvar ⟨indexCtx.ngen.curr⟩ ∧
    let majorCtx := recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices)
    info.motive = .fvar ⟨majorCtx.ngen.curr⟩ ∧
    (recursorIndexContext majorCtx (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel info.indices info.major majorCtx)).RecursorScopeFrame current

def RecursorInfoIndexSources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current

theorem RecursorInfoIndexSource.mono {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current next : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (frame : current.RecursorScopeFrame next) : RecursorInfoIndexSource stats types elimLevel parent original info next := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexCtx, hentry, hnormalized, htrace, hmajor, hmotive, hcurrent⟩ := source
  exact ⟨entry, normalized, terminal, finalIndex, indexCtx, hentry, hnormalized, htrace, hmajor, hmotive,
    hcurrent.trans frame⟩

theorem RecursorInfoIndexSource.withMinors {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) (minors : Array Expr) :
    RecursorInfoIndexSource stats types elimLevel parent original { info with minors } current := source

theorem RecursorInfoIndexSource.declared {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) :
    RecursorFieldsDeclared current.lctx ((info.indices.push info.major).push info.motive) := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexCtx, _, _, htrace, hmajor, hmotive, hcurrent⟩ := source
  have hindices : RecursorFieldsDeclared indexCtx.lctx info.indices := htrace.declared (by
    intro field hfield
    simp at hfield)
  have hdeclared := (hindices.push ⟨indexCtx.ngen.curr⟩ `t (recursorMajorDomain stats parent info.indices) .default).push
    ⟨(recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices)).ngen.curr⟩
    (recursorMotiveName types parent)
    (recursorMotiveDomain elimLevel info.indices info.major
      (recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices))) .default
  rw [← hmajor, ← hmotive] at hdeclared
  intro field hfield
  obtain ⟨decl, hdecl, hshape⟩ := hdeclared field hfield
  exact ⟨decl, hcurrent.declarations.subset hdecl, hshape⟩

theorem RecursorInfoIndexSource.majorLookup {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) :
    ∃ decl, current.lctx.find? info.major.fvarId! = some decl ∧ decl.toExpr = info.major ∧
      decl.type = recursorMajorDomain stats parent info.indices := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexCtx, hentry, _, htrace, hmajor, hmotive, hcurrent⟩ := source
  have hindices := htrace.scope hentry.wf hentry.reserved
  let majorCtx := recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent info.indices)
  have hmajorFrame : indexCtx.RecursorScopeFrame majorCtx :=
    Context.RecursorScopeFrame.push indexCtx hindices.wf hindices.reserved _ _ _
  have hmotiveFrame := Context.RecursorScopeFrame.push majorCtx hmajorFrame.wf hmajorFrame.reserved
    (recursorMotiveName types parent) .default (recursorMotiveDomain elimLevel info.indices info.major majorCtx)
  let decl := LocalDecl.cdecl indexCtx.lctx.decls.size ⟨indexCtx.ngen.curr⟩ `t
    (recursorMajorDomain stats parent info.indices) .default .default
  have hmember : decl ∈ majorCtx.lctx.toList := by
    simp only [majorCtx, recursorIndexContext, LocalContext.mkLocalDecl_toList, List.mem_cons]
    exact Or.inl rfl
  have hlookup : majorCtx.lctx.find? ⟨indexCtx.ngen.curr⟩ = some decl := hmajorFrame.wf.find?_of_mem hmember
  exact ⟨decl, by simpa only [hmajor, Expr.fvarId!] using (hmotiveFrame.trans hcurrent).oldLookup hmajorFrame.wf hlookup,
    hmajor.symm, rfl⟩

theorem RecursorInfoIndexSource.rawArity {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hparams : stats.ParamsAreFVars) :
    declareConstructors.arity 0 types[parent]!.type ≤ stats.params.size + info.indices.size := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexCtx, _, hnormalized, htrace, _⟩ := source
  have hinitial := whnf_arity types[parent]!.type entry normalized hnormalized
  have hbound := htrace.rawArity hparams
  have hparams := htrace.parameterRange.2
  simp only [Array.size_empty, Nat.zero_add, Nat.zero_max] at hbound hparams
  omega

theorem RecursorInfoIndexSources.rawArities {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : RecursorInfoIndexSources stats types elimLevel original infos current)
    (hparams : stats.ParamsAreFVars) : ∀ parent, parent < types.size →
      declareConstructors.arity 0 types[parent]!.type ≤ stats.params.size + infos[parent]!.indices.size :=
  fun parent hparent => (sources.2 parent hparent).rawArity hparams

private theorem loopInd1_sources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α) (original ctx : Context)
    (post : α → Prop) (hbound : parent ≤ types.size) (hsize : infos.size = parent)
    (hframe : original.RecursorScopeFrame ctx)
    (hsources : ∀ previous, previous < infos.size →
      RecursorInfoIndexSource stats types elimLevel previous original infos[previous]! ctx)
    (hnext : ∀ infos current, original.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel original infos current → (next infos current).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos next ctx).WF post := by
  rw [mkRecInfos.loopInd1.eq_def]
  split
  · rename_i hparent
    apply Lean4Lean.AddInductive.readWF
    apply bindResultWF
    intro normalized hnormalized
    apply mkRecInfos.loopArgs1.scopedTrace
    · exact hframe.wf
    · exact hframe.reserved
    intro terminal finalIndex indices indexCtx htrace hindices
    apply withIndexDeclWF
    let majorCtx := recursorIndexContext indexCtx `t .default (recursorMajorDomain stats parent indices)
    have hmajor : indexCtx.RecursorScopeFrame majorCtx :=
      Context.RecursorScopeFrame.push indexCtx hindices.wf hindices.reserved _ _ _
    apply Lean4Lean.AddInductive.getLCtxWF
    dsimp only
    apply withIndexDeclWF
    let motiveCtx := recursorIndexContext majorCtx (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel indices (.fvar ⟨indexCtx.ngen.curr⟩) majorCtx)
    have hmotive : majorCtx.RecursorScopeFrame motiveCtx :=
      Context.RecursorScopeFrame.push majorCtx hmajor.wf hmajor.reserved _ _ _
    have hnew := hindices.trans (hmajor.trans hmotive)
    apply loopInd1_sources
    · omega
    · simpa only [Array.size_push] using congrArg (· + 1) hsize
    · exact hframe.trans hnew
    · intro previous hprevious
      by_cases hlt : previous < infos.size
      · simpa only [getElem!_pos, hlt, hprevious, Array.getElem_push_lt] using (hsources previous hlt).mono hnew
      · have heq : previous = infos.size := by simp only [Array.size_push] at hprevious; omega
        subst previous
        simp only [getElem!_pos, Array.size_push, Nat.lt_add_one, Array.getElem_push_eq]
        rw [hsize]
        refine ⟨ctx, normalized, terminal, finalIndex, indexCtx, hframe, ?_, htrace, rfl, rfl,
          .refl motiveCtx hmotive.wf hmotive.reserved⟩
        simpa only [getElem!_pos, hparent] using hnormalized
    · exact hnext
  · apply hnext infos ctx hframe
    refine ⟨by omega, ?_⟩
    intro previous hprevious
    exact hsources previous (by omega)
termination_by types.size - parent
decreasing_by all_goals simp_wf; omega

private theorem sources_modifyMinors {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : RecursorInfoIndexSources stats types elimLevel original infos current) (parent : Nat) (minor : Expr) :
    RecursorInfoIndexSources stats types elimLevel original
      (infos.modify parent fun info => { info with minors := info.minors.push minor }) current := by
  refine ⟨by simpa only [Array.size_modify] using sources.1, ?_⟩
  intro index hindex
  have hinfo : index < infos.size := by rw [sources.1]; exact hindex
  have hmodified : index < (infos.modify parent fun info => { info with minors := info.minors.push minor }).size := by
    simpa only [Array.size_modify] using hinfo
  by_cases heq : index = parent
  · subst index
    simpa only [getElem!_pos, hinfo, hmodified, Array.getElem_modify, ↓reduceIte] using
      (sources.2 parent hindex).withMinors (infos[parent]!.minors.push minor)
  · simpa only [getElem!_pos, hinfo, hmodified, Array.getElem_modify, if_neg (Ne.symm heq)] using sources.2 index hindex

private theorem loopCtors_sources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (name : Name) (parent : Nat) (infos : Array RecInfo) (ctors : List Constructor) (next : Array RecInfo → M α)
    (original ctx : Context) (post : α → Prop) (hframe : original.RecursorScopeFrame ctx)
    (hsources : RecursorInfoIndexSources stats types elimLevel original infos ctx)
    (hnext : ∀ infos current, original.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel original infos current → (next infos current).WF post) :
    (mkRecInfos.loopCtors stats name parent infos ctors next ctx).WF post := by
  induction ctors generalizing infos ctx with
  | nil => exact hnext infos ctx hframe hsources
  | cons ctor ctors ih =>
    rw [mkRecInfos.loopCtors.eq_def]
    apply mkRecInfos.loopCtorArgs.scope
    · exact hframe.wf
    · exact hframe.reserved
    intro type fields recursiveFields fieldCtx hfields _ _
    apply Lean4Lean.AddInductive.loopU_scope
    · exact hfields.wf
    · exact hfields.reserved
    intro hypotheses hypothesisCtx hhypotheses
    apply Lean4Lean.AddInductive.getLCtxWF
    dsimp only
    apply Lean4Lean.AddInductive.withLocalDecl_scope
    · exact hhypotheses.wf
    · exact hhypotheses.reserved
    intro minor minorCtx hminor
    have hnew := hfields.trans (hhypotheses.trans hminor)
    apply ih
    · exact hframe.trans hnew
    · have hcurrent : RecursorInfoIndexSources stats types elimLevel original infos minorCtx :=
        ⟨hsources.1, fun index hindex => (hsources.2 index hindex).mono hnew⟩
      exact sources_modifyMinors hcurrent parent minor

private theorem loopInd2_sources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α) (original ctx : Context)
    (post : α → Prop) (hframe : original.RecursorScopeFrame ctx)
    (hsources : RecursorInfoIndexSources stats types elimLevel original infos ctx)
    (hnext : ∀ infos current, original.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel original infos current → (next infos current).WF post) :
    (mkRecInfos.loopInd2 stats types parent infos next ctx).WF post := by
  rw [mkRecInfos.loopInd2.eq_def]
  split
  · apply loopCtors_sources
    · exact hframe
    · exact hsources
    intro infos current hframe hsources
    exact loopInd2_sources stats types elimLevel (parent + 1) infos next original current post hframe hsources hnext
  · exact hnext infos ctx hframe hsources
termination_by types.size - parent
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.scopedIndexSources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  unfold mkRecInfos
  apply loopInd1_sources
  · exact Nat.zero_le _
  · rfl
  · exact .refl ctx hwf hreserved
  · intro previous hprevious
    simp at hprevious
  intro infos current hframe hsources
  exact loopInd2_sources stats types elimLevel 0 infos next ctx current post hframe hsources hnext

theorem mkRecInfos.getIndexSources (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 := by
  have hsources : (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF
      fun result => RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 := by
    apply mkRecInfos.scopedIndexSources
    · exact hwf
    · exact hreserved
    intro infos current _ hsources
    exact .pure hsources
  intro result hresult
  obtain ⟨hframe, hcounts⟩ := mkRecInfos.getScopeCounts stats types elimLevel ctx hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources result hresult⟩

theorem mkRecInfos.registeredIndexSources (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have hsources : (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF
      fun result => RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedIndexSources
    · exact hwf
    · exact hreserved
    intro infos current _ hsources
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure hsources
  intro result hresult
  obtain ⟨hframe, hcounts, hresultWF, hkeep, hmetadata, hscope⟩ :=
    mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources result hresult, hresultWF, hkeep, hmetadata, hscope⟩

end Lean4Lean.AddInductive
