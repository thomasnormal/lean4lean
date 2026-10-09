import Lean4Lean.Verify.InductiveHeaderTraces

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

inductive SortTelescope : Expr → Prop where
  | sort (level : Level) : SortTelescope (.sort level)
  | forallE (name : Name) (domain : Expr) (bi : BinderInfo) {body : Expr}
      (tail : SortTelescope body) : SortTelescope (.forallE name domain body bi)

theorem SortTelescope.instantiate1' {type : Expr} (htype : SortTelescope type)
    (param : Expr) (depth : Nat) : SortTelescope (type.instantiate1' param depth) := by
  induction htype generalizing depth with
  | sort level => exact .sort level
  | forallE name domain bi tail ih => exact .forallE name _ bi (ih (depth + 1))

theorem SortTelescope.instantiate1 {type : Expr} (htype : SortTelescope type) (param : Expr) :
    SortTelescope (type.instantiate1 param) := by
  rw [Expr.instantiate1_eq]
  exact htype.instantiate1' param 0

theorem SortTelescope.arity_instantiate1' {type : Expr} (htype : SortTelescope type)
    (param : Expr) (depth index : Nat) :
    declareConstructors.arity index (type.instantiate1' param depth) = declareConstructors.arity index type := by
  induction htype generalizing depth index with
  | sort level => rfl
  | forallE name domain bi tail ih => exact ih (depth + 1) (index + 1)

theorem SortTelescope.arity_instantiate1 {type : Expr} (htype : SortTelescope type) (param : Expr) :
    declareConstructors.arity 0 (type.instantiate1 param) = declareConstructors.arity 0 type := by
  rw [Expr.instantiate1_eq]
  exact htype.arity_instantiate1' param 0 0

theorem SortTelescope.nonForall {type : Expr} (htype : SortTelescope type)
    (hnot : ∀ name domain body bi, type ≠ .forallE name domain body bi) :
    ∃ level, type = .sort level := by
  cases htype with
  | sort level => exact ⟨level, rfl⟩
  | forallE name domain bi tail => exact False.elim (hnot _ _ _ _ rfl)

theorem SortTelescope.whnf {type : Expr} (htype : SortTelescope type) (ctx : Context) :
    ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF fun result => result = type := by
  intro result hresult
  change (TypeChecker.whnf type).run ctx.env ctx.safety ctx.lctx ctx.lparams ctx.fuel = .ok result at hresult
  cases htype <;>
    change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf _
      { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
        lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
  all_goals
    cases hdepth : ctx.fuel.recDepth with
    | zero =>
      rw [hdepth] at hresult
      change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
      cases hresult
    | succ depth =>
      rw [hdepth] at hresult
      change Except.ok _ = .ok result at hresult
      exact (Except.ok.inj hresult).symm

theorem SortTelescope.whnfStep {body : Expr} (htype : SortTelescope body)
    (name : Name) (domain : Expr) (bi : BinderInfo) (param : Expr) (ctx : Context) :
    ((monadLift (TypeChecker.whnf (body.instantiate1 param)) : M Expr) ctx).WF fun result =>
      SortTelescope result ∧ declareConstructors.arity 0 (.forallE name domain body bi) =
        1 + declareConstructors.arity 0 result := by
  refine ((htype.instantiate1 param).whnf ctx).mono ?_
  intro result heq
  subst result
  refine ⟨htype.instantiate1 param, ?_⟩
  rw [htype.arity_instantiate1 param]
  change declareConstructors.arity 1 body = _
  rw [declareConstructors.arity_eq_add]

theorem CheckedHeaderTrace.telescopeCount {nparams : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) :
    index + nindices + declareConstructors.arity 0 type = nparams + finalIndices := by
  induction trace with
  | stop hnot hparams =>
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    simp [declareConstructors.arity, hparams]
  | @freshParameter stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hnormalized tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      obtain ⟨hnext, hstep⟩ := hbody.whnfStep name domain bi (.fvar ⟨ctx.ngen.curr⟩)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      have hcount := ih hnext
      omega
  | @reusedParameter stats name domain body bi index nindices ctx paramType normalized terminal finalStats finalIndices finalCtx
      hparam hfirst hlookup hequal hnormalized tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      obtain ⟨hnext, hstep⟩ := hbody.whnfStep name domain bi stats.params[index]! ctx normalized hnormalized
      have hcount := ih hnext
      omega
  | @index stats name domain body bi index nindices ctx normalized terminal finalStats finalIndices finalCtx
      hparam hnormalized tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      obtain ⟨hnext, hstep⟩ := hbody.whnfStep name domain bi (.fvar ⟨ctx.ngen.curr⟩)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      have hcount := ih hnext
      omega

theorem RecursorIndexTrace.telescopeCounts {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hindex : index ≤ stats.params.size) :
    finalIndex = min (index + declareConstructors.arity 0 type) stats.params.size ∧
      finalIndex + finalIndices.size = index + indices.size + declareConstructors.arity 0 type := by
  induction trace with
  | stop hnot =>
    obtain ⟨level, rfl⟩ := htype.nonForall hnot
    simp [declareConstructors.arity, Nat.min_eq_left hindex]
  | @parameter name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      obtain ⟨hnext, hstep⟩ := hbody.whnfStep name domain bi stats.params[index]! ctx normalized hnormalized
      obtain ⟨hposition, hcount⟩ := ih hnext (by omega)
      constructor <;> omega
  | @index name domain body bi index indices ctx normalized terminal finalIndex finalIndices finalCtx
      hparam hnormalized tail ih =>
    cases htype with
    | forallE _ _ _ hbody =>
      obtain ⟨hnext, hstep⟩ := hbody.whnfStep name domain bi (.fvar ⟨ctx.ngen.curr⟩)
        (recursorIndexContext ctx name bi domain.consumeTypeAnnotations) normalized hnormalized
      obtain ⟨hposition, hcount⟩ := ih hnext hindex
      simp only [Array.size_push] at hcount
      constructor <;> omega

theorem CheckedHeaderSource.telescopeCount {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (htype : SortTelescope types[parent]!.type) :
    declareConstructors.arity 0 types[parent]!.type = params.size + count := by
  have hparamCount := source.paramsCount
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hprefixParams, htrace, hparams, hsort, hcurrent⟩ := source
  have heq := htype.whnf entry normalized hnormalized
  subst normalized
  have hcount := htrace.telescopeCount htype
  omega

theorem RecursorInfoIndexSource.telescopeIndexCount {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent count : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (htype : SortTelescope types[parent]!.type)
    (hcount : declareConstructors.arity 0 types[parent]!.type = stats.params.size + count) : info.indices.size = count := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexCtx, hentry, hnormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq := htype.whnf entry normalized hnormalized
  subst normalized
  obtain ⟨hposition, htotal⟩ := htrace.telescopeCounts htype (Nat.zero_le _)
  simp only [Nat.zero_add, Array.size_empty] at hposition htotal
  omega

def TelescopeHeaders (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → SortTelescope types[parent]!.type

def RecursorIndexCounts (stats : InductiveStats) (types : Array InductiveType) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size → infos[parent]!.indices.size = stats.nindices[parent]!

theorem CheckedHeaderSources.telescopeIndexCounts {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : TelescopeHeaders types) : RecursorIndexCounts stats types infos := by
  refine ⟨sources.1, ?_⟩
  intro parent hparent
  exact (sources.2 parent hparent).telescopeIndexCount (htypes parent hparent)
    ((headers.2 parent hparent).telescopeCount (htypes parent hparent))

theorem mkRecInfos.scopedAlignedIndices (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → RecursorIndexCounts stats types infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedIndexSources
  · exact hwf
  · exact hreserved
  intro infos current hframe hsources
  exact hnext infos current hframe hsources (headers.telescopeIndexCounts hsources htypes)

theorem mkRecInfos.getAlignedIndices (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧ RecursorIndexCounts stats types result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources⟩ := mkRecInfos.getIndexSources stats types elimLevel ctx hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, headers.telescopeIndexCounts hsources htypes⟩

theorem mkRecInfos.registeredAlignedIndices (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs⟩ :=
    mkRecInfos.registeredIndexSources stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs,
    headers.telescopeIndexCounts hsources htypes⟩

theorem checkInductiveTypes.safeRegisteredIndexCounts (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : TelescopeHeaders types) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result => RecursorIndexCounts result.1 types result.2.2.1 := by
  apply checkInductiveTypes.scopedHeaderTraces
  · exact hwf
  · exact hreserved
  intro stats current headers hframe
  apply Lean4Lean.AddInductive.bindWF
  intro headerEnv
  change ((checkConstructors types stats false >>= fun _ => _) { current with env := headerEnv }).WF _
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply Lean4Lean.AddInductive.bindWF
  intro constructorEnv
  change ((mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
    { current with env := constructorEnv }).bind fun result => .ok (stats, result)).WF _
  have hcounts : (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
      { current with env := constructorEnv }).WF fun result => RecursorIndexCounts stats types result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedAlignedIndices nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1) headers htypes
    · exact hframe.wf
    · exact hframe.reserved
    intro infos source _ _ hcounts
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure hcounts
  exact hcounts.bind fun result hcount => .pure hcount

end Lean4Lean.AddInductive
