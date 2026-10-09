import Lean4Lean.Verify.InductiveIndexAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def NormalizedSortTelescope (source normalized : Expr) : Prop :=
  SortTelescope normalized ∧
    ∀ ctx, ((monadLift (TypeChecker.whnf source) : M Expr) ctx).WF fun result => result = normalized

theorem CheckedHeaderSource.telescopeCount_of_normalized {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    declareConstructors.arity 0 normalized = params.size + count := by
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  have hcount := htrace.telescopeCount hnormalized.1
  have hparamCount := htrace.paramsCount (by simpa [Array.isEmpty, hconst] using hprefixParams)
  have hparamSize : params.size = nparams := by simpa [← hparams] using hparamCount
  omega

theorem RecursorInfoIndexSource.telescopeIndexCount_of_normalized
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent count : Nat} {original current : Context} {info : RecInfo} {normalized : Expr}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized)
    (hcount : declareConstructors.arity 0 normalized = stats.params.size + count) :
    info.indices.size = count := by
  obtain ⟨entry, sourceNormalized, terminal, finalIndex, indexCtx, hentry, hsourceNormalized, htrace,
    hmajor, hmotive, hcurrent⟩ := source
  have heq : sourceNormalized = normalized := hnormalized.2 entry sourceNormalized hsourceNormalized
  rw [heq] at htrace
  obtain ⟨hposition, htotal⟩ := htrace.telescopeCounts hnormalized.1 (Nat.zero_le _)
  simp only [Nat.zero_add, Array.size_empty] at hposition htotal
  omega

def NormalizedHeaderTelescope (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → ∃ normalized, NormalizedSortTelescope types[parent]!.type normalized

theorem CheckedHeaderSources.normalizedTelescopeIndexCounts {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) : RecursorIndexCounts stats types infos := by
  refine ⟨sources.1, ?_⟩
  intro parent hparent
  obtain ⟨normalized, hnormalized⟩ := htypes parent hparent
  exact (sources.2 parent hparent).telescopeIndexCount_of_normalized hnormalized
    ((headers.2 parent hparent).telescopeCount_of_normalized hnormalized)

theorem mkRecInfos.scopedNormalizedAlignedIndices (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedIndexSources
  · exact hwf
  · exact hreserved
  intro infos current hframe hsources
  exact hnext infos current hframe hsources (headers.normalizedTelescopeIndexCounts hsources htypes)

theorem mkRecInfos.getNormalizedAlignedIndices (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources⟩ :=
    mkRecInfos.getIndexSources stats types elimLevel ctx hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, headers.normalizedTelescopeIndexCounts hsources htypes⟩

theorem mkRecInfos.registeredNormalizedAlignedIndices (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
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
    headers.normalizedTelescopeIndexCounts hsources htypes⟩

theorem checkInductiveTypes.safeRegisteredNormalizedIndexCounts (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
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
    apply mkRecInfos.scopedNormalizedAlignedIndices nparams stats types elimLevel _ ctx current
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
