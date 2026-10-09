import Lean4Lean.Verify.InductiveIndexAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

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

end Lean4Lean.AddInductive
