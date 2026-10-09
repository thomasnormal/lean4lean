import Lean4Lean.Verify.InductiveBinderDomains
import Lean4Lean.Verify.InductiveWrappedHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderDomainAlignment (stats : InductiveStats) (types : Array InductiveType)
    (parent : Nat) (checkedRoot current : Context) (info : RecInfo) : Prop :=
  ∃ normalized checked generated checkedTerminal generatedTerminal,
    NormalizedSortTelescope types[parent]!.type normalized ∧
    OpenedTelescope normalized checked checkedTerminal ∧
    OpenedTelescope normalized generated generatedTerminal ∧
    checked.map BinderStep.signature = generated.map BinderStep.signature ∧
    BinderStep.parameterValues checked = stats.params.toList ∧
    BinderStep.parameterValues generated = stats.params.toList ∧
    (BinderStep.indexValues checked).length = stats.nindices[parent]! ∧
    BinderStep.indexValues generated = info.indices.toList ∧
    BinderStepsIndexDeclared checkedRoot checked ∧ BinderStepsIndexDeclared current generated

def RecursorBinderDomainAlignment (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderDomainAlignment stats types parent checkedRoot current infos[parent]!

theorem CheckedHeaderSources.normalizedBinderDomains {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) : RecursorBinderDomainAlignment stats types checkedRoot current infos := by
  refine ⟨sources.1, ?_⟩
  intro parent hparent
  obtain ⟨normalized, hnormalized⟩ := htypes parent hparent
  obtain ⟨checked, checkedTerminal, hopenChecked, hcheckedParams, hcheckedIndices, hcheckedDeclared⟩ :=
    (headers.2 parent hparent).opened_of_normalized hnormalized
  obtain ⟨generated, generatedTerminal, finalIndex, hopenGenerated, hgeneratedParams,
      hgeneratedIndices, hposition, hgeneratedDeclared⟩ :=
    (sources.2 parent hparent).opened_of_normalized hnormalized
  have hcount := (headers.2 parent hparent).telescopeCount_of_normalized hnormalized
  have hbound : stats.params.size ≤ declareConstructors.arity 0 normalized := by omega
  have hcomplete : finalIndex = stats.params.size := hposition.trans (Nat.min_eq_right hbound)
  rw [hcomplete] at hgeneratedParams
  simp only [← Array.length_toList, List.drop_length, List.append_nil] at hgeneratedParams
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hopenChecked, hopenGenerated, hopenChecked.sameSignature hopenGenerated hnormalized.1,
    hcheckedParams, hgeneratedParams.symm, hcheckedIndices, hgeneratedIndices.symm,
    hcheckedDeclared, hgeneratedDeclared⟩

theorem CheckedHeaderSources.wrappedBinderDomains {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types) : RecursorBinderDomainAlignment stats types checkedRoot current infos :=
  headers.normalizedBinderDomains sources htypes.normalizedHeaders

theorem mkRecInfos.scopedNormalizedBinderDomains (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderDomainAlignment stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedAlignedIndices nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved
  intro infos current hframe hsources hcounts
  exact hnext infos current hframe hsources hcounts (headers.normalizedBinderDomains hsources htypes)

theorem mkRecInfos.getNormalizedBinderDomains (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderDomainAlignment stats types checkedRoot result.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, haligned⟩ :=
    mkRecInfos.getNormalizedAlignedIndices nparams stats types elimLevel original checkedRoot ctx
      headers htypes hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, haligned, headers.normalizedBinderDomains hsources htypes⟩

theorem mkRecInfos.registeredNormalizedBinderDomains (nparams : Nat) (stats : InductiveStats)
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
      RecursorIndexCounts stats types result.2.1 ∧
      RecursorBinderDomainAlignment stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, haligned⟩ :=
    mkRecInfos.registeredNormalizedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, haligned,
    headers.normalizedBinderDomains hsources htypes⟩

theorem checkInductiveTypes.safeRegisteredNormalizedBinderDomains (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderDomainAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
  have hreceipts : (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
      { current with env := constructorEnv }).WF fun result =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderDomainAlignment stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderDomains nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderDomainAlignment stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved
    intro infos source _ _ hcounts hdomains
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers, hdomains⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredWrappedBinderDomains (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderDomainAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderDomains nparams types numNested elimLevel lparams
    isK ctx htypes.normalizedHeaders hwf hreserved

end Lean4Lean.AddInductive
