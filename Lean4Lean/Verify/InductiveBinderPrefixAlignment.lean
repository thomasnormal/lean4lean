import Lean4Lean.Verify.InductiveBinderPrefixes
import Lean4Lean.Verify.InductiveBinderOpening
import Lean4Lean.Verify.InductiveBinderAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderPrefixAlignment (stats : InductiveStats) (types : Array InductiveType)
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
    BinderStepsIndexDeclared checkedRoot checked ∧ BinderStepsIndexDeclared current generated ∧
    checked.map (·.role) = List.replicate stats.params.size .parameter ++
      List.replicate stats.nindices[parent]! .index ∧
    generated.map (·.role) = List.replicate stats.params.size .parameter ++
      List.replicate info.indices.size .index ∧
    checked.take stats.params.size = generated.take stats.params.size ∧
    ((checked.drop stats.params.size).head?).map BinderStep.domain =
      ((generated.drop stats.params.size).head?).map BinderStep.domain ∧
    ((checked.drop stats.params.size).head?).map BinderStep.localDomain =
      ((generated.drop stats.params.size).head?).map BinderStep.localDomain

def RecursorBinderPrefixAlignment (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderPrefixAlignment stats types parent checkedRoot current infos[parent]!

private theorem firstIndexRole {steps : List BinderStep} {nparams nindices : Nat}
    {first : BinderStep}
    (hroles : steps.map BinderStep.role = List.replicate nparams .parameter ++
      List.replicate nindices .index)
    (hfirst : (steps.drop nparams).head? = some first) : first.role = .index := by
  have hdropped : (steps.drop nparams).map BinderStep.role = List.replicate nindices .index := by
    rw [List.map_drop, hroles, List.drop_append_of_le_length (by simp)]
    simp only [List.drop_replicate, Nat.sub_self, List.replicate_zero, List.nil_append]
  have hmem : first.role ∈ (steps.drop nparams).map BinderStep.role :=
    List.mem_map.mpr ⟨first, List.mem_of_head? hfirst, rfl⟩
  rw [hdropped] at hmem
  exact (List.mem_replicate.mp hmem).2

theorem BinderStep.IndexDomainsDeclared.firstIndexTypeAgreement
    {checkedRoot current : Context} {checked generated : List BinderStep}
    {nparams checkedCount generatedCount : Nat} {checkedFirst generatedFirst : BinderStep}
    (hcheckedDeclared : IndexDomainsDeclared checkedRoot checked)
    (hgeneratedDeclared : IndexDomainsDeclared current generated)
    (hcheckedRoles : checked.map BinderStep.role = List.replicate nparams .parameter ++
      List.replicate checkedCount .index)
    (hgeneratedRoles : generated.map BinderStep.role = List.replicate nparams .parameter ++
      List.replicate generatedCount .index)
    (hcheckedFirst : (checked.drop nparams).head? = some checkedFirst)
    (hgeneratedFirst : (generated.drop nparams).head? = some generatedFirst)
    (hdomains : ((checked.drop nparams).head?).map BinderStep.localDomain =
      ((generated.drop nparams).head?).map BinderStep.localDomain) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      checkedDecl.type = generatedDecl.type := by
  obtain ⟨checkedDecl, hcheckedLookup, _, hcheckedType, _, _⟩ :=
    hcheckedDeclared checkedFirst (List.mem_of_mem_drop (List.mem_of_head? hcheckedFirst))
      (firstIndexRole hcheckedRoles hcheckedFirst)
  obtain ⟨generatedDecl, hgeneratedLookup, _, hgeneratedType, _, _⟩ :=
    hgeneratedDeclared generatedFirst (List.mem_of_mem_drop (List.mem_of_head? hgeneratedFirst))
      (firstIndexRole hgeneratedRoles hgeneratedFirst)
  simp only [hcheckedFirst, hgeneratedFirst, Option.map_some, Option.some.injEq] at hdomains
  exact ⟨checkedDecl, generatedDecl, hcheckedLookup, hgeneratedLookup,
    hcheckedType.trans (hdomains.trans hgeneratedType.symm)⟩

theorem ParentBinderPrefixAlignment.toBinderDomains {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderPrefixAlignment stats types parent checkedRoot current info) :
    ParentBinderDomainAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, _⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared⟩

theorem RecursorBinderPrefixAlignment.toBinderDomains {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderPrefixAlignment stats types checkedRoot current infos) :
    RecursorBinderDomainAlignment stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).toBinderDomains⟩

theorem CheckedHeaderSources.normalizedBinderPrefixes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) :
    RecursorBinderPrefixAlignment stats types checkedRoot current infos := by
  refine ⟨sources.1, ?_⟩
  intro parent hparent
  obtain ⟨normalized, hnormalized⟩ := htypes parent hparent
  obtain ⟨checked, checkedTerminal, hopenChecked, hcheckedParams, hcheckedIndices,
      hcheckedDeclared, hcheckedRoles⟩ :=
    (headers.2 parent hparent).openedPrefix_of_normalized hnormalized
  obtain ⟨generated, generatedTerminal, finalIndex, hopenGenerated, hgeneratedParams,
      hgeneratedIndices, hposition, hgeneratedDeclared, hgeneratedRoles⟩ :=
    (sources.2 parent hparent).openedPrefix_of_normalized hnormalized
  have hcount := (headers.2 parent hparent).telescopeCount_of_normalized hnormalized
  have hbound : stats.params.size ≤ declareConstructors.arity 0 normalized := by omega
  have hcomplete : finalIndex = stats.params.size := hposition.trans (Nat.min_eq_right hbound)
  rw [hcomplete] at hgeneratedParams hgeneratedRoles
  simp only [← Array.length_toList, List.drop_length, List.append_nil] at hgeneratedParams
  have hagreement := hopenChecked.sameParameterPrefix hopenGenerated hcheckedRoles hgeneratedRoles
    (hcheckedParams.trans hgeneratedParams)
  have hlocal : ((checked.drop stats.params.size).head?).map BinderStep.localDomain =
      ((generated.drop stats.params.size).head?).map BinderStep.localDomain := by
    simpa only [BinderStep.localDomain, Option.map_map, Function.comp_def] using
      congrArg (Option.map Expr.consumeTypeAnnotations) hagreement.2
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hopenChecked, hopenGenerated, hopenChecked.sameSignature hopenGenerated hnormalized.1,
    hcheckedParams, hgeneratedParams.symm, hcheckedIndices, hgeneratedIndices.symm,
    hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles, hagreement.1,
    hagreement.2, hlocal⟩

theorem CheckedHeaderSources.wrappedBinderPrefixes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types) :
    RecursorBinderPrefixAlignment stats types checkedRoot current infos :=
  headers.normalizedBinderPrefixes sources htypes.normalizedHeaders

theorem mkRecInfos.scopedNormalizedBinderPrefixes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderPrefixAlignment stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedAlignedIndices nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved
  intro infos current hframe hsources hcounts
  exact hnext infos current hframe hsources hcounts (headers.normalizedBinderPrefixes hsources htypes)

theorem mkRecInfos.getNormalizedBinderPrefixes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderPrefixAlignment stats types checkedRoot result.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, haligned⟩ :=
    mkRecInfos.getNormalizedAlignedIndices nparams stats types elimLevel original checkedRoot ctx
      headers htypes hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, haligned, headers.normalizedBinderPrefixes hsources htypes⟩

theorem mkRecInfos.registeredNormalizedBinderPrefixes (nparams : Nat) (stats : InductiveStats)
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
      RecursorBinderPrefixAlignment stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, haligned⟩ :=
    mkRecInfos.registeredNormalizedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, haligned,
    headers.normalizedBinderPrefixes hsources htypes⟩

theorem checkInductiveTypes.safeRegisteredNormalizedBinderPrefixes (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderPrefixAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderPrefixAlignment stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderPrefixes nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderPrefixAlignment stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved
    intro infos source _ _ hcounts hprefixes
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers, hprefixes⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredWrappedBinderPrefixes (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderPrefixAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderPrefixes nparams types numNested elimLevel lparams
    isK ctx htypes.normalizedHeaders hwf hreserved

end Lean4Lean.AddInductive
