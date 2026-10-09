import Lean4Lean.Verify.InductiveBinderAllocations
import Lean4Lean.Verify.InductiveBinderRenamingAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderAllocationAlignment (stats : InductiveStats) (types : Array InductiveType)
    (parent : Nat) (checkedRoot current : Context) (info : RecInfo) : Prop :=
  ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
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
      ((generated.drop stats.params.size).head?).map BinderStep.localDomain ∧
    BinderIndexAllocations checkedRoot checkedStart checked ∧
    BinderIndexAllocations current generatedStart generated ∧
    BinderIndexCorrespondence [] checked generated pairs ∧
    pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      (info.indices.toList.map Expr.fvarId!) ∧ IndexPairInjection pairs

def RecursorBinderAllocationAlignment (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderAllocationAlignment stats types parent checkedRoot current infos[parent]!

theorem ParentBinderAllocationAlignment.toBinderRenaming {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderAllocationAlignment stats types parent checkedRoot current info) :
    ParentBinderRenamingAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, _, _, hcorrespondence, hpairs, _⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles,
    hprefix, hraw, hlocal, pairs, hcorrespondence, hpairs⟩

theorem RecursorBinderAllocationAlignment.toBinderRenaming {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderAllocationAlignment stats types checkedRoot current infos) :
    RecursorBinderRenamingAlignment stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).toBinderRenaming⟩

theorem ParentBinderAllocationAlignment.injectiveIndexZip {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderAllocationAlignment stats types parent checkedRoot current info) :
    ∃ checkedIds pairs,
      checkedIds.length = stats.nindices[parent]! ∧
      pairs = checkedIds.zip (info.indices.toList.map Expr.fvarId!) ∧
      pairs.map Prod.fst = checkedIds ∧
      pairs.map Prod.snd = info.indices.toList.map Expr.fvarId! ∧ IndexPairInjection pairs := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection⟩ := alignment
  let checkedIds := (BinderStep.indexValues checked).map Expr.fvarId!
  have hcheckedLength : checkedIds.length = stats.nindices[parent]! := by
    simpa only [checkedIds, List.length_map] using hcheckedIndices
  have hstepLength : checked.length = generated.length := by
    simpa only [List.length_map] using congrArg List.length hsignature
  have hleftLength := congrArg List.length hcheckedRoles
  have hrightLength := congrArg List.length hgeneratedRoles
  simp only [List.length_map, List.length_append, List.length_replicate] at hleftLength hrightLength
  have hcount : stats.nindices[parent]! = info.indices.size := by omega
  have hlength : checkedIds.length = (info.indices.toList.map Expr.fvarId!).length := by
    simpa only [List.length_map, Array.length_toList] using hcheckedLength.trans hcount
  obtain ⟨hfst, hsnd⟩ := indexZipExactProjections hlength
  refine ⟨checkedIds, pairs, hcheckedLength, hpairs, ?_, ?_, hinjection⟩
  · simpa only [hpairs] using hfst
  · simpa only [hpairs] using hsnd

theorem CheckedHeaderSources.normalizedBinderAllocations {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) :
    RecursorBinderAllocationAlignment stats types checkedRoot current infos := by
  refine ⟨sources.1, ?_⟩
  intro parent hparent
  obtain ⟨normalized, hnormalized⟩ := htypes parent hparent
  obtain ⟨checked, checkedTerminal, hopenChecked, hcheckedParams, hcheckedIndices,
    hcheckedDeclared, hcheckedRoles, checkedStart, hcheckedAlloc⟩ :=
    (headers.2 parent hparent).openedAllocations_of_normalized hnormalized
  obtain ⟨generated, generatedTerminal, finalIndex, hopenGenerated, hgeneratedParams,
    hgeneratedIndices, hposition, hgeneratedDeclared, hgeneratedRoles, generatedStart, hgeneratedAlloc⟩ :=
    (sources.2 parent hparent).openedAllocations_of_normalized hnormalized
  have hcount := (headers.2 parent hparent).telescopeCount_of_normalized hnormalized
  have hbound : stats.params.size ≤ declareConstructors.arity 0 normalized := by omega
  have hcomplete : finalIndex = stats.params.size := hposition.trans (Nat.min_eq_right hbound)
  rw [hcomplete] at hgeneratedParams hgeneratedRoles
  simp only [← Array.length_toList, List.drop_length, List.append_nil] at hgeneratedParams
  have hindexCount := (sources.2 parent hparent).telescopeIndexCount_of_normalized hnormalized hcount
  have hroles : checked.map BinderStep.role = generated.map BinderStep.role := by
    rw [hcheckedRoles, hgeneratedRoles, hindexCount]
  have hagreement := hopenChecked.sameParameterPrefix hopenGenerated hcheckedRoles hgeneratedRoles
    (hcheckedParams.trans hgeneratedParams)
  have hlocal : ((checked.drop stats.params.size).head?).map BinderStep.localDomain =
      ((generated.drop stats.params.size).head?).map BinderStep.localDomain := by
    simpa only [BinderStep.localDomain, Option.map_map, Function.comp_def] using
      congrArg (Option.map peelTypeAnnotations) hagreement.2
  obtain ⟨pairs, hcorrespondence⟩ := hopenChecked.indexCorrespondence hopenGenerated hroles
    (hcheckedParams.trans hgeneratedParams) hcheckedDeclared hgeneratedDeclared
  have hactualPairs : pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!) := by
    simpa only [List.nil_append] using hcorrespondence.finalPairs
  have hinjection := IndexPairInjection.of_zip hcheckedAlloc.indexIdsNodup hgeneratedAlloc.indexIdsNodup
  rw [← hactualPairs] at hinjection
  have hpairs : pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      (infos[parent]!.indices.toList.map Expr.fvarId!) := by
    simpa only [hgeneratedIndices] using hactualPairs
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hopenChecked, hopenGenerated,
    hopenChecked.sameSignature hopenGenerated hnormalized.1, hcheckedParams, hgeneratedParams.symm,
    hcheckedIndices, hgeneratedIndices.symm, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles,
    hgeneratedRoles, hagreement.1, hagreement.2, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection⟩

theorem CheckedHeaderSources.wrappedBinderAllocations {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types) :
    RecursorBinderAllocationAlignment stats types checkedRoot current infos :=
  headers.normalizedBinderAllocations sources htypes.normalizedHeaders

theorem mkRecInfos.scopedNormalizedBinderAllocations (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderAllocationAlignment stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedAlignedIndices nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved
  intro infos current hframe hsources hcounts
  exact hnext infos current hframe hsources hcounts (headers.normalizedBinderAllocations hsources htypes)

theorem mkRecInfos.getNormalizedBinderAllocations (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderAllocationAlignment stats types checkedRoot result.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hcountsAligned⟩ :=
    mkRecInfos.getNormalizedAlignedIndices nparams stats types elimLevel original checkedRoot ctx
      headers htypes hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, hcountsAligned, headers.normalizedBinderAllocations hsources htypes⟩

theorem mkRecInfos.registeredNormalizedBinderAllocations (nparams : Nat) (stats : InductiveStats)
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
      RecursorBinderAllocationAlignment stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned⟩ :=
    mkRecInfos.registeredNormalizedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    headers.normalizedBinderAllocations hsources htypes⟩

theorem checkInductiveTypes.safeRegisteredNormalizedBinderAllocations (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderAllocationAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderAllocationAlignment stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderAllocations nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderAllocationAlignment stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved
    intro infos source _ _ hcounts hallocations
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers, hallocations⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredWrappedBinderAllocations (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderAllocationAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderAllocations nparams types numNested elimLevel lparams
    isK ctx htypes.normalizedHeaders hwf hreserved

end Lean4Lean.AddInductive
