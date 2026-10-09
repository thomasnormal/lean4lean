import Lean4Lean.Verify.InductiveBinderRawScopeExclusion
import Lean4Lean.Verify.InductiveBinderLookupTypes

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderScopedLookupTypes (stats : InductiveStats) (types : Array InductiveType)
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
      (info.indices.toList.map Expr.fvarId!) ∧ IndexPairInjection pairs ∧
    BinderParameterIndexDisjoint checked ∧ BinderParameterIndexDisjoint generated ∧
    BinderLookupCorrespondence [] checked generated pairs ∧
    IndexLookupRenaming pairs checkedTerminal generatedTerminal ∧
    BinderLookupNativeTypes [] checkedRoot current checkedStart generatedStart checked generated ∧
    BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
    BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
    BinderRawIndexExclusion checked ∧ BinderRawIndexExclusion generated

def RecursorBinderScopedLookupTypes (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderScopedLookupTypes stats types parent checkedRoot current infos[parent]!

theorem ParentBinderScopedLookupTypes.toBinderLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderScopedLookupTypes stats types parent checkedRoot current info) :
    ParentBinderLookupTypes stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, _, _, _, _⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal, hnative⟩

theorem RecursorBinderScopedLookupTypes.toBinderLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderScopedLookupTypes stats types checkedRoot current infos) :
    RecursorBinderLookupTypes stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).toBinderLookupTypes⟩

theorem ParentBinderLookupTypes.rawDomainScope {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderLookupTypes stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      IndexFVarsWithin (stats.params.toList.map Expr.fvarId!) normalized) :
    ParentBinderScopedLookupTypes stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal, hnative⟩ := receipt
  have hcheckedScope := hchecked.rawDomainScope (within normalized hnormalized)
    (hcheckedParams ▸ shapes) hcheckedDeclared
  have hgeneratedScope := hgenerated.rawDomainScope (within normalized hnormalized)
    (hgeneratedParams ▸ shapes) hgeneratedDeclared
  obtain ⟨hcheckedDistinct, hgeneratedDistinct⟩ := hlookup.indexIdsNodup hinjection
  have hcheckedDisjoint : List.Disjoint (stats.params.toList.map Expr.fvarId!)
      ((BinderStep.indexValues checked).map Expr.fvarId!) := by
    simpa only [BinderParameterIndexDisjoint, hcheckedParams] using hcheckedSupport
  have hgeneratedDisjoint : List.Disjoint (stats.params.toList.map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!) := by
    simpa only [BinderParameterIndexDisjoint, hgeneratedParams] using hgeneratedSupport
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope,
    hcheckedScope.indexExclusion hcheckedDistinct hcheckedDisjoint,
    hgeneratedScope.indexExclusion hgeneratedDistinct hgeneratedDisjoint⟩

theorem RecursorBinderLookupTypes.rawDomainScope {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderLookupTypes stats types checkedRoot current infos)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderScopedLookupTypes stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).rawDomainScope shapes (within parent hparent)⟩

theorem CheckedHeaderSupportSources.normalizedBinderScopedLookupTypes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderScopedLookupTypes stats types checkedRoot current infos :=
  (headers.normalizedBinderLookupTypes sources htypes support hwf within).rawDomainScope support.fvarValues within

theorem CheckedHeaderSupportSources.wrappedBinderScopedLookupTypes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) :
    RecursorBinderScopedLookupTypes stats types checkedRoot current infos :=
  headers.normalizedBinderScopedLookupTypes sources htypes.normalizedHeaders support hwf
    (headers.wrappedFVarsWithin htypes)

theorem mkRecInfos.scopedNormalizedBinderScopedLookupTypes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!))
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderScopedLookupTypes stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderLookupTypes nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support within
  intro infos current hframe hsources hcounts hlookup
  exact hnext infos current hframe hsources hcounts (hlookup.rawDomainScope support.fvarValues within)

theorem mkRecInfos.getNormalizedBinderScopedLookupTypes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧
      RecursorBinderScopedLookupTypes stats types checkedRoot result.2 result.1 :=
  (mkRecInfos.getNormalizedBinderLookupTypes nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support within).mono fun _ receipt =>
      ⟨receipt.1, receipt.2.1, receipt.2.2.1, receipt.2.2.2.1,
        receipt.2.2.2.2.rawDomainScope support.fvarValues within⟩

theorem mkRecInfos.registeredNormalizedBinderScopedLookupTypes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧
      RecursorBinderScopedLookupTypes stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hlookup⟩ :=
    mkRecInfos.registeredNormalizedBinderLookupTypes nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv support within result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    hlookup.rawDomainScope support.fvarValues within⟩

theorem checkInductiveTypes.safeRegisteredBinderScopedLookupTypes (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hwithin : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderScopedLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
  apply checkInductiveTypes.scopedHeaderSupportTraces
  · exact hwf
  · exact hreserved
  intro stats current headers hframe support
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
          RecursorBinderScopedLookupTypes stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderScopedLookupTypes nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderScopedLookupTypes stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved support (hwithin stats current headers)
    intro infos source _ _ hcounts hlookup
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers.toSources, hlookup⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredNormalizedBinderScopedLookupTypes
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnofvars : NormalizedHeaderFVarsWithin types []) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderScopedLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderScopedLookupTypes nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (List.nil_subset _))

theorem checkInductiveTypes.safeRegisteredWrappedBinderScopedLookupTypes
    (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderScopedLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderScopedLookupTypes nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsWithin htypes)

end Lean4Lean.AddInductive
