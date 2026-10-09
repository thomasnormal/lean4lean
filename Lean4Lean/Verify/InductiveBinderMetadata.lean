import Lean4Lean.Verify.InductiveBinderRangeFits
import Lean4Lean.Verify.InductiveBinderBoundedClosure

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderMetadata (stats : InductiveStats) (types : Array InductiveType)
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
    BinderRawIndexExclusion checked ∧ BinderRawIndexExclusion generated ∧
    BinderLookupStoredTypeScopes [] (stats.params.toList.map Expr.fvarId!)
      checkedRoot current checkedStart generatedStart checked generated ∧
    BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
    BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
    BinderStoredIndexExclusion checked ∧ BinderStoredIndexExclusion generated ∧
    BinderRawDomainFVarsIn (stats.params.toList.map Expr.fvarId!) checked ∧
    BinderRawDomainFVarsIn (stats.params.toList.map Expr.fvarId!) generated ∧
    BinderStoredIndexDomainFVarsIn (stats.params.toList.map Expr.fvarId!) checked ∧
    BinderStoredIndexDomainFVarsIn (stats.params.toList.map Expr.fvarId!) generated ∧
    BinderStoredIndexTypeFVarsIn (stats.params.toList.map Expr.fvarId!) checkedRoot checked ∧
    BinderStoredIndexTypeFVarsIn (stats.params.toList.map Expr.fvarId!) current generated ∧
    normalized.Closed 0 ∧ BinderRawDomainClosed checked ∧ BinderRawDomainClosed generated ∧
    BinderStoredIndexDomainClosed checked ∧ BinderStoredIndexDomainClosed generated ∧
    BinderStoredIndexTypeClosed checkedRoot checked ∧ BinderStoredIndexTypeClosed current generated ∧
    checkedTerminal.Closed 0 ∧ generatedTerminal.Closed 0 ∧
    BVarRangeFits normalized ∧ BinderRawDomainRangeFits checked ∧ BinderRawDomainRangeFits generated ∧
    BinderStoredIndexDomainRangeFits checked ∧ BinderStoredIndexDomainRangeFits generated ∧
    BinderStoredIndexTypeRangeFits checkedRoot checked ∧ BinderStoredIndexTypeRangeFits current generated ∧
    BVarRangeFits checkedTerminal ∧ BVarRangeFits generatedTerminal ∧
    NativeBinderClosed normalized ∧ BinderRawDomainNativeClosed checked ∧ BinderRawDomainNativeClosed generated ∧
    BinderStoredIndexDomainNativeClosed checked ∧ BinderStoredIndexDomainNativeClosed generated ∧
    BinderStoredIndexTypeNativeClosed checkedRoot checked ∧ BinderStoredIndexTypeNativeClosed current generated ∧
    NativeBinderClosed checkedTerminal ∧ NativeBinderClosed generatedTerminal

def RecursorBinderMetadata (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderMetadata stats types parent checkedRoot current infos[parent]!

theorem ParentBinderMetadata.toBinderClosure {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderMetadata stats types parent checkedRoot current info) :
    ParentBinderClosure stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedStoredClosed, hgeneratedStoredClosed,
    hcheckedTypeClosed, hgeneratedTypeClosed, hcheckedTerminalClosed, hgeneratedTerminalClosed, _⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedStoredClosed, hgeneratedStoredClosed,
    hcheckedTypeClosed, hgeneratedTypeClosed, hcheckedTerminalClosed, hgeneratedTerminalClosed⟩

theorem RecursorBinderMetadata.toBinderClosure {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderMetadata stats types checkedRoot current infos) :
    RecursorBinderClosure stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).toBinderClosure⟩

theorem ParentBinderMetadata.toBinderIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderMetadata stats types parent checkedRoot current info) :
    ParentBinderIntegrity stats types parent checkedRoot current info :=
  receipt.toBinderClosure.toBinderIntegrity

theorem RecursorBinderMetadata.toBinderIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderMetadata stats types checkedRoot current infos) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  receipt.toBinderClosure.toBinderIntegrity

theorem ParentBinderClosure.metadata {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderClosure stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id, value = .fvar id)
    (fits : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized → BVarRangeFits normalized) :
    ParentBinderMetadata stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedStoredClosed, hgeneratedStoredClosed,
    hcheckedTypeClosed, hgeneratedTypeClosed, hcheckedTerminalClosed, hgeneratedTerminalClosed⟩ := receipt
  have hnormalizedFits := fits normalized hnormalized
  have hcheckedValuesClosed := hcheckedDeclared.valuesClosed hcheckedParams shapes
  have hgeneratedValuesClosed := hgeneratedDeclared.valuesClosed hgeneratedParams shapes
  have hcheckedValues := hcheckedDeclared.valuesRangeFits hcheckedParams shapes
  have hgeneratedValues := hgeneratedDeclared.valuesRangeFits hgeneratedParams shapes
  have hcheckedFits := hchecked.rawDomainRangeFits hnormalizedFits hcheckedValuesClosed hcheckedValues
  have hgeneratedFits := hgenerated.rawDomainRangeFits hnormalizedFits hgeneratedValuesClosed hgeneratedValues
  have hcheckedStoredFits := hcheckedFits.storedIndexDomainRangeFits
  have hgeneratedStoredFits := hgeneratedFits.storedIndexDomainRangeFits
  have hcheckedTypeFits := hcheckedFits.storedIndexTypeRangeFits hcheckedDeclared
  have hgeneratedTypeFits := hgeneratedFits.storedIndexTypeRangeFits hgeneratedDeclared
  have hcheckedTerminalFits := hchecked.terminalRangeFits
  have hgeneratedTerminalFits := hgenerated.terminalRangeFits
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedStoredClosed, hgeneratedStoredClosed,
    hcheckedTypeClosed, hgeneratedTypeClosed, hcheckedTerminalClosed, hgeneratedTerminalClosed,
    hnormalizedFits, hcheckedFits, hgeneratedFits, hcheckedStoredFits, hgeneratedStoredFits,
    hcheckedTypeFits, hgeneratedTypeFits, hcheckedTerminalFits, hgeneratedTerminalFits,
    hnormalizedFits.nativeBinderClosed hnormalizedClosed,
    hcheckedClosed.nativeClosed hcheckedFits, hgeneratedClosed.nativeClosed hgeneratedFits,
    hcheckedStoredClosed.nativeClosed hcheckedStoredFits,
    hgeneratedStoredClosed.nativeClosed hgeneratedStoredFits,
    hcheckedTypeClosed.nativeClosed hcheckedTypeFits,
    hgeneratedTypeClosed.nativeClosed hgeneratedTypeFits,
    hcheckedTerminalFits.nativeBinderClosed hcheckedTerminalClosed,
    hgeneratedTerminalFits.nativeBinderClosed hgeneratedTerminalClosed⟩

theorem RecursorBinderClosure.metadata {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderClosure stats types checkedRoot current infos)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id, value = .fvar id)
    (fits : NormalizedHeaderRangeFits types) : RecursorBinderMetadata stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).metadata shapes (fits parent hparent)⟩

theorem CheckedHeaderSupportSources.normalizedBinderMetadata {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) (fits : NormalizedHeaderRangeFits types) :
    RecursorBinderMetadata stats types checkedRoot current infos :=
  (headers.normalizedBinderClosure sources htypes support hwf within closed).metadata support.closedShapes fits

theorem CheckedHeaderSupportSources.wrappedBinderMetadata {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) (fits : HeaderSourceBVarRangeFits types) :
    RecursorBinderMetadata stats types checkedRoot current infos :=
  (headers.wrappedBinderClosure_of_bvarRangeFits sources htypes support hwf fits).metadata
    support.closedShapes (headers.wrappedRangeFits htypes fits)

theorem mkRecInfos.scopedNormalizedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M ResultType)
    (original checkedRoot ctx : Context) (post : ResultType → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) (fits : NormalizedHeaderRangeFits types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderMetadata stats types checkedRoot current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderClosure nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support within closed
  intro infos current hframe hsources hcounts hclosure
  exact hnext infos current hframe hsources hcounts (hclosure.metadata support.closedShapes fits)

theorem mkRecInfos.getNormalizedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) (fits : NormalizedHeaderRangeFits types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderMetadata stats types checkedRoot result.2 result.1 :=
  (mkRecInfos.getNormalizedBinderClosure nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support within closed).mono fun _ receipt =>
      ⟨receipt.1, receipt.2.1, receipt.2.2.1, receipt.2.2.2.1,
        receipt.2.2.2.2.metadata support.closedShapes fits⟩

theorem mkRecInfos.registeredNormalizedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) (fits : NormalizedHeaderRangeFits types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderMetadata stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hclosure⟩ :=
    mkRecInfos.registeredNormalizedBinderClosure nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv support within closed result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    hclosure.metadata support.closedShapes fits⟩

theorem mkRecInfos.scopedWrappedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M ResultType)
    (original checkedRoot ctx : Context) (post : ResultType → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderMetadata stats types checkedRoot current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedNormalizedBinderMetadata nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes.normalizedHeaders hwf hreserved support (headers.wrappedFVarsIn htypes)
    (headers.wrappedClosed_of_bvarRangeFits htypes fits) (headers.wrappedRangeFits htypes fits) hnext

theorem mkRecInfos.getWrappedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderMetadata stats types checkedRoot result.2 result.1 :=
  mkRecInfos.getNormalizedBinderMetadata nparams stats types elimLevel original checkedRoot ctx
    headers htypes.normalizedHeaders hwf hreserved support (headers.wrappedFVarsIn htypes)
    (headers.wrappedClosed_of_bvarRangeFits htypes fits) (headers.wrappedRangeFits htypes fits)

theorem mkRecInfos.registeredWrappedBinderMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderMetadata stats types checkedRoot result.2.2 result.2.1 :=
  mkRecInfos.registeredNormalizedBinderMetadata nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes.normalizedHeaders hwf hreserved henv support
    (headers.wrappedFVarsIn htypes) (headers.wrappedClosed_of_bvarRangeFits htypes fits)
    (headers.wrappedRangeFits htypes fits)

theorem checkInductiveTypes.safeRegisteredBinderMetadata (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hwithin : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (hclosed : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderClosed types)
    (hfits : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderRangeFits types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderMetadata result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderMetadata stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderMetadata nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderMetadata stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved support (hwithin stats current headers)
      (hclosed stats current headers) (hfits stats current headers)
    intro infos source _ _ hcounts hmetadata
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers.toSources, hmetadata⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredNormalizedBinderMetadata
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnofvars : NormalizedHeaderFVarsIn types []) (closed : NormalizedHeaderClosed types)
    (fits : NormalizedHeaderRangeFits types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderMetadata result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderMetadata nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (fun _ hmem => by cases hmem))
    (fun _ _ _ => closed) (fun _ _ _ => fits)

theorem checkInductiveTypes.safeRegisteredWrappedBinderMetadata
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (fits : HeaderSourceBVarRangeFits types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderMetadata result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderMetadata nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsIn htypes)
    (fun _ _ headers => headers.wrappedClosed_of_bvarRangeFits htypes fits)
    (fun _ _ headers => headers.wrappedRangeFits htypes fits)

end Lean4Lean.AddInductive
