import Lean4Lean.Verify.InductiveBinderClosed
import Lean4Lean.Verify.InductiveBinderIntegrity

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def ParentBinderClosure (stats : InductiveStats) (types : Array InductiveType)
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
    checkedTerminal.Closed 0 ∧ generatedTerminal.Closed 0

def RecursorBinderClosure (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderClosure stats types parent checkedRoot current infos[parent]!

theorem ParentBinderClosure.toBinderIntegrity {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderClosure stats types parent checkedRoot current info) :
    ParentBinderIntegrity stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, _⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity⟩

theorem RecursorBinderClosure.toBinderIntegrity {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderClosure stats types checkedRoot current infos) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).toBinderIntegrity⟩

theorem ParentBinderClosure.toBinderStoredLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderClosure stats types parent checkedRoot current info) :
    ParentBinderStoredLookupTypes stats types parent checkedRoot current info :=
  receipt.toBinderIntegrity.toBinderStoredLookupTypes

theorem RecursorBinderClosure.toBinderStoredLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderClosure stats types checkedRoot current infos) :
    RecursorBinderStoredLookupTypes stats types checkedRoot current infos :=
  receipt.toBinderIntegrity.toBinderStoredLookupTypes

theorem ParentBinderIntegrity.closure {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderIntegrity stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id, value = .fvar id)
    (closed : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      normalized.Closed 0) : ParentBinderClosure stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity⟩ := receipt
  have hnormalizedClosed := closed normalized hnormalized
  have hcheckedValues := hcheckedDeclared.valuesClosed hcheckedParams shapes
  have hgeneratedValues := hgeneratedDeclared.valuesClosed hgeneratedParams shapes
  have hcheckedClosed := hchecked.rawDomainClosed hnormalizedClosed hcheckedValues
  have hgeneratedClosed := hgenerated.rawDomainClosed hnormalizedClosed hgeneratedValues
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity, hcheckedStoredIntegrity,
    hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedClosed.storedIndexDomainClosed,
    hgeneratedClosed.storedIndexDomainClosed, hcheckedClosed.storedIndexTypeClosed hcheckedDeclared,
    hgeneratedClosed.storedIndexTypeClosed hgeneratedDeclared,
    hchecked.terminalClosed hnormalizedClosed hcheckedValues,
    hgenerated.terminalClosed hnormalizedClosed hgeneratedValues⟩

theorem RecursorBinderIntegrity.closure {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderIntegrity stats types checkedRoot current infos)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id, value = .fvar id)
    (closed : NormalizedHeaderClosed types) : RecursorBinderClosure stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).closure shapes (closed parent hparent)⟩

theorem BinderValuesBefore.closedShapes {ctx : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) :
    ∀ value ∈ values, ∃ id, value = .fvar id := by
  intro value hvalue
  obtain ⟨id, _, hexpr⟩ := support.fvarValues value hvalue
  exact ⟨id, hexpr⟩

theorem CheckedHeaderSupportSources.normalizedBinderClosure {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) : RecursorBinderClosure stats types checkedRoot current infos :=
  (headers.normalizedBinderIntegrity sources htypes support hwf within).closure support.closedShapes closed

theorem CheckedHeaderSupportSources.wrappedBinderClosure {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) (closed : HeaderSourceClosed types) :
    RecursorBinderClosure stats types checkedRoot current infos :=
  headers.normalizedBinderClosure sources htypes.normalizedHeaders support hwf
    (headers.wrappedFVarsIn htypes) (headers.wrappedClosed htypes closed)

theorem mkRecInfos.scopedNormalizedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderClosure stats types checkedRoot current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderIntegrity nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support within
  intro infos current hframe hsources hcounts hintegrity
  exact hnext infos current hframe hsources hcounts (hintegrity.closure support.closedShapes closed)

theorem mkRecInfos.getNormalizedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderClosure stats types checkedRoot result.2 result.1 :=
  (mkRecInfos.getNormalizedBinderIntegrity nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support within).mono fun _ receipt =>
      ⟨receipt.1, receipt.2.1, receipt.2.2.1, receipt.2.2.2.1,
        receipt.2.2.2.2.closure support.closedShapes closed⟩

theorem mkRecInfos.registeredNormalizedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderClosure stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hintegrity⟩ :=
    mkRecInfos.registeredNormalizedBinderIntegrity nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv support within result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    hintegrity.closure support.closedShapes closed⟩

theorem mkRecInfos.scopedWrappedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (closed : HeaderSourceClosed types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderClosure stats types checkedRoot current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedNormalizedBinderClosure nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes.normalizedHeaders hwf hreserved support (headers.wrappedFVarsIn htypes)
    (headers.wrappedClosed htypes closed) hnext

theorem mkRecInfos.getWrappedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (closed : HeaderSourceClosed types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderClosure stats types checkedRoot result.2 result.1 :=
  mkRecInfos.getNormalizedBinderClosure nparams stats types elimLevel original checkedRoot ctx
    headers htypes.normalizedHeaders hwf hreserved support (headers.wrappedFVarsIn htypes)
    (headers.wrappedClosed htypes closed)

theorem mkRecInfos.registeredWrappedBinderClosure (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (closed : HeaderSourceClosed types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderClosure stats types checkedRoot result.2.2 result.2.1 :=
  mkRecInfos.registeredNormalizedBinderClosure nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes.normalizedHeaders hwf hreserved henv support
    (headers.wrappedFVarsIn htypes) (headers.wrappedClosed htypes closed)

theorem checkInductiveTypes.safeRegisteredBinderClosure (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hwithin : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (hclosed : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderClosed types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderClosure result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderClosure stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderClosure nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderClosure stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved support (hwithin stats current headers)
      (hclosed stats current headers)
    intro infos source _ _ hcounts hclosure
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers.toSources, hclosure⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredNormalizedBinderClosure
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnofvars : NormalizedHeaderFVarsIn types []) (closed : NormalizedHeaderClosed types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderClosure result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderClosure nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (fun _ hmem => by cases hmem))
    (fun _ _ _ => closed)

theorem checkInductiveTypes.safeRegisteredWrappedBinderClosure
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (closed : HeaderSourceClosed types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderClosure result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderClosure nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsIn htypes)
    (fun _ _ headers => headers.wrappedClosed htypes closed)

end Lean4Lean.AddInductive
