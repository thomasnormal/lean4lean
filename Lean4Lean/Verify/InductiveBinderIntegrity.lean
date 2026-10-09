import Lean4Lean.Verify.InductiveBinderFVarsIn
import Lean4Lean.Verify.InductiveBinderStoredTypeAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def BinderStoredIndexDomainFVarsIn (params : List FVarId) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    step.localDomain.FVarsIn
      (fun id => id ∈ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!)

def BinderStoredIndexTypeFVarsIn (params : List FVarId) (ctx : Context)
    (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep) (decl : LocalDecl),
    steps[position]? = some step → step.role = .index →
    ctx.lctx.find? step.value.fvarId! = some decl →
    decl.type.FVarsIn
      (fun id => id ∈ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!)

theorem BinderRawDomainFVarsIn.storedIndexDomainFVarsIn {params : List FVarId}
    {steps : List BinderStep} (within : BinderRawDomainFVarsIn params steps) :
    BinderStoredIndexDomainFVarsIn params steps :=
  fun position step hstep _ => (within position step hstep).peelTypeAnnotations

theorem BinderRawDomainFVarsIn.storedIndexTypeFVarsIn {params : List FVarId}
    {steps : List BinderStep} {ctx : Context} (within : BinderRawDomainFVarsIn params steps)
    (declared : BinderStepsIndexDeclared ctx steps) : BinderStoredIndexTypeFVarsIn params ctx steps := by
  intro position step decl hstep hindex hlookup
  obtain ⟨nativeDecl, hnativeLookup, _, htype, _, _⟩ := declared step (List.mem_of_getElem? hstep) hindex
  have heq : nativeDecl = decl := Option.some.inj (hnativeLookup.symm.trans hlookup)
  subst nativeDecl
  rw [htype]
  exact (within position step hstep).peelTypeAnnotations

def ParentBinderIntegrity (stats : InductiveStats) (types : Array InductiveType)
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
    BinderStoredIndexTypeFVarsIn (stats.params.toList.map Expr.fvarId!) current generated

def RecursorBinderIntegrity (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderIntegrity stats types parent checkedRoot current infos[parent]!

theorem ParentBinderIntegrity.toBinderStoredLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderIntegrity stats types parent checkedRoot current info) :
    ParentBinderStoredLookupTypes stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, _, _, _, _, _, _⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion⟩

theorem RecursorBinderIntegrity.toBinderStoredLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderIntegrity stats types checkedRoot current infos) :
    RecursorBinderStoredLookupTypes stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).toBinderStoredLookupTypes⟩

theorem ParentBinderStoredLookupTypes.integrity {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderStoredLookupTypes stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      normalized.FVarsIn (fun id => id ∈ stats.params.toList.map Expr.fvarId!)) :
    ParentBinderIntegrity stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion⟩ := receipt
  have hcheckedIntegrity := hchecked.rawDomainFVarsIn (within normalized hnormalized)
    (hcheckedParams ▸ shapes) hcheckedDeclared
  have hgeneratedIntegrity := hgenerated.rawDomainFVarsIn (within normalized hnormalized)
    (hgeneratedParams ▸ shapes) hgeneratedDeclared
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstored, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion,
    hgeneratedStoredExclusion, hcheckedIntegrity, hgeneratedIntegrity,
    hcheckedIntegrity.storedIndexDomainFVarsIn, hgeneratedIntegrity.storedIndexDomainFVarsIn,
    hcheckedIntegrity.storedIndexTypeFVarsIn hcheckedDeclared,
    hgeneratedIntegrity.storedIndexTypeFVarsIn hgeneratedDeclared⟩

theorem RecursorBinderStoredLookupTypes.integrity {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderStoredLookupTypes stats types checkedRoot current infos)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).integrity shapes (within parent hparent)⟩

theorem CheckedHeaderSupportSources.normalizedBinderIntegrity {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  (headers.normalizedBinderStoredLookupTypes sources htypes support hwf within.fvarsWithin).integrity
    support.fvarValues within

theorem CheckedHeaderSupportSources.wrappedBinderIntegrity {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  headers.normalizedBinderIntegrity sources htypes.normalizedHeaders support hwf (headers.wrappedFVarsIn htypes)

theorem mkRecInfos.scopedNormalizedBinderIntegrity (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderIntegrity stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderStoredLookupTypes nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support within.fvarsWithin
  intro infos current hframe hsources hcounts hlookup
  exact hnext infos current hframe hsources hcounts (hlookup.integrity support.fvarValues within)

theorem mkRecInfos.getNormalizedBinderIntegrity (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧
      RecursorBinderIntegrity stats types checkedRoot result.2 result.1 :=
  (mkRecInfos.getNormalizedBinderStoredLookupTypes nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support within.fvarsWithin).mono fun _ receipt =>
      ⟨receipt.1, receipt.2.1, receipt.2.2.1, receipt.2.2.2.1,
        receipt.2.2.2.2.integrity support.fvarValues within⟩

theorem mkRecInfos.registeredNormalizedBinderIntegrity (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧
      RecursorBinderIntegrity stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hlookup⟩ :=
    mkRecInfos.registeredNormalizedBinderStoredLookupTypes nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv support within.fvarsWithin result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    hlookup.integrity support.fvarValues within⟩

theorem checkInductiveTypes.safeRegisteredBinderIntegrity (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hwithin : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderIntegrity result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderIntegrity stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderIntegrity nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderIntegrity stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved support (hwithin stats current headers)
    intro infos source _ _ hcounts hlookup
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers.toSources, hlookup⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredNormalizedBinderIntegrity
    (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnofvars : NormalizedHeaderFVarsIn types []) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderIntegrity result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderIntegrity nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (fun _ hmem => by cases hmem))

theorem checkInductiveTypes.safeRegisteredWrappedBinderIntegrity
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
        RecursorBinderIntegrity result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderIntegrity nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsIn htypes)

end Lean4Lean.AddInductive
