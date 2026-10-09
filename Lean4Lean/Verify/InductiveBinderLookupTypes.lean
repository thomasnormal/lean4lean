import Lean4Lean.Verify.InductiveConsumedLookupRenaming
import Lean4Lean.Verify.InductiveBinderLookupPositions
import Lean4Lean.Verify.InductiveBinderLookupAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def NativeIndexTypeAt (initialPairs : List (FVarId × FVarId)) (checkedCtx generatedCtx : Context)
    (checkedStart generatedStart : Nat) (checked generated : List BinderStep) (position : Nat) : Prop :=
  ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
    checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
    checkedStep.role = .index ∧ generatedStep.role = .index ∧
    checkedStep.signature = generatedStep.signature ∧
    priorPairs = initialPairs ++ List.zip
      ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
      ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
    checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
    generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
    checkedDecl.toExpr = checkedStep.value ∧ generatedDecl.toExpr = generatedStep.value ∧
    checkedDecl.type = checkedStep.localDomain ∧ generatedDecl.type = generatedStep.localDomain ∧
    checkedDecl.userName = checkedStep.name ∧ generatedDecl.userName = generatedStep.name ∧
    checkedDecl.binderInfo = checkedStep.bi ∧ generatedDecl.binderInfo = generatedStep.bi ∧
    checkedDecl.index = checkedStart + (BinderStep.indexValues (checked.take position)).length ∧
    generatedDecl.index = generatedStart + (BinderStep.indexValues (generated.take position)).length ∧
    IndexLookupRenaming priorPairs checkedStep.domain generatedStep.domain ∧
    ConsumedIndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type

def BinderLookupNativeTypes (initialPairs : List (FVarId × FVarId)) (checkedCtx generatedCtx : Context)
    (checkedStart generatedStart : Nat) (checked generated : List BinderStep) : Prop :=
  ∀ position checkedStep, checked[position]? = some checkedStep → checkedStep.role = .index →
    NativeIndexTypeAt initialPairs checkedCtx generatedCtx checkedStart generatedStart checked generated position

theorem BinderLookupCorrespondence.nativeIndexTypes {initialPairs finalPairs : List (FVarId × FVarId)}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart : Nat}
    {checked generated : List BinderStep}
    (correspondence : BinderLookupCorrespondence initialPairs checked generated finalPairs)
    (checkedAllocated : BinderIndexAllocations checkedCtx checkedStart checked)
    (generatedAllocated : BinderIndexAllocations generatedCtx generatedStart generated) :
    BinderLookupNativeTypes initialPairs checkedCtx generatedCtx checkedStart generatedStart checked generated := by
  intro position checkedStep hchecked hindex
  obtain ⟨generatedStep, priorPairs, hgenerated, hroles, hsignature, hprior, hdomains⟩ :=
    correspondence.atPosition_of_getElem? hchecked
  have hgeneratedIndex : generatedStep.role = .index := hroles.symm.trans hindex
  obtain ⟨checkedDecl, hcheckedLookup, hcheckedExpr, hcheckedType, hcheckedName, hcheckedBi, hcheckedPosition⟩ :=
    checkedAllocated.atPosition hchecked hindex
  obtain ⟨generatedDecl, hgeneratedLookup, hgeneratedExpr, hgeneratedType, hgeneratedName, hgeneratedBi,
    hgeneratedPosition⟩ := generatedAllocated.atPosition hgenerated hgeneratedIndex
  refine ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs,
    hchecked, hgenerated, hindex, hgeneratedIndex, hsignature, hprior, hcheckedLookup, hgeneratedLookup,
    hcheckedExpr, hgeneratedExpr, hcheckedType, hgeneratedType, hcheckedName, hgeneratedName,
    hcheckedBi, hgeneratedBi, hcheckedPosition, hgeneratedPosition, hdomains, ?_⟩
  rw [hcheckedType, hgeneratedType]
  exact ConsumedIndexLookupRenaming.ofRaw hdomains

def ParentBinderLookupTypes (stats : InductiveStats) (types : Array InductiveType)
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
    BinderLookupNativeTypes [] checkedRoot current checkedStart generatedStart checked generated

def RecursorBinderLookupTypes (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderLookupTypes stats types parent checkedRoot current infos[parent]!

theorem ParentBinderLookupTypes.toBinderLookup {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderLookupTypes stats types parent checkedRoot current info) :
    ParentBinderLookupAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal, _⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal⟩

theorem RecursorBinderLookupTypes.toBinderLookup {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderLookupTypes stats types checkedRoot current infos) :
    RecursorBinderLookupAlignment stats types checkedRoot current infos :=
  ⟨receipt.1, fun parent hparent => (receipt.2 parent hparent).toBinderLookup⟩

theorem ParentBinderLookupAlignment.nativeIndexTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderLookupAlignment stats types parent checkedRoot current info) :
    ParentBinderLookupTypes stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal,
    hlookup.nativeIndexTypes hcheckedAlloc hgeneratedAlloc⟩

theorem RecursorBinderLookupAlignment.nativeIndexTypes {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderLookupAlignment stats types checkedRoot current infos) :
    RecursorBinderLookupTypes stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).nativeIndexTypes⟩

theorem CheckedHeaderSupportSources.normalizedBinderLookupTypes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderLookupTypes stats types checkedRoot current infos :=
  (headers.normalizedBinderLookup sources htypes support hwf within).nativeIndexTypes

theorem CheckedHeaderSupportSources.wrappedBinderLookupTypes {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) :
    RecursorBinderLookupTypes stats types checkedRoot current infos :=
  (headers.wrappedBinderLookup sources htypes support hwf).nativeIndexTypes

theorem mkRecInfos.scopedNormalizedBinderLookupTypes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!))
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderLookupTypes stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderLookup nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support within
  intro infos current hframe hsources hcounts hlookup
  exact hnext infos current hframe hsources hcounts hlookup.nativeIndexTypes

theorem mkRecInfos.getNormalizedBinderLookupTypes (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderLookupTypes stats types checkedRoot result.2 result.1 :=
  (mkRecInfos.getNormalizedBinderLookup nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support within).mono fun _ receipt =>
      ⟨receipt.1, receipt.2.1, receipt.2.2.1, receipt.2.2.2.1, receipt.2.2.2.2.nativeIndexTypes⟩

theorem mkRecInfos.registeredNormalizedBinderLookupTypes (nparams : Nat) (stats : InductiveStats)
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
      RecursorBinderLookupTypes stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  have receipt := mkRecInfos.registeredNormalizedBinderLookup nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes hwf hreserved henv support within result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hlookup⟩ := receipt
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hlookup.nativeIndexTypes⟩

theorem checkInductiveTypes.safeRegisteredBinderLookupTypes (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
  intro result hresult
  have receipt := checkInductiveTypes.safeRegisteredBinderLookup nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved hwithin result hresult
  obtain ⟨hcounts, checkedRoot, headers, hlookup⟩ := receipt
  exact ⟨hcounts, checkedRoot, headers, hlookup.nativeIndexTypes⟩

theorem checkInductiveTypes.safeRegisteredNormalizedBinderLookupTypes (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderLookupTypes nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (List.nil_subset _))

theorem checkInductiveTypes.safeRegisteredWrappedBinderLookupTypes (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderLookupTypes nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsWithin htypes)

end Lean4Lean.AddInductive
