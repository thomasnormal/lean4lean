import Lean4Lean.Verify.InductiveBinderLookupCorrespondence
import Lean4Lean.Verify.InductiveNormalizedFreeVars
import Lean4Lean.Verify.InductiveBinderSupportAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

def NormalizedHeaderFVarsWithin (types : Array InductiveType) (ids : List FVarId) : Prop :=
  ∀ parent, parent < types.size → ∀ normalized,
    NormalizedSortTelescope types[parent]!.type normalized → IndexFVarsWithin ids normalized

def ParentBinderLookupAlignment (stats : InductiveStats) (types : Array InductiveType)
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
    IndexLookupRenaming pairs checkedTerminal generatedTerminal

def RecursorBinderLookupAlignment (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderLookupAlignment stats types parent checkedRoot current infos[parent]!

theorem ParentBinderLookupAlignment.toBinderSupport {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderLookupAlignment stats types parent checkedRoot current info) :
    ParentBinderSupportAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, _, _⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport⟩

theorem RecursorBinderLookupAlignment.toBinderSupport {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderLookupAlignment stats types checkedRoot current infos) :
    RecursorBinderSupportAlignment stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).toBinderSupport⟩

theorem BinderValuesBefore.fvarValues {ctx : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) :
    ∀ value ∈ values, ∃ id ∈ values.map Expr.fvarId!, value = .fvar id := by
  intro value hvalue
  obtain ⟨decl, _, hexpr, _⟩ := support value hvalue
  have hshape : value = .fvar decl.fvarId := hexpr.symm
  refine ⟨decl.fvarId, ?_, hshape⟩
  exact List.mem_map.mpr ⟨value, hvalue, by rw [hshape]; rfl⟩

theorem CheckedHeaderSupportSources.wrappedFVarsWithin {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) :
    NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!) := by
  intro parent hparent normalized hnormalized
  have hclosed := (headers.2 parent hparent).normalizedNoFVars_of_normalized_wrapped hnormalized
    (htypes parent hparent)
  have hempty := fvarsList_eq_nil.mpr hclosed
  exact IndexFVarsWithin.of_subset (by rw [hempty]; exact List.nil_subset _)

theorem ParentBinderSupportAlignment.toBinderLookup {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      IndexFVarsWithin (stats.params.toList.map Expr.fvarId!) normalized) :
    ParentBinderLookupAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport⟩ := alignment
  have hactualPairs : pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!) := by
    simpa only [hgeneratedIndices] using hpairs
  have hstepLength : checked.length = generated.length := by
    simpa only [List.length_map] using congrArg List.length hsignature
  have hleftLength := congrArg List.length hcheckedRoles
  have hrightLength := congrArg List.length hgeneratedRoles
  simp only [List.length_map, List.length_append, List.length_replicate] at hleftLength hrightLength
  have hcount : stats.nindices[parent]! = info.indices.size := by omega
  have hroles : checked.map BinderStep.role = generated.map BinderStep.role := by
    rw [hcheckedRoles, hgeneratedRoles, hcount]
  have hsupport : IndexParameterSupport (List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!)) (stats.params.toList.map Expr.fvarId!) := by
    intro id hparam hmem
    rw [(indexZipProjections _ _).1] at hmem
    exact hcheckedSupport (by simpa only [hcheckedParams] using hparam) (List.mem_of_mem_take hmem)
  obtain ⟨lookupPairs, hlookup, hlookupPairs, hterminal⟩ := hchecked.lookupIndexCorrespondence hgenerated
    hroles (hcheckedParams.trans hgeneratedParams.symm) hcheckedDeclared hgeneratedDeclared
    (hactualPairs ▸ hinjection) hsupport (by simpa only [hcheckedParams] using shapes)
    (within normalized hnormalized)
  have heq : lookupPairs = pairs := hlookupPairs.trans hactualPairs.symm
  rw [heq] at hlookup hterminal
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hsignature, hcheckedParams,
    hgeneratedParams, hcheckedIndices, hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared,
    hcheckedRoles, hgeneratedRoles, hprefix, hraw, hlocal, hcheckedAlloc, hgeneratedAlloc,
    hcorrespondence, hpairs, hinjection, hcheckedSupport, hgeneratedSupport, hlookup, hterminal⟩

theorem CheckedHeaderSupportSources.normalizedBinderLookup {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderLookupAlignment stats types checkedRoot current infos := by
  have aligned := headers.normalizedBinderSupport sources htypes support hwf
  exact ⟨aligned.1, fun parent hparent => (aligned.2 parent hparent).toBinderLookup
    support.fvarValues (within parent hparent)⟩

theorem CheckedHeaderSupportSources.wrappedBinderLookup {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) :
    RecursorBinderLookupAlignment stats types checkedRoot current infos :=
  headers.normalizedBinderLookup sources htypes.normalizedHeaders support hwf (headers.wrappedFVarsWithin htypes)

theorem mkRecInfos.scopedNormalizedBinderLookup (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!))
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderLookupAlignment stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderSupport nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support
  intro infos current hframe hsources hcounts _
  exact hnext infos current hframe hsources hcounts
    (headers.normalizedBinderLookup hsources htypes support hwf within)

theorem mkRecInfos.getNormalizedBinderLookup (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderLookupAlignment stats types checkedRoot result.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hcountsAligned, _⟩ :=
    mkRecInfos.getNormalizedBinderSupport nparams stats types elimLevel original checkedRoot ctx
      headers htypes hwf hreserved support result hresult
  exact ⟨hframe, hcounts, hsources, hcountsAligned, headers.normalizedBinderLookup hsources htypes support hwf within⟩

theorem mkRecInfos.registeredNormalizedBinderLookup (nparams : Nat) (stats : InductiveStats)
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
      RecursorBinderLookupAlignment stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, _⟩ :=
    mkRecInfos.registeredNormalizedBinderSupport nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv support result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    headers.normalizedBinderLookup hsources htypes support hwf within⟩

theorem checkInductiveTypes.safeRegisteredBinderLookup (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
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
          RecursorBinderLookupAlignment stats types checkedRoot result.2.2 result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scopedNormalizedBinderLookup nparams stats types elimLevel _ ctx current
      { current with env := constructorEnv }
      (fun (result : Kernel.Environment × Array RecInfo × Context) =>
        RecursorIndexCounts stats types result.2.1 ∧ ∃ checkedRoot,
          CheckedHeaderSources nparams types ctx stats checkedRoot ∧
          RecursorBinderLookupAlignment stats types checkedRoot result.2.2 result.2.1)
      headers htypes hframe.wf hframe.reserved support (hwithin stats current headers)
    intro infos source _ _ hcounts hlookup
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure ⟨hcounts, current, headers.toSources, hlookup⟩
  exact hreceipts.bind fun result hreceipt => .pure hreceipt

theorem checkInductiveTypes.safeRegisteredNormalizedBinderLookup (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderLookup nparams types numNested elimLevel lparams isK ctx
    htypes hwf hreserved (fun _ _ _ parent hparent normalized hnormalized =>
      (hnofvars parent hparent normalized hnormalized).mono (List.nil_subset _))

theorem checkInductiveTypes.safeRegisteredWrappedBinderLookup (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderLookupAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderLookup nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsWithin htypes)

end Lean4Lean.AddInductive
