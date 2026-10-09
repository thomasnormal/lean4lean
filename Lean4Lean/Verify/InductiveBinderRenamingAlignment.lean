import Lean4Lean.Verify.InductiveBinderCorrespondence
import Lean4Lean.Verify.InductiveBinderPrefixAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def ParentBinderRenamingAlignment (stats : InductiveStats) (types : Array InductiveType)
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
      ((generated.drop stats.params.size).head?).map BinderStep.localDomain ∧
    ∃ pairs, BinderIndexCorrespondence [] checked generated pairs ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
        (info.indices.toList.map Expr.fvarId!)

def RecursorBinderRenamingAlignment (stats : InductiveStats) (types : Array InductiveType)
    (checkedRoot current : Context) (infos : Array RecInfo) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    ParentBinderRenamingAlignment stats types parent checkedRoot current infos[parent]!

theorem BinderDeclaredAt.renamingTypes {pairs : List (FVarId × FVarId)}
    {checkedRoot current : Context} {checkedValue generatedValue checkedDomain generatedDomain : Expr}
    {name : Name} {bi : BinderInfo}
    (checkedDeclared : BinderDeclaredAt checkedRoot checkedValue name checkedDomain.consumeTypeAnnotations bi)
    (generatedDeclared : BinderDeclaredAt current generatedValue name generatedDomain.consumeTypeAnnotations bi)
    (hdomains : IndexRenaming pairs checkedDomain generatedDomain) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedValue.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedValue.fvarId! = some generatedDecl ∧
      ConsumedIndexRenaming pairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedDecl, hcheckedLookup, _, hcheckedType, _, _⟩ := checkedDeclared
  obtain ⟨generatedDecl, hgeneratedLookup, _, hgeneratedType, _, _⟩ := generatedDeclared
  refine ⟨checkedDecl, generatedDecl, hcheckedLookup, hgeneratedLookup, ?_⟩
  rw [hcheckedType, hgeneratedType]
  exact ConsumedIndexRenaming.ofRaw hdomains

theorem BinderIndexCorrespondence.indexHeadTypes
    {pairs finalPairs : List (FVarId × FVarId)} {checkedFirst generatedFirst : BinderStep}
    {checkedTail generatedTail : List BinderStep} {checkedRoot current : Context}
    (correspondence : BinderIndexCorrespondence pairs
      (checkedFirst :: checkedTail) (generatedFirst :: generatedTail) finalPairs)
    (hindex : checkedFirst.role = .index)
    (checkedDeclared : BinderStepsIndexDeclared checkedRoot (checkedFirst :: checkedTail))
    (generatedDeclared : BinderStepsIndexDeclared current (generatedFirst :: generatedTail)) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      ConsumedIndexRenaming pairs checkedDecl.type generatedDecl.type := by
  cases correspondence with
  | parameter name bi checkedDomain generatedDomain value rawDomain localDomain tail =>
    cases hindex
  | index name bi checkedDomain generatedDomain checkedId generatedId rawDomain localDomain tail =>
    exact (checkedDeclared _ (by simp) rfl).renamingTypes
      (generatedDeclared _ (by simp) rfl) rawDomain

theorem ParentBinderRenamingAlignment.toBinderPrefixes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderRenamingAlignment stats types parent checkedRoot current info) :
    ParentBinderPrefixAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles,
    hprefix, hraw, hlocal, _⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles,
    hprefix, hraw, hlocal⟩

theorem ParentBinderPrefixAlignment.toBinderRenaming {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderPrefixAlignment stats types parent checkedRoot current info) :
    ParentBinderRenamingAlignment stats types parent checkedRoot current info := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles,
    hprefix, hraw, hlocal⟩ := alignment
  have hlength : checked.length = generated.length := by
    simpa only [List.length_map] using congrArg List.length hsignature
  have hcheckedLength := congrArg List.length hcheckedRoles
  have hgeneratedLength := congrArg List.length hgeneratedRoles
  simp only [List.length_map, List.length_append, List.length_replicate] at hcheckedLength hgeneratedLength
  have hcount : stats.nindices[parent]! = info.indices.size := by omega
  have hroles : checked.map BinderStep.role = generated.map BinderStep.role := by
    rw [hcheckedRoles, hgeneratedRoles, hcount]
  obtain ⟨pairs, hcorrespondence⟩ := hchecked.indexCorrespondence hgenerated hroles
    (hcheckedParams.trans hgeneratedParams.symm) hcheckedDeclared hgeneratedDeclared
  have hpairs : pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      (info.indices.toList.map Expr.fvarId!) := by
    simpa only [List.nil_append, hgeneratedIndices] using hcorrespondence.finalPairs
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, hnormalized,
    hchecked, hgenerated, hsignature, hcheckedParams, hgeneratedParams, hcheckedIndices,
    hgeneratedIndices, hcheckedDeclared, hgeneratedDeclared, hcheckedRoles, hgeneratedRoles,
    hprefix, hraw, hlocal, pairs, hcorrespondence, hpairs⟩

theorem RecursorBinderRenamingAlignment.toBinderPrefixes {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderRenamingAlignment stats types checkedRoot current infos) :
    RecursorBinderPrefixAlignment stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).toBinderPrefixes⟩

theorem RecursorBinderPrefixAlignment.toBinderRenaming {stats : InductiveStats}
    {types : Array InductiveType} {checkedRoot current : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderPrefixAlignment stats types checkedRoot current infos) :
    RecursorBinderRenamingAlignment stats types checkedRoot current infos :=
  ⟨alignment.1, fun parent hparent => (alignment.2 parent hparent).toBinderRenaming⟩

theorem CheckedHeaderSources.normalizedBinderRenaming {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) :
    RecursorBinderRenamingAlignment stats types checkedRoot current infos :=
  (headers.normalizedBinderPrefixes sources htypes).toBinderRenaming

theorem CheckedHeaderSources.wrappedBinderRenaming {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types) :
    RecursorBinderRenamingAlignment stats types checkedRoot current infos :=
  (headers.wrappedBinderPrefixes sources htypes).toBinderRenaming

theorem mkRecInfos.scopedNormalizedBinderRenaming (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M α)
    (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderRenamingAlignment stats types checkedRoot current infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  apply mkRecInfos.scopedNormalizedBinderPrefixes nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved
  intro infos current hframe hsources hcounts hprefix
  exact hnext infos current hframe hsources hcounts hprefix.toBinderRenaming

theorem mkRecInfos.getNormalizedBinderRenaming (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderRenamingAlignment stats types checkedRoot result.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hcountsAligned, hprefix⟩ :=
    mkRecInfos.getNormalizedBinderPrefixes nparams stats types elimLevel original checkedRoot ctx
      headers htypes hwf hreserved result hresult
  exact ⟨hframe, hcounts, hsources, hcountsAligned, hprefix.toBinderRenaming⟩

theorem mkRecInfos.registeredNormalizedBinderRenaming (nparams : Nat) (stats : InductiveStats)
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
      RecursorBinderRenamingAlignment stats types checkedRoot result.2.2 result.2.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned, hprefix⟩ :=
    mkRecInfos.registeredNormalizedBinderPrefixes nparams stats types elimLevel lparams isK isUnsafe
      original checkedRoot ctx headers htypes hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hsources, hmap, hkeep, hmetadata, hrhs, hcountsAligned,
    hprefix.toBinderRenaming⟩

theorem checkInductiveTypes.safeRegisteredNormalizedBinderRenaming (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderRenamingAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 := by
  intro result hresult
  obtain ⟨hcounts, checkedRoot, hsources, hprefix⟩ :=
    checkInductiveTypes.safeRegisteredNormalizedBinderPrefixes nparams types numNested elimLevel lparams
      isK ctx htypes hwf hreserved result hresult
  exact ⟨hcounts, checkedRoot, hsources, hprefix.toBinderRenaming⟩

theorem checkInductiveTypes.safeRegisteredWrappedBinderRenaming (nparams : Nat) (types : Array InductiveType)
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
        RecursorBinderRenamingAlignment result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderRenaming nparams types numNested elimLevel lparams
    isK ctx htypes.normalizedHeaders hwf hreserved

end Lean4Lean.AddInductive
