import Lean4Lean.Verify.InductiveBinderIntegrity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderIntegrityTest

private def sortType : Expr := .sort (.succ .zero)

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr := .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`BinderIntegrityTag, .ofNat 37)] }

private theorem fvarOnlySupportAdmitsExprMeta (metavar : MVarId) :
    IndexFVarsWithin [] (.mvar metavar) ∧ ¬ (Expr.mvar metavar).FVarsIn (fun _ => False) := by
  simp [IndexFVarsWithin, FVarsIn]

private theorem fvarOnlySupportAdmitsSortLevelMeta (metavar : LMVarId) :
    IndexFVarsWithin [] (.sort (.mvar metavar)) ∧
      ¬ (Expr.sort (.mvar metavar)).FVarsIn (fun _ => False) := by
  simp [IndexFVarsWithin, FVarsIn, Level.hasMVar']

private theorem fvarOnlySupportAdmitsConstLevelMeta (metavar : LMVarId) :
    IndexFVarsWithin [] (.const ``Nat [.mvar metavar]) ∧
      ¬ (Expr.const ``Nat [.mvar metavar]).FVarsIn (fun _ => False) := by
  simp [IndexFVarsWithin, FVarsIn, Level.hasMVar']

private theorem syntaxIntegrityAdmitsLooseUntypedTerms :
    (Expr.app (.const `BinderIntegrityUnknown [.param `u]) (.bvar 7)).FVarsIn (fun _ => False) ∧
      ¬ (Expr.app (.const `BinderIntegrityUnknown [.param `u]) (.bvar 7)).Closed := by
  simp [FVarsIn, Closed, Level.hasMVar']

private theorem discardedOptExprMetaDoesNotReflectIntegrity (metavar : MVarId) :
    (peelTypeAnnotations (binary ``optParam [.succ .zero] (.const ``Nat []) (.mvar metavar))).FVarsIn
      (fun _ => False) ∧
      ¬ (binary ``optParam [.succ .zero] (.const ``Nat []) (.mvar metavar)).FVarsIn (fun _ => False) := by
  simp [peelTypeAnnotations, binary, FVarsIn, Level.hasMVar']

private theorem discardedAutoLevelMetaDoesNotReflectIntegrity (metavar : LMVarId) :
    (peelTypeAnnotations
      (binary ``autoParam [.succ .zero] (.const ``Nat []) (.sort (.mvar metavar)))).FVarsIn (fun _ => False) ∧
      ¬ (binary ``autoParam [.succ .zero] (.const ``Nat []) (.sort (.mvar metavar))).FVarsIn
        (fun _ => False) := by
  simp [peelTypeAnnotations, binary, FVarsIn, Level.hasMVar']

private theorem discardedGadgetUniverseMetaDoesNotReflectIntegrity (metavar : LMVarId) :
    (peelTypeAnnotations (unary ``outParam [.mvar metavar] (.const ``Nat []))).FVarsIn (fun _ => False) ∧
      ¬ (unary ``outParam [.mvar metavar] (.const ``Nat [])).FVarsIn (fun _ => False) := by
  simp [peelTypeAnnotations, unary, FVarsIn, Level.hasMVar']

private theorem metadataBarrierRetainsMeta (metavar : MVarId) :
    ¬ (peelTypeAnnotations (.mdata tagged (unary ``outParam [] (.mvar metavar)))).FVarsIn
      (fun _ => False) := by
  simp [peelTypeAnnotations, unary, FVarsIn]

private theorem wrongArityRetainsMeta (metavar : MVarId) :
    ¬ (peelTypeAnnotations (binary ``outParam [] (.const ``Nat []) (.mvar metavar))).FVarsIn
      (fun _ => False) := by
  simp [peelTypeAnnotations, binary, FVarsIn]

private theorem telescopeShapeAndSupportDoNotEstablishIntegrity (metavar : MVarId) :
    SortTelescope (.forallE `index (.mvar metavar) sortType .default) ∧
      IndexFVarsWithin [] (.forallE `index (.mvar metavar) sortType .default) ∧
      ¬ (Expr.forallE `index (.mvar metavar) sortType .default).FVarsIn (fun _ => False) := by
  refine ⟨.forallE `index (.mvar metavar) .default (.sort (.succ .zero)), ?_⟩
  simp [IndexFVarsWithin, FVarsIn, sortType]

private theorem normalizedWhnfDoesNotEstablishIntegrity (metavar : MVarId) :
    NormalizedSortTelescope (.forallE `index (.mvar metavar) sortType .default)
      (.forallE `index (.mvar metavar) sortType .default) ∧
      ¬ (Expr.forallE `index (.mvar metavar) sortType .default).FVarsIn (fun _ => False) := by
  refine ⟨?_, by simp [FVarsIn]⟩
  exact (WrappedSortTelescope.telescope
    (.forallE `index (.mvar metavar) .default (.sort (.succ .zero)))).normalized

private def discardedLet (metavar : MVarId) : Expr :=
  .letE `unused (.const ``Nat []) (.mvar metavar) sortType true

private theorem normalizationDoesNotReflectIntegrity (metavar : MVarId) :
    WrappedSortTelescope (discardedLet metavar) sortType ∧
      sortType.FVarsIn (fun _ => False) ∧ ¬ (discardedLet metavar).FVarsIn (fun _ => False) := by
  refine ⟨?_, ?_⟩
  · unfold discardedLet
    apply WrappedSortTelescope.letE
    rw [Expr.instantiate1_eq]
    exact .telescope (.sort (.succ .zero))
  · simp [discardedLet, sortType, FVarsIn, Level.hasMVar']

private theorem modelPreservesIntegrity {predicate : FVarId → Prop} {value : Expr}
    (integrity : value.FVarsIn predicate) : (peelTypeAnnotations value).FVarsIn predicate :=
  integrity.peelTypeAnnotations

private theorem integrityImpliesFVarOnlySupport {ids : List FVarId} {value : Expr}
    (integrity : value.FVarsIn (· ∈ ids)) : IndexFVarsWithin ids value :=
  integrity.indexFVarsWithin

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def dependent : Expr :=
  .forallE `carrier sortType
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0))
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1)))
          sortType .strictImplicit) .instImplicit) .default) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0)) .default
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))) .instImplicit
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1))) .strictImplicit
          (.sort (.succ .zero)))))

private def wrappedLet (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private theorem wrappedLetTrace (data : MData) : WrappedSortTelescope (wrappedLet data) dependent := by
  unfold wrappedLet
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def wrappedBeta (data : MData) : Expr :=
  .mdata data (.app (.lam `unused (.const ``Nat []) dependent .implicit) (.lit (.natVal 0)))

private theorem wrappedBetaTrace (data : MData) : WrappedSortTelescope (wrappedBeta data) dependent := by
  unfold wrappedBeta
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `BinderIntegrityLet (wrappedLet data), header `BinderIntegrityBeta (wrappedBeta data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem openedTelescopeRetainsChronologicalIntegrity
    {params : List FVarId} {type terminal : Expr} {steps : List BinderStep} {ctx : Context}
    (opened : OpenedTelescope type steps terminal) (within : type.FVarsIn (· ∈ params))
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id ∈ params, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) : BinderRawDomainFVarsIn params steps :=
  opened.rawDomainFVarsIn within shapes declared

private theorem chronologicalIntegrityRetainsPriorFVarScope {params : List FVarId} {steps : List BinderStep}
    (integrity : BinderRawDomainFVarsIn params steps) : BinderRawDomainScope params steps :=
  integrity.rawDomainScope

private theorem normalizedIntegrityRetainsPriorFVarSupport {types : Array InductiveType} {params : List FVarId}
    (integrity : NormalizedHeaderFVarsIn types params) : NormalizedHeaderFVarsWithin types params :=
  integrity.fvarsWithin

private theorem checkedSourceGuardSuppliesIntegrity {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    types[parent]!.type.FVarsIn (fun _ => False) := source.sourceFVarsIn

private theorem wrappedSourceGuardSuppliesNormalizedIntegrity
    {nparams : Nat} {types : Array InductiveType} {stats : InductiveStats} {original checkedRoot : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (wrapped : WrappedHeaderTelescope types) :
    NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!) := headers.wrappedFVarsIn wrapped

private theorem rawDomainsHaveNoExprOrUniverseMetas {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} (integrity : BinderRawDomainFVarsIn params steps)
    (selected : steps[position]? = some step) : step.domain.hasMVar = false :=
  fvarsIn_iff_hasMVar.mp ((integrity position step selected).mono (fun _ _ => True.intro))

private theorem parentRetainsStoredContracts {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderIntegrity stats types parent checked current info) :
    ParentBinderStoredLookupTypes stats types parent checked current info := receipt.toBinderStoredLookupTypes

private theorem recursorsRetainStoredContracts {stats : InductiveStats} {types : Array InductiveType}
    {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderIntegrity stats types checked current infos) :
    RecursorBinderStoredLookupTypes stats types checked current infos := receipt.toBinderStoredLookupTypes

private theorem parentUpgradeRequiresNormalizedIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderStoredLookupTypes stats types parent checked current info)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      normalized.FVarsIn (· ∈ stats.params.toList.map Expr.fvarId!)) :
    ParentBinderIntegrity stats types parent checked current info := receipt.integrity shapes within

private theorem recursorsUpgradeRequiresNormalizedIntegrity {stats : InductiveStats}
    {types : Array InductiveType} {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderStoredLookupTypes stats types checked current infos)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderIntegrity stats types checked current infos := receipt.integrity shapes within

private theorem sameWitnessRawStoredNativeIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderIntegrity stats types parent checkedRoot current info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧ OpenedTelescope normalized generated generatedTerminal ∧
      BinderStepsIndexDeclared checkedRoot checked ∧ BinderStepsIndexDeclared current generated ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧ BinderIndexAllocations current generatedStart generated ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!) (info.indices.toList.map Expr.fvarId!) ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      BinderLookupStoredTypeScopes [] (stats.params.toList.map Expr.fvarId!)
        checkedRoot current checkedStart generatedStart checked generated ∧
      BinderRawDomainFVarsIn (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderRawDomainFVarsIn (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderStoredIndexDomainFVarsIn (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderStoredIndexDomainFVarsIn (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderStoredIndexTypeFVarsIn (stats.params.toList.map Expr.fvarId!) checkedRoot checked ∧
      BinderStoredIndexTypeFVarsIn (stats.params.toList.map Expr.fvarId!) current generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, _, _, _, _, hcheckedDeclared,
    hgeneratedDeclared, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, hpairs, _, _, _, hlookup,
    _, _, _, _, _, _, hstoredTypes, _, _, _, _, hcheckedRawIntegrity, hgeneratedRawIntegrity,
    hcheckedStoredIntegrity, hgeneratedStoredIntegrity, hcheckedTypeIntegrity, hgeneratedTypeIntegrity⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedDeclared, hgeneratedDeclared,
    hcheckedAlloc, hgeneratedAlloc, hpairs, hlookup, hstoredTypes, hcheckedRawIntegrity,
    hgeneratedRawIntegrity, hcheckedStoredIntegrity, hgeneratedStoredIntegrity,
    hcheckedTypeIntegrity, hgeneratedTypeIntegrity⟩

private theorem actualIndexLookupTypeIntegrityIsUsable {params : List FVarId} {ctx : Context}
    {steps : List BinderStep} {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (integrity : BinderStoredIndexTypeFVarsIn params ctx steps)
    (selected : steps[position]? = some step) (index : step.role = .index)
    (lookup : ctx.lctx.find? step.value.fvarId! = some decl) :
    decl.type.FVarsIn (· ∈ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!) :=
  integrity position step decl selected index lookup

private theorem actualIndexLookupTypesHaveNoMetas {params : List FVarId} {ctx : Context}
    {steps : List BinderStep} {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (integrity : BinderStoredIndexTypeFVarsIn params ctx steps)
    (selected : steps[position]? = some step) (index : step.role = .index)
    (lookup : ctx.lctx.find? step.value.fvarId! = some decl) : decl.type.hasMVar = false :=
  fvarsIn_iff_hasMVar.mp ((integrity position step decl selected index lookup).mono (fun _ _ => True.intro))

private theorem rawIntegritySuppliesActualStoredIntegrity {params : List FVarId} {ctx : Context}
    {steps : List BinderStep} (integrity : BinderRawDomainFVarsIn params steps)
    (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexDomainFVarsIn params steps ∧ BinderStoredIndexTypeFVarsIn params ctx steps :=
  ⟨integrity.storedIndexDomainFVarsIn, integrity.storedIndexTypeFVarsIn declared⟩

private theorem normalizedSourcesCarryIntegrity {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (normalized : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderIntegrity stats types checkedRoot current infos :=
  headers.normalizedBinderIntegrity sources normalized support hwf within

private theorem wrappedSourcesCarryDerivedIntegrity {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (wrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) : RecursorBinderIntegrity stats types checkedRoot current infos :=
  headers.wrappedBinderIntegrity sources wrapped support hwf

private theorem cpsCarriesSyntaxIntegrity {α : Type}
    (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (continuation : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → RecursorIndexCounts stats types infos →
      RecursorBinderIntegrity stats types checkedRoot current infos → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedNormalizedBinderIntegrity nparams stats types elimLevel next original checkedRoot ctx post
    headers normalized hwf reserved support within continuation

private theorem getterCarriesSyntaxIntegrity (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧ RecursorIndexCounts stats types result.1 ∧
      RecursorBinderIntegrity stats types checkedRoot result.2 result.1 :=
  mkRecInfos.getNormalizedBinderIntegrity nparams stats types elimLevel original checkedRoot ctx
    headers normalized hwf reserved support within

private theorem registrationPreservesFlagsAndSyntaxIntegrity (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧ result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderIntegrity stats types checkedRoot result.2.2 result.2.1 :=
  mkRecInfos.registeredNormalizedBinderIntegrity nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers normalized hwf reserved henv support within

private theorem safeRegistrationCarriesDerivedSyntaxIntegrity (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (within : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!)) :
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
    normalized hwf reserved within

private theorem safeNormalizedRegistrationKeepsExplicitIntegrity (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (closed : NormalizedHeaderFVarsIn types []) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderIntegrity result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderIntegrity nparams types numNested elimLevel lparams isK ctx
    normalized hwf reserved closed

private theorem provedSafeWrappedRegistrationHasIntegrity (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderIntegrity result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderIntegrity 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf reserved

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let generatorRoot ← readThe Context
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          generatorRoot.lparams false false
        return (stats, checked, generatorRoot, result)

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some declaration := ctx.lctx.getAt? (start + offset)
      | throwError "binder-integrity actual source index points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkDomainIntegrity (allowed : List FVarId) (domain : Expr) : MetaM Unit := do
  unless !domain.hasMVar && domain.fvarsList.all allowed.contains do
    throwError "binder-integrity raw/peeled/native stored domain has an expr/universe metavariable or unsupported FVar"

private def checkDeclaration (ctx : Context) (value : Expr) (name : Name) (domain : Expr)
    (bi : BinderInfo) (position : Nat) : MetaM Expr := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "binder-integrity actual index declaration missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations domain &&
      declaration.userName == name && declaration.binderInfo == bi && declaration.index == position do
    throwError "binder-integrity actual index lookup/value/name/type/binder-info/native-position anchor changed"
  return declaration.type

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut pairs : List (FVarId × FVarId) := []
  let mut leftPast : List Expr := []
  let mut rightPast : List Expr := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftRaw leftBody leftBi := left
      | throwError "binder-integrity actual checked opening ended before its values"
    let .forallE rightName rightRaw rightBody rightBi := right
      | throwError "binder-integrity actual generated opening ended before its values"
    let leftAllowed := params.toList.map Expr.fvarId! ++ leftPast.map Expr.fvarId!
    let rightAllowed := params.toList.map Expr.fvarId! ++ rightPast.map Expr.fvarId!
    checkDomainIntegrity leftAllowed leftRaw
    checkDomainIntegrity rightAllowed rightRaw
    checkDomainIntegrity leftAllowed (peelTypeAnnotations leftRaw)
    checkDomainIntegrity rightAllowed (peelTypeAnnotations rightRaw)
    unless pairs == List.zip (leftPast.map Expr.fvarId!) (rightPast.map Expr.fvarId!) &&
        leftName == rightName && leftBi == rightBi && indexRenameExpr pairs leftRaw == rightRaw do
      throwError "binder-integrity same-history strictly-prior deterministic raw-domain correspondence changed"
    if position ≥ nparams then
      let leftStored ← checkDeclaration checkedCtx leftValues[position]! leftName leftRaw leftBi
        (checkedStart + position - nparams)
      let rightStored ← checkDeclaration generatedCtx rightValues[position]! rightName rightRaw rightBi
        (generatedStart + position - nparams)
      checkDomainIntegrity leftAllowed leftStored
      checkDomainIntegrity rightAllowed rightStored
      unless indexRenameExpr pairs leftStored == rightStored do
        throwError "binder-integrity actual deterministic stored-domain correspondence changed"
      pairs := pairs ++ [(leftValues[position]!.fvarId!, rightValues[position]!.fvarId!)]
      leftPast := leftPast ++ [leftValues[position]!]
      rightPast := rightPast ++ [rightValues[position]!]
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  unless left == sortType && right == sortType &&
      pairs == List.zip (checked.toList.map Expr.fvarId!) (generated.toList.map Expr.fvarId!) do
    throwError "binder-integrity same-history terminal/full actual index-ID zip anchor changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "binder-integrity actual safe/header/recursor registration failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-integrity actual count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "binder-integrity actual checked source normalization failed"
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-integrity actual registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-integrity actual registered recursor metadata changed"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderIntegrityEmpty sortType] #[0]
  for nparams in [0, 1, 2, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderIntegrityDependent nparams) dependent] #[4 - nparams]
  for nparams in [0, 1, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderIntegrityMutualFirst nparams) dependent,
      header (Name.mkNum `BinderIntegrityMutualSecond nparams) dependent] #[4 - nparams, 4 - nparams]
  checkFixture ctx 1 (provedTypes tagged) #[3, 3]
  let nat := Expr.const ``Nat []
  let annotationTypes := #[
    header `BinderIntegrityOut (.forallE `index (unary ``outParam [.succ .zero] nat) sortType .default),
    header `BinderIntegrityAuto (.forallE `index
      (binary ``autoParam [.succ .zero] nat (.const ``Lean.Syntax.missing [])) sortType .default),
    header `BinderIntegrityMetaData (.forallE `index (.mdata tagged (unary ``outParam [.succ .zero] nat)) sortType .default)]
  checkFixture ctx 0 annotationTypes #[1, 1, 1]

private def rejectedMetaSources (ctx : Context) : MetaM Unit := do
  let expressionMeta := Expr.mvar ⟨`BinderIntegrityRejectedExprMeta⟩
  let levelMeta := Level.mvar ⟨`BinderIntegrityRejectedLevelMeta⟩
  let domains := #[expressionMeta, Expr.sort levelMeta, Expr.const ``Nat [levelMeta],
    binary ``optParam [.succ .zero] (.const ``Nat []) expressionMeta,
    unary ``outParam [levelMeta] (.const ``Nat [])]
  for position in [:domains.size] do
    let name := Name.mkNum `BinderIntegrityRejected position
    let type := Expr.forallE `index domains[position]! sortType .default
    match checkInductiveTypes 0 #[header name type] (fun _ => pure ()) ctx with
    | .error (.declHasMVars _ actual original) =>
      unless actual == name && original == type do
        throwError "binder-integrity source guard rejected the wrong source declaration"
    | _ => throwError "binder-integrity checked header unexpectedly accepted or differently rejected a meta source"
  logInfo "five checked source guards reject expr/sort-level/const-level/default-expression/gadget-universe metas before annotation peeling can discard them"

private def uncheckedHelperBoundary (ctx : Context) : MetaM Unit := do
  let expressionMeta := Expr.mvar ⟨`BinderIntegrityUncheckedMeta⟩
  let type := Expr.forallE `index expressionMeta sortType .default
  let stats : InductiveStats := { lctx := ctx.lctx, levels := [], resultLevel := .succ .zero, indConsts := #[], params := #[], nindices := #[], isNotZero := true }
  let .ok (values, current) := mkRecInfos.loopArgs1 stats type 0 #[] ctx.fuel.inductiveFuel
      (fun values => do return (values, ← readThe Context)) ctx
    | throwError "binder-integrity unchecked helper control unexpectedly rejected its raw expression-meta domain"
  let some declaration := current.lctx.find? values[0]!.fvarId!
    | throwError "binder-integrity unchecked helper control did not allocate an index"
  unless declaration.type == expressionMeta && declaration.type.hasMVar do
    throwError "binder-integrity unchecked helper falsely acquired safe-source syntax integrity"
  let discardedRaw := binary ``optParam [.succ .zero] (.const ``Nat []) expressionMeta
  let discardedType := Expr.forallE `discarded discardedRaw sortType .default
  let .ok (discardedValues, discardedCtx) := mkRecInfos.loopArgs1 stats discardedType 0 #[] ctx.fuel.inductiveFuel
      (fun values => do return (values, ← readThe Context)) ctx
    | throwError "binder-integrity unchecked discarded-meta helper failed"
  let some discardedDeclaration := discardedCtx.lctx.find? discardedValues[0]!.fvarId!
    | throwError "binder-integrity unchecked discarded-meta helper did not allocate an index"
  unless discardedRaw.hasMVar && !discardedDeclaration.type.hasMVar &&
      discardedDeclaration.type == (.const ``Nat [] : Expr) do
    throwError "binder-integrity unchecked clean stored output incorrectly reflected raw integrity"
  logInfo "two unchecked index helpers distinguish stored meta persistence from discarded-default meta elimination: actual source/normalization integrity premises cannot be dropped or reflected from clean stored output"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let expressions := [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let normalized := binding ++ expressions ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  audit ``fvarOnlySupportAdmitsExprMeta
  audit ``fvarOnlySupportAdmitsSortLevelMeta
  audit ``fvarOnlySupportAdmitsConstLevelMeta
  audit ``syntaxIntegrityAdmitsLooseUntypedTerms
  audit ``discardedOptExprMetaDoesNotReflectIntegrity
  audit ``discardedAutoLevelMetaDoesNotReflectIntegrity
  audit ``discardedGadgetUniverseMetaDoesNotReflectIntegrity
  audit ``metadataBarrierRetainsMeta
  audit ``wrongArityRetainsMeta
  audit ``telescopeShapeAndSupportDoNotEstablishIntegrity
  audit ``normalizedWhnfDoesNotEstablishIntegrity normalized
  audit ``normalizationDoesNotReflectIntegrity binding
  audit ``modelPreservesIntegrity
  audit ``integrityImpliesFVarOnlySupport
  audit ``dependentShape
  audit ``wrappedLetTrace binding
  audit ``wrappedBetaTrace binding
  audit ``provedHeaders binding
  audit ``openedTelescopeRetainsChronologicalIntegrity binding
  audit ``chronologicalIntegrityRetainsPriorFVarScope
  audit ``normalizedIntegrityRetainsPriorFVarSupport
  audit ``checkedSourceGuardSuppliesIntegrity expressions
  audit ``wrappedSourceGuardSuppliesNormalizedIntegrity normalized
  audit ``rawDomainsHaveNoExprOrUniverseMetas expressions
  audit ``parentRetainsStoredContracts
  audit ``recursorsRetainStoredContracts
  audit ``parentUpgradeRequiresNormalizedIntegrity binding
  audit ``recursorsUpgradeRequiresNormalizedIntegrity binding
  audit ``sameWitnessRawStoredNativeIntegrity
  audit ``actualIndexLookupTypeIntegrityIsUsable
  audit ``actualIndexLookupTypesHaveNoMetas expressions
  audit ``rawIntegritySuppliesActualStoredIntegrity
  audit ``normalizedSourcesCarryIntegrity (binding ++ scope)
  audit ``wrappedSourcesCarryDerivedIntegrity (normalized ++ scope)
  audit ``cpsCarriesSyntaxIntegrity (binding ++ scope)
  audit ``getterCarriesSyntaxIntegrity (binding ++ scope)
  audit ``registrationPreservesFlagsAndSyntaxIntegrity
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``safeRegistrationCarriesDerivedSyntaxIntegrity (binding ++ scope)
  audit ``safeNormalizedRegistrationKeepsExplicitIntegrity (binding ++ scope)
  audit ``provedSafeWrappedRegistrationHasIntegrity (normalized ++ scope)
  audit ``FVarsIn.peelTypeAnnotations
  audit ``FVarsIn.indexFVarsWithin
  audit ``peelTypeAnnotations_hasMVar_eq_false expressions
  audit ``FVarsIn.instantiate1_native binding
  audit ``WrappedSortTelescope.fvarsIn binding
  audit ``CheckedHeaderSource.sourceFVarsIn expressions
  audit ``CheckedHeaderSource.normalizedFVarsIn_of_wrapped normalized
  audit ``NormalizedHeaderFVarsIn
  audit ``NormalizedHeaderFVarsIn.fvarsWithin
  audit ``CheckedHeaderSupportSources.wrappedFVarsIn normalized
  audit ``BinderRawDomainFVarsIn
  audit ``OpenedTelescope.rawDomainFVarsIn binding
  audit ``BinderRawDomainFVarsIn.rawDomainScope
  audit ``BinderStoredIndexDomainFVarsIn
  audit ``BinderStoredIndexTypeFVarsIn
  audit ``BinderRawDomainFVarsIn.storedIndexDomainFVarsIn
  audit ``BinderRawDomainFVarsIn.storedIndexTypeFVarsIn
  audit ``ParentBinderIntegrity
  audit ``RecursorBinderIntegrity
  audit ``ParentBinderIntegrity.toBinderStoredLookupTypes
  audit ``RecursorBinderIntegrity.toBinderStoredLookupTypes
  audit ``ParentBinderStoredLookupTypes.integrity binding
  audit ``RecursorBinderStoredLookupTypes.integrity binding
  audit ``CheckedHeaderSupportSources.normalizedBinderIntegrity (binding ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderIntegrity (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderIntegrity (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderIntegrity (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderIntegrity
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredBinderIntegrity (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderIntegrity (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderIntegrity (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderIntegritySeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderIntegritySeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderIntegritySeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderIntegritySeed, idx := 71 } }] do
    fixtures reader
  rejectedMetaSources ctx
  uncheckedHelperBoundary ctx
  logInfo "30 full registrations / 48 parent pairs / 153 paired binder domains / 96 paired index declarations / three dense readers retain raw/peeled/native stored-domain syntax integrity and chronological deterministic correspondence"

end InductiveBinderIntegrityTest
