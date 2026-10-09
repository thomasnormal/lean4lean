import Lean4Lean.Verify.InductiveBinderStoredTypeAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderStoredTypesTest

abbrev CarrierAlias := Type

private def sortType : Expr := .sort (.succ .zero)

private def unary (name : Name) (level : Level) (carrier : Expr) : Expr := .app (.const name [level]) carrier

private def binary (name : Name) (level : Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name [level]) carrier) extra

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def tagged : MData := { entries := [(`BinderStoredTypesTag, .ofNat 31)] }

private def dependent : Expr :=
  .forallE `carrier sortType
    (.forallE `element (unary ``semiOutParam (.succ .zero) (.bvar 0))
      (.forallE `witness (unary ``outParam .zero (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
        (.forallE `optional
          (binary ``optParam .zero (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1)))
          (.forallE `automatic
            (binary ``autoParam .zero (equalityDomain (.bvar 3) (.bvar 2) (.bvar 2))
              (.const ``Lean.Syntax.missing []))
            sortType .default) .strictImplicit) .instImplicit) .default) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (unary ``semiOutParam (.succ .zero) (.bvar 0)) .default
      (.forallE `witness (unary ``outParam .zero (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))) .instImplicit
        (.forallE `optional
          (binary ``optParam .zero (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1))) .strictImplicit
          (.forallE `automatic
            (binary ``autoParam .zero (equalityDomain (.bvar 3) (.bvar 2) (.bvar 2))
              (.const ``Lean.Syntax.missing [])) .default (.sort (.succ .zero))))))

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
  header `BinderStoredLet (wrappedLet data), header `BinderStoredBeta (wrappedBeta data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem actualNativeAnchorsRetained {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeStoredIndexTypeAt pairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated position) :
    ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
      checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
      priorPairs = pairs ++ List.zip
        ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
      checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
      checkedDecl.toExpr = checkedStep.value ∧ generatedDecl.toExpr = generatedStep.value ∧
      checkedDecl.type = peelTypeAnnotations checkedStep.domain ∧
      generatedDecl.type = peelTypeAnnotations generatedStep.domain ∧
      checkedDecl.userName = checkedStep.name ∧ generatedDecl.userName = generatedStep.name ∧
      checkedDecl.binderInfo = checkedStep.bi ∧ generatedDecl.binderInfo = generatedStep.bi ∧
      checkedDecl.index = checkedStart + (BinderStep.indexValues (checked.take position)).length ∧
      generatedDecl.index = generatedStart + (BinderStep.indexValues (generated.take position)).length ∧
      IndexLookupRenaming priorPairs checkedStep.domain generatedStep.domain ∧
      IndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    _, _, _, hprior, hcheckedLookup, hgeneratedLookup, hcheckedExpr, hgeneratedExpr, hcheckedType,
    hgeneratedType, hcheckedName, hgeneratedName, hcheckedBi, hgeneratedBi, hcheckedIndex,
    hgeneratedIndex, hraw, _, _, _, hstored⟩ := receipt
  exact ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    hprior, hcheckedLookup, hgeneratedLookup, hcheckedExpr, hgeneratedExpr, hcheckedType,
    hgeneratedType, hcheckedName, hgeneratedName, hcheckedBi, hgeneratedBi, hcheckedIndex,
    hgeneratedIndex, hraw, hstored⟩

private theorem rawScopeStillNeedsInitialSupport (dropped current : FVarId) :
    IndexFVarsWithin [] (peelTypeAnnotations (binary ``optParam (.succ .zero) (.const ``Nat []) (.fvar dropped))) ∧
      ¬ BinderRawDomainScope []
        [{ role := .index, name := `index, domain := binary ``optParam (.succ .zero) (.const ``Nat []) (.fvar dropped), bi := .default, value := .fvar current }] := by
  refine ⟨by simp [peelTypeAnnotations, binary, IndexFVarsWithin], ?_⟩
  intro scope
  have selected := scope 0 _ rfl
  simp [IndexFVarsWithin, binary, BinderStep.indexValues] at selected

private theorem discardedSharedDefaultDisappears (param : FVarId) :
    (peelTypeAnnotations (binary ``optParam (.succ .zero) (.const ``Nat []) (.fvar param))).fvarsList = [] ∧
      param ∈ (binary ``optParam (.succ .zero) (.const ``Nat []) (.fvar param)).fvarsList := by
  simp [peelTypeAnnotations, binary, Expr.fvarsList]

private theorem sharedParameterTypeEqualityIsNotRequired (source : FVarId) :
    BinderStoredIndexDomainScope []
      [{ role := .parameter, name := `shared, domain := .fvar source, bi := .implicit, value := .fvar source }] := by
  intro position step selected index
  cases position with
  | zero =>
    obtain rfl := Option.some.inj selected
    cases index
  | succ position =>
    simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
    cases selected

private theorem parentRetainsScopedContracts {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderStoredLookupTypes stats types parent checked current info) :
    ParentBinderScopedLookupTypes stats types parent checked current info := receipt.toBinderScopedLookupTypes

private theorem recursorsRetainScopedContracts {stats : InductiveStats} {types : Array InductiveType}
    {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderStoredLookupTypes stats types checked current infos) :
    RecursorBinderScopedLookupTypes stats types checked current infos := receipt.toBinderScopedLookupTypes

private theorem parentUpgradeNeedsNoNativeModel {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderScopedLookupTypes stats types parent checked current info) :
    ParentBinderStoredLookupTypes stats types parent checked current info := receipt.storedTypes

private theorem recursorsUpgradeNeedsNoNativeModel {stats : InductiveStats} {types : Array InductiveType}
    {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderScopedLookupTypes stats types checked current infos) :
    RecursorBinderStoredLookupTypes stats types checked current infos := receipt.storedTypes

private theorem sameWitnessAllRawStoredContracts {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderStoredLookupTypes stats types parent checkedRoot current info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧ OpenedTelescope normalized generated generatedTerminal ∧
      BinderStep.parameterValues checked = stats.params.toList ∧
      BinderStep.parameterValues generated = stats.params.toList ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧ BinderIndexAllocations current generatedStart generated ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!) (info.indices.toList.map Expr.fvarId!) ∧
      IndexPairInjection pairs ∧ BinderLookupCorrespondence [] checked generated pairs ∧
      IndexLookupRenaming pairs checkedTerminal generatedTerminal ∧
      BinderLookupNativeTypes [] checkedRoot current checkedStart generatedStart checked generated ∧
      BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderRawIndexExclusion checked ∧ BinderRawIndexExclusion generated ∧
      BinderLookupStoredTypeScopes [] (stats.params.toList.map Expr.fvarId!)
        checkedRoot current checkedStart generatedStart checked generated ∧
      BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderStoredIndexExclusion checked ∧ BinderStoredIndexExclusion generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, hcheckedParams, hgeneratedParams,
    _, _, _, _, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, hpairs, hinjection, _, _, hlookup,
    hterminal, hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion,
    hstoredTypes, hcheckedStoredScope, hgeneratedStoredScope, hcheckedStoredExclusion, hgeneratedStoredExclusion⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedParams, hgeneratedParams,
    hcheckedAlloc, hgeneratedAlloc, hpairs, hinjection, hlookup, hterminal, hnative, hcheckedScope,
    hgeneratedScope, hcheckedExclusion, hgeneratedExclusion, hstoredTypes, hcheckedStoredScope,
    hgeneratedStoredScope, hcheckedStoredExclusion, hgeneratedStoredExclusion⟩

private theorem exactStoredPositionIsUsable {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep} {step : BinderStep}
    (receipt : BinderLookupStoredTypeScopes pairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated) (selected : checked[position]? = some step) (index : step.role = .index) :
    NativeStoredIndexTypeAt pairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated position := receipt position step selected index

private theorem storedCurrentAndFutureExclusionIsUsable {steps : List BinderStep}
    {position futurePosition : Nat} {domainStep futureStep : BinderStep}
    (exclusion : BinderStoredIndexExclusion steps) (domain : steps[position]? = some domainStep)
    (future : steps[futurePosition]? = some futureStep) (index : futureStep.role = .index)
    (later : position ≤ futurePosition) : IndexAvoids futureStep.value.fvarId! domainStep.localDomain :=
  exclusion position domainStep futurePosition futureStep domain future index later

private theorem normalizedSourcesRetainStoredContracts {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (normalized : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderStoredLookupTypes stats types checkedRoot current infos :=
  headers.normalizedBinderStoredLookupTypes sources normalized support hwf within

private theorem wrappedSourcesDischargeSupport {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (wrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) : RecursorBinderStoredLookupTypes stats types checkedRoot current infos :=
  headers.wrappedBinderStoredLookupTypes sources wrapped support hwf

private theorem cpsCarriesUnconditionalStoredContracts {α : Type}
    (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!))
    (continuation : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → RecursorIndexCounts stats types infos →
      RecursorBinderStoredLookupTypes stats types checkedRoot current infos → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedNormalizedBinderStoredLookupTypes nparams stats types elimLevel next original checkedRoot ctx post
    headers normalized hwf reserved support within continuation

private theorem getterCarriesUnconditionalStoredContracts (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧ RecursorIndexCounts stats types result.1 ∧
      RecursorBinderStoredLookupTypes stats types checkedRoot result.2 result.1 :=
  mkRecInfos.getNormalizedBinderStoredLookupTypes nparams stats types elimLevel original checkedRoot ctx
    headers normalized hwf reserved support within

private theorem registrationPreservesFlagsAndStoredContracts (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧ result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧
      RecursorBinderStoredLookupTypes stats types checkedRoot result.2.2 result.2.1 :=
  mkRecInfos.registeredNormalizedBinderStoredLookupTypes nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers normalized hwf reserved henv support within

private theorem safeRegistrationRetainsDerivedSupport (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (within : ∀ stats current, CheckedHeaderSupportSources nparams types ctx stats current →
      NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderStoredLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderStoredLookupTypes nparams types numNested elimLevel lparams isK ctx
    normalized hwf reserved within

private theorem safeNormalizedRegistrationWithEmptySourceSupport (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (normalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (closed : NormalizedHeaderFVarsWithin types []) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderStoredLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderStoredLookupTypes nparams types numNested elimLevel lparams isK ctx
    normalized hwf reserved closed

private theorem provedSafeWrappedRegistration (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderStoredLookupTypes result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderStoredLookupTypes 1 (provedTypes data) 0 (.succ .zero) [] false ctx
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
      | throwError "stored-types checked allocation points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkStoredSupport (params indices : Array Expr) (steps : List BinderStep)
    (raw stored : Expr) : MetaM Unit := do
  let earlier := BinderStep.indexValues steps
  let allowed := params.toList.map Expr.fvarId! ++ earlier.map Expr.fvarId!
  unless raw.fvarsList.all allowed.contains && stored.fvarsList.all allowed.contains do
    throwError "stored-types raw/stored domain gained support beyond shared parameters/strictly earlier own indices"
  for future in indices.toList.drop earlier.length do
    unless !(raw.containsFVar future.fvarId!) && !(stored.containsFVar future.fvarId!) do
      throwError "stored-types raw/stored domain mentions a current/future own-history index"

private def getExactDeclaration (ctx : Context) (value : Expr) (name : Name) (raw : Expr)
    (bi : BinderInfo) (position : Nat) : MetaM LocalDecl := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "stored-types actual index find? lookup is missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations raw &&
      declaration.userName == name && declaration.binderInfo == bi && declaration.index == position do
    throwError "stored-types actual lookup/value/type/name/binder-info/native-index anchor changed"
  return declaration

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut checkedSteps : List BinderStep := []
  let mut generatedSteps : List BinderStep := []
  let mut pairs : List (FVarId × FVarId) := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftRaw leftBody leftBi := left
      | throwError "stored-types checked opening ended before actual substitutions"
    let .forallE rightName rightRaw rightBody rightBi := right
      | throwError "stored-types generated opening ended before actual substitutions"
    let incoming := List.zip ((BinderStep.indexValues checkedSteps).map Expr.fvarId!)
      ((BinderStep.indexValues generatedSteps).map Expr.fvarId!)
    unless pairs == incoming && leftName == rightName && leftBi == rightBi &&
        indexRenameExpr incoming leftRaw == rightRaw do
      throwError "stored-types strictly-prior raw correspondence changed"
    checkStoredSupport params checked checkedSteps leftRaw (peelTypeAnnotations leftRaw)
    checkStoredSupport params generated generatedSteps rightRaw (peelTypeAnnotations rightRaw)
    let role := if position < nparams then BinderRole.parameter else .index
    if role = .index then
      let leftDecl ← getExactDeclaration checkedCtx leftValues[position]! leftName leftRaw leftBi
        (checkedStart + position - nparams)
      let rightDecl ← getExactDeclaration generatedCtx rightValues[position]! rightName rightRaw rightBi
        (generatedStart + position - nparams)
      unless indexRenameExpr incoming leftDecl.type == rightDecl.type do
        throwError "stored-types deterministic consumed declaration-type correspondence changed"
      pairs := pairs ++ [(leftValues[position]!.fvarId!, rightValues[position]!.fvarId!)]
    checkedSteps := checkedSteps ++ [{ role, name := leftName, domain := leftRaw, bi := leftBi, value := leftValues[position]! }]
    generatedSteps := generatedSteps ++ [{ role, name := rightName, domain := rightRaw, bi := rightBi, value := rightValues[position]! }]
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  unless left == sortType && right == sortType &&
      pairs == List.zip (checked.toList.map Expr.fvarId!) (generated.toList.map Expr.fvarId!) do
    throwError "stored-types same-witness terminal/full actual index-ID zip anchor changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "stored-types actual full registration failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "stored-types actual parameter/index/parent count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "stored-types actual header normalization failed"
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "stored-types actual recursor registration is missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "stored-types actual recursor metadata changed"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderStoredEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderStoredDependent nparams) dependent] #[5 - nparams]
  for nparams in [0, 1, 2, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderStoredMutualFirst nparams) dependent,
      header (Name.mkNum `BinderStoredMutualSecond nparams) dependent] #[5 - nparams, 5 - nparams]
  checkFixture ctx 1 (provedTypes tagged) #[4, 4]
  let defaulted := Expr.forallE `defaultValue (.const ``Nat [])
    (.forallE `index (binary ``optParam (.succ .zero) (.const ``Nat []) (.bvar 0)) sortType .default) .implicit
  checkFixture ctx 1 #[header `BinderStoredDiscardedSharedDefault defaulted] #[1]

private def reusedParameterBoundary (ctx : Context) : MetaM Unit := do
  let source := Expr.forallE `firstCarrier (.const ``CarrierAlias [])
    (.forallE `element (unary ``semiOutParam (.succ .zero) (.bvar 0)) sortType .default) .implicit
  let later := Expr.forallE `changedCarrier sortType
    (.forallE `element (unary ``semiOutParam (.succ .zero) (.bvar 0)) sortType .default) .implicit
  let types := #[header `BinderStoredAliasFirst source, header `BinderStoredAliasSecond later]
  let .ok (stats, checked, _, _, _, _) := stage 1 types ctx
    | throwError "stored-types reused shared parameter setup failed"
  let some declaration := checked.lctx.find? stats.params[0]!.fvarId!
    | throwError "stored-types reused shared parameter declaration is missing"
  let .ok equivalent := ((monadLift (TypeChecker.isDefEq declaration.type (peelTypeAnnotations sortType)) : M Bool) checked)
    | throwError "stored-types reused shared parameter definitional equality failed"
  unless equivalent && declaration.type != peelTypeAnnotations sortType do
    throwError "stored-types reused parameter boundary incorrectly acquired literal stored-domain equality"
  logInfo "one shared-parameter boundary keeps isDefEq acceptance distinct from literal stored-domain equality"

private def independentReaderBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `BinderStoredIndependent dependent]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "stored-types independent reader setup failed"
  for overlap in [false, true] do
    let secondRoot := if overlap then { generatorRoot with ngen := generatorRoot.ngen.next } else generatorRoot
    let .ok (first, firstCtx) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) generatorRoot
      | throwError "stored-types first independent opening failed"
    let .ok (second, secondCtx) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) secondRoot
      | throwError "stored-types second independent opening failed"
    let sources := first[0]!.indices.toList.map Expr.fvarId!
    let targets := second[0]!.indices.toList.map Expr.fvarId!
    unless (if overlap then sources.any targets.contains && sources != targets else sources == targets) do
      throwError "stored-types independent identity/overlapping ID fixture changed"
    checkOpening firstCtx secondCtx 1 generatorRoot.lctx.numIndices secondRoot.lctx.numIndices
      dependent stats.params first[0]!.indices second[0]!.indices
  logInfo "two independent-reader stored correspondence controls allow identity/overlapping source and target IDs while enforcing each history's own current/future exclusion"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let normalized := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``dependentShape
  audit ``wrappedLetTrace binding
  audit ``wrappedBetaTrace binding
  audit ``provedHeaders binding
  audit ``actualNativeAnchorsRetained
  audit ``rawScopeStillNeedsInitialSupport
  audit ``discardedSharedDefaultDisappears
  audit ``sharedParameterTypeEqualityIsNotRequired
  audit ``parentRetainsScopedContracts
  audit ``recursorsRetainScopedContracts
  audit ``parentUpgradeNeedsNoNativeModel
  audit ``recursorsUpgradeNeedsNoNativeModel
  audit ``sameWitnessAllRawStoredContracts
  audit ``exactStoredPositionIsUsable
  audit ``storedCurrentAndFutureExclusionIsUsable
  audit ``normalizedSourcesRetainStoredContracts (binding ++ scope)
  audit ``wrappedSourcesDischargeSupport (normalized ++ scope)
  audit ``cpsCarriesUnconditionalStoredContracts (binding ++ scope)
  audit ``getterCarriesUnconditionalStoredContracts (binding ++ scope)
  audit ``registrationPreservesFlagsAndStoredContracts
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``safeRegistrationRetainsDerivedSupport (binding ++ scope)
  audit ``safeNormalizedRegistrationWithEmptySourceSupport (binding ++ scope)
  audit ``provedSafeWrappedRegistration (normalized ++ scope)
  audit ``ParentBinderStoredLookupTypes
  audit ``RecursorBinderStoredLookupTypes
  audit ``ParentBinderStoredLookupTypes.toBinderScopedLookupTypes
  audit ``RecursorBinderStoredLookupTypes.toBinderScopedLookupTypes
  audit ``ParentBinderScopedLookupTypes.storedTypes
  audit ``RecursorBinderScopedLookupTypes.storedTypes
  audit ``CheckedHeaderSupportSources.normalizedBinderStoredLookupTypes (binding ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderStoredLookupTypes (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderStoredLookupTypes (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderStoredLookupTypes (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderStoredLookupTypes
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredBinderStoredLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderStoredLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderStoredLookupTypes (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderStoredSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderStoredSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderStoredSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderStoredSeed, idx := 71 } }] do
    fixtures reader
  reusedParameterBoundary ctx
  independentReaderBoundaries ctx
  logInfo "39 full registrations / 54 parent pairs / 246 paired binder domains / 144 paired index declarations / three dense readers preserve unconditional actual stored-type support/exclusion/deterministic correspondence and exact native declaration anchors"

end InductiveBinderStoredTypesTest
