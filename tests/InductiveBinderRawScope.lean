import Lean4Lean.Verify.InductiveBinderRawScopeAlignment
import Lean4Lean.Verify.InductiveBinderRawScopeExclusion
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderRawScopeTest

abbrev CarrierAlias := Type

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`BinderRawScopeTag, .ofNat 1)] }

private def dependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
      (.forallE `again
        (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
        sortType .default) .instImplicit) .strictImplicit) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) .instImplicit
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          .default (.sort (.succ .zero)))))

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
  header `BinderRawScopeLet (wrappedLet data), header `BinderRawScopeBeta (wrappedBeta data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private def indexStep (name : Name) (domain : Expr) (id : FVarId) : BinderStep :=
  { role := .index, name, domain, bi := .default, value := .fvar id }

private def parameterStep (id : FVarId) : BinderStep :=
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar id }

private def sequentialSteps (param first second : FVarId) : List BinderStep := [
  parameterStep param, indexStep `first (.fvar param) first, indexStep `second (.fvar first) second]

private theorem emptyRawScope (params : List FVarId) : BinderRawDomainScope params [] := by
  intro position step selected
  simp only [List.getElem?_nil] at selected
  cases selected

private theorem ownIndexMissingFromAllowedPrefix (source : FVarId) :
    ((BinderStep.indexValues ([indexStep `index sortType source].take 0)).map Expr.fvarId!) = [] := rfl

private theorem currentSelfDomainRejected (source : FVarId) :
    ¬ BinderRawDomainScope [] [indexStep `index (.fvar source) source] := by
  intro scope
  have selected := scope 0 (indexStep `index (.fvar source) source) rfl
  simp [IndexFVarsWithin, BinderStep.indexValues, indexStep] at selected

private theorem arbitraryInitialFVarNeedsSupport (old source : FVarId) :
    ¬ BinderRawDomainScope [] [indexStep `index (.fvar old) source] := by
  intro scope
  have selected := scope 0 (indexStep `index (.fvar old) source) rfl
  simp [IndexFVarsWithin, BinderStep.indexValues, indexStep] at selected

private theorem arbitraryInitialFVarCanBeAdmitted (old source : FVarId) :
    BinderRawDomainScope [old] [indexStep `index (.fvar old) source] := by
  intro position step selected
  cases position with
  | zero =>
    have equal : indexStep `index (.fvar old) source = step := Option.some.inj selected
    subst step
    simp [IndexFVarsWithin, BinderStep.indexValues, indexStep]
  | succ position =>
    simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
    cases selected

private theorem currentIdCanOccurWithoutDisjointness (source : FVarId) :
    BinderRawDomainScope [source] [indexStep `index (.fvar source) source] :=
  arbitraryInitialFVarCanBeAdmitted source source

private theorem futureIndexDomainRejected (first second : FVarId) :
    ¬ BinderRawDomainScope []
      [indexStep `first (.fvar second) first, indexStep `second sortType second] := by
  intro scope
  have selected := scope 0 (indexStep `first (.fvar second) first) rfl
  simp [IndexFVarsWithin, BinderStep.indexValues, indexStep] at selected

private theorem singletonRawScope {params : List FVarId} {domain : Expr}
    (name : Name) (source : FVarId) (within : IndexFVarsWithin params domain) :
    BinderRawDomainScope params [indexStep name domain source] := by
  intro position step selected
  cases position with
  | zero =>
    obtain rfl := Option.some.inj selected
    simpa only [List.take_zero, BinderStep.indexValues, List.map_nil, List.append_nil] using within
  | succ position =>
    simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
    cases selected

private theorem supportOnlyPermitsUnclosedUntypedDomains (source : FVarId) (metavar : MVarId) :
    BinderRawDomainScope []
      [indexStep `index (.app (.const `BinderRawScopeUnknown []) (.app (.bvar 7) (.mvar metavar))) source] :=
  singletonRawScope `index source (by simp [IndexFVarsWithin])

private theorem openingOnlyPermitsUnclosedUntypedDomains (source : FVarId) (metavar : MVarId) :
    OpenedTelescope
      (.forallE `index (.app (.const `BinderRawScopeUnknown []) (.app (.bvar 7) (.mvar metavar))) sortType .default)
      [indexStep `index (.app (.const `BinderRawScopeUnknown []) (.app (.bvar 7) (.mvar metavar))) source]
      sortType := by
  apply OpenedTelescope.bind
  rw [Expr.instantiate1_eq]
  exact .sort (.succ .zero)

private theorem sequentialRawScope (param first second : FVarId) :
    BinderRawDomainScope [param] (sequentialSteps param first second) := by
  intro position step selected
  cases position with
  | zero =>
    obtain rfl := Option.some.inj selected
    simp [sequentialSteps, parameterStep, sortType, IndexFVarsWithin, BinderStep.indexValues]
  | succ position =>
    cases position with
    | zero =>
      obtain rfl := Option.some.inj selected
      simp [sequentialSteps, parameterStep, indexStep, IndexFVarsWithin, BinderStep.indexValues]
    | succ position =>
      cases position with
      | zero =>
        obtain rfl := Option.some.inj selected
        simp [sequentialSteps, parameterStep, indexStep, IndexFVarsWithin, BinderStep.indexValues,
          Expr.fvarId!]
      | succ position =>
        simp only [sequentialSteps, List.getElem?_cons_succ, List.getElem?_nil] at selected
        cases selected

private theorem earlierIndexIncluded (param first second : FVarId) :
    first ∈ [param] ++
      (BinderStep.indexValues ((sequentialSteps param first second).take 2)).map Expr.fvarId! := by
  simp [sequentialSteps, parameterStep, indexStep, BinderStep.indexValues, Expr.fvarId!]

private theorem reusedIndexIdRequiresDistinctness (source : FVarId) :
    BinderRawDomainScope []
      [indexStep `first sortType source, indexStep `second (.fvar source) source] ∧
      ¬ IndexAvoids source (.fvar source) := by
  refine ⟨?_, by simp [IndexAvoids]⟩
  intro position step selected
  cases position with
  | zero =>
    obtain rfl := Option.some.inj selected
    simp [indexStep, sortType, IndexFVarsWithin]
  | succ position =>
    cases position with
    | zero =>
      obtain rfl := Option.some.inj selected
      simp [indexStep, BinderStep.indexValues, IndexFVarsWithin, Expr.fvarId!]
    | succ position =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
      cases selected

private theorem rawScopeSubset {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} (scope : BinderRawDomainScope params steps)
    (selected : steps[position]? = some step) :
    step.domain.fvarsList ⊆ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId! :=
  scope.domainSubset selected

private theorem rawScopeWiden {params wider : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) (additional : params ⊆ wider) :
    BinderRawDomainScope wider steps := scope.mono additional

private theorem openingProducesChronologicalRawScope {params : List FVarId} {type terminal : Expr}
    {steps : List BinderStep} {ctx : Context} (opened : OpenedTelescope type steps terminal)
    (within : IndexFVarsWithin params type)
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id ∈ params, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) : BinderRawDomainScope params steps :=
  opened.rawDomainScope within shapes declared

private theorem suffixRawExclusion {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} {id : FVarId} (scope : BinderRawDomainScope params steps)
    (selected : steps[position]? = some step)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (suffix : id ∈ (BinderStep.indexValues (steps.drop position)).map Expr.fvarId!) :
    IndexAvoids id step.domain := scope.avoidsSuffixIndex selected distinct disjoint suffix

private theorem currentRawExclusion {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} (scope : BinderRawDomainScope params steps)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (selected : steps[position]? = some step) (index : step.role = .index) :
    IndexAvoids step.value.fvarId! step.domain := scope.avoidsCurrentIndex distinct disjoint selected index

private theorem allocatedFutureRawExclusion {params : List FVarId} {steps : List BinderStep}
    {ctx : Context} {start position futurePosition : Nat} {domainStep futureStep : BinderStep}
    (scope : BinderRawDomainScope params steps) (allocated : BinderIndexAllocations ctx start steps)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (hdomain : steps[position]? = some domainStep) (hfuture : steps[futurePosition]? = some futureStep)
    (index : futureStep.role = .index) (later : position ≤ futurePosition) :
    IndexAvoids futureStep.value.fvarId! domainStep.domain :=
  scope.avoidsCurrentOrFutureIndex_of_allocations allocated disjoint hdomain hfuture index later

private theorem bundledRawExclusion {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!)) :
    BinderRawIndexExclusion steps := scope.indexExclusion distinct disjoint

private theorem parentRetainsNativeTypes {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked generated : Context} {info : RecInfo}
    (receipt : ParentBinderScopedLookupTypes stats types parent checked generated info) :
    ParentBinderLookupTypes stats types parent checked generated info := receipt.toBinderLookupTypes

private theorem recursorsRetainNativeTypes {stats : InductiveStats} {types : Array InductiveType}
    {checked generated : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderScopedLookupTypes stats types checked generated infos) :
    RecursorBinderLookupTypes stats types checked generated infos := receipt.toBinderLookupTypes

private theorem sameWitnessScopedNativeHistories {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot generatedRoot : Context} {info : RecInfo}
    (receipt : ParentBinderScopedLookupTypes stats types parent checkedRoot generatedRoot info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧
      OpenedTelescope normalized generated generatedTerminal ∧
      BinderStep.parameterValues checked = stats.params.toList ∧
      BinderStep.parameterValues generated = stats.params.toList ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧
      BinderIndexAllocations generatedRoot generatedStart generated ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      IndexLookupRenaming pairs checkedTerminal generatedTerminal ∧
      BinderLookupNativeTypes [] checkedRoot generatedRoot checkedStart generatedStart checked generated ∧
      BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderRawDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderRawIndexExclusion checked ∧ BinderRawIndexExclusion generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, hcheckedParams, hgeneratedParams,
    _, _, _, _, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, _, _, _, _, hlookup, hterminal,
    hnative, hcheckedScope, hgeneratedScope, hcheckedExclusion, hgeneratedExclusion⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedParams, hgeneratedParams,
    hcheckedAlloc, hgeneratedAlloc, hlookup, hterminal, hnative, hcheckedScope, hgeneratedScope,
    hcheckedExclusion, hgeneratedExclusion⟩

private theorem nativeParentNeedsExplicitInitialSupport {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderLookupTypes stats types parent checkedRoot current info)
    (shapes : ∀ value ∈ stats.params.toList,
      ∃ id ∈ stats.params.toList.map Expr.fvarId!, value = .fvar id)
    (within : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized →
      IndexFVarsWithin (stats.params.toList.map Expr.fvarId!) normalized) :
    ParentBinderScopedLookupTypes stats types parent checkedRoot current info :=
  receipt.rawDomainScope shapes within

private theorem normalizedSourcesNeedExplicitSupport {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (typesNormalized : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderScopedLookupTypes stats types checkedRoot current infos :=
  headers.normalizedBinderScopedLookupTypes sources typesNormalized support hwf within

private theorem wrappedSourcesDischargeInitialSupport {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (typesWrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) : RecursorBinderScopedLookupTypes stats types checkedRoot current infos :=
  headers.wrappedBinderScopedLookupTypes sources typesWrapped support hwf

private theorem provedRegisteredRawScope (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderScopedLookupTypes result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderScopedLookupTypes 1 (provedTypes data) 0 (.succ .zero)
    [] false ctx (provedHeaders data) hwf hreserved

private theorem normalizedSafeRegistrationNeedsEmptySupport (types : Array InductiveType)
    (ctx : Context) (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (closed : NormalizedHeaderFVarsWithin types []) :
    (checkInductiveTypes 1 types (fun stats => do
      withEnv (← declareInductiveTypes stats 1 types 0 false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 types ctx result.1 checkedRoot ∧
        RecursorBinderScopedLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderScopedLookupTypes 1 types 0 (.succ .zero)
    [] false ctx htypes hwf hreserved closed

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
    let some decl := ctx.lctx.getAt? (start + offset)
      | throwError "binder-raw-scope checked allocation points at a hole"
    values := values.push decl.toExpr
  return values

private def allowedIds (params : Array Expr) (steps : List BinderStep) : List FVarId :=
  params.toList.map Expr.fvarId! ++ (BinderStep.indexValues steps).map Expr.fvarId!

private def withinIds (allowed : List FVarId) (domain : Expr) : Bool :=
  domain.fvarsList.all allowed.contains

private def checkDomainScope (params indices : Array Expr) (steps : List BinderStep)
    (rawDomain : Expr) : MetaM Unit := do
  let earlier := BinderStep.indexValues steps
  unless withinIds (allowedIds params steps) rawDomain do
    throwError "binder-raw-scope raw domain mentions neither a shared parameter nor an earlier index"
  for future in indices.toList.drop earlier.length do
    unless !(rawDomain.containsFVar future.fvarId!) do
      throwError "binder-raw-scope raw domain mentions its current or a future own-history index ID"

private def checkIndexDeclaration (ctx : Context) (value : Expr) (name : Name)
    (domain : Expr) (bi : BinderInfo) (position : Nat) : MetaM Unit := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "binder-raw-scope actual index declaration missing"
  unless declaration.toExpr == value && declaration.type == domain.consumeTypeAnnotations &&
      declaration.userName == name && declaration.binderInfo == bi && declaration.index == position do
    throwError "binder-raw-scope native index declaration anchors changed"

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut checkedSteps : List BinderStep := []
  let mut generatedSteps : List BinderStep := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftRaw leftBody leftBi := left
      | throwError "binder-raw-scope checked opening ended before actual substitutions"
    let .forallE rightName rightRaw rightBody rightBi := right
      | throwError "binder-raw-scope generated opening ended before actual substitutions"
    checkDomainScope params checked checkedSteps leftRaw
    checkDomainScope params generated generatedSteps rightRaw
    let incoming := List.zip ((BinderStep.indexValues checkedSteps).map Expr.fvarId!)
      ((BinderStep.indexValues generatedSteps).map Expr.fvarId!)
    unless leftName == rightName && leftBi == rightBi && indexRenameExpr incoming leftRaw == rightRaw do
      throwError "binder-raw-scope deterministic raw correspondence changed"
    let role := if position < nparams then BinderRole.parameter else .index
    if role = .index then
      checkIndexDeclaration checkedCtx leftValues[position]! leftName leftRaw leftBi
        (checkedStart + position - nparams)
      checkIndexDeclaration generatedCtx rightValues[position]! rightName rightRaw rightBi
        (generatedStart + position - nparams)
    checkedSteps := checkedSteps ++ [{ role, name := leftName, domain := leftRaw, bi := leftBi, value := leftValues[position]! }]
    generatedSteps := generatedSteps ++ [{ role, name := rightName, domain := rightRaw, bi := rightBi, value := rightValues[position]! }]
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  unless left == sortType && right == sortType do
    throwError "binder-raw-scope actual opening terminal changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "binder-raw-scope actual registration failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-raw-scope actual count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "binder-raw-scope actual source normalization failed"
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-raw-scope registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-raw-scope registered metadata changed"

private def multipleParams : Expr := .forallE `carrier sortType
  (.forallE `pivot (.bvar 0)
    (.forallE `element (.bvar 1)
      (.forallE `witness (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1))
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 3) (.bvar 1) (.bvar 2)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .default) .implicit

private def family (carrierDomain : Expr) (names : Name) (marked : Bool) : Expr :=
  let elementDomain := if marked then Expr.mdata tagged (.bvar 0) else .bvar 0
  .forallE (names ++ `carrier) carrierDomain
    (.forallE (names ++ `element) elementDomain
      (.forallE (names ++ `witness) (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.forallE (names ++ `again)
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .implicit

private def annotatedDependent : Expr := .forallE `carrier sortType
  (.forallE `element (mkApp (.const ``outParam [.succ .zero]) (.bvar 0))
    (.forallE `witness
      (mkApp (.const ``outParam [.zero]) (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
      sortType .instImplicit) .strictImplicit) .implicit

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderRawScopeEmpty sortType] #[0]
  for nparams in [0, 1, 2, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderRawScopeDependent nparams) dependent] #[4 - nparams]
  checkFixture ctx 2 #[header `BinderRawScopeMultiple multipleParams] #[3]
  checkFixture ctx 1 #[header `BinderRawScopeMutualFirst (family sortType `first false),
    header `BinderRawScopeMutualSecond (family sortType `second true)] #[3, 3]
  checkFixture ctx 1 #[header `BinderRawScopeAliasFirst (family (.const ``CarrierAlias []) `first false),
    header `BinderRawScopeAliasSecond (family sortType `second false)] #[3, 3]
  checkFixture ctx 1 #[header `BinderRawScopeWrappedLet (wrappedLet tagged)] #[3]
  checkFixture ctx 1 #[header `BinderRawScopeWrappedBeta (wrappedBeta tagged)] #[3]
  checkFixture ctx 1 #[header `BinderRawScopeAnnotated annotatedDependent] #[2]

private def independentReaderBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `BinderRawScopeIndependentReaders dependent]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "binder-raw-scope independent reader setup failed"
  let .ok (first, firstCtx) := mkRecInfos stats types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) generatorRoot
    | throwError "binder-raw-scope first independent helper failed"
  for offset in [0, 1] do
    let other := { generatorRoot with
      lparams := [`OtherBinderRawScopeReader]
      ngen := { generatorRoot.ngen with idx := generatorRoot.ngen.idx + offset } }
    let .ok (second, secondCtx) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) other
      | throwError "binder-raw-scope second independent helper failed"
    let sources := first[0]!.indices.toList.map Expr.fvarId!
    let targets := second[0]!.indices.toList.map Expr.fvarId!
    if offset = 0 then
      unless sources == targets do
        throwError "binder-raw-scope identity paired-reader control changed"
    else
      unless (sources.any (targets.contains ·)) && sources != targets do
        throwError "binder-raw-scope overlapping paired-reader control changed"
    checkOpening firstCtx secondCtx 1 generatorRoot.lctx.numIndices generatorRoot.lctx.numIndices
      dependent stats.params first[0]!.indices second[0]!.indices
  logInfo "two independent-reader controls exclude current/future IDs within each own history while permitting cross-history identity/overlap"

private def reusedParameterBoundary (ctx : Context) : MetaM Unit := do
  let first := family (.const ``CarrierAlias []) `first false
  let second := Expr.forallE `changedCarrier sortType (.forallE `element (.bvar 0) sortType .default) .default
  let types := #[header `BinderRawScopeReusedFirst first, header `BinderRawScopeReusedSecond second]
  let .ok (stats, checked, _, _, _, _) := stage 1 types ctx
    | throwError "binder-raw-scope reused parameter setup failed"
  let some declaration := checked.lctx.find? stats.params[0]!.fvarId!
    | throwError "binder-raw-scope reused shared parameter disappeared"
  let raw := sortType.consumeTypeAnnotations
  let .ok equivalent := ((monadLift (TypeChecker.isDefEq declaration.type raw) : M Bool) checked)
    | throwError "binder-raw-scope reused parameter definitional equality failed"
  unless equivalent && declaration.type != raw do
    throwError "binder-raw-scope reused parameter unexpectedly acquired literal raw-domain type equality"
  logInfo "one reused shared parameter remains definitionally equal but not literally equal to its later consumed source domain"

private def initialSupportBoundary (ctx : Context) : MetaM Unit := do
  let old : FVarId := ⟨`BinderRawScopeOldCarrier⟩
  let seeded := { ctx with lctx := ctx.lctx.mkLocalDecl old `oldCarrier sortType .default }
  let name := `BinderRawScopeUncheckedOpen
  let closed := Expr.forallE `index (.const ``Nat []) sortType .default
  let .ok (stats, _, generatorRoot, _, _, _) := stage 0 #[header name closed] seeded
    | throwError "binder-raw-scope initial-support setup failed"
  let opened := Expr.forallE `index (.fvar old) sortType .default
  let .ok (infos, current) := mkRecInfos stats #[header name opened] (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) generatorRoot
    | throwError "binder-raw-scope bare generator unexpectedly rejects a declared preexisting source FVar"
  let some declaration := current.lctx.find? infos[0]!.indices[0]!.fvarId!
    | throwError "binder-raw-scope unchecked open-domain index missing"
  unless declaration.type == (.fvar old : Expr).consumeTypeAnnotations &&
      !(withinIds [] (.fvar old)) && withinIds [old] (.fvar old) do
    throwError "binder-raw-scope an arbitrary initial source FVar incorrectly acquired empty support"
  logInfo "one unchecked helper accepts a declared preexisting raw-domain FVar; its explicit initial support cannot be dropped"

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
  audit ``emptyRawScope
  audit ``ownIndexMissingFromAllowedPrefix
  audit ``currentSelfDomainRejected
  audit ``arbitraryInitialFVarNeedsSupport
  audit ``arbitraryInitialFVarCanBeAdmitted
  audit ``currentIdCanOccurWithoutDisjointness
  audit ``futureIndexDomainRejected
  audit ``singletonRawScope
  audit ``supportOnlyPermitsUnclosedUntypedDomains
  audit ``openingOnlyPermitsUnclosedUntypedDomains binding
  audit ``sequentialRawScope
  audit ``earlierIndexIncluded
  audit ``reusedIndexIdRequiresDistinctness
  audit ``rawScopeSubset
  audit ``rawScopeWiden
  audit ``openingProducesChronologicalRawScope binding
  audit ``suffixRawExclusion
  audit ``currentRawExclusion
  audit ``allocatedFutureRawExclusion
  audit ``bundledRawExclusion
  audit ``parentRetainsNativeTypes
  audit ``recursorsRetainNativeTypes
  audit ``sameWitnessScopedNativeHistories
  audit ``nativeParentNeedsExplicitInitialSupport binding
  audit ``normalizedSourcesNeedExplicitSupport (binding ++ scope)
  audit ``wrappedSourcesDischargeInitialSupport (normalized ++ scope)
  audit ``provedRegisteredRawScope (normalized ++ scope)
  audit ``normalizedSafeRegistrationNeedsEmptySupport (binding ++ scope)
  audit ``BinderRawDomainScope
  audit ``BinderRawDomainScope.domainSubset
  audit ``BinderRawDomainScope.mono
  audit ``OpenedTelescope.rawDomainScope binding
  audit ``BinderRawIndexExclusion
  audit ``BinderLookupCorrespondence.indexLengths
  audit ``BinderLookupCorrespondence.indexIdsNodup
  audit ``indexIdsSuffixOutsidePrefix
  audit ``indexRawDomain_avoidsSuffix
  audit ``BinderRawDomainScope.avoidsSuffixIndex
  audit ``BinderRawDomainScope.avoidsCurrentOrFutureIndex
  audit ``BinderRawDomainScope.avoidsCurrentIndex
  audit ``BinderRawDomainScope.avoidsCurrentOrFutureIndex_of_allocations
  audit ``BinderRawDomainScope.indexExclusion
  audit ``ParentBinderScopedLookupTypes
  audit ``RecursorBinderScopedLookupTypes
  audit ``ParentBinderScopedLookupTypes.toBinderLookupTypes
  audit ``RecursorBinderScopedLookupTypes.toBinderLookupTypes
  audit ``ParentBinderLookupTypes.rawDomainScope binding
  audit ``RecursorBinderLookupTypes.rawDomainScope binding
  audit ``CheckedHeaderSupportSources.normalizedBinderScopedLookupTypes (binding ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderScopedLookupTypes (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderScopedLookupTypes (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderScopedLookupTypes (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderScopedLookupTypes
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredBinderScopedLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderScopedLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderScopedLookupTypes (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderRawScopeSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderRawScopeSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderRawScopeSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderRawScopeSeed, idx := 71 } },
      { ctx with lparams := [`u] }] do
    fixtures reader
  independentReaderBoundaries ctx
  reusedParameterBoundary ctx
  initialSupportBoundary ctx
  logInfo "44 dense-reader full registrations retain chronological raw-domain FVar support and own-history current/future exclusion across 52 parent pairs/192 paired binder domains/four readers"

end InductiveBinderRawScopeTest
