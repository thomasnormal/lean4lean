import Lean4Lean.Verify.InductiveRecursorIndexTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveRecursorIndexTranslationTest

abbrev HeaderAlias := Nat → Type

private theorem actualParentCounterRequiresZeroParameters (stats : InductiveStats) :
    stats.params.size ≤ 0 ↔ stats.params.size = 0 := by omega

private theorem nonemptyParametersExcludeParentIndexOnlyTransport (stats : InductiveStats)
    (nonempty : 0 < stats.params.size) : ¬ stats.params.size ≤ 0 := by omega

private theorem zeroParameterBoundIsNotAnArbitraryPositiveCounter :
    1 ≤ 1 ∧ ¬ 1 ≤ 0 := by decide

private theorem scopeFrameAloneDoesNotGiveTranslatedReader {env : VEnv} {universes : List Name}
    (reader : Context) (readerWF : reader.lctx.WF)
    (reserved : ContextReserved reader.lctx reader.ngen) (missing : MVarId) :
    reader.RecursorScopeFrame (recursorIndexContext reader `untyped .default (.mvar missing)) ∧
      ∀ virtual, ¬ TrLCtx env universes
        (recursorIndexContext reader `untyped .default (.mvar missing)).lctx virtual := by
  refine ⟨Context.RecursorScopeFrame.push reader readerWF reserved `untyped .default (.mvar missing), ?_⟩
  intro virtual correspondence
  have translated := correspondence.2
  simp only [recursorIndexContext, LocalContext.mkLocalDecl_toList] at translated
  cases translated with
  | cons _ declarationTranslation =>
    cases declarationTranslation with
    | vlam domainTranslation _ => cases domainTranslation

private theorem arbitraryScopeEntryCorrespondenceWouldBeImpossible {env : VEnv} {universes : List Name}
    (reader : Context) (readerWF : reader.lctx.WF)
    (reserved : ContextReserved reader.lctx reader.ngen) (missing : MVarId) :
    ¬ (∀ entry, reader.RecursorScopeFrame entry →
      ∃ virtual, TrLCtx env universes entry.lctx virtual) := by
  intro uniform
  obtain ⟨scope, impossible⟩ := scopeFrameAloneDoesNotGiveTranslatedReader
    (env := env) (universes := universes) reader readerWF reserved missing
  obtain ⟨virtual, correspondence⟩ := uniform _ scope
  exact impossible virtual correspondence

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def dependentTwo : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private theorem dependentTwoTelescope : SortTelescope dependentTwo :=
  .forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero)))

private theorem aliasSourceIsNotLiteralTelescope : ¬ SortTelescope (.const ``HeaderAlias []) := by
  intro telescope
  cases telescope

private theorem genericNormalizationRetainsExactRecordedResult {env : VEnv} {universes : List Name}
    {virtual : VLCtx} {reader : Context} {body normalized : Expr} {value : Expr} {semantic : VExpr}
    (telescope : SortTelescope body)
    (actual : ((monadLift (TypeChecker.whnf (body.instantiate1 value)) : M Expr) reader) = .ok normalized)
    (translated : TrExpr env universes virtual (body.instantiate1 value) semantic) :
    ∃ normalizedSemantic, TrExprS env universes virtual normalized normalizedSemantic ∧
      env.IsDefEqU universes.length virtual.toCtx normalizedSemantic semantic :=
  telescope.normalizedTranslation actual translated

private theorem actualTraceNormalizationsFollowLiteralSource {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (literal : SortTelescope source) : IndexTraceNormalizationSupport env universes trace :=
  trace.normalizationSupport_ofSortTelescope literal

private theorem actualParentSourceTransport {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : ParentRecursorIndexTranslationSupport env universes stats types elimLevel
      original parent info current) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current :=
  source.translated envWF constants definitions indexOnly support

private theorem sameSourceContainsActualSemanticNativeHistory {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current) :
    ∃ entry normalized terminal finalIndex indexReader virtual semantic finalVirtual finalSemantic,
      ∃ trace : RecursorIndexTrace stats normalized 0 #[] entry
        terminal finalIndex info.indices indexReader,
      original.RecursorScopeFrame entry ∧
      ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
      TrLCtx env universes indexReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic ∧
      indexReader.RecursorScopeFrame current ∧
      finalIndex = 0 ∧ info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame _ _ history =>
    exact ⟨_, _, _, _, _, _, _, _, _, trace, entryFrame, initialNormalization,
      history, history.finalTranslation.1, history.finalTranslation.2,
      history.majorMotiveScope entryFrame.reserved types elimLevel parent info.major currentFrame,
      history.indexUnchanged, major, motive⟩

private theorem sameHistoryAllocationsReachObservedReader {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current) :
    ∃ (entry indexReader : Context) (steps : List BinderStep),
      info.indices.toList = steps.map BinderStep.value ∧
      (∀ step ∈ steps, step.role = .index) ∧
      BinderIndexAllocations indexReader entry.lctx.decls.size steps ∧
      BinderIndexAllocations current entry.lctx.decls.size steps := by
  cases source with
  | mk entryFrame _ _ _ _ currentFrame _ _ history =>
    have scope := history.majorMotiveScope entryFrame.reserved types elimLevel parent info.major currentFrame
    obtain ⟨steps, indices, roles, native, observed⟩ :=
      history.allocationsInContinuation entryFrame.reserved scope
    exact ⟨_, _, steps, by simpa only [Array.toList_empty, List.nil_append] using indices,
      roles, native, observed⟩

private theorem typedIndexHistoryDoesNotReplaceActualMajorMotive {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current) :
    RecursorFieldsDeclared current.lctx ((info.indices.push info.major).push info.motive) ∧
      ∃ declaration, current.lctx.find? info.major.fvarId! = some declaration ∧
        declaration.toExpr = info.major ∧ declaration.type = recursorMajorDomain stats parent info.indices :=
  ⟨source.toSource.declared, source.toSource.majorLookup⟩

private theorem observedParentIndexIdentifiersRemainDistinct {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current) :
    (info.indices.toList.map Expr.fvarId!).Nodup := source.indexIdsNodup

private theorem selectedActualIndexKeepsBothNativePositions {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current)
    (ordinal : Nat) (value : Expr) (selected : info.indices.toList[ordinal]? = some value) :
    ∃ (entry indexReader : Context) (steps : List BinderStep) (step : BinderStep),
      original.RecursorScopeFrame entry ∧ info.indices.toList = steps.map BinderStep.value ∧
      step ∈ steps ∧ step.role = .index ∧ step.value = value ∧
      BinderPositionedAt indexReader value step.name step.localDomain step.bi (entry.lctx.decls.size + ordinal) ∧
      BinderPositionedAt current value step.name step.localDomain step.bi (entry.lctx.decls.size + ordinal) :=
  source.indexPositioned ordinal value selected

private theorem sourceSurvivesActualMinorUpdate {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current)
    (minors : Array Expr) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original { info with minors } current :=
  source.withMinors minors

private theorem sourceSurvivesObservedReaderExtension {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current next : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current)
    (frame : current.RecursorScopeFrame next) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info next :=
  source.mono frame

private theorem parentFamiliesPreserveCardinalityAndSources {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current) :
    infos.size = types.size ∧ RecursorInfoIndexSources stats types elimLevel original infos current :=
  ⟨sources.1, sources.toSources⟩

private theorem parentFamiliesRetainOthersAfterMinorUpdate {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current)
    (parent : Nat) (minor : Expr) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original
      (infos.modify parent fun info => { info with minors := info.minors.push minor }) current :=
  sources.modifyMinors parent minor

private theorem parentFamiliesSurviveObservedReaderExtension {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current next : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current)
    (frame : current.RecursorScopeFrame next) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos next :=
  sources.mono frame

private theorem sameSourceSupportRequiresActualMajorMotiveAndReader {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current entry indexReader : Context} {parent finalIndex : Nat} {info : RecInfo}
    {normalized terminal : Expr}
    (support : ParentRecursorIndexTranslationSupport env universes stats types elimLevel
      original parent info current)
    (frame : original.RecursorScopeFrame entry)
    (actual : ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized)
    (trace : RecursorIndexTrace stats normalized 0 #[] entry terminal finalIndex info.indices indexReader)
    (major : info.major = .fvar ⟨indexReader.ngen.curr⟩)
    (motive : info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
      (recursorMajorDomain stats parent info.indices)).ngen.curr⟩)
    (observed : (recursorIndexContext
      (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices))
      (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel info.indices info.major
        (recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats parent info.indices)))).RecursorScopeFrame current) :
    ∃ virtual semantic, TrLCtx env universes entry.lctx virtual ∧
      TrExprS env universes virtual normalized semantic ∧
      IndexTraceAnnotationSupport env universes trace ∧
      IndexTraceNormalizationSupport env universes trace :=
  support entry normalized terminal finalIndex indexReader frame actual trace major motive observed

private theorem literalParentNeedsActualEntryCorrespondence {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {parent : Nat} {info : RecInfo}
    (telescope : SortTelescope types[parent]!.type)
    (entries : ∀ entry terminal finalIndex indexReader,
      original.RecursorScopeFrame entry →
      ∀ trace : RecursorIndexTrace stats types[parent]!.type 0 #[] entry
        terminal finalIndex info.indices indexReader,
      info.major = .fvar ⟨indexReader.ngen.curr⟩ →
      info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ →
      (recursorIndexContext
        (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices))
        (recursorMotiveName types parent) .default
        (recursorMotiveDomain elimLevel info.indices info.major
          (recursorIndexContext indexReader `t .default
            (recursorMajorDomain stats parent info.indices)))).RecursorScopeFrame current →
      ∃ virtual semantic, TrLCtx env universes entry.lctx virtual ∧
        TrExprS env universes virtual types[parent]!.type semantic ∧
        IndexTraceAnnotationSupport env universes trace) :
    ParentRecursorIndexTranslationSupport env universes stats types elimLevel original parent info current := by
  intro entry normalized terminal finalIndex indexReader frame actual trace major motive observed
  have sourceEquality := telescope.whnf entry normalized actual
  cases sourceEquality
  obtain ⟨virtual, semantic, correspondence, translated, annotations⟩ :=
    entries entry terminal finalIndex indexReader frame trace major motive observed
  exact ⟨virtual, semantic, correspondence, translated, annotations,
    trace.normalizationSupport_ofSortTelescope telescope⟩

private def capture (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) :
    M (Array RecInfo × Context) :=
  mkRecInfos stats types elimLevel fun infos => do return (infos, ← readThe Context)

private theorem actualCaptureSupportRequiresSuccessfulResult {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (support : (capture stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2)
    (infos : Array RecInfo) (current : Context)
    (success : capture stats types elimLevel reader = .ok (infos, current)) :
    RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader infos current :=
  support (infos, current) success

private theorem actualCaptureFailureCannotSupplySuccessfulReceipt
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : capture stats types elimLevel reader = .error failure) :
    ∀ infos current, capture stats types elimLevel reader ≠ .ok (infos, current) := by
  intro infos current success
  rw [failed] at success
  cases success

private theorem actualGetterHasTypedIndexHistoriesAtObservedReader {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (capture stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2) :
    (capture stats types elimLevel reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoIndexSources env universes stats types elimLevel reader result.1 result.2 :=
  mkRecInfos.getTranslatedIndexSources stats types elimLevel reader envWF constants definitions
    indexOnly readerWF reserved support

private theorem actualCpsDoesNotAssumeTypedFinalReader {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (capture stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoIndexSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedIndexSources stats types elimLevel next reader post envWF constants definitions
    indexOnly readerWF reserved support nextWF

private def prepare (types : Array InductiveType) : M (InductiveStats × Context) :=
  checkInductiveTypes 0 types fun stats => do
    let reader ← readThe Context
    let headers ← declareInductiveTypes stats 0 types 0 false
    let root := { reader with env := headers }
    checkConstructors types stats false root
    let constructors ← declareConstructors stats types false root
    return (stats, { root with env := constructors })

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "parent-translation actual native declaration disappeared after continuation extensions"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "parent-translation actual native declaration changed after continuation extensions"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "parent-translation callback changed reader fields outside local allocation scope"

private def checkIndexDeclarations (entry current : Context) (source : Expr) (indices : Array Expr) :
    MetaM Unit := do
  let mut opened := source
  let mut generator := entry.ngen
  for position in [:indices.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "parent-translation allocation history exhausted literal telescope"
    let value := indices[position]!
    let some declaration := current.lctx.find? value.fvarId!
      | throwError "parent-translation exact actual index declaration absent"
    unless value == Expr.fvar ⟨generator.curr⟩ && declaration.toExpr == value &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == entry.lctx.decls.size + position &&
        declaration.type == peelTypeAnnotations domain &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "parent-translation exact positioned/peeled/dependency native index receipt changed"
    opened := body.instantiate1 value
    generator := generator.next
  unless opened == Expr.sort (.succ .zero) do
    throwError "parent-translation actual terminal sort changed"

private def checkParent (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (info : RecInfo) (entry current : Context) : MetaM Context := do
  let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry)
    | throwError "parent-translation actual parent normalization failed"
  let .ok (indices, indexReader) := mkRecInfos.loopArgs1 stats normalized 0 #[] entry.fuel.inductiveFuel
      (fun indices => do return (indices, ← readThe Context)) entry
    | throwError "parent-translation actual per-parent callback failed"
  unless info.indices == indices && indexReader.lctx.decls.size == entry.lctx.decls.size + indices.size do
    throwError "parent-translation callback did not retain exact actual parent indices/index reader"
  checkIndexDeclarations entry indexReader normalized indices
  checkRetained indexReader current
  let majorReader := recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices)
  let expectedMajor := Expr.fvar ⟨indexReader.ngen.curr⟩
  let motiveDomain := recursorMotiveDomain (.succ .zero) indices expectedMajor majorReader
  let motiveReader := recursorIndexContext majorReader (recursorMotiveName types parent) .default motiveDomain
  unless info.major == expectedMajor && info.motive == Expr.fvar ⟨majorReader.ngen.curr⟩ do
    throwError "parent-translation major/motive do not use the same actual parent allocation reader"
  checkRetained motiveReader current
  return motiveReader

private def checkRegistration (stats : InductiveStats) (types : Array InductiveType)
    (root current : Context) (infos : Array RecInfo) : MetaM Unit := do
  let .ok (registered, registeredInfos, registeredReader) :=
    mkRecInfos.scopeRegistration stats types (.succ .zero) root.lparams false false root
    | throwError "parent-translation actual registration callback failed"
  unless registeredInfos.size == infos.size && registeredReader.lctx.decls.size == current.lctx.decls.size &&
      registeredReader.ngen.curr == current.ngen.curr do
    throwError "parent-translation registration replaced exact callback values/native allocation sequence"
  for parent in [:types.size] do
    unless registeredInfos[parent]!.indices == infos[parent]!.indices &&
        registeredInfos[parent]!.major == infos[parent]!.major &&
        registeredInfos[parent]!.motive == infos[parent]!.motive &&
        registeredInfos[parent]!.minors == infos[parent]!.minors do
      throwError "parent-translation registered exact parent fields changed"
    let name := mkRecName types[parent]!.name
    let some (.recInfo recursor) := registered.find? name
      | throwError "parent-translation registered recursor absent"
    unless recursor.numParams == 0 && recursor.numIndices == infos[parent]!.indices.size do
      throwError "parent-translation registered parent index metadata changed"
  checkRetained current registeredReader

private def checkFixture (reader : Context) (types : Array InductiveType) (expected : Array Nat)
    (hasMinors := false) : MetaM Unit := do
  let .ok (stats, root) := prepare types reader
    | throwError "parent-translation checked runtime fixture preparation failed"
  let .ok (infos, current) := capture stats types (.succ .zero) root
    | throwError "parent-translation actual infos/current-reader callback failed"
  unless stats.params.isEmpty && stats.nindices == expected && infos.size == types.size do
    throwError "parent-translation runtime zero-parameter/count boundary changed"
  let mut entry := root
  for parent in [:types.size] do
    unless infos[parent]!.indices.size == expected[parent]! do
      throwError "parent-translation runtime parent index count changed"
    entry ← checkParent stats types parent infos[parent]! entry current
  unless entry.lctx.decls.size ≤ current.lctx.decls.size do
    throwError "parent-translation final observed reader lost prefix allocations"
  if hasMinors then
    unless infos.any (fun info => !info.minors.isEmpty) && entry.lctx.decls.size < current.lctx.decls.size do
      throwError "parent-translation constructor pass failed to retain source under minor extensions"
  checkRegistration stats types root current infos

private def header (name : Name) (count : Nat) : InductiveType :=
  { name, type := (List.range count).foldr
      (fun _ body => .forallE `index (.const ``Nat []) body .implicit) (.sort (.succ .zero)), ctors := [] }

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let seeded := { reader with
    ngen := { namePrefix := `ParentTranslationSeed, idx := 29 }
    lctx := reader.lctx.mkLocalDecl ⟨`ParentTranslationOld⟩ `old (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨`ParentTranslationLet⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  checkFixture seeded #[] #[]
  checkFixture seeded #[header `ParentTranslationEmpty 0] #[0]
  checkFixture seeded #[header `ParentTranslationTwo 2] #[2]
  checkFixture seeded #[{ name := `ParentTranslationDependent, type := dependentTwo, ctors := [] }] #[2]
  checkFixture seeded #[header `ParentTranslationLeft 0,
    { name := `ParentTranslationMiddle, type := dependentTwo, ctors := [] },
    header `ParentTranslationRight 3] #[0, 2, 3]
  checkFixture seeded #[{ name := `ParentTranslationAlias, type := .const ``HeaderAlias [], ctors := [] }] #[1]
  let recursive : Array InductiveType := #[{
    name := `ParentTranslationRecursive
    type := .sort (.succ .zero)
    ctors := [
      { name := `ParentTranslationRecursive.zero, type := .const `ParentTranslationRecursive [] },
      { name := `ParentTranslationRecursive.step
        type := .forallE `field (.const `ParentTranslationRecursive [])
          (.const `ParentTranslationRecursive []) .default }] }]
  checkFixture seeded recursive #[0] true
  let indexed : Array InductiveType := #[{
    name := `ParentTranslationIndexed
    type := .forallE `index (.const ``Nat []) (.sort (.succ .zero)) .implicit
    ctors := [{
      name := `ParentTranslationIndexed.mk
      type := .forallE `index (.const ``Nat [])
        (.app (.const `ParentTranslationIndexed []) (.bvar 0)) .default }] }]
  checkFixture seeded indexed #[1] true
  let aliasSource := Expr.const ``HeaderAlias []
  let .ok normalizedAlias := ((monadLift (TypeChecker.whnf aliasSource) : M Expr) seeded)
    | throwError "parent-translation generic alias normalization failed"
  unless normalizedAlias != aliasSource do
    throwError "parent-translation generic normalization boundary no longer reduces its actual source"
  logInfo "parent-translation runtime: eight checked callbacks/registrations; ten parents; eleven exact indices; retained constructor/minor extensions; one nonliteral normalized source"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "parent-translation unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "parent-translation audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "parent-translation module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let environment ← getEnv
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.defeqDFC', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas)] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? moduleName do
      throwError "parent-translation inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "parent-translation inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    logInfo m!"pinned inherited parent foundation: {name} from {moduleName}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "parent-translation native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "parent-translation native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

private def auditRegistrationFoundation : MetaM Unit := do
  let environment ← getEnv
  unless environment.getModuleIdxFor? ``mkRecInfos.registeredIndexSources ==
      environment.getModuleIdx? `Lean4Lean.Verify.RecursorInfoIndices do
    throwError "parent-translation prior registration foundation provenance changed"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let registration := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``PersistentHashMap.findAux_isSome]
  let axioms ← collectAxioms ``mkRecInfos.registeredIndexSources
  unless axioms.contains ``PersistentHashMap.findAux_isSome && !axioms.contains ``sorryAx do
    throwError "parent-translation prior registration dependency boundary changed"
  auditDeclaration ``mkRecInfos.registeredIndexSources (logical ++ registration)
  logInfo "pinned prior registration-only hash lookup interface; inherited registration foundation remains admission-free"

#print axioms genericNormalizationRetainsExactRecordedResult
#print axioms scopeFrameAloneDoesNotGiveTranslatedReader
#print axioms sameSourceContainsActualSemanticNativeHistory
#print axioms sameHistoryAllocationsReachObservedReader
#print axioms actualGetterHasTypedIndexHistoriesAtObservedReader
#print axioms mkRecInfos.registeredTranslatedIndexSources
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``actualParentCounterRequiresZeroParameters, ``nonemptyParametersExcludeParentIndexOnlyTransport,
      ``zeroParameterBoundIsNotAnArbitraryPositiveCounter, ``dependentTwoTelescope,
      ``aliasSourceIsNotLiteralTelescope,
      ``actualCaptureFailureCannotSupplySuccessfulReceipt,
      ``capture, ``prepare, ``checkRetained, ``checkIndexDeclarations, ``checkParent,
      ``checkRegistration, ``checkFixture, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``genericNormalizationRetainsExactRecordedResult, ``actualTraceNormalizationsFollowLiteralSource] do
    auditDeclaration name native
  for name in [``scopeFrameAloneDoesNotGiveTranslatedReader, ``arbitraryScopeEntryCorrespondenceWouldBeImpossible] do
    auditDeclaration name native
  for name in [``actualParentSourceTransport, ``sameSourceContainsActualSemanticNativeHistory,
      ``sameHistoryAllocationsReachObservedReader, ``typedIndexHistoryDoesNotReplaceActualMajorMotive,
      ``observedParentIndexIdentifiersRemainDistinct, ``selectedActualIndexKeepsBothNativePositions,
      ``sourceSurvivesActualMinorUpdate, ``sourceSurvivesObservedReaderExtension,
      ``parentFamiliesPreserveCardinalityAndSources, ``parentFamiliesRetainOthersAfterMinorUpdate,
      ``parentFamiliesSurviveObservedReaderExtension, ``literalParentNeedsActualEntryCorrespondence,
      ``sameSourceSupportRequiresActualMajorMotiveAndReader, ``actualCaptureSupportRequiresSuccessfulResult,
      ``actualGetterHasTypedIndexHistoriesAtObservedReader, ``actualCpsDoesNotAssumeTypedFinalReader] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  for moduleName in [`Lean4Lean.Verify.InductiveRecursorIndexTranslation,
      `Lean4Lean.Verify.InductiveRecursorIndexTranslationFacts] do
    auditModule moduleName native
  auditModule `Lean4Lean.Verify.InductiveRecursorIndexTranslationCPS
    (native ++ [``PersistentHashMap.findAux_isSome])
  auditFoundations (nativeInterfaces ++ [``PersistentHashMap.findAux_isSome])
  auditRegistrationFoundation
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader

end InductiveRecursorIndexTranslationTest
