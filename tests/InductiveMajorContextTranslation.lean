import Lean4Lean.Verify.InductiveMajorContextTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveMajorContextTranslationTest

abbrev MajorHeaderAlias := Nat → Type

private theorem parentApplicationNeedsZeroParameters (stats : InductiveStats) :
    stats.params.size ≤ 0 ↔ stats.params.size = 0 := by omega

private theorem nonemptyParametersDoNotGiveParentIndexOnlyApplication (stats : InductiveStats)
    (nonempty : 0 < stats.params.size) : ¬ stats.params.size ≤ 0 := by omega

private theorem metadataDoesNotPeelMajorHead (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem unaryAnnotationMajorHeadReallyPeels (identifier : FVarId) :
    peelTypeAnnotations (.app (.const ``outParam [.succ .zero]) (.fvar identifier)) =
      .fvar identifier := by simp [peelTypeAnnotations]

private theorem unaryAnnotationHeadCannotClaimRawApplicationEquality (identifier : FVarId) :
    peelTypeAnnotations (.app (.const ``outParam [.succ .zero]) (.fvar identifier)) ≠
      .app (.const ``outParam [.succ .zero]) (.fvar identifier) := by
  simp [peelTypeAnnotations]

private theorem binaryAnnotationMajorHeadReallyPeels (carrier extra : FVarId) :
    peelTypeAnnotations (.app (.app (.const ``optParam [.succ .zero]) (.fvar carrier))
      (.fvar extra)) = .fvar carrier := by simp [peelTypeAnnotations]

private theorem overappliedAnnotationDoesNotPeel (carrier extra third : Expr) :
    peelTypeAnnotations (.app (.app (.app (.const ``optParam [.succ .zero]) carrier) extra) third) =
      .app (.app (.app (.const ``optParam [.succ .zero]) carrier) extra) third := rfl

private theorem syntacticallyNonuniformAnnotationRemainsOutsideUniformSupport (source : Expr) :
    ¬ UniformAnnotationUniverse []
      (.app (.const ``outParam [.max .zero (.succ .zero)]) source) (.succ .zero) := by
  simp [UniformAnnotationUniverse, VLevel.ofLevel]

private theorem rawDomainEqualityNeedsAnExplicitHeadPremise (stats : InductiveStats)
    (parent : Nat) (indices : Array Expr)
    (unpeeled : peelTypeAnnotations (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) =
      mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) :
    recursorMajorDomain stats parent indices = mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices :=
  unpeeled

private theorem actualApplicationPushPreservesInitialPrefix (head value : Expr) (initialIndices : Array Expr) :
    mkAppN head (initialIndices.push value) = .app (mkAppN head initialIndices) value :=
  mkAppN_indexPush head value initialIndices

private theorem zeroParametersKeepTheActualConstantHead (head : Expr) : mkAppN head #[] = head := rfl

private theorem semanticApplicationUsesExactPeeledDependencyContext
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semanticDomain bodySemantic peeled : VExpr} {level : VLevel}
    (opening : PeeledIndexOpening env universes reader virtual name domain body bi
      semanticDomain bodySemantic level peeled)
    (envWF : env.WF) {value : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual value semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue
      (.forallE semanticDomain bodySemantic)) :
    TrExprS env universes
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
        (.app value (.fvar ⟨reader.ngen.curr⟩)) (.app semanticValue.lift (.bvar 0)) ∧
      env.HasType universes.length
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
        (.app semanticValue.lift (.bvar 0)) bodySemantic :=
  opening.application envWF translated typed

private theorem actualApplicationTransportUsesTheSameNormalizedHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) {head : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual (mkAppN head indices) semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue semantic) :
    ∃ finalValue, TrExprS env universes finalVirtual (mkAppN head finalIndices) finalValue ∧
      env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic :=
  history.application envWF translated typed

private theorem exactTerminalSortGivesTheActualMajorApplicationType
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) {head : Expr} {semanticValue : VExpr} {level : VLevel}
    (translated : TrExprS env universes virtual (mkAppN head indices) semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue semantic)
    (terminalSort : finalSemantic = .sort level) :
    ∃ finalValue, TrExprS env universes finalVirtual (mkAppN head finalIndices) finalValue ∧
      env.HasType universes.length finalVirtual.toCtx finalValue (.sort level) := by
  simpa only [terminalSort] using history.application envWF translated typed

private theorem actualMajorOpeningRetainsHeadAlignmentAndUniformSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context} {virtual finalVirtual : VLCtx}
    {semantic finalSemantic headSemantic : VExpr} {level : VLevel}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
    (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
    (terminalSort : finalSemantic = .sort level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled,
      RecursorMajorOpening env universes stats parent indices indexReader finalVirtual
        rawSemantic peeled level :=
  history.majorOpening envWF constants definitions indexOnly reserved headTranslated headTyped
    terminalSort uniform

private theorem majorReceiptUsesPeeledDependenciesNotAnEmptyList
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level) :
    TrLCtx env universes
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx
      ((some (⟨reader.ngen.curr⟩, (recursorMajorDomain stats parent indices).fvarsList),
        .vlam peeled) :: virtual) :=
  opening.2.2.2.2.2.1

private theorem majorReceiptKeepsTheRawAndPeeledSemanticsSeparate
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level) :
    TrExprS env universes virtual
        (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) rawSemantic ∧
      TrExprS env universes virtual (recursorMajorDomain stats parent indices) peeled ∧
      env.IsDefEq universes.length virtual.toCtx rawSemantic peeled (.sort level) ∧
      env.HasType universes.length virtual.toCtx peeled (.sort level) :=
  ⟨opening.1, opening.2.2.1, opening.2.2.2.1, opening.2.2.2.2.1⟩

private theorem perParentMajorRequiresResultLocalHeadSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : ParentRecursorMajorTranslationSupport env universes stats types elimLevel
      original parent info current) :
    TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current :=
  source.majorTranslated envWF constants definitions indexOnly support

private theorem majorSourceKeepsTheSameActualIndexSource
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current :=
  source.toIndexSource

private theorem sourceTranslationIsAtTheExactMajorReaderNotCurrent
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current) :
    ∃ indexReader virtual peeled,
      info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      TrLCtx env universes
        (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices)).lctx
        (recursorMajorVirtualContext stats parent info.indices indexReader virtual peeled) := by
  obtain ⟨indexReader, virtual, _, peeled, _, major, _, opening⟩ := source.majorReaderReceipt
  exact ⟨indexReader, virtual, peeled, major, opening.2.2.2.2.2.1⟩

private theorem sameMajorSourceRetainsTheActualHeaderAndHeadTyping
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current) :
    ∃ (entry indexReader : Context) (normalized terminal : Expr) (finalIndex : Nat)
      (virtual finalVirtual : VLCtx) (semantic finalSemantic headSemantic rawSemantic peeled : VExpr)
      (level : VLevel),
      ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
      ∃ trace : RecursorIndexTrace stats normalized 0 #[] entry terminal finalIndex info.indices indexReader,
        TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
        TrExprS env universes virtual stats.indConsts[parent]! headSemantic ∧
        env.HasType universes.length virtual.toCtx headSemantic semantic ∧
        finalSemantic = .sort level ∧
        RecursorMajorOpening env universes stats parent info.indices indexReader finalVirtual
          rawSemantic peeled level := by
  cases source with
  | mk _ normalization trace _ _ _ _ _ history headTranslated headTyped finalSort opening =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, normalization, trace,
      history, headTranslated, headTyped, finalSort, opening⟩

private theorem parentFamiliesRequireActualCapturedMajorSupports
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : RecursorMajorSourcesTranslationSupport env universes stats types elimLevel original infos current) :
    TranslatedRecursorInfoMajorSources env universes stats types elimLevel original infos current :=
  sources.majorTranslated envWF constants definitions indexOnly support

private theorem majorFamiliesRetainTheirActualIndexFamilies
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoMajorSources env universes stats types elimLevel original infos current) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current :=
  sources.toIndexSources

private theorem sameMajorSourceKeepsActualIndexIdentifiersDistinct
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current) :
    (info.indices.toList.map Expr.fvarId!).Nodup := source.toIndexSource.indexIdsNodup

private def captureMajorOnly (stats : InductiveStats) (parent : Nat) (indices : Array Expr) :
    M (Expr × Context) :=
  withLocalDecl `t .default (recursorMajorDomain stats parent indices) fun major => do
    return (major, ← readThe Context)

private theorem actualWithLocalDeclCallbackReceivesTheSameHistoryOpening
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context} {virtual finalVirtual : VLCtx}
    {semantic finalSemantic headSemantic : VExpr} {level : VLevel}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
    (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
    (terminalSort : finalSemantic = .sort level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    (captureMajorOnly stats parent indices indexReader).WF fun result =>
      result.1 = .fvar ⟨indexReader.ngen.curr⟩ ∧
      result.2 = recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices) ∧
      ∃ rawSemantic peeled,
        RecursorMajorOpening env universes stats parent indices indexReader finalVirtual
          rawSemantic peeled level := by
  obtain ⟨rawSemantic, peeled, opening⟩ := history.majorOpening envWF constants definitions
    indexOnly reserved headTranslated headTyped terminalSort uniform
  intro result success
  obtain rfl := Except.ok.inj success
  exact ⟨rfl, rfl, rawSemantic, peeled, opening⟩

private theorem actualConstantHeadNeedsItsStoredHeaderAlignment
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {name : Name} {nativeLevels : List Level} {semanticLevels : List VLevel}
    {constant : VConstant} {headerSemantic : VExpr}
    (envWF : env.WF) (contextWF : OnCtx virtual.toCtx (env.IsType universes.length))
    (lookup : env.constants name = some constant)
    (levels : nativeLevels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : nativeLevels.length = constant.uvars)
    (alignment : env.IsDefEqU universes.length virtual.toCtx
      (constant.type.instL semanticLevels) headerSemantic) :
    TrExprS env universes virtual (.const name nativeLevels) (.const name semanticLevels) ∧
      env.HasType universes.length virtual.toCtx (.const name semanticLevels) headerSemantic :=
  translatedConstantHeader envWF contextWF lookup levels arity alignment

private theorem constantApplicationDerivesTypingFromTheSameHeaderLookup
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index #[] reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (readerWF : reader.lctx.WF)
    {name : Name} {nativeLevels : List Level} {semanticLevels : List VLevel} {constant : VConstant}
    (lookup : env.constants name = some constant)
    (levels : nativeLevels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : nativeLevels.length = constant.uvars)
    (alignment : env.IsDefEqU universes.length virtual.toCtx
      (constant.type.instL semanticLevels) semantic) :
    ∃ finalValue, TrExprS env universes finalVirtual (mkAppN (.const name nativeLevels) finalIndices) finalValue ∧
      env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic :=
  history.constantApplication envWF readerWF lookup levels arity alignment

private theorem actualWithLocalDeclPassesTheExactTypedMajorReader {ResultType : Type}
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : TrLCtx env universes
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx
      (recursorMajorVirtualContext stats parent indices reader virtual peeled) →
      (next (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))).WF post) :
    (withLocalDecl `t .default (recursorMajorDomain stats parent indices) next reader).WF post :=
  withLocalDecl.majorTranslation opening next post nextWF

private def captureSources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) :
    M (Array RecInfo × Context) :=
  mkRecInfos stats types elimLevel fun infos => do return (infos, ← readThe Context)

private theorem failedActualCaptureCannotProvideMajorSupport (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : captureSources stats types elimLevel reader = .error failure) :
    ∀ infos current, captureSources stats types elimLevel reader ≠ .ok (infos, current) := by
  intro infos current success
  rw [failed] at success
  cases success

private theorem actualGetterSupportIsConsumedOnlyOnTheSameSuccessfulCapture
    {env : VEnv} {universes : List Name} (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2)
    (infos : Array RecInfo) (current : Context)
    (actual : captureSources stats types elimLevel reader = .ok (infos, current)) :
    RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader infos current ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader infos current :=
  support (infos, current) actual

private theorem actualGetterRetainsMajorReaderCorrespondenceNotCurrentCorrespondence
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2) :
    (captureSources stats types elimLevel reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoMajorSources env universes stats types elimLevel reader result.1 result.2 :=
  mkRecInfos.getTranslatedMajorSources stats types elimLevel reader envWF constants definitions indexOnly
    readerWF reserved support

private theorem actualCpsRetainsSameCapturedSupportsAndSourceReaders {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoMajorSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedMajorSources stats types elimLevel next reader post envWF constants definitions
    indexOnly readerWF reserved support nextWF

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def dependentHeader : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private theorem dependentHeaderIsLiteral : SortTelescope dependentHeader :=
  .forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero)))

private theorem aliasSourceRequiresActualNormalization : ¬ SortTelescope (.const ``MajorHeaderAlias []) := by
  intro literal
  cases literal

private def captureMajor (stats : InductiveStats) (source : Expr) (initialIndices : Array Expr) :
    M (Array Expr × Context × Expr × Context) := do
  let reader ← readThe Context
  mkRecInfos.loopArgs1 stats source 0 initialIndices reader.fuel.inductiveFuel fun indices => do
    let indexReader ← readThe Context
    withLocalDecl `t .default (recursorMajorDomain stats 0 indices) fun major => do
      return (indices, indexReader, major, ← readThe Context)

private def plainHeader (count : Nat) : Expr :=
  (List.range count).foldr
    (fun _ body => .forallE `index (.const ``Nat []) body .implicit) (.sort (.succ .zero))

private def fixtureStats (reader : Context) (head : Expr) : InductiveStats :=
  { lctx := reader.lctx, levels := [], resultLevel := .succ .zero, indConsts := #[head],
    params := #[], isNotZero := true }

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "major-translation prior declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "major-translation prior declaration/value/dependency changed"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive &&
      before.fuel.inductiveFuel == after.fuel.inductiveFuel && before.fuel.whnf == after.fuel.whnf &&
      before.fuel.whnfEager == after.fuel.whnfEager && before.fuel.lazyDelta == after.fuel.lazyDelta &&
      before.fuel.etaExpand == after.fuel.etaExpand && before.fuel.recDepth == after.fuel.recDepth do
    throwError "major-translation callback changed nonallocation reader fields"

private def checkIndexHistory (entry current : Context) (source : Expr) (initialIndices indices : Array Expr) :
    MetaM Unit := do
  unless indices[:initialIndices.size].toArray == initialIndices do
    throwError "major-translation mkAppN history lost initial index-array prefix"
  let mut opened := source
  let mut generator := entry.ngen
  for ordinal in [:indices.size - initialIndices.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "major-translation actual index history exhausted source"
    let value := indices[initialIndices.size + ordinal]!
    let some declaration := current.lctx.find? value.fvarId!
      | throwError "major-translation same-history native index absent"
    unless value == Expr.fvar ⟨generator.curr⟩ && declaration.toExpr == value &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == entry.lctx.decls.size + ordinal &&
        declaration.type == peelTypeAnnotations domain &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "major-translation same-history positioned/peeled/dependency index mismatch"
    opened := body.instantiate1 value
    generator := generator.next
  unless opened == Expr.sort (.succ .zero) do
    throwError "major-translation terminal literal sort changed"

private def checkMajorCallback (reader : Context) (source : Expr) (head : Expr)
    (initialIndices : Array Expr) (expectedNew : Nat) (expectPeeling : Bool) : MetaM Unit := do
  let stats := fixtureStats reader head
  let .ok (indices, indexReader, major, majorReader) := captureMajor stats source initialIndices reader
    | throwError "major-translation actual index/withLocalDecl callback failed"
  unless indices.size == initialIndices.size + expectedNew &&
      indexReader.lctx.decls.size == reader.lctx.decls.size + expectedNew &&
      majorReader.lctx.decls.size == indexReader.lctx.decls.size + 1 &&
      majorReader.ngen.curr == indexReader.ngen.next.curr &&
      major == Expr.fvar ⟨indexReader.ngen.curr⟩ do
    throwError "major-translation callback exact index/major allocation sequence changed"
  checkIndexHistory reader indexReader source initialIndices indices
  checkRetained reader indexReader
  checkRetained indexReader majorReader
  let rawDomain := mkAppN (mkAppN stats.indConsts[0]! stats.params) indices
  let domain := recursorMajorDomain stats 0 indices
  unless rawDomain == mkAppN head indices && (domain != rawDomain) == expectPeeling do
    throwError "major-translation explicit raw constant-head/annotation-peeling boundary changed"
  let some declaration := majorReader.lctx.find? major.fvarId!
    | throwError "major-translation exact pushed major reader lacks major"
  unless declaration.toExpr == major && declaration.type == domain &&
      declaration.userName == `t && declaration.binderInfo == .default &&
      declaration.index == indexReader.lctx.decls.size && declaration.deps == domain.fvarsList &&
      declaration.value? (allowNondep := true) == none do
    throwError "major-translation actual callback major domain/dependency/value/position changed"
  let motiveReader := recursorIndexContext majorReader `motive .default (.sort (.succ .zero))
  unless motiveReader.lctx.decls.size != majorReader.lctx.decls.size do
    throwError "major-translation major reader accidentally conflated with motive/current reader"
  checkRetained majorReader motiveReader

private def checkActualParentCallback (reader : Context) (source : Expr) (head : Expr) : MetaM Unit := do
  let stats := fixtureStats reader head
  let types : Array InductiveType := #[{ name := `MajorTranslationParent, type := source, ctors := [] }]
  let .ok (indices, indexReader, major, majorReader) := captureMajor stats source #[] reader
    | throwError "major-translation same-history comparison callback failed"
  let .ok (infos, current) := mkRecInfos.loopInd1 stats types (.succ .zero) 0 #[]
      (fun infos => do return (infos, ← readThe Context)) reader
    | throwError "major-translation actual zero-parameter parent callback failed"
  unless stats.params.isEmpty && infos.size == 1 && infos[0]!.indices == indices &&
      infos[0]!.major == major && infos[0]!.motive == Expr.fvar ⟨majorReader.ngen.curr⟩ &&
      current.lctx.decls.size == majorReader.lctx.decls.size + 1 &&
      current.ngen.curr == majorReader.ngen.next.curr do
    throwError "major-translation actual parent changed same indices/major/native-reader sequence"
  checkIndexHistory reader indexReader source #[] indices
  checkRetained indexReader majorReader
  checkRetained majorReader current
  let some declaration := current.lctx.find? major.fvarId!
    | throwError "major-translation actual parent discarded its exact major declaration"
  unless declaration.type == recursorMajorDomain stats 0 indices &&
      declaration.deps == (recursorMajorDomain stats 0 indices).fvarsList &&
      declaration.index == indexReader.lctx.decls.size do
    throwError "major-translation actual parent lost exact major domain/dependencies/position"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `MajorTranslationOld
  let oldLet := FVarId.mk `MajorTranslationLet
  let seeded := { reader with
    ngen := { namePrefix := `MajorTranslationSeed, idx := 31 }
    lctx := reader.lctx.mkLocalDecl carrier `old (.const ``Nat []) .implicit
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 11)) false }
  let head := Expr.const `MajorTranslationHead []
  for count in [:4] do
    checkMajorCallback seeded (plainHeader count) head #[] count false
    checkMajorCallback seeded (plainHeader count) head #[.fvar carrier, .fvar oldLet] count false
  checkMajorCallback seeded dependentHeader head #[] 2 false
  checkMajorCallback seeded dependentHeader (.mdata {} head) #[] 2 false
  let nonuniformDomain := Expr.app
    (.const ``outParam [.max .zero (.succ .zero)]) (.const ``Nat [])
  checkMajorCallback seeded
    (.forallE `nonuniform nonuniformDomain (.sort (.succ .zero)) .default) head #[] 1 false
  checkMajorCallback seeded
    (.forallE `metadata (.mdata {} nonuniformDomain) (.sort (.succ .zero)) .default) head #[] 1 false
  checkMajorCallback seeded (plainHeader 1) (.const ``outParam [.succ .zero]) #[] 1 true
  checkMajorCallback seeded (plainHeader 1) (.const ``semiOutParam [.succ .zero]) #[] 1 true
  checkMajorCallback seeded (plainHeader 2) (.const ``optParam [.succ .zero]) #[] 2 true
  checkMajorCallback seeded (plainHeader 2) (.const ``autoParam [.succ .zero]) #[] 2 true
  checkMajorCallback seeded (plainHeader 3) (.const ``optParam [.succ .zero]) #[] 3 false
  let aliasSource := Expr.const ``MajorHeaderAlias []
  let .ok normalized := ((monadLift (TypeChecker.whnf aliasSource) : M Expr) seeded)
    | throwError "major-translation actual nonliteral source normalization failed"
  unless normalized != aliasSource do
    throwError "major-translation source/normalized-header alignment collapsed"
  checkMajorCallback seeded normalized head #[] 1 false
  checkActualParentCallback seeded (plainHeader 0) head
  checkActualParentCallback seeded dependentHeader head
  checkActualParentCallback seeded (plainHeader 1) (.const ``outParam [.succ .zero])
  logInfo "major-translation runtime: eighteen allocation-only opening callbacks and three actual parent callbacks; prefixes, dependent peeled domains, metadata/nonuniform annotations and annotation-name heads; exact major reader distinct from motive/current reader"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "major-translation unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "major-translation audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "major-translation module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let environment ← getEnv
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrProj.weak', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.defeqDFC', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas),
      (``VEnv.HasType.defeqU_r, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? moduleName do
      throwError "major-translation inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "major-translation inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    logInfo m!"pinned inherited major foundation: {name} from {moduleName}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "major-translation native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "major-translation native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

#print axioms unaryAnnotationHeadCannotClaimRawApplicationEquality
#print axioms semanticApplicationUsesExactPeeledDependencyContext
#print axioms actualApplicationTransportUsesTheSameNormalizedHistory
#print axioms actualMajorOpeningRetainsHeadAlignmentAndUniformSupport
#print axioms sameMajorSourceRetainsTheActualHeaderAndHeadTyping
#print axioms actualWithLocalDeclCallbackReceivesTheSameHistoryOpening
#print axioms actualConstantHeadNeedsItsStoredHeaderAlignment
#print axioms actualGetterRetainsMajorReaderCorrespondenceNotCurrentCorrespondence
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let applicationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := ``Expr.instantiate1_eq :: applicationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``parentApplicationNeedsZeroParameters,
      ``nonemptyParametersDoNotGiveParentIndexOnlyApplication, ``metadataDoesNotPeelMajorHead,
      ``unaryAnnotationMajorHeadReallyPeels, ``unaryAnnotationHeadCannotClaimRawApplicationEquality,
      ``binaryAnnotationMajorHeadReallyPeels, ``overappliedAnnotationDoesNotPeel,
      ``syntacticallyNonuniformAnnotationRemainsOutsideUniformSupport,
      ``rawDomainEqualityNeedsAnExplicitHeadPremise, ``dependentHeaderIsLiteral,
      ``actualApplicationPushPreservesInitialPrefix, ``zeroParametersKeepTheActualConstantHead,
      ``aliasSourceRequiresActualNormalization, ``unary, ``dependentHeader, ``captureMajor,
      ``captureMajorOnly,
      ``captureSources, ``failedActualCaptureCannotProvideMajorSupport,
      ``plainHeader, ``fixtureStats, ``checkRetained, ``checkIndexHistory,
      ``checkMajorCallback, ``checkActualParentCallback, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``semanticApplicationUsesExactPeeledDependencyContext,
      ``actualApplicationTransportUsesTheSameNormalizedHistory,
      ``exactTerminalSortGivesTheActualMajorApplicationType] do
    auditDeclaration name (logical ++ [``sorryAx] ++ applicationInterfaces)
  for name in [``actualMajorOpeningRetainsHeadAlignmentAndUniformSupport,
      ``majorReceiptUsesPeeledDependenciesNotAnEmptyList, ``majorReceiptKeepsTheRawAndPeeledSemanticsSeparate,
      ``perParentMajorRequiresResultLocalHeadSupport, ``majorSourceKeepsTheSameActualIndexSource,
      ``sourceTranslationIsAtTheExactMajorReaderNotCurrent,
      ``sameMajorSourceRetainsTheActualHeaderAndHeadTyping,
      ``parentFamiliesRequireActualCapturedMajorSupports, ``majorFamiliesRetainTheirActualIndexFamilies,
      ``sameMajorSourceKeepsActualIndexIdentifiersDistinct,
      ``actualWithLocalDeclCallbackReceivesTheSameHistoryOpening,
      ``actualConstantHeadNeedsItsStoredHeaderAlignment,
      ``constantApplicationDerivesTypingFromTheSameHeaderLookup,
      ``actualWithLocalDeclPassesTheExactTypedMajorReader,
      ``actualGetterSupportIsConsumedOnlyOnTheSameSuccessfulCapture,
      ``actualGetterRetainsMajorReaderCorrespondenceNotCurrentCorrespondence,
      ``actualCpsRetainsSameCapturedSupportsAndSourceReaders] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveIndexApplicationTranslation
    (logical ++ [``sorryAx] ++ applicationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveMajorContextTranslation
    (logical ++ [``sorryAx] ++ applicationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveMajorContextTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader

end InductiveMajorContextTranslationTest
