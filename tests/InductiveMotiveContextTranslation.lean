import Lean4Lean.Verify.InductiveMotiveContextTranslationCPS
import Lean4Lean.Verify.InductiveMotiveContextTranslation
import Lean4Lean.Verify.InductiveMotiveBindingFacts
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveMotiveContextTranslationTest

private theorem parentMotiveNeedsTheActualZeroParameterBoundary (stats : InductiveStats) :
    stats.params.size ≤ 0 ↔ stats.params.size = 0 := by omega

private theorem nonemptyParametersRemainOutsideTheParentIndexOnlyReceipt (stats : InductiveStats)
    (nonempty : 0 < stats.params.size) : ¬ stats.params.size ≤ 0 := by omega

private theorem forallMotiveHeadIsNotATypeAnnotation (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (.forallE name domain body bi) = .forallE name domain body bi := rfl

private theorem metadataMotiveHeadIsNotPeeled (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem annotationPeelingDoesNotPreserveEveryRawMajorHead (identifier : FVarId) :
    peelTypeAnnotations (.app (.const ``outParam [.succ .zero]) (.fvar identifier)) ≠
      .app (.const ``outParam [.succ .zero]) (.fvar identifier) := by
  simp [peelTypeAnnotations]

private theorem nonuniformAnnotationIsNotUniformMotiveDomainSupport (source : Expr) :
    ¬ UniformAnnotationUniverse []
      (.app (.const ``outParam [.max .zero (.succ .zero)]) source) (.succ .zero) := by
  simp [UniformAnnotationUniverse, VLevel.ofLevel]

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def dependentHeader : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private theorem dependentHeaderIsLiteral : SortTelescope dependentHeader :=
  .forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero)))

private theorem modelForallMatchesTheExactNativeMotiveAbstraction
    {env : VEnv} {universes : List Name} {model : TypeChecker.MLCtx}
    (modelWF : model.WF env universes) {count : Nat} (bound : count ≤ model.length)
    {array : Array Expr} {body : Expr}
    (selection : array.toList.reverse = (model.fvarRevList count bound).map .fvar)
    (closed : body.looseBVarRange' = 0) :
    model.lctx.mkForall array body = model.mkForall count bound body :=
  modelWF.mkForall_eq count bound selection closed

private theorem motiveHistoryBuildsOnlyAnActualModelExtension
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ (finalModel : TypeChecker.MLCtx) (ids : List FVarId),
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar :=
  history.mixedContext model modelWF modelNative modelVirtual reserved

private theorem modelExtensionReceiptRetainsExactMotivePrefix
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    ∃ bound : ids.length ≤ final.length,
      final.dropN ids.length bound = initial ∧
      final.fvarRevList ids.length bound = ids.reverse ∧
      VLCtx.FVLift initial.vlctx final.vlctx 0 ids.length 0 :=
  ⟨extension.bound, extension.drop_eq, extension.selection, extension.weakening⟩

private theorem mappedEliminationUniverseDerivesTypedModelAbstraction
    {env : VEnv} {universes : List Name} {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) (envWF : env.WF)
    (modelWF : final.WF env universes) {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ semantic level,
      TrExprS env universes final.vlctx
        (final.mkForall ids.length extension.bound (.sort elimLevel)) semantic ∧
      env.HasType universes.length final.vlctx.toCtx semantic (.sort level) :=
  extension.typedAbstraction envWF modelWF mapped

private theorem exactNativeMotiveBindingComesFromTheSameSelectedHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel}
    {initial model : TypeChecker.MLCtx} {ids : List FVarId}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    (extension : IndexMLCtxExtension initial ids model) (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (array : indices.toList = ids.map Expr.fvar) (elimLevel : Level) :
    recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)) =
    (recursorMajorMLCtx stats parent indices reader model peeled).mkForall (ids.length + 1)
      (Nat.add_le_add_right extension.bound 1) (.sort elimLevel) :=
  opening.motiveBindingEquation extension modelWF modelNative modelVirtual reserved array elimLevel

private theorem sameHistoryDerivesActualMotiveDomainTypingAtTheMajorReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {source terminal : Expr} {index finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    {rawSemantic peeled : VExpr} {majorLevel : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices indexReader
      finalVirtual rawSemantic peeled majorLevel)
    (envWF : env.WF) {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ motiveSemantic motiveLevel,
      RecursorMotiveDomainTranslation env universes stats parent indices indexReader
        finalVirtual peeled elimLevel motiveSemantic motiveLevel :=
  history.motiveDomainTranslation opening envWF model modelWF modelNative modelVirtual reserved mapped

private theorem modelForallTopHeadDoesNotNeedAnAnnotationUniverseRestriction
    {initial model : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids model)
    (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (model.mkForall ids.length extension.bound (.forallE name domain body bi)) =
      model.mkForall ids.length extension.bound (.forallE name domain body bi) :=
  extension.peelForall name domain body bi

private theorem majorOpeningBuildsExactMajorThenMotiveModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorMajorMLCtx stats parent indices reader model peeled).WF env universes ∧
      (recursorMajorMLCtx stats parent indices reader model peeled).lctx =
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx ∧
      (recursorMajorMLCtx stats parent indices reader model peeled).vlctx =
        recursorMajorVirtualContext stats parent indices reader virtual peeled :=
  opening.mixedContext model modelWF modelNative modelVirtual reserved

private theorem nilModelSupportsOnlyItsExactEmptyReaders :
    (TypeChecker.MLCtx.nil : TypeChecker.MLCtx).lctx = ({} : LocalContext) ∧
      (TypeChecker.MLCtx.nil : TypeChecker.MLCtx).vlctx = [] := ⟨rfl, rfl⟩

private theorem motiveBaseModelGivesTheExactNativeAndSemanticReader
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual) :
    TrLCtx env universes reader.lctx virtual := by
  simpa only [modelNative, modelVirtual] using modelWF.tr

private theorem arbitraryNativeScopeCannotSupplyATypedMotiveBaseModel
    {env : VEnv} {universes : List Name} (reader : Context) (missing : MVarId) :
    ∀ model : TypeChecker.MLCtx, model.WF env universes →
      model.lctx = (recursorIndexContext reader `untyped .default (.mvar missing)).lctx → False := by
  intro model modelWF modelNative
  have correspondence := modelWF.tr
  rw [modelNative] at correspondence
  have declarations := correspondence.2
  generalize model.vlctx = virtual at declarations
  simp only [recursorIndexContext, LocalContext.mkLocalDecl_toList] at declarations
  cases declarations with
  | cons _ declaration =>
    cases declaration with
    | vlam translated _ => cases translated

private theorem sameDomainTranslationOpensTheExactPushedMotiveReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled semantic : VExpr} {majorLevel level : VLevel} {elimLevel : Level}
    (translated : RecursorMotiveDomainTranslation env universes stats parent indices reader virtual peeled
      elimLevel semantic level)
    (major : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled majorLevel)
    (name : Name) :
    RecursorMotiveOpening env universes stats parent indices reader virtual peeled elimLevel name semantic level :=
  translated.opening major name

private theorem motiveOpeningRetainsActualDependenciesAndMajorReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {peeled semantic : VExpr} {level : VLevel} {elimLevel : Level} {name : Name}
    (opening : RecursorMotiveOpening env universes stats parent indices reader virtual peeled
      elimLevel name semantic level) :
    TrLCtx env universes (recursorMotiveContext stats parent indices reader elimLevel name).lctx
      (recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic) ∧
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).RecursorScopeFrame
        (recursorMotiveContext stats parent indices reader elimLevel name) :=
  ⟨opening.2.1, opening.2.2.2⟩

private theorem withLocalDeclPassesTheExactTranslatedMotiveReader {ResultType : Type}
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {peeled semantic : VExpr} {level : VLevel} {elimLevel : Level} {name : Name}
    (opening : RecursorMotiveOpening env universes stats parent indices reader virtual peeled
      elimLevel name semantic level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : TrLCtx env universes (recursorMotiveContext stats parent indices reader elimLevel name).lctx
      (recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic) →
      (next (.fvar ⟨(recursorIndexContext reader `t .default
          (recursorMajorDomain stats parent indices)).ngen.curr⟩)
        (recursorMotiveContext stats parent indices reader elimLevel name)).WF post) :
    (withLocalDecl name .default
      (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)))
      next (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))).WF post :=
  withLocalDecl.motiveTranslation opening next post nextWF

private theorem motiveSourceRetainsTheSameActualMajorAndIndexSources
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel parent original info current :=
  source.toMajorSource.toIndexSource

private theorem motiveSourceTranslationIsAtMotiveReaderNotAnArbitraryCurrentReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current) :
    ∃ (indexReader : Context) (virtual : VLCtx) (peeled semantic : VExpr),
      info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ ∧
      TrLCtx env universes
        (recursorMotiveContext stats parent info.indices indexReader elimLevel (recursorMotiveName types parent)).lctx
        (recursorMotiveVirtualContext stats parent info.indices indexReader virtual peeled elimLevel semantic) := by
  obtain ⟨indexReader, virtual, peeled, semantic, _, major, motive, opening⟩ := source.motiveReaderReceipt
  exact ⟨indexReader, virtual, peeled, semantic, major, motive, opening.2.1⟩

private theorem sameMotiveSourceRetainsActualNormalizationHistoryAndBothOpenings
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current) :
    ∃ (entry indexReader : Context) (normalized terminal : Expr) (finalIndex : Nat)
      (virtual finalVirtual : VLCtx) (semantic finalSemantic rawSemantic peeled motiveSemantic : VExpr)
      (majorLevel motiveLevel : VLevel),
      ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
      ∃ trace : RecursorIndexTrace stats normalized 0 #[] entry terminal finalIndex info.indices indexReader,
        TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
        RecursorMajorOpening env universes stats parent info.indices indexReader finalVirtual
          rawSemantic peeled majorLevel ∧
        RecursorMotiveOpening env universes stats parent info.indices indexReader finalVirtual peeled
          elimLevel (recursorMotiveName types parent) motiveSemantic motiveLevel := by
  cases source with
  | mk _ normalization trace _ _ _ _ _ history _ _ _ majorOpening motiveOpening =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, normalization, trace, history,
      majorOpening, motiveOpening⟩

private theorem emptyActualParentResultsNeedNoUniversalMotiveBaseModels
    {env : VEnv} {universes : List Name} (stats : InductiveStats) (elimLevel : Level)
    (original current : Context) (infos : Array RecInfo) :
    RecursorMotiveModelsSupport env universes stats #[] elimLevel original infos current := by
  intro parent bound
  simp at bound

private theorem actualParentMajorGetsMotiveTypingFromItsSupportedBaseModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {semanticElimLevel : VLevel} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current)
    (envWF : env.WF) (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : ParentRecursorMotiveModelSupport env universes stats types elimLevel original parent info current) :
    TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current :=
  source.motiveTranslated envWF mapped support

private theorem actualParentFamiliesKeepTheirMajorAndIndexReceipts
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoMotiveSources env universes stats types elimLevel original infos current) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current :=
  sources.toMajorSources.toIndexSources

private def captureSources (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) :
    M (Array RecInfo × Context) :=
  mkRecInfos stats types elimLevel fun infos => do return (infos, ← readThe Context)

private theorem failedCaptureCannotYieldASuccessfulMotiveSource (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : captureSources stats types elimLevel reader = .error failure) :
    ∀ infos current, captureSources stats types elimLevel reader ≠ .ok (infos, current) := by
  intro infos current success
  rw [failed] at success
  cases success

private theorem jointSupportIsConsumedOnlyForTheSameSuccessfulCapture
    {env : VEnv} {universes : List Name} (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader result.1 result.2)
    (infos : Array RecInfo) (current : Context)
    (actual : captureSources stats types elimLevel reader = .ok (infos, current)) :
    RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader infos current ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader infos current ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader infos current :=
  support (infos, current) actual

private theorem actualGetterRetainsExactMotiveReadersNotSemanticCurrentReaders
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader result.1 result.2) :
    (captureSources stats types elimLevel reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoMotiveSources env universes stats types elimLevel reader result.1 result.2 :=
  mkRecInfos.getTranslatedMotiveSources stats types elimLevel reader envWF constants definitions indexOnly
    readerWF reserved mapped support

private theorem actualCpsRequiresOnlySameCapturedSupportsAndMotiveReceipts {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (captureSources stats types elimLevel reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoMotiveSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedMotiveSources stats types elimLevel next reader post envWF constants definitions
    indexOnly readerWF reserved mapped support nextWF

private structure Observation where
  indices : Array Expr
  indexReader : Context
  major : Expr
  majorReader : Context
  domain : Expr
  motive : Expr
  motiveReader : Context

private def captureMotive (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (source : Expr) (initialIndices : Array Expr) (elimLevel : Level) : M Observation := do
  let entry ← readThe Context
  mkRecInfos.loopArgs1 stats source 0 initialIndices entry.fuel.inductiveFuel fun indices => do
    let indexReader ← readThe Context
    withLocalDecl `t .default (recursorMajorDomain stats parent indices) fun major => do
      let majorReader ← readThe Context
      let domain := recursorMotiveDomain elimLevel indices major majorReader
      withLocalDecl (recursorMotiveName types parent) .default domain fun motive => do
        let motiveReader ← readThe Context
        return { indices, indexReader, major, majorReader, domain, motive, motiveReader }

private def plainHeader (count : Nat) : Expr :=
  (List.range count).foldr
    (fun _ body => .forallE `index (.const ``Nat []) body .implicit) (.sort (.succ .zero))

private def fixtureStats (reader : Context) (head : Expr) : InductiveStats :=
  { lctx := reader.lctx, levels := [], resultLevel := .succ .zero, indConsts := #[head],
    params := #[], isNotZero := true }

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "motive-translation prior native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "motive-translation prior native type/dependency/value/position changed"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "motive-translation callback changed nonallocation reader fields"

private def checkOpenedBinderOrder (reader : Context) (selected : Array Expr)
    (telescope : Expr) (terminal : Expr) : MetaM Unit := do
  let mut opened := telescope
  for value in selected do
    let .forallE name domain body binderInfo := opened
      | throwError "motive-translation actual mkForall lost a selected cdecl binder"
    let some declaration := reader.lctx.find? value.fvarId!
      | throwError "motive-translation selected binder lookup absent"
    unless name == declaration.userName && domain == declaration.type &&
        binderInfo == declaration.binderInfo do
      throwError "motive-translation native abstraction changed selected order/name/domain/binder-info"
    opened := body.instantiate1 value
  unless opened == terminal do
    throwError "motive-translation native abstraction/opening failed terminal roundtrip"

private def checkMotiveDeclaration (stats : InductiveStats) (types : Array InductiveType)
    (parent : Nat) (observed : Observation) : MetaM Unit := do
  unless observed.major == Expr.fvar ⟨observed.indexReader.ngen.curr⟩ &&
      observed.motive == Expr.fvar ⟨observed.majorReader.ngen.curr⟩ &&
      observed.majorReader.lctx.decls.size == observed.indexReader.lctx.decls.size + 1 &&
      observed.motiveReader.lctx.decls.size == observed.majorReader.lctx.decls.size + 1 &&
      observed.motiveReader.ngen.curr == observed.majorReader.ngen.next.curr do
    throwError "motive-translation exact index/major/motive native readers were conflated"
  let some majorDeclaration := observed.majorReader.lctx.find? observed.major.fvarId!
    | throwError "motive-translation exact major reader lost actual major"
  unless majorDeclaration.type == recursorMajorDomain stats parent observed.indices do
    throwError "motive-translation selected major domain differs from actual stored major type"
  let some declaration := observed.motiveReader.lctx.find? observed.motive.fvarId!
    | throwError "motive-translation exact pushed motive reader lacks actual motive"
  unless declaration.toExpr == observed.motive && declaration.type == observed.domain &&
      declaration.userName == recursorMotiveName types parent && declaration.binderInfo == .default &&
      declaration.index == observed.majorReader.lctx.decls.size &&
      declaration.deps == observed.domain.fvarsList && declaration.value? (allowNondep := true) == none do
    throwError "motive-translation actual motive declaration type/deps/name/value/position changed"

private def checkCallback (reader : Context) (source : Expr) (head : Expr)
    (initialIndices : Array Expr) (newIndices : Nat) (elimLevel : Level) : MetaM Unit := do
  let stats := fixtureStats reader head
  let types : Array InductiveType := #[{ name := `MotiveTranslationParent, type := source, ctors := [] }]
  let .ok observed := captureMotive stats types 0 source initialIndices elimLevel reader
    | throwError "motive-translation actual index/major/motive callback failed"
  unless observed.indices[:initialIndices.size].toArray == initialIndices &&
      observed.indices.size == initialIndices.size + newIndices &&
      observed.indexReader.lctx.decls.size == reader.lctx.decls.size + newIndices do
    throwError "motive-translation initial selected-index prefix or actual allocation count changed"
  let nested := observed.majorReader.lctx.mkForall observed.indices
    (observed.majorReader.lctx.mkForall #[observed.major] (.sort elimLevel))
  unless observed.domain == peelTypeAnnotations nested && observed.domain == nested do
    throwError "motive-translation exact native nested mkForall/peeling operation changed"
  checkOpenedBinderOrder observed.majorReader (observed.indices.push observed.major)
    observed.domain (.sort elimLevel)
  checkMotiveDeclaration stats types 0 observed
  checkRetained reader observed.indexReader
  checkRetained observed.indexReader observed.majorReader
  checkRetained observed.majorReader observed.motiveReader

private def checkActualParent (reader : Context) (source : Expr) (elimLevel : Level) : MetaM Unit := do
  let stats := fixtureStats reader (.const `MotiveTranslationParent [])
  let types : Array InductiveType := #[{ name := `MotiveTranslationParent, type := source, ctors := [] }]
  let .ok observed := captureMotive stats types 0 source #[] elimLevel reader
    | throwError "motive-translation actual-parent cross-check callback failed"
  let .ok (infos, current) := mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun infos => do return (infos, ← readThe Context)) reader
    | throwError "motive-translation actual parameter-free parent callback failed"
  unless stats.params.isEmpty && infos.size == 1 && infos[0]!.indices == observed.indices &&
      infos[0]!.major == observed.major && infos[0]!.motive == observed.motive &&
      current.lctx.decls.size == observed.motiveReader.lctx.decls.size &&
      current.ngen.curr == observed.motiveReader.ngen.curr do
    throwError "motive-translation actual parent did not retain same index/major/motive callback sequence"
  checkMotiveDeclaration stats types 0 observed
  checkRetained observed.motiveReader current

private def checkSelectedLetBoundary (reader : Context) (letIdentifier : FVarId) : MetaM Unit := do
  let value := Expr.fvar letIdentifier
  let emptySelection := reader.lctx.mkForall #[] (.sort (.succ .zero))
  let unusedLet := reader.lctx.mkForall #[value] (.sort (.succ .zero))
  unless emptySelection == Expr.sort (.succ .zero) && unusedLet == emptySelection do
    throwError "motive-translation unused-let selection boundary changed"
  let selectedLet := reader.lctx.mkForall #[value] value
  let .letE name domain stored body nondep := selectedLet
    | throwError "motive-translation used let was incorrectly represented as a forall/cdecl"
  let some declaration := reader.lctx.find? letIdentifier
    | throwError "motive-translation selected-let lookup absent"
  unless name == declaration.userName && domain == declaration.type &&
      some stored == declaration.value? (allowNondep := true) && body == Expr.bvar 0 && !nondep do
    throwError "motive-translation selected native let boundary did not retain type/value/body"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `MotiveTranslationCarrier
  let element := FVarId.mk `MotiveTranslationElement
  let oldLet := FVarId.mk `MotiveTranslationLet
  let seeded := { reader with
    ngen := { namePrefix := `MotiveTranslationSeed, idx := 37 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 13)) false }
  let head := Expr.const `MotiveTranslationParent []
  for count in [:4] do
    checkCallback seeded (plainHeader count) head #[] count (.succ .zero)
    checkCallback seeded (plainHeader count) head #[.fvar carrier, .fvar element] count .zero
  checkCallback seeded dependentHeader head #[] 2 (.succ (.succ .zero))
  checkCallback seeded dependentHeader (.mdata {} head) #[] 2 (.succ .zero)
  let annotated := Expr.app (.const ``outParam [.max .zero (.succ .zero)]) (.const ``Nat [])
  checkCallback seeded (.forallE `nonuniform annotated (.sort (.succ .zero)) .default)
    head #[] 1 (.succ .zero)
  checkCallback seeded (.forallE `metadata (.mdata {} annotated) (.sort (.succ .zero)) .default)
    head #[] 1 (.succ .zero)
  checkCallback seeded (plainHeader 1) (.const ``outParam [.succ .zero]) #[] 1 (.succ .zero)
  checkCallback seeded (plainHeader 2) (.const ``optParam [.succ .zero]) #[] 2 (.succ .zero)
  let externalCarrier := Expr.forallE `externalElement (.fvar carrier) (.sort (.succ .zero)) .default
  checkCallback seeded externalCarrier head #[] 1 (.succ .zero)
  checkActualParent seeded (plainHeader 0) (.succ .zero)
  checkActualParent seeded dependentHeader .zero
  checkActualParent seeded (plainHeader 3) (.succ (.succ .zero))
  checkSelectedLetBoundary seeded oldLet
  logInfo "motive-translation runtime: fifteen allocation-only motive callbacks and three actual-parent cross-checks; exact native mkForall selected order/prefixes, external base dependencies, metadata/nonuniform domains and major/motive reader separation; used/unused let boundary"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "motive-translation unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "motive-translation audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "motive-translation module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrProj.weak', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.defeqDFC', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas),
      (``VEnv.HasType.defeqU_r, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? moduleName do
      throwError "motive-translation inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "motive-translation inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited motive foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "motive-translation inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "motive-translation native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "motive-translation native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

#print axioms annotationPeelingDoesNotPreserveEveryRawMajorHead
#print axioms modelForallMatchesTheExactNativeMotiveAbstraction
#print axioms motiveHistoryBuildsOnlyAnActualModelExtension
#print axioms mappedEliminationUniverseDerivesTypedModelAbstraction
#print axioms exactNativeMotiveBindingComesFromTheSameSelectedHistory
#print axioms sameHistoryDerivesActualMotiveDomainTypingAtTheMajorReader
#print axioms majorOpeningBuildsExactMajorThenMotiveModel
#print axioms arbitraryNativeScopeCannotSupplyATypedMotiveBaseModel
#print axioms sameMotiveSourceRetainsActualNormalizationHistoryAndBothOpenings
#print axioms actualGetterRetainsExactMotiveReadersNotSemanticCurrentReaders
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``parentMotiveNeedsTheActualZeroParameterBoundary,
      ``nonemptyParametersRemainOutsideTheParentIndexOnlyReceipt, ``forallMotiveHeadIsNotATypeAnnotation,
      ``metadataMotiveHeadIsNotPeeled, ``annotationPeelingDoesNotPreserveEveryRawMajorHead,
      ``nonuniformAnnotationIsNotUniformMotiveDomainSupport, ``dependentHeaderIsLiteral,
      ``nilModelSupportsOnlyItsExactEmptyReaders,
      ``modelForallTopHeadDoesNotNeedAnAnnotationUniverseRestriction,
      ``captureSources, ``failedCaptureCannotYieldASuccessfulMotiveSource,
      ``unary, ``dependentHeader, ``captureMotive, ``plainHeader, ``fixtureStats,
      ``checkRetained, ``checkOpenedBinderOrder, ``checkMotiveDeclaration, ``checkCallback,
      ``checkActualParent, ``checkSelectedLetBoundary, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``modelForallMatchesTheExactNativeMotiveAbstraction,
      ``motiveHistoryBuildsOnlyAnActualModelExtension, ``modelExtensionReceiptRetainsExactMotivePrefix,
      ``mappedEliminationUniverseDerivesTypedModelAbstraction,
      ``exactNativeMotiveBindingComesFromTheSameSelectedHistory,
      ``sameHistoryDerivesActualMotiveDomainTypingAtTheMajorReader,
      ``majorOpeningBuildsExactMajorThenMotiveModel, ``motiveBaseModelGivesTheExactNativeAndSemanticReader,
      ``arbitraryNativeScopeCannotSupplyATypedMotiveBaseModel] do
    auditDeclaration name native
  for name in [``sameDomainTranslationOpensTheExactPushedMotiveReader,
      ``motiveOpeningRetainsActualDependenciesAndMajorReader,
      ``withLocalDeclPassesTheExactTranslatedMotiveReader,
      ``motiveSourceRetainsTheSameActualMajorAndIndexSources,
      ``motiveSourceTranslationIsAtMotiveReaderNotAnArbitraryCurrentReader,
      ``sameMotiveSourceRetainsActualNormalizationHistoryAndBothOpenings,
      ``emptyActualParentResultsNeedNoUniversalMotiveBaseModels,
      ``actualParentMajorGetsMotiveTypingFromItsSupportedBaseModel,
      ``actualParentFamiliesKeepTheirMajorAndIndexReceipts,
      ``jointSupportIsConsumedOnlyForTheSameSuccessfulCapture,
      ``actualGetterRetainsExactMotiveReadersNotSemanticCurrentReaders,
      ``actualCpsRequiresOnlySameCapturedSupportsAndMotiveReceipts] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveMotiveBindingFacts native
  auditModule `Lean4Lean.Verify.InductiveMotiveContextTranslation native
  auditModule `Lean4Lean.Verify.InductiveMotiveContextTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader

end InductiveMotiveContextTranslationTest
