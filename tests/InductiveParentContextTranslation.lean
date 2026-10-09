import Lean4Lean.Verify.InductiveParentContextTranslationCPS
import Lean4Lean.Verify.InductiveParentContextTranslation
import Lean4Lean.Verify.InductiveParentPassTrace
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveParentContextTranslationTest

abbrev ParentHeaderAlias := Nat → Type

private theorem actualParentCounterNeedsZeroParameters (stats : InductiveStats) :
    stats.params.size ≤ 0 ↔ stats.params.size = 0 := by omega

private theorem nonemptyParametersDoNotGiveIndexOnlyParentModels (stats : InductiveStats)
    (nonempty : 0 < stats.params.size) : ¬ stats.params.size ≤ 0 := by omega

private theorem forallBinderPeelingDoesNotDependOnTheParentName
    (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (.forallE name domain body bi) = .forallE name domain body bi := rfl

private theorem metadataDoesNotJustifyReplacingTheStoredIndexDomain (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem annotationHeadStillNeedsCompatibleMajorSupport (identifier : FVarId) :
    peelTypeAnnotations (.app (.const ``outParam [.succ .zero]) (.fvar identifier)) ≠
      .app (.const ``outParam [.succ .zero]) (.fvar identifier) := by
  simp [peelTypeAnnotations]

private theorem eliminationLevelMappingIsNotAutomaticForMetavariables
    (universes : List Name) (missing : LMVarId) :
    VLevel.ofLevel universes (.mvar missing) = none := rfl

private theorem oneInitialModelCannotBeReplacedByAnArbitraryNativeScope
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

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def dependentHeader : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private theorem dependentHeaderIsLiteral : SortTelescope dependentHeader :=
  .forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero)))

private theorem completedParentTraceKeepsTheExactOriginalReaderAndPrefix
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (reader : Context) (complete : ¬ parent < types.size) :
    RecursorParentPassTrace stats types elimLevel parent infos reader infos reader :=
  .stop complete

private theorem actualParentTracePreservesCountsAndGeneratedMinorBoundary
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader) :
    finalInfos.size = infos.size + (types.size - parent) ∧
      ∃ appended, finalInfos.toList = infos.toList ++ appended ∧
        appended.length = types.size - parent ∧ ∀ info ∈ appended, info.minors = #[] :=
  ⟨trace.counts, trace.prefix⟩

private theorem actualNativeParentTraceScopeIsNotSemanticMinorCorrespondence
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := trace.scope readerWF reserved

private theorem actualNativeGetterCapturesTheSameWholeParentTrace
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2 ∧
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size + (types.size - parent) :=
  mkRecInfos.loopInd1.getParentPassTrace stats types elimLevel parent infos reader readerWF reserved

private theorem motiveModelPushUsesTheExactCurrentMajorModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {peeled semantic : VExpr} {level : VLevel} {elimLevel : Level} {name : Name}
    (opening : RecursorMotiveOpening env universes stats parent indices reader virtual peeled
      elimLevel name semantic level)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx =
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx)
    (modelVirtual : model.vlctx = recursorMajorVirtualContext stats parent indices reader virtual peeled) :
    (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).WF env universes ∧
      (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).lctx =
        (recursorMotiveContext stats parent indices reader elimLevel name).lctx ∧
      (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).vlctx =
        recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic :=
  opening.mixedContext model modelWF modelNative modelVirtual

private theorem parentStepExportsItsDerivedFinalModelNotAnAssumedLaterModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) :
    final.WF env universes ∧ final.lctx =
      (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)).lctx :=
  step.model

private theorem parentStepKeepsOneInitialModelAcrossAllSelectedAllocations
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) : IndexMLCtxExtension initial ids final :=
  step.extension

private theorem actualIndexHistoryDerivesTheWholeSingleParentModelStep
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader indexReader : Context} {virtual indexVirtual : VLCtx}
    {semantic finalSemantic headSemantic : VExpr} {majorLevel : VLevel}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic indexVirtual finalSemantic)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (modelVirtual : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
    (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
    (finalSort : finalSemantic = .sort majorLevel)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) majorLevel)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ (finalModel : TypeChecker.MLCtx) (allocated : List FVarId),
      RecursorParentModelStep env universes stats types elimLevel parent indices indexReader indexVirtual
        model finalModel allocated :=
  history.parentModelStep envWF constants definitions indexOnly model modelWF modelNative modelVirtual
    reserved headTranslated headTyped finalSort uniform mapped

private theorem singleParentModelStepAllocatesOnlyActualIndicesMajorAndMotive
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) : ids.length = indices.size + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, array⟩ := step
  have counts := congrArg List.length array
  simpa only [List.length_map, List.length_append, Array.length_toList, List.length_cons,
    List.length_nil] using counts

private theorem singleParentModelStepDerivesNativeMotiveReaderCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) :
    TrLCtx env universes
      (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)).lctx
      final.vlctx := by
  simpa only [step.model.2] using step.model.1.tr

private theorem exactNodeSupportDerivesItsSameActualIndexHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context}
    {trace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader}
    (support : ParentModelTranslationSupport env universes stats parent trace)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ semantic finalVirtual finalSemantic,
      ∃ _history : TranslatedRecursorIndexTrace env universes trace model.vlctx semantic finalVirtual finalSemantic,
      ∃ headSemantic level,
        TrExprS env universes model.vlctx stats.indConsts[parent]! headSemantic ∧
        env.HasType universes.length model.vlctx.toCtx headSemantic semantic ∧
        finalSemantic = .sort level ∧
        UniformAnnotationUniverse universes
          (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level :=
  support.translatedIndices envWF constants definitions indexOnly model modelWF modelNative reserved

private theorem completedNativeTraceRequiresNoLaterParentModelSupport
    {env : VEnv} {universes : List Name} (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (complete : ¬ parent < types.size) :
    RecursorParentPassTranslationSupport env universes
      (RecursorParentPassTrace.stop (stats := stats) (types := types) (elimLevel := elimLevel)
        (parent := parent) (infos := infos) (reader := reader) complete) :=
  .stop complete

private theorem wholeActualParentTraceExtendsOnlyTheSuppliedInitialModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader)
    (support : RecursorParentPassTranslationSupport env universes trace)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    {model : TypeChecker.MLCtx} (modelWF : model.WF env universes)
    (modelNative : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ finalModel, TranslatedRecursorParentPass env universes trace model finalModel :=
  trace.translated support envWF constants definitions indexOnly model modelWF modelNative reserved mapped

private theorem wholeTypedPassDerivesTheExactFinalParentPhaseReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (translated : TranslatedRecursorParentPass env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx :=
  translated.context

private theorem wholeTypedPassExtensionKeepsItsOneInitialBaseModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (translated : TranslatedRecursorParentPass env universes trace initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final :=
  translated.extension

private theorem wholeTypedPassRetainsTheActualPrefixAndNoGeneratedMinors
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (translated : TranslatedRecursorParentPass env universes trace initial final) :
    TrLCtx env universes finalReader.lctx final.vlctx ∧
      ∃ appended, finalInfos.toList = infos.toList ++ appended ∧
        appended.length = types.size - parent ∧ ∀ info ∈ appended, info.minors = #[] :=
  ⟨translated.context.2.2, trace.prefix⟩

private theorem zeroParentSemanticReceiptUsesNoOtherStartingModel
    {env : VEnv} {universes : List Name} (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (complete : ¬ parent < types.size) {model : TypeChecker.MLCtx}
    (modelWF : model.WF env universes) (modelNative : model.lctx = reader.lctx) :
    TranslatedRecursorParentPass env universes
      (RecursorParentPassTrace.stop (stats := stats) (types := types) (elimLevel := elimLevel)
        (parent := parent) (infos := infos) (reader := reader) complete) model model :=
  .stop complete modelWF modelNative

private def plainHeader (name : Name) (count : Nat) : InductiveType :=
  { name, type := (List.range count).foldr
      (fun _ body => .forallE `index (.const ``Nat []) body .implicit) (.sort (.succ .zero)), ctors := [] }

private def captureParents (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (start : Nat) (initialInfos : Array RecInfo) : M (Array RecInfo × Context) :=
  mkRecInfos.loopInd1 stats types elimLevel start initialInfos fun infos => do
    return (infos, ← readThe Context)

private theorem actualGetterDerivesOneFinalModelFromOneInitialModel
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (captureParents stats types elimLevel parent infos reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace) :
    (captureParents stats types elimLevel parent infos reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size + (types.size - parent) ∧
      ∃ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
      ∃ finalModel, TranslatedRecursorParentPass env universes trace model finalModel ∧
        finalModel.WF env universes ∧ finalModel.lctx = result.2.lctx ∧
        TrLCtx env universes result.2.lctx finalModel.vlctx ∧
        ∃ allocated, IndexMLCtxExtension model allocated finalModel :=
  mkRecInfos.loopInd1.getTranslatedParentPass stats types elimLevel parent infos reader
    envWF constants definitions indexOnly model modelWF native reserved mapped support

private theorem scopedCPSReceivesExactlyTheDerivedParentPhaseModel
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (captureParents stats types elimLevel parent infos reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      TranslatedRecursorParentPass env universes trace model finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos next reader).WF post :=
  mkRecInfos.loopInd1.scopedTranslatedParentPass stats types elimLevel parent infos next reader post
    envWF constants definitions indexOnly model modelWF native reserved mapped support nextWF

private theorem fullBuilderStillRequiresTheExplicitMinorPhaseObligation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (captureParents stats types elimLevel 0 #[] reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorWF : ∀ finalInfos parentReader
      (trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader finalInfos parentReader) finalModel,
      reader.RecursorScopeFrame parentReader →
      TranslatedRecursorParentPass env universes trace model finalModel →
      TrLCtx env universes parentReader.lctx finalModel.vlctx →
      (mkRecInfos.loopInd2 stats types 0 finalInfos next parentReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.fromTypedParentPass stats types elimLevel next reader post
    envWF constants definitions indexOnly model modelWF native reserved mapped support minorWF

private def fixtureStats (reader : Context) (types : Array InductiveType) : InductiveStats :=
  { lctx := reader.lctx, levels := [], resultLevel := .succ .zero,
    indConsts := types.map (fun datatype => .const datatype.name []), params := #[], isNotZero := true }

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "parent-context prior native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "parent-context prior declaration type/dependency/value/position changed"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "parent-context actual parent pass changed nonallocation reader fields"

private def checkInfoEqual (expected observed : RecInfo) : MetaM Unit := do
  unless observed.indices == expected.indices && observed.major == expected.major &&
      observed.motive == expected.motive && observed.minors == expected.minors do
    throwError "parent-context actual pass changed a prefixed recursor info"

private def checkIndexDeclarations (entry current : Context) (source : Expr) (indices : Array Expr) :
    MetaM Unit := do
  let mut opened := source
  let mut generator := entry.ngen
  for ordinal in [:indices.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "parent-context actual index callback exhausted normalized header"
    let value := indices[ordinal]!
    let some declaration := current.lctx.find? value.fvarId!
      | throwError "parent-context actual positioned index disappeared"
    unless value == Expr.fvar ⟨generator.curr⟩ && declaration.toExpr == value &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == entry.lctx.decls.size + ordinal &&
        declaration.type == peelTypeAnnotations domain &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "parent-context same index history lost its native domain/deps/name/position"
    opened := body.instantiate1 value
    generator := generator.next
  unless opened == Expr.sort (.succ .zero) do
    throwError "parent-context normalized literal index callback terminal changed"

private def checkMajorAndMotive (stats : InductiveStats) (types : Array InductiveType)
    (parent : Nat) (elimLevel : Level) (info : RecInfo) (indexReader current : Context) : MetaM Context := do
  let majorReader := recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices)
  let expectedMajor := Expr.fvar ⟨indexReader.ngen.curr⟩
  let motiveDomain := recursorMotiveDomain elimLevel info.indices expectedMajor majorReader
  let motiveReader := recursorIndexContext majorReader (recursorMotiveName types parent) .default motiveDomain
  unless info.major == expectedMajor && info.motive == Expr.fvar ⟨majorReader.ngen.curr⟩ &&
      info.minors.isEmpty do
    throwError "parent-context actual parent did not preserve exact major/motive or allocated minors too early"
  let some major := current.lctx.find? info.major.fvarId!
    | throwError "parent-context current parent-phase reader lacks actual major"
  let some motive := current.lctx.find? info.motive.fvarId!
    | throwError "parent-context current parent-phase reader lacks actual motive"
  unless major.type == recursorMajorDomain stats parent info.indices &&
      major.index == indexReader.lctx.decls.size && major.deps == major.type.fvarsList &&
      motive.type == motiveDomain && motive.index == majorReader.lctx.decls.size &&
      motive.deps == motiveDomain.fvarsList && motive.userName == recursorMotiveName types parent do
    throwError "parent-context actual major/motive domains/dependencies/order/name changed"
  checkRetained indexReader majorReader
  checkRetained majorReader motiveReader
  checkRetained motiveReader current
  return motiveReader

private def checkParent (stats : InductiveStats) (types : Array InductiveType)
    (parent : Nat) (elimLevel : Level) (info : RecInfo) (entry current : Context) : MetaM Context := do
  let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry)
    | throwError "parent-context actual source header normalization failed"
  let .ok (indices, indexReader) := mkRecInfos.loopArgs1 stats normalized 0 #[] entry.fuel.inductiveFuel
      (fun indices => do return (indices, ← readThe Context)) entry
    | throwError "parent-context actual nested index/reader capture failed"
  unless info.indices == indices && indexReader.lctx.decls.size == entry.lctx.decls.size + indices.size do
    throwError "parent-context parent pass did not keep exact nested index callback"
  checkIndexDeclarations entry indexReader normalized indices
  checkRetained entry indexReader
  return ← checkMajorAndMotive stats types parent elimLevel info indexReader current

private def checkFixture (reader : Context) (types : Array InductiveType) (elimLevel : Level)
    (start : Nat) (initialInfos : Array RecInfo) : MetaM Unit := do
  let stats := fixtureStats reader types
  let .ok (infos, current) := captureParents stats types elimLevel start initialInfos reader
    | throwError "parent-context actual whole parent-pass capture failed"
  unless stats.params.isEmpty && infos.size == initialInfos.size + (types.size - start) do
    throwError "parent-context actual parent-pass cardinality/zero-parameter boundary changed"
  for ordinal in [:initialInfos.size] do
    checkInfoEqual initialInfos[ordinal]! infos[ordinal]!
  let mut entry := reader
  for parent in [start:types.size] do
    entry ← checkParent stats types parent elimLevel infos[initialInfos.size + parent - start]! entry current
  unless entry.lctx.decls.size == current.lctx.decls.size && entry.ngen.curr == current.ngen.curr do
    throwError "parent-context actual whole pass lost exact final motive-reader suffix"
  checkRetained reader current
  checkRetained entry current
  let later := recursorIndexContext current `laterMinor .default (.const ``Nat [])
  unless later.lctx.decls.size != current.lctx.decls.size do
    throwError "parent-context parent-phase reader was conflated with an untyped later minor reader"
  checkRetained current later

private def prepare (types : Array InductiveType) : M (InductiveStats × Context) :=
  checkInductiveTypes 0 types fun stats => do
    let reader ← readThe Context
    let headers ← declareInductiveTypes stats 0 types 0 false
    let root := { reader with env := headers }
    checkConstructors types stats false root
    let constructors ← declareConstructors stats types false root
    return (stats, { root with env := constructors })

private def checkActualMinorPhaseBoundary (reader : Context) : MetaM Unit := do
  let types : Array InductiveType := #[{
    name := `ParentContextRecursive
    type := .sort (.succ .zero)
    ctors := [
      { name := `ParentContextRecursive.zero, type := .const `ParentContextRecursive [] },
      { name := `ParentContextRecursive.step
        type := .forallE `field (.const `ParentContextRecursive [])
          (.const `ParentContextRecursive []) .default }] }]
  let .ok (stats, root) := prepare types reader
    | throwError "parent-context actual minor-boundary fixture preparation failed"
  let .ok (parentInfos, parentReader) := captureParents stats types (.succ .zero) 0 #[] root
    | throwError "parent-context actual pre-minor capture failed"
  let .ok (infos, current) := mkRecInfos stats types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) root
    | throwError "parent-context actual full capture for minor-boundary control failed"
  unless parentInfos.size == 1 && parentInfos[0]!.minors.isEmpty && infos.size == 1 &&
      !infos[0]!.minors.isEmpty && current.lctx.decls.size > parentReader.lctx.decls.size &&
      infos[0]!.indices == parentInfos[0]!.indices && infos[0]!.major == parentInfos[0]!.major &&
      infos[0]!.motive == parentInfos[0]!.motive do
    throwError "parent-context parent-phase/full-minor-phase boundary or retained parent fields changed"
  checkRetained parentReader current

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `ParentContextCarrier
  let element := FVarId.mk `ParentContextElement
  let oldLet := FVarId.mk `ParentContextLet
  let seeded := { reader with
    ngen := { namePrefix := `ParentContextSeed, idx := 41 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 17)) false }
  let initialInfos : Array RecInfo := #[{
    indices := #[.fvar carrier], major := .fvar element, motive := .fvar oldLet,
    minors := #[.lit (.natVal 5)] }]
  checkFixture seeded #[] (.succ .zero) 0 #[]
  checkFixture seeded #[] .zero 0 initialInfos
  checkFixture seeded #[plainHeader `ParentContextEmpty 0] (.succ .zero) 0 #[]
  checkFixture seeded #[plainHeader `ParentContextThree 3] .zero 0 #[]
  checkFixture seeded #[{ name := `ParentContextDependent, type := dependentHeader, ctors := [] }]
    (.succ (.succ .zero)) 0 #[]
  let types := #[plainHeader `ParentContextFirst 0,
    { name := `ParentContextSecond, type := dependentHeader, ctors := [] },
    plainHeader `ParentContextThird 3]
  checkFixture seeded types (.succ .zero) 0 #[]
  checkFixture seeded types .zero 1 initialInfos
  checkFixture seeded types (.succ .zero) types.size initialInfos
  checkFixture seeded types (.succ .zero) (types.size + 2) initialInfos
  let annotated := Expr.app (.const ``outParam [.max .zero (.succ .zero)]) (.const ``Nat [])
  let metadataTypes : Array InductiveType := #[{
    name := `ParentContextMetadata
    type := .forallE `metadata (.mdata {} annotated) (.sort (.succ .zero)) .default
    ctors := [] }]
  let externalTypes : Array InductiveType := #[{
    name := `ParentContextExternal
    type := .forallE `external (.fvar carrier) (.sort (.succ .zero)) .default
    ctors := [] }]
  checkFixture seeded metadataTypes (.succ .zero) 0 #[]
  checkFixture seeded externalTypes (.succ .zero) 0 #[]
  checkFixture seeded #[{ name := `ParentContextAlias, type := .const ``ParentHeaderAlias [], ctors := [] }]
    (.succ .zero) 0 #[]
  checkActualMinorPhaseBoundary seeded
  logInfo "parent-context runtime: twelve allocation-only whole-parent callbacks plus one checked runtime parent/minor boundary; zero/one/multiple parents, prefixes and starts, dependent/metadata/alias/base-dependent headers and retained values; semantic scope remains the exact parent-phase reader"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "parent-context unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "parent-context audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "parent-context module-owned axiom {name}"
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
      throwError "parent-context inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "parent-context inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited parent-model foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "parent-context inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "parent-context native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "parent-context native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

#print axioms oneInitialModelCannotBeReplacedByAnArbitraryNativeScope
#print axioms actualNativeGetterCapturesTheSameWholeParentTrace
#print axioms actualIndexHistoryDerivesTheWholeSingleParentModelStep
#print axioms exactNodeSupportDerivesItsSameActualIndexHistory
#print axioms wholeTypedPassDerivesTheExactFinalParentPhaseReader
#print axioms actualGetterDerivesOneFinalModelFromOneInitialModel
#print axioms scopedCPSReceivesExactlyTheDerivedParentPhaseModel
#print axioms fullBuilderStillRequiresTheExplicitMinorPhaseObligation
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``actualParentCounterNeedsZeroParameters, ``nonemptyParametersDoNotGiveIndexOnlyParentModels,
      ``forallBinderPeelingDoesNotDependOnTheParentName, ``metadataDoesNotJustifyReplacingTheStoredIndexDomain,
      ``annotationHeadStillNeedsCompatibleMajorSupport, ``eliminationLevelMappingIsNotAutomaticForMetavariables,
      ``dependentHeaderIsLiteral, ``unary, ``dependentHeader, ``plainHeader, ``captureParents, ``fixtureStats,
      ``completedParentTraceKeepsTheExactOriginalReaderAndPrefix,
      ``checkRetained, ``checkInfoEqual, ``checkIndexDeclarations, ``checkMajorAndMotive,
      ``checkParent, ``checkFixture, ``prepare, ``checkActualMinorPhaseBoundary, ``runtimeFixtures] do
    auditDeclaration name logical
  auditDeclaration ``oneInitialModelCannotBeReplacedByAnArbitraryNativeScope
    (logical ++ [``sorryAx, ``PersistentArray.toList'_push])
  for name in [``actualParentTracePreservesCountsAndGeneratedMinorBoundary,
      ``actualNativeParentTraceScopeIsNotSemanticMinorCorrespondence,
      ``actualNativeGetterCapturesTheSameWholeParentTrace] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``motiveModelPushUsesTheExactCurrentMajorModel,
      ``parentStepExportsItsDerivedFinalModelNotAnAssumedLaterModel,
      ``parentStepKeepsOneInitialModelAcrossAllSelectedAllocations,
      ``actualIndexHistoryDerivesTheWholeSingleParentModelStep,
      ``singleParentModelStepAllocatesOnlyActualIndicesMajorAndMotive,
      ``singleParentModelStepDerivesNativeMotiveReaderCorrespondence,
      ``exactNodeSupportDerivesItsSameActualIndexHistory,
      ``completedNativeTraceRequiresNoLaterParentModelSupport,
      ``wholeActualParentTraceExtendsOnlyTheSuppliedInitialModel,
      ``wholeTypedPassDerivesTheExactFinalParentPhaseReader,
      ``wholeTypedPassExtensionKeepsItsOneInitialBaseModel,
      ``wholeTypedPassRetainsTheActualPrefixAndNoGeneratedMinors,
      ``zeroParentSemanticReceiptUsesNoOtherStartingModel,
      ``actualGetterDerivesOneFinalModelFromOneInitialModel,
      ``scopedCPSReceivesExactlyTheDerivedParentPhaseModel,
      ``fullBuilderStillRequiresTheExplicitMinorPhaseObligation] do
    auditDeclaration name native
  for name in [``recursorParentPassInfo, ``RecursorParentPassTrace,
      ``RecursorParentPassTrace.counts, ``RecursorParentPassTrace.prefix,
      ``mkRecInfos.loopInd1.morphism] do
    auditDeclaration name logical
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveParentPassTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveParentContextTranslation native
  auditModule `Lean4Lean.Verify.InductiveParentContextTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader

end InductiveParentContextTranslationTest
