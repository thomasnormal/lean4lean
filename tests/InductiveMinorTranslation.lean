import Lean4Lean.Verify.InductiveIHTranslationCPS
import Lean4Lean.Verify.InductiveCtorFieldTranslationCPS
import Lean4Lean.Verify.InductiveMinorTrace
import Lean4Lean.Verify.InductiveMinorTranslation
import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveMinorTranslationTest

abbrev MinorDomainAlias := Nat
abbrev MinorHeaderAlias := Nat → Nat

inductive MinorTree where
  | leaf : MinorTree
  | higher (children : Nat → MinorTree) : MinorTree
  | dependent (children : (carrier : Type) → carrier → MinorTree) : MinorTree
  | pair (left right : MinorTree) : MinorTree
  | mixed (carrier : Type) (payload : carrier) (children : carrier → MinorTree) : MinorTree

inductive MinorFamily (carrier : Type) : Nat → Type where
  | leaf (ordinal : Nat) (payload : carrier) : MinorFamily carrier ordinal
  | direct (ordinal : Nat) (child : MinorFamily carrier ordinal) : MinorFamily carrier ordinal
  | higher (ordinal : Nat) (children : Nat → MinorFamily carrier ordinal) : MinorFamily carrier ordinal

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private theorem metadataMinorBarrierKeepsTheActualDomain (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem nestedMinorWeakeningCannotUseTheOriginalOrOneSuffixBody :
    (VExpr.app (.bvar 1) (.bvar 0)).liftN 2 = .app (.bvar 3) (.bvar 2) ∧
      (VExpr.app (.bvar 1) (.bvar 0)).liftN 2 ≠ .app (.bvar 1) (.bvar 0) ∧
      (VExpr.app (.bvar 1) (.bvar 0)).liftN 2 ≠ .app (.bvar 2) (.bvar 1) := by
  constructor
  · rfl
  · constructor <;> intro equality <;> cases equality

private theorem minorFailureCannotSupplySuccessfulOutputs
    {ResultType : Type} (action : M ResultType) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : action reader = .error failure) :
    ∀ result, action reader ≠ .ok result := by
  intro result success
  rw [failed] at success
  cases success

private theorem actualMinorNameUsesTheDeclaredConstructorPrefixReplacement
    (parent : Name) (constructor : Constructor) :
    recursorMinorName parent constructor = constructor.name.replacePrefix parent .anonymous := rfl

private theorem actualMinorUsesTheCurrentHypothesisReaderGenerator
    (reader : Context) (parent : Name) (constructor : Constructor) (domain : Expr) :
    (recursorMinorContext reader parent constructor domain).ngen = reader.ngen.next := rfl

private theorem nativeMinorUpdateKeepsTheWholeRecInfoArraySize
    (index : Nat) (infos : Array RecInfo) (minor : Expr) :
    (recursorMinorUpdate index infos minor).size = infos.size := recursorMinorUpdate.size index infos minor

private theorem selectedMinorUpdateNeedsItsActualParentBound
    (index : Nat) (infos : Array RecInfo) (minor : Expr) (bound : index < infos.size) :
    (recursorMinorUpdate index infos minor)[index]! =
      { infos[index]! with minors := infos[index]!.minors.push minor } :=
  recursorMinorUpdate.selected index infos minor bound

private theorem completedMinorTraceKeepsItsCurrentNestedReader
    (stats : InductiveStats) (parent : Name) (index : Nat) (infos : Array RecInfo) (reader : Context) :
    RecursorMinorTrace stats parent index infos [] reader infos reader := .stop

private theorem sameActualMinorSourceDerivesItsNestedFieldAndHypothesisScope
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame domainReader := source.scope readerWF reserved

private theorem wholeMinorTraceKeepsPreviousFieldsAndHypothesesInItsScope
    {stats : InductiveStats} {parent : Name} {index : Nat} {infos finalInfos : Array RecInfo}
    {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := trace.scope readerWF reserved

private theorem wholeMinorTraceKeepsEveryOtherParentExactly
    {stats : InductiveStats} {parent : Name} {index : Nat} {infos finalInfos : Array RecInfo}
    {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
    (other : Nat) (bound : other < infos.size) (different : other ≠ index) :
    finalInfos[other]! = infos[other]! := trace.other other bound different

private theorem wholeMinorTraceAddsOnlyTheActualConstructorCount
    {stats : InductiveStats} {parent : Name} {index : Nat} {infos finalInfos : Array RecInfo}
    {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
    (bound : index < infos.size) :
    finalInfos[index]!.minors.size = infos[index]!.minors.size + constructors.length :=
  trace.minorCounts bound

private theorem wholeMinorTraceKeepsItsExactSeededMinorPrefix
    {stats : InductiveStats} {parent : Name} {index : Nat} {infos finalInfos : Array RecInfo}
    {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
    (bound : index < infos.size) :
    ∃ appended, finalInfos[index]!.minors.toList = infos[index]!.minors.toList ++ appended ∧
      appended.length = constructors.length := trace.minorPrefix bound

private theorem nativeMinorDomainAbstractsHypothesesBeforeConstructorFields
    (stats : InductiveStats) (infos : Array RecInfo) (constructor : Constructor)
    (terminal : Expr) (fields hypotheses : Array Expr) (reader : Context) :
    recursorMinorDomain stats infos constructor terminal fields hypotheses reader =
      reader.lctx.mkForall fields (reader.lctx.mkForall hypotheses
        (recursorMinorBody stats infos constructor terminal fields)) := rfl

private theorem actualMinorBodyKeepsOriginalConstructorLevelsAndParameters
    (stats : InductiveStats) (infos : Array RecInfo) (constructor : Constructor)
    (terminal : Expr) (fields : Array Expr) :
    recursorMinorBody stats infos constructor terminal fields =
      Expr.app (mkAppN infos[(getIIndices stats terminal).1]!.motive
        (getIIndices stats terminal).2)
        (mkAppN (mkAppN (.const constructor.name stats.levels) stats.params) fields) := rfl

private theorem actualNativeGetterDoesNotAssumeWholeMinorDomainTyping
    (stats : InductiveStats) (parent : Name) (index : Nat) (infos : Array RecInfo)
    (constructors : List Constructor) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopCtors stats parent index infos constructors
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      RecursorMinorTrace stats parent index infos constructors reader result.1 result.2 ∧
        reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size :=
  mkRecInfos.loopCtors.getTrace stats parent index infos constructors reader readerWF reserved

private theorem sameConstructorFieldEndpointTypesItsOwnExactAppliedConstructor
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursive : Array Expr}
    {reader fieldReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursive fieldReader}
    {initial fieldModel : TypeChecker.MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial fieldModel semantic)
    (envWF : env.WF) {head : Expr} {headSemantic : VExpr}
    (headTranslated : TrExprS env universes initial.vlctx head headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS env universes fieldModel.vlctx (mkAppN head fields) value ∧
      TrExprS env universes fieldModel.vlctx terminal terminalSemantic ∧
      env.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic :=
  endpoint.application envWF headTranslated headTyped

private theorem bindingEarlierFieldsAtTheIHReaderRequiresTheSameSelectedDeclarations
    {env : VEnv} {universes : List Name} {initial fieldModel hypothesisModel : TypeChecker.MLCtx}
    {ids : List FVarId} {fieldReader hypothesisReader : Context}
    (extension : IndexMLCtxExtension initial ids fieldModel)
    (fieldWF : fieldModel.WF env universes) (hypothesisWF : hypothesisModel.WF env universes)
    (fieldNative : fieldModel.lctx = fieldReader.lctx)
    (hypothesisNative : hypothesisModel.lctx = hypothesisReader.lctx)
    (frame : fieldReader.RecursorScopeFrame hypothesisReader)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes fieldModel.vlctx body bodySemantic) :
    hypothesisReader.lctx.mkForall (ids.map Expr.fvar).toArray body =
      fieldReader.lctx.mkForall (ids.map Expr.fvar).toArray body :=
  extension.selectedBindingAtLaterContext fieldWF hypothesisWF fieldNative hypothesisNative frame translated

private theorem minorBodyTypingUsesTheSameActualConstructorAndSelectedMotive
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursive : Array Expr} {reader fieldReader : Context}
    {trace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursive fieldReader}
    {initial fieldModel : TypeChecker.MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial fieldModel semantic)
    (envWF : env.WF)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ body level,
      TrExprS env universes fieldModel.vlctx
        (recursorMinorBody stats infos constructor terminal fields) body ∧
      env.HasType universes.length fieldModel.vlctx.toCtx body (.sort level) :=
  endpoint.minorBodyTranslation envWF headTranslated headTyped motiveSupport

private theorem nestedMinorDomainAbstractionReturnsToTheInitialConstructorModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursive hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursive fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursive infos 0 #[] fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : TypeChecker.MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ domain level,
      TrExprS env universes initial.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader) domain ∧
      env.HasType universes.length initial.vlctx.toCtx domain (.sort level) :=
  endpoint.minorDomainTranslation history envWF modelWF reserved headTranslated headTyped motiveSupport

private theorem theSameMinorDomainAtTheIHReaderIsLiftedByBothPersistentSuffixes
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursive hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursive fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursive infos 0 #[] fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : TypeChecker.MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ domain level,
      TrExprS env universes initial.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader) domain ∧
      env.HasType universes.length initial.vlctx.toCtx domain (.sort level) ∧
      TrExprS env universes hypothesisModel.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)
        (domain.liftN (fields.size + hypotheses.size)) ∧
      env.HasType universes.length hypothesisModel.vlctx.toCtx
        (domain.liftN (fields.size + hypotheses.size)) (.sort level) :=
  endpoint.liftedMinorDomainTranslation history envWF modelWF reserved headTranslated headTyped motiveSupport

private theorem actualMinorOpeningStillNeedsAnnotationsAtTheCurrentHypothesisReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursive hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursive fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursive infos 0 #[] fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : TypeChecker.MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (parent : Name) (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal)
    (annotations : IndexAnnotationSupport env universes hypothesisReader
      (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)) :
    ∃ raw peeled level,
      RecursorMinorOpening env universes hypothesisReader hypothesisModel.vlctx parent constructor
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader) raw peeled level :=
  endpoint.minorOpening history parent envWF constants definitions modelWF reserved
    headTranslated headTyped motiveSupport annotations

private theorem allocatedMinorExtendsTheCurrentHypothesisModelNotTheInitialConstructorModel
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parent : Name} {constructor : Constructor} {domain : Expr} {raw peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parent constructor domain raw peeled level)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorMinorMLCtx reader model parent constructor domain peeled).WF env universes ∧
      (recursorMinorMLCtx reader model parent constructor domain peeled).lctx =
        (recursorMinorContext reader parent constructor domain).lctx ∧
      (recursorMinorMLCtx reader model parent constructor domain peeled).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled :=
  opening.mixedContext model modelWF native converted reserved

private theorem minorAllocationAddsExactlyItsOwnIdentifierToTheCurrentModel
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parent : Name} {constructor : Constructor} {domain : Expr} {raw peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parent constructor domain raw peeled level)
    (model : TypeChecker.MLCtx) :
    IndexMLCtxExtension model [⟨reader.ngen.curr⟩]
      (recursorMinorMLCtx reader model parent constructor domain peeled) := opening.extension model

private theorem sameActualMinorSourceDerivesItsWholeFieldHypothesisAndMinorModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (parent : Name) (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : MinorSourceTranslationSupport env universes source model) :
    ∃ finalModel, MinorModelStep env universes parent source model finalModel :=
  source.translatedStep parent envWF constants definitions fieldOnly model modelWF native reserved support

private theorem sameTypedMinorStepRetainsFieldsHypothesesAndMinorInItsFinalModel
    {env : VEnv} {universes : List Name} {parent : Name} {stats : InductiveStats}
    {infos : Array RecInfo} {constructor : Constructor} {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : TypeChecker.MLCtx} (step : MinorModelStep env universes parent source initial final) :
    (final.WF env universes ∧
      final.lctx = (recursorMinorContext domainReader parent constructor domain).lctx) ∧
      ∃ ids, IndexMLCtxExtension initial ids final := ⟨step.context, step.extension⟩

private theorem wholeMinorHistoryThreadsAllLaterModelsFromOneInitialConstructorModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Name} {index : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : MinorTraceTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorMinorTrace env universes trace model finalModel :=
  trace.translated envWF constants definitions fieldOnly model modelWF native reserved support

private theorem wholeTypedMinorHistoryKeepsItsExactFinalNativeReaderAndPersistentExtension
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Name} {index : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    {trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (history : TranslatedRecursorMinorTrace env universes trace initial final) :
    (final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx) ∧
      ∃ ids, IndexMLCtxExtension initial ids final := ⟨history.context, history.extension⟩

private theorem actualTypedMinorGetterKeepsTheRealEmptyOriginalParameterRestriction
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (parent : Name) (index : Nat) (infos : Array RecInfo)
    (constructors : List Constructor) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopCtors stats parent index infos constructors
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorTrace stats parent index infos constructors reader result.1 result.2,
        MinorTraceTranslationSupport env universes trace) :
    (mkRecInfos.loopCtors stats parent index infos constructors
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size ∧
      ∃ trace : RecursorMinorTrace stats parent index infos constructors reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorMinorTrace env universes trace model finalModel :=
  mkRecInfos.loopCtors.getTranslatedMinors stats parent index infos constructors reader envWF constants
    definitions fieldOnly model modelWF native reserved support

private theorem scopedTypedMinorCpsKeepsLaterWholeRecursorCorrectnessExplicit
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (parent : Name) (index : Nat) (infos : Array RecInfo)
    (constructors : List Constructor) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopCtors stats parent index infos constructors
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorTrace stats parent index infos constructors reader result.1 result.2,
        MinorTraceTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorMinorTrace stats parent index infos constructors reader finalInfos finalReader)
      finalModel, reader.RecursorScopeFrame finalReader →
      TranslatedRecursorMinorTrace env universes trace model finalModel →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopCtors stats parent index infos constructors next reader).WF post :=
  mkRecInfos.loopCtors.scopedTranslatedMinors stats parent index infos constructors next reader post
    envWF constants definitions fieldOnly model modelWF native reserved support nextWF

private structure DomainCapture where
  terminal : Expr
  fields : Array Expr
  recursive : Array Expr
  hypotheses : Array Expr
  fieldReader : Context
  hypothesisReader : Context
  body : Expr
  domain : Expr

private def captureDomain (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) : M DomainCapture :=
  mkRecInfos.loopCtorArgs stats constructor.type fun terminal fields recursive => do
    let fieldReader ← readThe Context
    mkRecInfos.loopU stats recursive infos 0 #[] fun hypotheses => do
      let hypothesisReader ← readThe Context
      let (parent, indices) := getIIndices stats terminal
      let body := Expr.app (mkAppN infos[parent]!.motive indices)
        (mkAppN (mkAppN (.const constructor.name stats.levels) stats.params) fields)
      return {
        terminal := terminal
        fields := fields
        recursive := recursive
        hypotheses := hypotheses
        fieldReader := fieldReader
        hypothesisReader := hypothesisReader
        body := body
        domain := hypothesisReader.lctx.mkForall fields
          (hypothesisReader.lctx.mkForall hypotheses body) }

private def capture (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) : M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos.loopCtors stats parent index infos constructors fun updated =>
    return (updated, ← readThe Context)
  return (result, ← readThe Context)

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "minor retained native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "minor retained declaration changed type/dependencies/value/order"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "minor nonallocation reader fields changed"

private def checkFields (stats : InductiveStats) (constructor : Constructor)
    (source : DomainCapture) (before finalReader : Context) : MetaM Unit := do
  let mut opened := constructor.type
  for parameter in stats.params do
    let .forallE _ _ body _ := opened
      | throwError "minor original constructor parameter telescope ended early"
    opened := body.instantiate1 parameter
  let mut generator := before.ngen
  for ordinal in [:source.fields.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "minor actual constructor field telescope ended early"
    let field := source.fields[ordinal]!
    let some declaration := finalReader.lctx.find? field.fvarId!
      | throwError "minor persistent constructor field disappeared"
    unless field == Expr.fvar ⟨generator.curr⟩ && declaration.userName == name &&
        declaration.type == peelTypeAnnotations domain && declaration.binderInfo == binderInfo &&
        declaration.index == before.lctx.decls.size + ordinal &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "minor field ID/name/type/binder/dependencies/order changed"
    opened := body.instantiate1 field
    generator := generator.next
  unless source.terminal == opened && source.fieldReader.ngen.curr == generator.curr do
    throwError "minor constructor terminal or field reader generator changed"
  checkRetained before source.fieldReader
  checkRetained source.fieldReader finalReader

private def checkIHStep (stats : InductiveStats) (infos : Array RecInfo)
    (field hypothesis : Expr) (before finalReader : Context) : MetaM Context := do
  let action := mkRecInfos.loopUArgs field fun terminal arguments => do
    let (parent, indices) := getIIndices stats terminal
    return (arguments, (← getLCtx).mkForall arguments
      (.app (mkAppN infos[parent]!.motive indices) (mkAppN field arguments)))
  let .ok (arguments, raw) := action before
    | throwError "minor independently captured recursive-hypothesis domain failed"
  let domain := peelTypeAnnotations raw
  let some declaration := finalReader.lctx.find? hypothesis.fvarId!
    | throwError "minor retained recursive hypothesis disappeared"
  unless hypothesis == Expr.fvar ⟨before.ngen.curr⟩ &&
      declaration.userName == (before.lctx.get! field.fvarId!).userName.appendAfter "_ih" &&
      declaration.type == domain && declaration.binderInfo == .default &&
      declaration.deps == domain.fvarsList && declaration.index == before.lctx.decls.size do
    throwError "minor exact hypothesis ID/name/type/binder/dependencies/order changed"
  for argument in arguments do
    unless !domain.fvarsList.contains argument.fvarId! do
      throwError "minor temporary recursive-argument fvar survived IH abstraction"
  if !arguments.isEmpty then
    unless arguments[0]! == hypothesis do
      throwError "minor IH did not reuse the dropped first temporary argument ID"
  return recursorIndexContext before declaration.userName .default domain

private def checkHypotheses (stats : InductiveStats) (infos : Array RecInfo)
    (source : DomainCapture) (finalReader : Context) : MetaM Unit := do
  unless source.hypotheses.size == source.recursive.size do
    throwError "minor recursive-hypothesis count changed"
  let mut current := source.fieldReader
  for ordinal in [:source.recursive.size] do
    unless source.fields.contains source.recursive[ordinal]! do
      throwError "minor selected recursive argument is not an actual constructor field"
    current ← checkIHStep stats infos source.recursive[ordinal]! source.hypotheses[ordinal]!
      current finalReader
  unless current.ngen.curr == source.hypothesisReader.ngen.curr &&
      current.lctx.decls.size == source.hypothesisReader.lctx.decls.size do
    throwError "minor temporary UArgs leaked into the persistent hypothesis reader"
  checkRetained current source.hypothesisReader
  checkRetained source.hypothesisReader finalReader

private def checkMinorStep (stats : InductiveStats) (parent : Name) (infos : Array RecInfo)
    (constructor : Constructor) (counts : Nat × Nat) (before finalReader : Context) : MetaM (Context × Expr) := do
  let .ok source := captureDomain stats infos constructor before
    | throwError "minor independently captured actual field/IH/domain source failed"
  unless source.fields.size == counts.1 && source.recursive.size == counts.2 do
    throwError "minor actual field/recursive classification counts changed"
  checkFields stats constructor source before finalReader
  checkHypotheses stats infos source finalReader
  let identifier := FVarId.mk source.hypothesisReader.ngen.curr
  let some declaration := finalReader.lctx.find? identifier
    | throwError "minor actual allocated declaration disappeared"
  let domain := peelTypeAnnotations source.domain
  let name := constructor.name.replacePrefix parent .anonymous
  unless declaration.toExpr == Expr.fvar identifier && declaration.userName == name &&
      declaration.type == domain && declaration.binderInfo == .default &&
      declaration.deps == domain.fvarsList && declaration.index == source.hypothesisReader.lctx.decls.size do
    throwError "minor exact ID/name/domain/binder/dependencies/order changed"
  for field in source.fields ++ source.hypotheses do
    unless !domain.fvarsList.contains field.fvarId! do
      throwError "minor nested field/IH abstraction retained a bound native fvar"
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType domain) : M Expr) finalReader)
    | throwError "minor actual native domain does not fully type-check as a sort"
  let next := recursorIndexContext source.hypothesisReader name .default domain
  checkRetained before next
  return (next, .fvar identifier)

private def checkInfos (expected actual : Array RecInfo) : MetaM Unit := do
  unless actual.size == expected.size do throwError "minor recInfos size changed"
  for ordinal in [:expected.size] do
    let desired := expected[ordinal]!
    let found := actual[ordinal]!
    unless found.motive == desired.motive && found.major == desired.major &&
        found.indices == desired.indices && found.minors == desired.minors do
      throwError "minor exact recInfos update or seeded prefix changed"

private def checkFixture (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) (counts : List (Nat × Nat))
    (reader : Context) : MetaM Unit := do
  let .ok ((updated, finalReader), returnedBase) := capture stats parent index infos constructors reader
    | throwError "minor actual whole-constructor-loop capture failed"
  unless constructors.length == counts.length do throwError "minor fixture counts misaligned"
  let mut expectedInfos := infos
  let mut current := reader
  for (constructor, expectedCount) in constructors.zip counts do
    let (next, minor) ← checkMinorStep stats parent expectedInfos constructor expectedCount current finalReader
    current := next
    expectedInfos := expectedInfos.modify index fun info => { info with minors := info.minors.push minor }
  checkInfos expectedInfos updated
  unless finalReader.ngen.curr == current.ngen.curr &&
      finalReader.lctx.decls.size == current.lctx.decls.size &&
      returnedBase.ngen.curr == reader.ngen.curr && returnedBase.lctx.decls.size == reader.lctx.decls.size do
    throwError "minor ReaderT nested allocation retention or outside-reader restoration changed"
  checkRetained current finalReader
  checkRetained reader returnedBase

private def prepareMotives (reader : Context) (heads : Array Expr)
    (params : Array Expr := #[]) (counts : Array Nat := #[0]) :
    InductiveStats × Array RecInfo × Context := Id.run do
  let mut current := reader
  let mut infos := #[]
  for ordinal in [:heads.size] do
    let count := counts[ordinal]!
    let indices := (Array.range count).map (fun offset => Expr.bvar (count - 1 - offset))
    let majorDomain := mkAppN (mkAppN heads[ordinal]! params) indices
    let motiveType := (List.range count).foldr
      (fun _ body => Expr.forallE `index (.const ``Nat []) body .default)
      (.forallE `major majorDomain (.sort (.succ .zero)) .default)
    let identifier := FVarId.mk ((`MinorFixtureMotive).appendIndexAfter ordinal)
    current := { current with lctx := current.lctx.mkLocalDecl identifier `motive motiveType .default }
    infos := infos.push { motive := .fvar identifier, indices := #[], minors := #[], major := .const ``Nat.zero [] }
  let stats : InductiveStats := {
    lctx := current.lctx, levels := [], resultLevel := .succ .zero,
    indConsts := heads, params, nindices := counts, isNotZero := true }
  return (stats, infos, current)

private def constructorFor (name : Name) : MetaM Constructor := do
  let some information := (← getEnv).find? name
    | throwError "minor genuine constructor declaration missing: {name}"
  return { name, type := (information.type.instantiateLevelParams information.levelParams
    (information.levelParams.map fun _ => .zero)) }

private def checkFailures (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (reader : Context) : MetaM Unit := do
  let noOpening := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match capture stats `Nat 0 infos [constructor] noOpening with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor constructor opening-fuel failure must propagate"
  let noNormalization := { reader with fuel := { reader.fuel with whnf := 0 } }
  match capture stats `Nat 0 infos [constructor] noNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "minor field classification WHNF failure must propagate"
  let noRecursion := { reader with fuel := { reader.fuel with recDepth := 0 } }
  match capture stats `Nat 0 infos [constructor] noRecursion with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor recursive-field recursion-fuel failure must propagate"
  let limited := { reader with fuel := { reader.fuel with inductiveFuel := 2 } }
  let higherOrder := { constructor with type := (.forallE `higherOrder
    (.forallE `first (.const ``Nat [])
      (.forallE `second (.const ``Nat []) (.const ``Nat []) .default) .default)
    (.const ``Nat []) .default) }
  match capture stats `Nat 0 infos [higherOrder] limited with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor actual recursive-field classification fuel failure must propagate"
  let message := "minor callback failure"
  match mkRecInfos.loopCtors stats `Nat 0 infos [constructor]
      (fun _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "minor post-allocation callback exception changed"
  | _ => throwError "minor post-allocation callback failure must propagate"
  checkFixture stats `Nat 0 infos [] [] noOpening

private def checkUntypedMotiveControl (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (reader : Context) : MetaM Unit := do
  let invalid := infos.modify 0 fun info => { info with motive := .mvar ⟨`MinorUntypedMotive⟩ }
  let .ok ((updated, current), _) := capture stats `Nat 0 invalid [constructor] reader
    | throwError "minor allocation-only untyped-motive control unexpectedly failed"
  let declaration := current.lctx.get! updated[0]!.minors.back!.fvarId!
  match ((monadLift (TypeChecker.inferType declaration.type) : M Expr) current) with
  | .error (.other _) => pure ()
  | _ => throwError "minor allocation alone must not justify selected motive/body typing"

private def checkUntypedSourceControl (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (reader : Context) : MetaM Unit := do
  let invalid := { constructor with type := (.forallE `invalid (.mvar ⟨`MinorMissingDomain⟩)
    (.const ``Nat []) .default) }
  let .ok ((updated, current), _) := capture stats `Nat 0 infos [invalid] reader
    | throwError "minor raw untyped-field allocation unexpectedly failed"
  let declaration := current.lctx.get! updated[0]!.minors.back!.fvarId!
  match ((monadLift (TypeChecker.checkType declaration.type) : M Expr) current) with
  | .error (.other _) => pure ()
  | _ => throwError "minor raw untyped-field allocation must not justify constructor application typing"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `MinorOldCarrier
  let element := FVarId.mk `MinorOldElement
  let oldLet := FVarId.mk `MinorOldLet
  let seeded := { reader with
    ngen := { namePrefix := `MinorSeed, idx := 91 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 29)) false }
  let nat := Expr.const ``Nat []
  let (stats, infos, current) := prepareMotives seeded #[nat]
  let zero ← constructorFor ``Nat.zero
  let successor ← constructorFor ``Nat.succ
  checkFixture stats `Nat 0 infos [] [] current
  checkFixture stats `Nat 0 infos [zero] [(0, 0)] current
  checkFixture stats `Nat 0 infos [successor] [(1, 1)] current
  checkFixture stats `Nat 0 infos [zero, successor, successor] [(0, 0), (1, 1), (1, 1)] current
  let prefixed := infos.modify 0 fun info => { info with minors := #[.fvar oldLet] }
  checkFixture stats `Nat 0 prefixed [successor] [(1, 1)] current
  checkFixture stats `NotNat 0 infos [successor] [(1, 1)] current
  checkFixture stats `Nat infos.size infos [successor] [(1, 1)] current
  let aliased := { successor with type := .forallE `aliased (.const ``MinorDomainAlias []) nat .implicit }
  let annotated := { successor with type := .forallE `annotated (unary ``outParam nat) nat .default }
  let metadata := { successor with type := .forallE `metadata (.mdata {} (unary ``outParam nat)) nat .default }
  checkFixture stats `Nat 0 infos [aliased, annotated, metadata] [(1, 1), (1, 1), (1, 1)] current
  let tree := Expr.const ``MinorTree []
  let (treeStats, treeInfos, treeCurrent) := prepareMotives seeded #[tree]
  let treeLeaf ← constructorFor ``MinorTree.leaf
  let higher ← constructorFor ``MinorTree.higher
  let dependent ← constructorFor ``MinorTree.dependent
  let pair ← constructorFor ``MinorTree.pair
  let mixed ← constructorFor ``MinorTree.mixed
  checkFixture treeStats ``MinorTree 0 treeInfos [treeLeaf, higher, dependent, pair, mixed]
    [(0, 0), (1, 1), (1, 1), (2, 2), (3, 1)] treeCurrent
  let (mutualStats, mutualInfos, mutualCurrent) := prepareMotives seeded
    #[nat, .const ``Bool []] #[] #[0, 0]
  let flag ← constructorFor ``Bool.true
  checkFixture mutualStats `Nat 0 mutualInfos [successor] [(1, 1)] mutualCurrent
  checkFixture mutualStats `Bool 1 mutualInfos [flag] [(0, 0)] mutualCurrent
  let list := Expr.const ``List [.zero]
  let (listStats, listInfos, listCurrent) := prepareMotives seeded #[list] #[.fvar carrier]
  let listStats := { listStats with levels := [.zero] }
  let nil ← constructorFor ``List.nil
  let cons ← constructorFor ``List.cons
  checkFixture listStats `List 0 listInfos [nil, cons] [(0, 0), (2, 1)] listCurrent
  let family := Expr.const ``MinorFamily []
  let (familyStats, familyInfos, familyCurrent) := prepareMotives seeded #[family] #[.fvar carrier] #[1]
  let indexedLeaf ← constructorFor ``MinorFamily.leaf
  let indexedDirect ← constructorFor ``MinorFamily.direct
  let indexedHigher ← constructorFor ``MinorFamily.higher
  checkFixture familyStats ``MinorFamily 0 familyInfos [indexedLeaf, indexedDirect, indexedHigher]
    [(2, 0), (2, 1), (2, 1)] familyCurrent
  checkFailures stats infos successor current
  checkUntypedMotiveControl stats infos zero current
  checkUntypedSourceControl stats infos successor current
  logInfo "minor runtime: fourteen positive whole-loop captures with full domain type-checking plus two allocation-only untyped-motive/field-source controls; exact domains/names/IDs/dependencies/recInfos updates; previous fields/IHs/minors persist inside the nested ReaderT scope; temporary UArgs disappear before IH allocation with intentional ID reuse; direct/higher-order/dependent and multiple IHs, aliases/metadata/annotations, multiple constructors/parents and parameterized indexed families; five classification/fuel/post-allocation-callback failures"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "minor unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "minor audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "minor new module-owned axiom {name}"
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
      throwError "minor inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "minor inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited minor foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "minor inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context minor abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "minor native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "minor native interface provenance changed: {name}"
    logInfo m!"pinned existing native minor interface: {name}"

#print axioms actualNativeGetterDoesNotAssumeWholeMinorDomainTyping
#print axioms sameConstructorFieldEndpointTypesItsOwnExactAppliedConstructor
#print axioms bindingEarlierFieldsAtTheIHReaderRequiresTheSameSelectedDeclarations
#print axioms minorBodyTypingUsesTheSameActualConstructorAndSelectedMotive
#print axioms nestedMinorDomainAbstractionReturnsToTheInitialConstructorModel
#print axioms theSameMinorDomainAtTheIHReaderIsLiftedByBothPersistentSuffixes
#print axioms actualMinorOpeningStillNeedsAnnotationsAtTheCurrentHypothesisReader
#print axioms allocatedMinorExtendsTheCurrentHypothesisModelNotTheInitialConstructorModel
#print axioms actualTypedMinorGetterKeepsTheRealEmptyOriginalParameterRestriction
#print axioms scopedTypedMinorCpsKeepsLaterWholeRecursorCorrectnessExplicit
#print axioms nestedMinorWeakeningCannotUseTheOriginalOrOneSuffixBody
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``metadataMinorBarrierKeepsTheActualDomain,
      ``nestedMinorWeakeningCannotUseTheOriginalOrOneSuffixBody,
      ``minorFailureCannotSupplySuccessfulOutputs,
      ``actualMinorNameUsesTheDeclaredConstructorPrefixReplacement,
      ``actualMinorUsesTheCurrentHypothesisReaderGenerator,
      ``nativeMinorUpdateKeepsTheWholeRecInfoArraySize,
      ``selectedMinorUpdateNeedsItsActualParentBound,
      ``completedMinorTraceKeepsItsCurrentNestedReader,
      ``wholeMinorTraceKeepsEveryOtherParentExactly,
      ``wholeMinorTraceAddsOnlyTheActualConstructorCount,
      ``wholeMinorTraceKeepsItsExactSeededMinorPrefix,
      ``nativeMinorDomainAbstractsHypothesesBeforeConstructorFields,
      ``actualMinorBodyKeepsOriginalConstructorLevelsAndParameters,
      ``unary, ``captureDomain, ``capture, ``checkRetained, ``checkFields, ``checkIHStep,
      ``checkHypotheses, ``checkMinorStep, ``checkInfos, ``checkFixture, ``prepareMotives,
      ``constructorFor, ``checkFailures, ``checkUntypedMotiveControl, ``checkUntypedSourceControl,
      ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``sameActualMinorSourceDerivesItsNestedFieldAndHypothesisScope,
      ``wholeMinorTraceKeepsPreviousFieldsAndHypothesesInItsScope,
      ``actualNativeGetterDoesNotAssumeWholeMinorDomainTyping] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``sameConstructorFieldEndpointTypesItsOwnExactAppliedConstructor,
      ``bindingEarlierFieldsAtTheIHReaderRequiresTheSameSelectedDeclarations,
      ``minorBodyTypingUsesTheSameActualConstructorAndSelectedMotive,
      ``nestedMinorDomainAbstractionReturnsToTheInitialConstructorModel,
      ``theSameMinorDomainAtTheIHReaderIsLiftedByBothPersistentSuffixes,
      ``actualMinorOpeningStillNeedsAnnotationsAtTheCurrentHypothesisReader,
      ``allocatedMinorExtendsTheCurrentHypothesisModelNotTheInitialConstructorModel,
      ``minorAllocationAddsExactlyItsOwnIdentifierToTheCurrentModel,
      ``sameActualMinorSourceDerivesItsWholeFieldHypothesisAndMinorModel,
      ``sameTypedMinorStepRetainsFieldsHypothesesAndMinorInItsFinalModel,
      ``wholeMinorHistoryThreadsAllLaterModelsFromOneInitialConstructorModel,
      ``wholeTypedMinorHistoryKeepsItsExactFinalNativeReaderAndPersistentExtension,
      ``actualTypedMinorGetterKeepsTheRealEmptyOriginalParameterRestriction,
      ``scopedTypedMinorCpsKeepsLaterWholeRecursorCorrectnessExplicit] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveMinorTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveMinorTranslation native
  auditModule `Lean4Lean.Verify.InductiveMinorTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "minor translation: 30 proof controls; exact constructor application and selected motive support derive minor body/domain typing; nested abstraction at the initial constructor model and real combined suffix lifting at the current IH reader; whole-pass model threading keeps fields/IHs/minors and the real zero-original-parameter typed restriction; native nonzero-parameter controls are not stronger typing claims; inherited foundations/eight native interfaces pinned and global native range axiom forbidden"

end InductiveMinorTranslationTest
