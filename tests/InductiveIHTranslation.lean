import Lean4Lean.Verify.InductiveIHTrace
import Lean4Lean.Verify.InductiveIHTranslationCPS
import Lean4Lean.Verify.InductiveUArgTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIHTranslationTest

abbrev IHHeaderAlias := Nat → Nat
abbrev IHDomainAlias := Nat

inductive IndexedFamily (carrier : Type) : Nat → Type where
  | make (ordinal : Nat) (value : carrier) : IndexedFamily carrier ordinal

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def equalityDomain (carrier left right : Expr) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) carrier) left) right

private theorem metadataBarrierDoesNotPermitReplacingAnIHDomain (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem actualIHNameComesFromTheStoredFieldName (reader : Context) (field : Expr) :
    recursorIHName reader field = (reader.lctx.get! field.fvarId!).userName.appendAfter "_ih" := rfl

private theorem IHScopeReusesTheBaseGeneratorNotTheTemporaryArgumentReader
    (reader : Context) (field domain : Expr) :
    (recursorIHContext reader field domain).ngen = reader.ngen.next := rfl

private theorem retainedParentLocalCannotUseIdentityIHWeakening :
    (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 = .forallE (.sort .zero) (.bvar 2) ∧
      (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 ≠ .forallE (.sort .zero) (.bvar 1) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem failureCannotSupplySuccessfulIHOutputs
    {ResultType : Type} (action : M ResultType) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : action reader = .error failure) :
    ∀ result, action reader ≠ .ok result := by
  intro result success
  rw [failed] at success
  cases success

private theorem completedIHTraceKeepsEveryOriginalOutput
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context) (complete : ¬ index < fields.size) :
    RecursorIHTrace stats fields infos index hypotheses reader hypotheses reader := .stop complete

private theorem actualIHTraceAddsOnlyOneHypothesisPerRemainingField
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    finalHypotheses.size = hypotheses.size + (fields.size - index) := trace.counts

private theorem actualIHTraceKeepsTheExactHypothesisPrefix
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    ∃ appended, finalHypotheses.toList = hypotheses.toList ++ appended ∧
      appended.length = fields.size - index := trace.prefix

private theorem actualIHArrayMatchesThePersistedNativeAllocationSuffix
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    ∃ allocated : List LocalDecl,
      finalReader.lctx.toList = allocated.reverse ++ reader.lctx.toList ∧
      finalHypotheses.toList = hypotheses.toList ++ allocated.map LocalDecl.toExpr ∧
      ∀ declaration ∈ allocated,
        declaration.value? (allowNondep := true) = none ∧ declaration.kind = .default := trace.allocations

private theorem actualNativeIHScopeDoesNotDischargeMotiveTyping
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := trace.scope readerWF reserved

private theorem actualIHDeclarationsNeedOnlyTheSuppliedNativePrefixDeclarationReceipt
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (declared : RecursorFieldsDeclared reader.lctx hypotheses) :
    RecursorFieldsDeclared finalReader.lctx finalHypotheses := trace.declared declared

private theorem actualDomainCpsRetainsItsActualUArgWitnessNotAnInventedDomain
    (stats : InductiveStats) (infos : Array RecInfo) (field : Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopUArgs field (fun terminal arguments => do
      let (parent, indices) := getIIndices stats terminal
      return (← getLCtx).mkForall arguments
        (.app (mkAppN infos[parent]!.motive indices) (mkAppN field arguments))) reader).WF
      (RecursorIHDomainSource stats infos field reader) :=
  mkRecInfos.loopUArgs.ihDomainSource stats infos field reader readerWF reserved

private theorem actualGetterCarriesTheSameWholeIHTrace
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopU stats fields infos index hypotheses
      (fun finalHypotheses => do return (finalHypotheses, ← readThe Context)) reader).WF fun result =>
      RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2 ∧
        reader.RecursorScopeFrame result.2 ∧ result.1.size = hypotheses.size + (fields.size - index) :=
  mkRecInfos.loopU.getTrace stats fields infos index hypotheses reader readerWF reserved

private theorem defaultingNativeSelectionStillNeedsItsExactMotiveTypingPremise
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {virtual : VLCtx} {terminal : Expr}
    (support : IHMotiveApplicationSupport env universes stats infos virtual terminal)
    (terminalSemantic : VExpr) (translated : TrExprS env universes virtual terminal terminalSemantic) :
    ∃ motive level,
      TrExprS env universes virtual
        (mkAppN infos[(getIIndices stats terminal).1]!.motive (getIIndices stats terminal).2) motive ∧
      env.HasType universes.length virtual.toCtx motive (.forallE terminalSemantic (.sort level)) :=
  support terminalSemantic translated

private theorem sameUArgEndpointTypesTheExactMotiveApplicationBody
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace field reader terminal arguments argumentReader}
    {initial argumentModel : TypeChecker.MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal) :
    ∃ body level, TrExprS env universes argumentModel.vlctx
        (recursorIHBody stats infos field terminal arguments) body ∧
      env.HasType universes.length argumentModel.vlctx.toCtx body (.sort level) :=
  endpoint.ihBodyTranslation envWF motiveSupport

private theorem IHDomainAbstractionReturnsItsStrongTranslationToTheInitialFieldModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace field reader terminal arguments argumentReader}
    {initial argumentModel : TypeChecker.MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal) :
    ∃ domain level, TrExprS env universes initial.vlctx
        (recursorIHDomain stats infos field terminal arguments argumentReader) domain ∧
      env.HasType universes.length initial.vlctx.toCtx domain (.sort level) :=
  endpoint.ihDomainTranslation envWF modelWF motiveSupport

private theorem actualIHOpeningStillNeedsItsOwnAnnotationSupportAtTheBase
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace field reader terminal arguments argumentReader}
    {initial argumentModel : TypeChecker.MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (modelWF : initial.WF env universes) (native : initial.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal)
    (annotations : IndexAnnotationSupport env universes reader
      (recursorIHDomain stats infos field terminal arguments argumentReader)) :
    ∃ raw peeled level, RecursorIHOpening env universes reader initial.vlctx field
      (recursorIHDomain stats infos field terminal arguments argumentReader) raw peeled level :=
  endpoint.ihOpening envWF constants definitions modelWF native reserved motiveSupport annotations

private theorem typedIHOpeningUsesTheSameRestoredGeneratorAndCurrentNativeBase
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {field domain : Expr} {raw : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual domain raw)
    (typed : env.HasType universes.length virtual.toCtx raw (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled, RecursorIHOpening env universes reader virtual field domain raw peeled level :=
  translatedIHOpening_ofDomain envWF constants definitions correspondence reserved translated typed uniform

private theorem oneIHOpeningPushesItsInitialModelNotItsTemporaryArgumentModel
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {field domain : Expr} {raw peeled : VExpr} {level : VLevel}
    (opening : RecursorIHOpening env universes reader virtual field domain raw peeled level)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorIHMLCtx reader model field domain peeled).WF env universes ∧
      (recursorIHMLCtx reader model field domain peeled).lctx = (recursorIHContext reader field domain).lctx ∧
      (recursorIHMLCtx reader model field domain peeled).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled :=
  opening.mixedContext model modelWF native converted reserved

private theorem oneIHOpeningPersistsExactlyOneIHIdentifier
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {field domain : Expr} {raw peeled : VExpr} {level : VLevel}
    (opening : RecursorIHOpening env universes reader virtual field domain raw peeled level)
    (model : TypeChecker.MLCtx) :
    IndexMLCtxExtension model [⟨reader.ngen.curr⟩] (recursorIHMLCtx reader model field domain peeled) :=
  opening.extension model

private theorem exactNativeDomainSourceDerivesOnlyItsOwnTypedIHStep
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field domain : Expr} {reader : Context}
    (source : RecursorIHDomainSource stats infos field reader domain)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : IHDomainSourceTranslationSupport env universes source model) :
    ∃ finalModel, IHModelStep env universes source model finalModel :=
  source.translatedStep envWF constants definitions model modelWF native reserved support

private theorem sameTypedIHStepDerivesItsOwnCurrentNativeReader
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos field reader domain} {initial final : TypeChecker.MLCtx}
    (step : IHModelStep env universes source initial final) :
    final.WF env universes ∧ final.lctx = (recursorIHContext reader field domain).lctx := step.context

private theorem sameTypedIHStepPersistsOnlyTheRestoredIHAllocation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {field domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos field reader domain} {initial final : TypeChecker.MLCtx}
    (step : IHModelStep env universes source initial final) :
    IndexMLCtxExtension initial [⟨reader.ngen.curr⟩] final := step.extension

private theorem wholeIHHistoryDerivesAllLaterModelsFromOnlyTheInitialFieldModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : IHTraceTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorIHTrace env universes trace model finalModel :=
  trace.translated envWF constants definitions model modelWF native reserved support

private theorem wholeTypedIHHistoryDerivesTheExactCurrentIHReaderCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader}
    {initial final : TypeChecker.MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := history.context

private theorem wholeTypedIHHistoryPersistsOnlyItsActualHypothesisSuffix
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader}
    {initial final : TypeChecker.MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final) :
    ∃ ids, IndexMLCtxExtension initial ids final ∧
      finalHypotheses.toList = hypotheses.toList ++ ids.map Expr.fvar := history.extension

private theorem typedHypothesisAbstractionReturnsToTheInitialFieldModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index #[] reader finalHypotheses finalReader}
    {initial final : TypeChecker.MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall finalHypotheses body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted :=
  history.typedHypothesisAbstraction envWF translated typed

private theorem zeroIHHistoryKeepsTheSameInitialModelAndPrefix
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context) (complete : ¬ index < fields.size)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx) :
    TranslatedRecursorIHTrace env universes
      (RecursorIHTrace.stop (stats := stats) (fields := fields) (infos := infos)
        (index := index) (hypotheses := hypotheses) (reader := reader) complete) model model :=
  .stop complete modelWF native

private def captureTuple (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) : M (Array Expr × Context) :=
  mkRecInfos.loopU stats fields infos index hypotheses fun finalHypotheses => do
    return (finalHypotheses, ← readThe Context)

private theorem actualGetterBuildsOneFinalIHModelFromOneInitialModel
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureTuple stats fields infos index hypotheses reader).WF fun result =>
      ∀ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        IHTraceTranslationSupport env universes trace) :
    (captureTuple stats fields infos index hypotheses reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = hypotheses.size + (fields.size - index) ∧
      ∃ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorIHTrace env universes trace model finalModel :=
  mkRecInfos.loopU.getTranslatedHypotheses stats fields infos index hypotheses reader
    envWF constants definitions model modelWF native reserved support

private theorem scopedTypedIHCpsKeepsTheLaterMinorDomainCorrectnessObligationExplicit
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (next : Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureTuple stats fields infos index hypotheses reader).WF fun result =>
      ∀ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        IHTraceTranslationSupport env universes trace)
    (nextWF : ∀ finalHypotheses finalReader
      (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) finalModel,
      reader.RecursorScopeFrame finalReader → TranslatedRecursorIHTrace env universes trace model finalModel →
      (next finalHypotheses finalReader).WF post) :
    (mkRecInfos.loopU stats fields infos index hypotheses next reader).WF post :=
  mkRecInfos.loopU.scopedTranslatedHypotheses stats fields infos index hypotheses next reader post
    envWF constants definitions model modelWF native reserved support nextWF

private structure DomainCapture where
  domain : Expr
  terminal : Expr
  arguments : Array Expr
  reader : Context

private def captureDomain (stats : InductiveStats) (infos : Array RecInfo) (field : Expr) :
    M (DomainCapture × Context) := do
  let result ← mkRecInfos.loopUArgs field fun terminal arguments => do
    let reader ← readThe Context
    let (parent, indices) := getIIndices stats terminal
    let body := Expr.app (mkAppN infos[parent]!.motive indices) (mkAppN field arguments)
    return { domain := reader.lctx.mkForall arguments body, terminal, arguments, reader }
  return (result, ← readThe Context)

private def capture (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (start : Nat) (initialHypotheses : Array Expr) : M ((Array Expr × Context) × Context) := do
  let result ← mkRecInfos.loopU stats fields infos start initialHypotheses fun hypotheses => do
    return (hypotheses, ← readThe Context)
  return (result, ← readThe Context)

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "IH retained native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "IH retained native declaration changed type/dependencies/value/order"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "IH nonallocation reader fields changed"

private def checkStep (stats : InductiveStats) (infos : Array RecInfo) (field hypothesis : Expr)
    (before finalReader : Context) : MetaM Context := do
  let .ok (source, restored) := captureDomain stats infos field before
    | throwError "IH independently captured actual UArgs domain source failed"
  unless restored.ngen.curr == before.ngen.curr && restored.lctx.decls.size == before.lctx.decls.size do
    throwError "IH temporary argument reader did not restore the base before IH allocation"
  checkRetained before restored
  let fieldDeclaration := before.lctx.get! field.fvarId!
  let expectedName := fieldDeclaration.userName.appendAfter "_ih"
  let expectedDomain := peelTypeAnnotations source.domain
  let some declaration := finalReader.lctx.find? hypothesis.fvarId!
    | throwError "IH actual newly allocated declaration disappeared"
  unless hypothesis == Expr.fvar ⟨before.ngen.curr⟩ && declaration.toExpr == hypothesis &&
      declaration.userName == expectedName && declaration.binderInfo == .default &&
      declaration.type == expectedDomain && declaration.deps == expectedDomain.fvarsList &&
      declaration.index == before.lctx.decls.size do
    throwError "IH exact restored-generator ID/name/domain/dependencies/binder/order changed"
  for argument in source.arguments do
    unless !expectedDomain.fvarsList.contains argument.fvarId! do
      throwError "IH abstracted domain still contains a dropped temporary argument fvar"
  if !source.arguments.isEmpty then
    unless source.arguments[0]! == hypothesis do
      throwError "IH allocation did not intentionally reuse the first dropped temporary argument ID"
  let .ok (.sort _) := ((monadLift (TypeChecker.inferType declaration.type) : M Expr) finalReader)
    | throwError "IH actual persisted declaration domain is not inferable at the actual final reader"
  let next := recursorIndexContext before expectedName .default expectedDomain
  checkRetained before next
  return next

private def checkFixture (stats : InductiveStats) (infos : Array RecInfo) (fields : Array Expr)
    (start : Nat) (initialHypotheses : Array Expr) (reader : Context) : MetaM Unit := do
  let .ok ((hypotheses, finalReader), returnedBase) := capture stats fields infos start initialHypotheses reader
    | throwError "IH actual whole-loop capture failed"
  let count := fields.size - start
  unless hypotheses.size == initialHypotheses.size + count &&
      hypotheses.extract 0 initialHypotheses.size == initialHypotheses &&
      finalReader.lctx.decls.size == reader.lctx.decls.size + count do
    throwError "IH whole-loop counts, prefixed hypotheses or retained-base allocation count changed"
  let mut current := reader
  for offset in [:count] do
    current ← checkStep stats infos fields[start + offset]!
      hypotheses[initialHypotheses.size + offset]! current finalReader
  unless finalReader.ngen.curr == current.ngen.curr && returnedBase.ngen.curr == reader.ngen.curr &&
      returnedBase.lctx.decls.size == reader.lctx.decls.size do
    throwError "IH generator restoration leaked temporary argument allocation or callback IH scope"
  checkRetained reader finalReader
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
    let identifier := FVarId.mk ((`IHFixtureMotive).appendIndexAfter ordinal)
    current := { current with lctx := current.lctx.mkLocalDecl identifier `motive motiveType .default }
    infos := infos.push { motive := .fvar identifier, indices := #[], minors := #[], major := .const ``Nat.zero [] }
  let stats : InductiveStats := {
    lctx := current.lctx, levels := [], resultLevel := .succ .zero,
    indConsts := heads, params, nindices := counts, isNotZero := true }
  return (stats, infos, current)

private def prepareFields (reader : Context) (types : Array (Name × Expr)) : Array Expr × Context := Id.run do
  let mut current := reader
  let mut fields := #[]
  for ordinal in [:types.size] do
    let identifier := FVarId.mk ((`IHRecursiveField).appendIndexAfter ordinal)
    let (name, type) := types[ordinal]!
    current := { current with lctx := current.lctx.mkLocalDecl identifier name type .implicit }
    fields := fields.push (.fvar identifier)
  return (fields, current)

private def dependentField : Expr :=
  .forallE `carrier (.sort (.succ .zero))
    (.forallE `element (.bvar 0)
      (.forallE `agreement (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.const ``Nat []) .default) .implicit) .default

private def checkInferenceFailures (stats : InductiveStats) (infos : Array RecInfo)
    (field : Expr) (reader : Context) : MetaM Unit := do
  match capture stats #[.mvar ⟨`IHMissingMetavariable⟩] infos 0 #[] reader with
  | .error (.other _) => pure ()
  | _ => throwError "IH actual recursive-field inference failure must propagate"
  match capture stats #[.bvar 0] infos 0 #[] reader with
  | .error (.other _) => pure ()
  | _ => throwError "IH loose-bound-variable inference failure must propagate"
  let message := "IH callback failure"
  match mkRecInfos.loopU stats #[field] infos 0 #[] (fun _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "IH callback exception changed"
  | _ => throwError "IH callback failure must propagate"

private def checkFuelFailures (stats : InductiveStats) (infos : Array RecInfo)
    (field directField : Expr) (reader : Context) : MetaM Unit := do
  let noInference := { reader with fuel := { reader.fuel with recDepth := 0 } }
  match capture stats #[field] infos 0 #[] noInference with
  | .error .deepRecursion => pure ()
  | _ => throwError "IH recursive-field inference recursion-fuel failure must propagate"
  let noOpening := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match capture stats #[field] infos 0 #[] noOpening with
  | .error .deepRecursion => pure ()
  | _ => throwError "IH actual UArgs opening fuel failure must propagate"
  let noBodyNormalization := { reader with fuel := { reader.fuel with whnf := 0 } }
  match capture stats #[field] infos 0 #[] noBodyNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "IH actual recursive-field body WHNF failure must propagate"
  match capture stats #[directField] infos 0 #[] noBodyNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "IH actual recursive-field initial WHNF failure must propagate"
  checkFixture stats infos #[.mvar ⟨`IHSkippedFailure⟩] 1 #[] noOpening

private def checkUntypedMotiveControl (stats : InductiveStats) (infos : Array RecInfo)
    (field : Expr) (reader : Context) : MetaM Unit := do
  let invalid := infos.modify 0 fun info => { info with motive := .mvar ⟨`IHUntypedMotive⟩ }
  let .ok ((hypotheses, current), _) := capture stats #[field] invalid 0 #[] reader
    | throwError "IH allocation-only untyped-motive control unexpectedly failed before semantic support"
  let declaration := current.lctx.get! hypotheses[0]!.fvarId!
  match ((monadLift (TypeChecker.inferType declaration.type) : M Expr) current) with
  | .error (.other _) => pure ()
  | _ => throwError "IH raw native allocation alone must not silently justify motive/domain typing"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `IHOldCarrier
  let element := FVarId.mk `IHOldElement
  let oldLet := FVarId.mk `IHOldLet
  let seeded := { reader with
    ngen := { namePrefix := `IHSeed, idx := 71 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 29)) false }
  let nat := Expr.const ``Nat []
  let (stats, infos, root) := prepareMotives seeded #[nat]
  let (fields, current) := prepareFields root #[(`direct, nat),
    (`higherOrder, .forallE `argument nat nat .default), (`dependent, dependentField),
    (`aliasHeader, .const ``IHHeaderAlias []),
    (`aliasBody, .forallE `argument nat (.const ``IHHeaderAlias []) .default),
    (`metadataHeader, .mdata {} (.forallE `argument nat nat .default)),
    (`annotated, .forallE `argument (unary ``outParam nat) nat .default),
    (`metadataDomain, .forallE `argument (.mdata {} (unary ``outParam nat)) nat .default),
    (`aliasDomain, .forallE `argument (.const ``IHDomainAlias []) nat .default)]
  checkFixture stats infos #[] 0 #[] current
  checkFixture stats infos fields fields.size #[.fvar oldLet] current
  for ordinal in [:fields.size] do
    checkFixture stats infos #[fields[ordinal]!] 0 #[] current
  checkFixture stats infos fields 0 #[] current
  checkFixture stats infos fields 2 #[.fvar oldLet] current
  checkFixture stats infos #[.mvar ⟨`IHSkippedField⟩, fields[1]!] 1 #[.fvar oldLet] current
  let (mutualStats, mutualInfos, mutualRoot) := prepareMotives seeded #[nat, .const ``Bool []] #[] #[0, 0]
  let (mutualFields, mutualCurrent) := prepareFields mutualRoot #[(`natural, nat), (`flag, .const ``Bool [])]
  checkFixture mutualStats mutualInfos mutualFields 0 #[] mutualCurrent
  let list := Expr.const ``List [.zero]
  let (paramStats, paramInfos, paramRoot) := prepareMotives seeded #[list] #[.fvar carrier]
  let (paramFields, paramCurrent) := prepareFields paramRoot #[(`parameterized,
    .forallE `argument nat (.app list (.fvar carrier)) .default)]
  checkFixture paramStats paramInfos paramFields 0 #[] paramCurrent
  let family := Expr.const ``IndexedFamily []
  let (indexStats, indexInfos, indexRoot) := prepareMotives seeded #[family] #[.fvar carrier] #[1]
  let (indexFields, indexCurrent) := prepareFields indexRoot #[(`indexed,
    .forallE `ordinal nat (.app (.app family (.fvar carrier)) (.bvar 0)) .default)]
  checkFixture indexStats indexInfos indexFields 0 #[] indexCurrent
  checkInferenceFailures stats infos fields[0]! current
  checkFuelFailures stats infos fields[1]! fields[0]! current
  checkUntypedMotiveControl stats infos fields[0]! current
  logInfo "IH runtime: eighteen positive whole-loop captures plus one allocation-only untyped-motive control; direct/higher-order/dependent/alias/metadata/annotated and multiple IHs; exact names/IDs/domains/dependencies/order; temporary arguments disappear and first temporary ID is deliberately reused as IH; original parameters/indices and prefix/skipped-field controls; seven inference/initial/body-WHNF/fuel/post-allocation-callback failure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "IH unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "IH audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "IH new module-owned axiom {name}"
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
      throwError "IH inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "IH inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited IH foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "IH inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context IH abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "IH native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "IH native interface provenance changed: {name}"
    logInfo m!"pinned existing native IH interface: {name}"

#print axioms actualGetterCarriesTheSameWholeIHTrace
#print axioms defaultingNativeSelectionStillNeedsItsExactMotiveTypingPremise
#print axioms sameUArgEndpointTypesTheExactMotiveApplicationBody
#print axioms IHDomainAbstractionReturnsItsStrongTranslationToTheInitialFieldModel
#print axioms typedIHOpeningUsesTheSameRestoredGeneratorAndCurrentNativeBase
#print axioms exactNativeDomainSourceDerivesOnlyItsOwnTypedIHStep
#print axioms wholeIHHistoryDerivesAllLaterModelsFromOnlyTheInitialFieldModel
#print axioms typedHypothesisAbstractionReturnsToTheInitialFieldModel
#print axioms actualGetterBuildsOneFinalIHModelFromOneInitialModel
#print axioms scopedTypedIHCpsKeepsTheLaterMinorDomainCorrectnessObligationExplicit
#print axioms retainedParentLocalCannotUseIdentityIHWeakening
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``metadataBarrierDoesNotPermitReplacingAnIHDomain,
      ``actualIHNameComesFromTheStoredFieldName,
      ``IHScopeReusesTheBaseGeneratorNotTheTemporaryArgumentReader,
      ``retainedParentLocalCannotUseIdentityIHWeakening,
      ``failureCannotSupplySuccessfulIHOutputs,
      ``completedIHTraceKeepsEveryOriginalOutput,
      ``actualIHTraceAddsOnlyOneHypothesisPerRemainingField,
      ``actualIHTraceKeepsTheExactHypothesisPrefix,
      ``unary, ``equalityDomain, ``captureTuple, ``captureDomain, ``capture, ``checkRetained,
      ``checkStep, ``checkFixture, ``prepareMotives, ``prepareFields, ``dependentField,
      ``checkInferenceFailures, ``checkFuelFailures, ``checkUntypedMotiveControl,
      ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``actualIHArrayMatchesThePersistedNativeAllocationSuffix,
      ``actualNativeIHScopeDoesNotDischargeMotiveTyping,
      ``actualIHDeclarationsNeedOnlyTheSuppliedNativePrefixDeclarationReceipt,
      ``actualDomainCpsRetainsItsActualUArgWitnessNotAnInventedDomain,
      ``actualGetterCarriesTheSameWholeIHTrace] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``defaultingNativeSelectionStillNeedsItsExactMotiveTypingPremise,
      ``sameUArgEndpointTypesTheExactMotiveApplicationBody,
      ``IHDomainAbstractionReturnsItsStrongTranslationToTheInitialFieldModel,
      ``actualIHOpeningStillNeedsItsOwnAnnotationSupportAtTheBase,
      ``typedIHOpeningUsesTheSameRestoredGeneratorAndCurrentNativeBase,
      ``oneIHOpeningPushesItsInitialModelNotItsTemporaryArgumentModel,
      ``oneIHOpeningPersistsExactlyOneIHIdentifier,
      ``exactNativeDomainSourceDerivesOnlyItsOwnTypedIHStep,
      ``sameTypedIHStepDerivesItsOwnCurrentNativeReader,
      ``sameTypedIHStepPersistsOnlyTheRestoredIHAllocation,
      ``wholeIHHistoryDerivesAllLaterModelsFromOnlyTheInitialFieldModel,
      ``wholeTypedIHHistoryDerivesTheExactCurrentIHReaderCorrespondence,
      ``wholeTypedIHHistoryPersistsOnlyItsActualHypothesisSuffix,
      ``typedHypothesisAbstractionReturnsToTheInitialFieldModel,
      ``zeroIHHistoryKeepsTheSameInitialModelAndPrefix,
      ``actualGetterBuildsOneFinalIHModelFromOneInitialModel,
      ``scopedTypedIHCpsKeepsTheLaterMinorDomainCorrectnessObligationExplicit] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveIHTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveIHTranslation native
  auditModule `Lean4Lean.Verify.InductiveIHTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "IH translation: 30 proof controls; pinned inherited foundations and eight existing native interfaces; global native range axiom forbidden; same actual recursive-hypothesis domain typing and whole-trace model threading from one initial field model; explicit motive alignment and later minor-domain correctness obligations"

end InductiveIHTranslationTest
