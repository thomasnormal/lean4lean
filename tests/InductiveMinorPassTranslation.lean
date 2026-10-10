import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveParentContextTranslationCPS
import Lean4Lean.Verify.InductiveMinorPassTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveMinorPassTranslationTest

mutual
  inductive PassLeft where
    | leaf : PassLeft
    | right (child : PassRight) : PassLeft
  inductive PassRight where
    | left (child : PassLeft) : PassRight
    | higher (children : Nat → PassLeft) : PassRight
end

inductive PassHigher where
  | leaf : PassHigher
  | higher (children : Nat → PassHigher) : PassHigher
  | dependent (children : (carrier : Type) → carrier → PassHigher) : PassHigher
  | pair (left right : PassHigher) : PassHigher

inductive PassIndexed : Nat → Type where
  | leaf (ordinal : Nat) : PassIndexed ordinal
  | direct (ordinal : Nat) (child : PassIndexed ordinal) : PassIndexed ordinal
  | higher (ordinal : Nat) (children : Nat → PassIndexed ordinal) : PassIndexed ordinal

inductive PassFamily (carrier : Type) : Nat → Type where
  | leaf (ordinal : Nat) (payload : carrier) : PassFamily carrier ordinal
  | direct (ordinal : Nat) (child : PassFamily carrier ordinal) : PassFamily carrier ordinal

private theorem retainingEarlierParentLocalsNeedsRealSuffixWeakening :
    (VExpr.forallE (.bvar 0) (.bvar 2)).liftN 3 = .forallE (.bvar 3) (.bvar 5) ∧
      (VExpr.forallE (.bvar 0) (.bvar 2)).liftN 3 ≠ .forallE (.bvar 0) (.bvar 2) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem wholePassFailureCannotSupplySuccessfulOutputs
    {ResultType : Type} (action : M ResultType) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : action reader = .error failure) :
    ∀ result, action reader ≠ .ok result := by
  intro result success
  rw [failed] at success
  cases success

private theorem completedMinorPassKeepsEverySeedAndTheSameReader
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (reader : Context) (complete : ¬ parent < types.size) :
    RecursorMinorPassTrace stats types parent infos reader infos reader := .stop complete

private theorem oneActualParentStepUsesTheSameSelectedConstructorPassAndItsLaterReader
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos middleInfos finalInfos : Array RecInfo} {reader middleReader finalReader : Context}
    (bound : parent < types.size)
    (head : RecursorMinorTrace stats types[parent]!.name parent infos types[parent]!.ctors
      reader middleInfos middleReader)
    (tail : RecursorMinorPassTrace stats types (parent + 1) middleInfos middleReader finalInfos finalReader) :
    RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader := .step bound head tail

private theorem nativeWholePassScopeRetainsEarlierParentsResidualFieldsHypothesesAndMinors
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := trace.scope readerWF reserved

private theorem nativeWholePassNeverChangesRecInfoArraySize
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader) :
    finalInfos.size = infos.size := trace.infoSize

private theorem nativeWholePassKeepsAlreadyProcessedParentRecordsExactly
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (bound : index < infos.size) (before : index < parent) :
    finalInfos[index]! = infos[index]! := trace.before index bound before

private theorem nativeWholePassKeepsSeedRecordsBeyondTheDeclaredParentArrayExactly
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (bound : index < infos.size) (after : types.size ≤ index) :
    finalInfos[index]! = infos[index]! := trace.after index bound after

private theorem visitedParentMinorPrefixNeedsBothSourceAndInfoBounds
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (pending : parent ≤ index) (within : index < types.size) (bound : index < infos.size) :
    ∃ appended, finalInfos[index]!.minors.toList = infos[index]!.minors.toList ++ appended ∧
      appended.length = types[index]!.ctors.length := trace.minorPrefix index pending within bound

private theorem visitedParentReceivesExactlyItsOwnConstructorCount
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (pending : parent ≤ index) (within : index < types.size) (bound : index < infos.size) :
    finalInfos[index]!.minors.size = infos[index]!.minors.size + types[index]!.ctors.length :=
  trace.minorCounts index pending within bound

private theorem actualNativePassGetterCarriesItsSameHistoryNotAnInventedFinalReader
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopInd2 stats types parent infos
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      RecursorMinorPassTrace stats types parent infos reader result.1 result.2 ∧
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size :=
  mkRecInfos.loopInd2.getMinorPassTrace stats types parent infos reader readerWF reserved

private theorem nativeScopedPassCpsStillRequiresItsSameSuccessfulContinuation
    {ResultType : Type} (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ finalInfos finalReader,
      RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader →
      reader.RecursorScopeFrame finalReader → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd2 stats types parent infos next reader).WF post :=
  mkRecInfos.loopInd2.scopedMinorPassTrace stats types parent infos next reader post readerWF reserved nextWF

private theorem completedTypedMinorPassKeepsOneInitialModelAndEverySeed
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    (parent : Nat) (infos : Array RecInfo) (reader : Context) (model : TypeChecker.MLCtx)
    (complete : ¬ parent < types.size) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx) :
    TranslatedRecursorMinorPass env universes
      (.stop (stats := stats) (types := types) (parent := parent) (infos := infos) (reader := reader) complete)
      model model := .stop complete modelWF native

private theorem laterTypedParentStartsAtTheEarlierParentsDerivedModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {infos middleInfos finalInfos : Array RecInfo} {reader middleReader finalReader : Context}
    {initial middle final : TypeChecker.MLCtx} (bound : parent < types.size)
    (head : RecursorMinorTrace stats types[parent]!.name parent infos types[parent]!.ctors
      reader middleInfos middleReader)
    (tail : RecursorMinorPassTrace stats types (parent + 1) middleInfos middleReader finalInfos finalReader)
    (headTranslated : TranslatedRecursorMinorTrace env universes head initial middle)
    (tailTranslated : TranslatedRecursorMinorPass env universes tail middle final) :
    TranslatedRecursorMinorPass env universes (.step bound head tail) initial final :=
  .step bound head tail headTranslated tailTranslated

private theorem typedWholePassDerivesTheExactFinalNativeReaderCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx} (history : TranslatedRecursorMinorPass env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := history.context

private theorem typedWholePassExtendsThroughAllResidualFieldsHypothesesAndMinors
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx} (history : TranslatedRecursorMinorPass env universes trace initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final := history.extension

private theorem sameSupportedPassDerivesAllModelsFromOnlyOneInitialModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen) (support : MinorPassTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorMinorPass env universes trace model finalModel :=
  trace.translated envWF constants definitions fieldOnly model modelWF native reserved support

private theorem actualTypedPassGetterKeepsItsRealZeroOriginalParameterRestriction
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopInd2 stats types parent infos
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        MinorPassTranslationSupport env universes trace) :
    (mkRecInfos.loopInd2 stats types parent infos
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size ∧
      ∃ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorMinorPass env universes trace model finalModel :=
  mkRecInfos.loopInd2.getTranslatedMinorPass stats types parent infos reader envWF constants definitions
    fieldOnly model modelWF native reserved support

private theorem scopedTypedPassCpsSuppliesOnlyTheSameDerivedCurrentModel
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopInd2 stats types parent infos
      (fun updated => do return (updated, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        MinorPassTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader) finalModel,
      reader.RecursorScopeFrame finalReader → TranslatedRecursorMinorPass env universes trace model finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd2 stats types parent infos next reader).WF post :=
  mkRecInfos.loopInd2.scopedTranslatedMinorPass stats types parent infos next reader post envWF constants
    definitions fieldOnly model modelWF native reserved support nextWF

private theorem composedEndpointDerivesTheExactFinalNativeCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : TypeChecker.MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := endpoint.context

private theorem composedEndpointRetainsTheCombinedParentAndMinorAllocationHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : TypeChecker.MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final := endpoint.extension

private theorem composedEndpointReturnsExactlyOneRecInfoPerActualParent
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : TypeChecker.MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    finalInfos.size = types.size := endpoint.infoSize

private theorem actualFullGetterComposesTheSameParentAndMinorReceiptsWithoutFinalModelAssumptions
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun infos => do return (infos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = types.size ∧
      RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel :=
  mkRecInfos.getTranslatedPasses stats types elimLevel reader envWF constants definitions fieldOnly
    model modelWF native reserved mapped parentSupport minorSupport

private theorem fullScopedCpsKeepsRecursorTypesRulesAndRegistrationAsLaterObligations
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun infos => do return (infos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (nextWF : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel finalInfos finalReader
      (minorTrace : RecursorMinorPassTrace stats types 0 parentInfos parentReader finalInfos finalReader) finalModel,
      reader.RecursorScopeFrame parentReader → parentReader.RecursorScopeFrame finalReader →
      TranslatedRecursorParentPass env universes parentTrace model parentModel →
      TranslatedRecursorMinorPass env universes minorTrace parentModel finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.fromTypedPasses stats types elimLevel next reader post envWF constants definitions fieldOnly
    model modelWF native reserved mapped parentSupport minorSupport nextWF

private structure DomainCapture where
  fields : Array Expr
  hypotheses : Array Expr
  reader : Context
  domain : Expr

private def captureDomain (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) : M DomainCapture :=
  mkRecInfos.loopCtorArgs stats constructor.type fun terminal fields recursive =>
    mkRecInfos.loopU stats recursive infos 0 #[] fun hypotheses => do
      let reader ← readThe Context
      return { fields, hypotheses, reader, domain :=
        recursorMinorDomain stats infos constructor terminal fields hypotheses reader }

private def captureParents (stats : InductiveStats) (types : Array InductiveType) :
    M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos.loopInd1 stats types (.succ .zero) 0 #[] fun infos =>
    return (infos, ← readThe Context)
  return (result, ← readThe Context)

private def capturePass (stats : InductiveStats) (types : Array InductiveType)
    (start : Nat) (infos : Array RecInfo) : M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos.loopInd2 stats types start infos fun updated =>
    return (updated, ← readThe Context)
  return (result, ← readThe Context)

private def captureFull (stats : InductiveStats) (types : Array InductiveType) :
    M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos stats types (.succ .zero) fun infos =>
    return (infos, ← readThe Context)
  return (result, ← readThe Context)

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "minor-pass earlier native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "minor-pass earlier declaration changed type/dependencies/value/order"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "minor-pass nonallocation reader fields changed"

private def checkSameReader (expected actual : Context) : MetaM Unit := do
  unless actual.ngen.curr == expected.ngen.curr && actual.lctx.decls.size == expected.lctx.decls.size do
    throwError "minor-pass exact reader allocation state changed"
  checkRetained expected actual
  checkRetained actual expected

private def checkParentInfos (stats : InductiveStats) (infos : Array RecInfo)
    (parentReader finalReader : Context) : MetaM Unit := do
  for ordinal in [:infos.size] do
    let info := infos[ordinal]!
    unless info.indices.size == stats.nindices[ordinal]! do
      throwError "minor-pass actual parent index count changed"
    for value in info.indices ++ #[info.major, info.motive] do
      let some declaration := parentReader.lctx.find? value.fvarId!
        | throwError "minor-pass parent index/major/motive declaration disappeared"
      let .ok (.sort _) := ((monadLift (TypeChecker.checkType declaration.type) : M Expr) finalReader)
        | throwError "minor-pass actual parent domain does not fully type-check as a sort"
  checkRetained parentReader finalReader

private def checkInfos (expected actual : Array RecInfo) : MetaM Unit := do
  unless actual.size == expected.size do throwError "minor-pass recInfo array size changed"
  for ordinal in [:expected.size] do
    let desired := expected[ordinal]!
    let found := actual[ordinal]!
    unless found.motive == desired.motive && found.major == desired.major &&
        found.indices == desired.indices && found.minors == desired.minors do
      throwError "minor-pass exact motive/index/major/minor updates or seeded prefixes changed"

private def checkMinor (stats : InductiveStats) (parent : Name) (infos : Array RecInfo)
    (constructor : Constructor) (before finalReader : Context) : MetaM (Expr × Context) := do
  let .ok source := captureDomain stats infos constructor before
    | throwError "minor-pass independently captured actual field/IH/minor domain failed"
  let count := source.fields.size + source.hypotheses.size
  let generator := (List.range count).foldl (fun current _ => current.next) before.ngen
  unless source.reader.lctx.decls.size == before.lctx.decls.size + count &&
      source.reader.ngen.curr == generator.curr do
    throwError "minor-pass temporary recursive arguments leaked into persistent allocation state"
  checkRetained before source.reader
  checkRetained source.reader finalReader
  let identifier := FVarId.mk source.reader.ngen.curr
  let some declaration := finalReader.lctx.find? identifier
    | throwError "minor-pass actual minor disappeared from the later parent reader"
  let name := constructor.name.replacePrefix parent .anonymous
  let domain := peelTypeAnnotations source.domain
  unless declaration.toExpr == Expr.fvar identifier && declaration.userName == name &&
      declaration.binderInfo == .default && declaration.type == domain &&
      declaration.deps == domain.fvarsList && declaration.index == source.reader.lctx.decls.size do
    throwError "minor-pass exact minor ID/name/type/dependencies/binder/order changed"
  for argument in source.fields ++ source.hypotheses do
    unless !domain.fvarsList.contains argument.fvarId! do
      throwError "minor-pass abstraction kept a bound constructor field or hypothesis fvar"
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType domain) : M Expr) finalReader)
    | throwError "minor-pass actual domain does not fully type-check as a sort"
  return (.fvar identifier, recursorIndexContext source.reader name .default domain)

private def checkPass (stats : InductiveStats) (types : Array InductiveType)
    (start : Nat) (infos : Array RecInfo) (reader : Context) : MetaM (Array RecInfo × Context) := do
  let .ok ((updated, finalReader), returnedBase) := capturePass stats types start infos reader
    | throwError "minor-pass actual whole-parent-loop capture failed"
  let mut expectedInfos := infos
  let mut current := reader
  for ordinal in [start:types.size] do
    let type := types[ordinal]!
    for constructor in type.ctors do
      let (minor, next) ← checkMinor stats type.name expectedInfos constructor current finalReader
      expectedInfos := expectedInfos.modify ordinal fun info => { info with minors := info.minors.push minor }
      current := next
  checkInfos expectedInfos updated
  checkSameReader current finalReader
  checkSameReader reader returnedBase
  return (updated, finalReader)

private def checkFull (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) : MetaM Unit := do
  let .ok ((parents, parentReader), parentBase) := captureParents stats types reader
    | throwError "minor-pass independent actual parent construction failed"
  checkSameReader reader parentBase
  checkRetained reader parentReader
  unless parents.size == types.size do throwError "minor-pass actual parent array size changed"
  let (expected, expectedReader) ← checkPass stats types 0 parents parentReader
  let .ok ((actual, finalReader), returnedBase) := captureFull stats types reader
    | throwError "minor-pass actual composed mkRecInfos capture failed"
  checkInfos expected actual
  checkSameReader expectedReader finalReader
  checkSameReader reader returnedBase
  checkParentInfos stats parents parentReader finalReader

private def typeFor (name : Name) (constructors : List Name) : MetaM InductiveType := do
  let some information := (← getEnv).find? name
    | throwError "minor-pass genuine parent declaration missing: {name}"
  let mut ctors : List Constructor := []
  for constructor in constructors do
    let some declaration := (← getEnv).find? constructor
      | throwError "minor-pass genuine constructor declaration missing: {constructor}"
    ctors := ctors ++ [{ name := constructor, type := (declaration.type.instantiateLevelParams
      declaration.levelParams (declaration.levelParams.map fun _ => .zero)) }]
  return { name, ctors, type := (information.type.instantiateLevelParams information.levelParams
    (information.levelParams.map fun _ => .zero)) }

private def statsFor (reader : Context) (types : Array InductiveType)
    (counts : Array Nat) (params : Array Expr := #[]) (levels : List Level := []) : InductiveStats :=
  { lctx := reader.lctx, resultLevel := .succ .zero, levels, params, isNotZero := true,
    nindices := counts, indConsts := types.map fun type => .const type.name levels }

private def checkAllocationOnlyControls (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (reader : Context) : MetaM Unit := do
  let invalidInfos := infos.modify 0 fun info => { info with motive := .mvar ⟨`PassUntypedMotive⟩ }
  let .ok ((updated, current), _) := capturePass stats types 0 invalidInfos reader
    | throwError "minor-pass allocation-only untyped-motive control unexpectedly failed"
  let declaration := current.lctx.get! updated[0]!.minors.back!.fvarId!
  match ((monadLift (TypeChecker.checkType declaration.type) : M Expr) current) with
  | .error (.other _) => pure ()
  | _ => throwError "minor-pass native allocation does not justify selected motive typing"
  let invalidConstructor : Constructor := {
    name := ``Nat.succ
    type := .forallE `invalid (.mvar ⟨`PassUntypedField⟩) (.const ``Nat []) .default }
  let invalidType := { types[0]! with ctors := [invalidConstructor] }
  let .ok ((fieldInfos, fieldReader), _) := capturePass stats #[invalidType] 0 infos reader
    | throwError "minor-pass allocation-only untyped-field control unexpectedly failed"
  let fieldDeclaration := fieldReader.lctx.get! fieldInfos[0]!.minors.back!.fvarId!
  match ((monadLift (TypeChecker.checkType fieldDeclaration.type) : M Expr) fieldReader) with
  | .error (.other _) => pure ()
  | _ => throwError "minor-pass raw field classification does not justify constructor typing"

private def checkPassFailures (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (reader : Context) : MetaM Unit := do
  let noOpening := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match capturePass stats types 0 infos noOpening with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor-pass constructor opening-fuel failure must propagate"
  let noNormalization := { reader with fuel := { reader.fuel with whnf := 0 } }
  match capturePass stats types 0 infos noNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "minor-pass actual classification WHNF failure must propagate"
  let noRecursion := { reader with fuel := { reader.fuel with recDepth := 0 } }
  match capturePass stats types 0 infos noRecursion with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor-pass recursive-field recursion-fuel failure must propagate"
  let message := "minor-pass callback failure"
  match mkRecInfos.loopInd2 stats types 0 infos (fun _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "minor-pass post-allocation callback exception changed"
  | _ => throwError "minor-pass post-allocation callback failure must propagate"
  discard <| checkPass stats #[] 0 infos noOpening

private def checkFullFailures (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) : MetaM Unit := do
  let noOpening := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match captureFull stats types noOpening with
  | .error .deepRecursion => pure ()
  | _ => throwError "minor-pass composed parent opening-fuel failure must propagate"
  let noNormalization := { reader with fuel := { reader.fuel with whnf := 0 } }
  match captureFull stats types noNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "minor-pass composed parent initial-WHNF failure must propagate"
  let message := "full-recInfos callback failure"
  match mkRecInfos stats types (.succ .zero) (fun _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "minor-pass composed callback exception changed"
  | _ => throwError "minor-pass composed post-allocation callback failure must propagate"
  checkFull stats #[] noOpening

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `PassOldCarrier
  let oldLet := FVarId.mk `PassOldLet
  let seeded := { reader with
    ngen := { namePrefix := `PassSeed, idx := 113 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 31)) false }
  let natural ← typeFor ``Nat [``Nat.zero, ``Nat.succ]
  let flag ← typeFor ``Bool [``Bool.false, ``Bool.true]
  let types := #[natural, flag]
  let stats := statsFor seeded types #[0, 0]
  let .ok ((parents, current), _) := captureParents stats types seeded
    | throwError "minor-pass prepared native parent capture failed"
  discard <| checkPass stats #[] 0 parents current
  discard <| checkPass stats #[] 3 parents current
  discard <| checkPass stats types types.size parents current
  discard <| checkPass stats types (types.size + 3) parents current
  let prefixed := parents.modify 0 fun info => { info with minors := #[.fvar oldLet] }
  discard <| checkPass stats types 0 prefixed current
  let invalid := { natural with ctors := [{ name := ``Nat.succ, type := .mvar ⟨`SkippedPassSource⟩ }] }
  discard <| checkPass stats #[invalid, flag] 1 parents current
  discard <| checkPass stats types 0 (parents.push parents[0]!) current
  checkFull (statsFor seeded #[natural] #[0]) #[natural] seeded
  checkFull stats types seeded
  let left ← typeFor ``PassLeft [``PassLeft.leaf, ``PassLeft.right]
  let right ← typeFor ``PassRight [``PassRight.left, ``PassRight.higher]
  let paired := #[left, right]
  checkFull (statsFor seeded paired #[0, 0]) paired seeded
  let higher ← typeFor ``PassHigher [``PassHigher.leaf, ``PassHigher.higher,
    ``PassHigher.dependent, ``PassHigher.pair]
  checkFull (statsFor seeded #[higher] #[0]) #[higher] seeded
  let indexed ← typeFor ``PassIndexed [``PassIndexed.leaf, ``PassIndexed.direct, ``PassIndexed.higher]
  checkFull (statsFor seeded #[indexed] #[1]) #[indexed] seeded
  let list ← typeFor ``List [``List.nil, ``List.cons]
  checkFull (statsFor seeded #[list] #[0] #[.fvar carrier] [.zero]) #[list] seeded
  let family ← typeFor ``PassFamily [``PassFamily.leaf, ``PassFamily.direct]
  checkFull (statsFor seeded #[family] #[1] #[.fvar carrier]) #[family] seeded
  checkAllocationOnlyControls stats types parents current
  checkPassFailures stats types parents current
  checkFullFailures stats types seeded
  logInfo "minor-pass runtime: sixteen positive loopInd2 captures and eight composed mkRecInfos captures; thirty-one minor and twenty parent/index/major/motive domain type-checks; mutual/cross-parent recursive arguments, direct/higher-order/dependent/multiple IHs, indexed and original-parameter native controls; exact selected record updates/prefixes, residual earlier fields/IHs/minors at later parents and outer reader restoration; empty/exact-end/beyond-end/skipped-source controls; two allocation-only untyped controls and seven failure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "minor-pass unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "minor-pass audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "minor-pass new module-owned axiom {name}"
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
      throwError "minor-pass inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "minor-pass inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited minor-pass foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "minor-pass inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context minor-pass abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "minor-pass native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "minor-pass native interface provenance changed: {name}"
    logInfo m!"pinned existing native minor-pass interface: {name}"

#print axioms actualNativePassGetterCarriesItsSameHistoryNotAnInventedFinalReader
#print axioms nativeWholePassKeepsSeedRecordsBeyondTheDeclaredParentArrayExactly
#print axioms laterTypedParentStartsAtTheEarlierParentsDerivedModel
#print axioms typedWholePassDerivesTheExactFinalNativeReaderCorrespondence
#print axioms typedWholePassExtendsThroughAllResidualFieldsHypothesesAndMinors
#print axioms sameSupportedPassDerivesAllModelsFromOnlyOneInitialModel
#print axioms actualTypedPassGetterKeepsItsRealZeroOriginalParameterRestriction
#print axioms composedEndpointRetainsTheCombinedParentAndMinorAllocationHistory
#print axioms actualFullGetterComposesTheSameParentAndMinorReceiptsWithoutFinalModelAssumptions
#print axioms fullScopedCpsKeepsRecursorTypesRulesAndRegistrationAsLaterObligations
#print axioms retainingEarlierParentLocalsNeedsRealSuffixWeakening
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``retainingEarlierParentLocalsNeedsRealSuffixWeakening,
      ``wholePassFailureCannotSupplySuccessfulOutputs,
      ``completedMinorPassKeepsEverySeedAndTheSameReader,
      ``oneActualParentStepUsesTheSameSelectedConstructorPassAndItsLaterReader,
      ``nativeWholePassNeverChangesRecInfoArraySize,
      ``nativeWholePassKeepsAlreadyProcessedParentRecordsExactly,
      ``nativeWholePassKeepsSeedRecordsBeyondTheDeclaredParentArrayExactly,
      ``visitedParentMinorPrefixNeedsBothSourceAndInfoBounds,
      ``visitedParentReceivesExactlyItsOwnConstructorCount,
      ``captureDomain, ``captureParents, ``capturePass, ``captureFull,
      ``checkRetained, ``checkSameReader, ``checkParentInfos, ``checkInfos, ``checkMinor,
      ``checkPass, ``checkFull, ``typeFor, ``statsFor, ``checkAllocationOnlyControls,
      ``checkPassFailures, ``checkFullFailures, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``nativeWholePassScopeRetainsEarlierParentsResidualFieldsHypothesesAndMinors,
      ``actualNativePassGetterCarriesItsSameHistoryNotAnInventedFinalReader,
      ``nativeScopedPassCpsStillRequiresItsSameSuccessfulContinuation] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``completedTypedMinorPassKeepsOneInitialModelAndEverySeed,
      ``laterTypedParentStartsAtTheEarlierParentsDerivedModel,
      ``typedWholePassDerivesTheExactFinalNativeReaderCorrespondence,
      ``typedWholePassExtendsThroughAllResidualFieldsHypothesesAndMinors,
      ``sameSupportedPassDerivesAllModelsFromOnlyOneInitialModel,
      ``actualTypedPassGetterKeepsItsRealZeroOriginalParameterRestriction,
      ``scopedTypedPassCpsSuppliesOnlyTheSameDerivedCurrentModel,
      ``composedEndpointDerivesTheExactFinalNativeCorrespondence,
      ``composedEndpointRetainsTheCombinedParentAndMinorAllocationHistory,
      ``composedEndpointReturnsExactlyOneRecInfoPerActualParent,
      ``actualFullGetterComposesTheSameParentAndMinorReceiptsWithoutFinalModelAssumptions,
      ``fullScopedCpsKeepsRecursorTypesRulesAndRegistrationAsLaterObligations] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveMinorPassTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveMinorPassTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "minor-pass translation: 24 proof controls; one initial model threads through the actual whole parent-minor pass and composed mkRecInfos receipt; successful-result-local supports, real zero-original-parameter typed restriction and final native correspondence derived; recursor types/rules/registration still explicit; old clean core and inherited foundations/eight native interfaces pinned; global native range axiom forbidden even if whitelisted"

end InductiveMinorPassTranslationTest
