import Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS
import Lean4Lean.Verify.InductiveRecursorApplicationTranslation
import Lean4Lean.Verify.InductiveRecursorApplicationNative
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean4Lean.Verify.RecursorHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveRecursorApplicationTranslationTest

mutual
  inductive ApplicationLeft where
    | leaf : ApplicationLeft
    | right (child : ApplicationRight) : ApplicationLeft
  inductive ApplicationRight where
    | left (child : ApplicationLeft) : ApplicationRight
    | higher (children : Nat → ApplicationLeft) : ApplicationRight
end

inductive ApplicationIndexed : Nat → Type where
  | leaf (ordinal : Nat) : ApplicationIndexed ordinal
  | direct (ordinal : Nat) (child : ApplicationIndexed ordinal) : ApplicationIndexed ordinal

inductive ApplicationDependent : (carrier : Type) → carrier → Nat → Type where
  | leaf (carrier : Type) (value : carrier) (ordinal : Nat) :
      ApplicationDependent carrier value ordinal
  | direct (carrier : Type) (value : carrier) (ordinal : Nat)
      (child : ApplicationDependent carrier value ordinal) :
      ApplicationDependent carrier value ordinal

inductive ApplicationParam (carrier : Type) : Nat → Type where
  | leaf (ordinal : Nat) (payload : carrier) : ApplicationParam carrier ordinal
  | direct (ordinal : Nat) (child : ApplicationParam carrier ordinal) : ApplicationParam carrier ordinal

private theorem actualBodyHasExactlyTheSelectedMotiveIndicesAndMajor
    (infos : Array RecInfo) (parent : Nat) :
    recursorTypeBody infos parent =
      mkAppN infos[parent]!.motive (infos[parent]!.indices.push infos[parent]!.major) := by
  simp only [recursorTypeBody, mkAppN, Array.foldl_push, mkApp]

private theorem realDependentApplicationCannotReplaceCombinedSuffixLiftingWithIdentity :
    (VExpr.app (.bvar 2) (.bvar 0)).liftN 5 = .app (.bvar 7) (.bvar 5) ∧
      (VExpr.app (.bvar 2) (.bvar 0)).liftN 5 ≠ .app (.bvar 2) (.bvar 0) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem cancellationAllowsArbitraryPreexistingBoundVariablesWithoutAClosurePremise
    (expression : Expr) (identifier : FVarId) (depth : Nat) :
    (expression.abstract1 identifier depth).instantiate1' (.fvar identifier) depth = expression :=
  Expr.instantiate1'_abstract1 expression identifier depth

private theorem cancellationKeepsNestedBindersAndBothSidesOfTheDepthBoundary
    (identifier : FVarId) :
    ((Expr.forallE `carrier (.app (.bvar 4) (.fvar identifier))
      (.app (.bvar 0) (.fvar identifier)) .implicit).abstract1 identifier 2).instantiate1'
      (.fvar identifier) 2 =
        .forallE `carrier (.app (.bvar 4) (.fvar identifier))
          (.app (.bvar 0) (.fvar identifier)) .implicit :=
  Expr.instantiate1'_abstract1 _ identifier 2

private theorem cancellationPreservesMetadataWithoutDiscardingItsPayload
    (metadata : MData) (expression : Expr) (identifier : FVarId) (depth : Nat) :
    ((Expr.mdata metadata expression).abstract1 identifier depth).instantiate1'
      (.fvar identifier) depth = .mdata metadata expression :=
  Expr.instantiate1'_abstract1 _ identifier depth

private theorem mismatchedCancellationDepthDoesNotRestoreTheOriginalBoundVariable
    (identifier : FVarId) :
    ((Expr.bvar 0).abstract1 identifier 0).instantiate1' (.fvar identifier) 1 = .fvar identifier ∧
      ((Expr.bvar 0).abstract1 identifier 0).instantiate1' (.fvar identifier) 1 ≠ .bvar 0 := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem arrayApplicationPreservesOrderedOriginalFVarsNotASetOfArguments
    (head : Expr) (first second : FVarId) (distinct : first ≠ second) :
    mkAppN head #[.fvar first, .fvar second] ≠ mkAppN head #[.fvar second, .fvar first] := by
  intro equality
  change Expr.app (Expr.app head (.fvar first)) (.fvar second) =
    Expr.app (Expr.app head (.fvar second)) (.fvar first) at equality
  exact distinct (Expr.fvar.inj (Expr.app.inj equality).2).symm

private theorem actualCDeclTranslationDerivesTheTypedArgumentFromMixedContextWellFormedness
    (env : VEnv) (universes : List Name) (model : MLCtx)
    (modelWF : model.WF env universes) (envWF : env.WF)
    (identifier : FVarId) (index : Nat) (name : Name) (domain : Expr)
    (binder : BinderInfo) (kind : LocalDeclKind)
    (lookup : model.lctx.find? identifier = some (.cdecl index identifier name domain binder kind)) :
    ∃ valueSemantic domainSemantic,
      model.vlctx.find? (.inr identifier) = some (valueSemantic, domainSemantic) ∧
      TrExprS env universes model.vlctx (.fvar identifier) valueSemantic ∧
      TrExprS env universes model.vlctx domain domainSemantic ∧
      env.HasType universes.length model.vlctx.toCtx valueSemantic domainSemantic :=
  modelWF.cdeclTranslation envWF lookup

private theorem nativeForallSelfApplicationDerivesEveryAppliedArgumentInsteadOfAssumingBodyTyping
    (env : VEnv) (universes : List Name) (model : MLCtx)
    (modelWF : model.WF env universes) (envWF : env.WF)
    (identifiers : List FVarId) (distinct : identifiers.Nodup)
    (bindings : SelectedCDeclBindings model.lctx identifiers)
    (body : Expr) (bodyClosed : body.looseBVarRange' = 0)
    (value : Expr) (valueSemantic typeSemantic : VExpr)
    (valueTranslated : TrExprS env universes model.vlctx value valueSemantic)
    (valueTyped : env.HasType universes.length model.vlctx.toCtx valueSemantic typeSemantic)
    (typeTranslated : TrExprS env universes model.vlctx
      (model.lctx.mkForall (identifiers.map Expr.fvar).toArray body) typeSemantic) :
    ∃ applicationSemantic bodySemantic,
      TrExprS env universes model.vlctx
        (mkAppN value (identifiers.map Expr.fvar).toArray) applicationSemantic ∧
      env.HasType universes.length model.vlctx.toCtx applicationSemantic bodySemantic ∧
      TrExprS env universes model.vlctx body bodySemantic :=
  modelWF.selectedForallApplication envWF identifiers distinct bindings bodyClosed
    valueTranslated valueTyped typeTranslated

private theorem actualSelectedForallSortApplicationUsesOnlyTheTranslatedNativeMotiveType
    (env : VEnv) (universes : List Name) (model : MLCtx)
    (modelWF : model.WF env universes) (envWF : env.WF)
    (identifiers : List FVarId) (distinct : identifiers.Nodup)
    (bindings : SelectedCDeclBindings model.lctx identifiers)
    (level : Level) (semanticLevel : VLevel)
    (mapped : VLevel.ofLevel universes level = some semanticLevel)
    (value : Expr) (valueSemantic typeSemantic : VExpr)
    (valueTranslated : TrExprS env universes model.vlctx value valueSemantic)
    (valueTyped : env.HasType universes.length model.vlctx.toCtx valueSemantic typeSemantic)
    (typeTranslated : TrExprS env universes model.vlctx
      (model.lctx.mkForall (identifiers.map Expr.fvar).toArray (.sort level)) typeSemantic) :
    ∃ applicationSemantic,
      TrExprS env universes model.vlctx
        (mkAppN value (identifiers.map Expr.fvar).toArray) applicationSemantic ∧
      env.HasType universes.length model.vlctx.toCtx applicationSemantic (.sort semanticLevel) :=
  modelWF.selectedForallSortApplication envWF identifiers distinct bindings mapped
    valueTranslated valueTyped typeTranslated

private theorem actualSourceRecoversTheUnpeeledOriginalMotiveDomainAtTheCurrentReader
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (original current : Context) (info : RecInfo)
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (scope : current.lctx.BindingScope) :
    ∃ physicalIndex identifier,
      current.lctx.find? info.motive.fvarId! = some (.cdecl physicalIndex identifier
        (recursorMotiveName types parent)
        (current.lctx.mkForall info.indices (current.lctx.mkForall #[info.major] (.sort elimLevel)))
        .default .default) ∧ Expr.fvar identifier = info.motive :=
  source.motiveLookupAtCurrent scope

private theorem selectedDomainHistoryDerivesMotiveAndMajorApplicationSupportInsteadOfReceivingIt
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (infos : Array RecInfo) (parent : Nat)
    (original current : Context) (initial projected : MLCtx) (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes current.lctx initial ids projected)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (fullScope : current.lctx.BindingScope) (bound : parent < infos.size)
    (selected : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    (source : RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current)
    (semanticElimLevel : VLevel)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    RecursorTypeBodyApplicationSupport env universes infos parent projected.vlctx :=
  telescope.bodyApplicationSupport envWF initialWF fullScope bound selected source mapped

private theorem domainOnlySupportDerivesWholeRawSupportFromTheSameActualSource
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (infos : Array RecInfo) (parent : Nat)
    (original current : Context) (initial : MLCtx)
    (support : RecursorSelectedDomainSupport env universes stats infos parent current.lctx initial)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (fullScope : current.lctx.BindingScope) (bound : parent < infos.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current)
    (semanticElimLevel : VLevel)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    RecursorRawTypeTranslationSupport env universes stats infos parent current.lctx initial :=
  support.rawTypeSupport envWF initialWF fullScope bound source mapped

private theorem actualEndpointDerivesRawStoredReceiptsFromDomainsWithoutWholeBodyTyping
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    (semanticElimLevel : VLevel)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final :=
  endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support

private theorem actualEndpointExposesFinalStoredTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic :=
  endpoint.finalStoredTypehoodFromDomains envWF initialWF parameterFree parent bound source mapped support

private theorem actualEndpointExposesFinalRawTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic :=
  endpoint.finalRawTypehoodFromDomains envWF initialWF parameterFree parent bound source mapped support

private theorem actualEndpointExposesFinalMetadataTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic :=
  endpoint.finalMetadataTypehoodFromDomains envWF initialWF parameterFree parent bound source mapped support
    lparams isK isUnsafe rules

private theorem actualEndpointDerivesInitialStoredWFOfDeclaredRecursorFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constant : VConstVal) (lparams : List Name) (isK isUnsafe : Bool)
    (rules : List RecursorRule)
    (native : TrConstVal .safe env
      (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules)) constant)
    (levels : (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
      isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env :=
  endpoint.initialStoredWF_of_declaredRecursorFromDomains envWF initialWF parameterFree parent bound
    source mapped support constant lparams isK isUnsafe rules native levels empty

private theorem actualEndpointDerivesInitialStoredWFForDeclaredRecursorsFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constants : ∀ parent, parent < types.size → VConstVal)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (native : ∀ parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules)) (constants parent bound))
    (levels : ∀ parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) :
    ∀ parent (bound : parent < types.size), (constants parent bound).toVConstant.WF env :=
  endpoint.initialStoredWFOfDeclaredRecursorsFromDomains envWF initialWF parameterFree sources mapped
    supports constants lparams isK isUnsafe rules native levels empty

private theorem actualGetterExposesInitialStoredWFOfDeclaredRecursors
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (recursorConstant : ∀ (_finalInfos : Array RecInfo) (_finalReader : Context) (_finalModel : MLCtx)
      parent, parent < types.size → VConstVal)
    (recursorNative : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (finalModel : MLCtx)
      parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel finalInfos lparams
          finalReader.lctx isK isUnsafe parent rules))
        (recursorConstant finalInfos finalReader finalModel parent bound))
    (recursorLevels : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (_finalModel : MLCtx)
      parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : model.vlctx.toCtx = []) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∀ bound, (recursorConstant result.1 result.2 finalModel parent bound).toVConstant.WF env :=
  mkRecInfos.getTranslatedAppliedInitialStoredWFOfDeclaredRecursors stats types elimLevel reader envWF
    constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
    domainSupport lparams isK isUnsafe rules recursorConstant recursorNative recursorLevels empty

private theorem actualEndpointExposesAllFinalTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
      lparams isK isUnsafe rules :=
  endpoint.finalTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
    lparams isK isUnsafe rules

private theorem actualEndpointExposesAllInitialTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
      lparams isK isUnsafe rules :=
  endpoint.initialTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
    lparams isK isUnsafe rules

private theorem actualEndpointExposesAllInitialAndFinalTypehoodFromSelectedDomains
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
        lparams isK isUnsafe rules ∧
      RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
        lparams isK isUnsafe rules :=
  endpoint.initialAndFinalTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
    lparams isK isUnsafe rules

private theorem actualGetterRecoversSourcesAtItsSameSuccessAndNeedsOnlySelectedDomainSupport
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats result.1 parent result.2 model finalModel :=
  mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport

private theorem actualGetterExposesInitialTypehoodAtEveryBoundedParent
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules :=
  mkRecInfos.getTranslatedAppliedInitialTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules

private theorem actualGetterExposesInitialAndFinalTypehoodAtEveryBoundedParent
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.1 result.2
            finalModel lparams isK isUnsafe rules) :=
  mkRecInfos.getTranslatedAppliedInitialAndFinalTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules

private theorem actualGetterExposesFinalStoredTypehoodAtEveryBoundedParent
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats result.1 parent result.2.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic :=
  mkRecInfos.getTranslatedAppliedFinalStoredTypehood stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport

private theorem actualGetterExposesFinalRawTypehoodAtEveryBoundedParent
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats result.1 parent result.2.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic :=
  mkRecInfos.getTranslatedAppliedFinalRawTypehood stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport

private theorem actualGetterExposesFinalMetadataTypehoodAtEveryBoundedParent
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel result.1 lparams result.2.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic :=
  mkRecInfos.getTranslatedAppliedFinalMetadataTypehood stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules

private theorem scopedAppliedGetterPassesFinalMetadataTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedFinalMetadataTypehood stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules nextWF

private theorem scopedAppliedGetterPassesFinalStoredTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats finalInfos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedFinalStoredTypehood stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport nextWF

private theorem scopedAppliedGetterPassesFinalRawTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats finalInfos parent finalReader.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedFinalRawTypehood stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport nextWF

private theorem scopedAppliedGetterPassesAllFinalTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
        finalModel lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedFinalTypehood stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules nextWF

private theorem scopedAppliedGetterPassesAllInitialTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
        model lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedInitialTypehood stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules nextWF

private theorem scopedAppliedGetterPassesAllInitialAndFinalTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedInitialAndFinalTypehood stats types elimLevel next reader post envWF
    constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules nextWF

private theorem scopedAppliedGetterKeepsOneDerivedModelAndLeavesRulesAndRegistrationSeparate
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedAppliedRecursorTypes stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport nextWF

private theorem registeredAppliedGetterKeepsReceiptsWithEnvironmentRegistration
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        ∀ parent, parent < types.size →
          RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 :=
  mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel lparams isK isUnsafe reader
    envWF constants definitions fieldOnly model modelWF native reserved nativeEnvWF mapped
    parentSupport minorSupport domainSupport

private theorem actualRegisteredRecursorsHaveModelsAndGeneratedRules
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : model.vlctx = []) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false reader).WF fun result =>
      ∀ parent, parent < types.size → ∃ (info : RecursorVal) (constant : VConstVal),
        result.1.find? (mkRecName types[parent]!.name) = some (.recInfo info) ∧
        mkRecRules types elimLevel stats parent (result.2.1.map (·.motive))
          (result.2.1.flatMap (·.minors)) (recursorMinorOffset types parent) result.2.2 =
          .ok (info.rules, recursorMinorOffset types (parent + 1)) ∧
        constant.name = mkRecName types[parent]!.name ∧ constant.uvars = universes.length ∧
        TrConstVal .safe env (.recInfo info) constant ∧ constant.toVConstant.WF env := by
  refine (mkRecInfos.registeredTranslatedAppliedDeclaredRecursors stats types elimLevel
    lparams isK reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport levels empty).mono ?_
  rintro result ⟨_, _, _, _, _, metadata, _, models⟩ parent bound
  obtain ⟨rules, generated, lookup⟩ := metadata parent bound
  obtain ⟨info, constant, sameLookup, translated, wellFormed⟩ := models parent bound
  have sameInfo := Option.some.inj (lookup.symm.trans sameLookup)
  cases sameInfo
  refine ⟨_, constant, lookup, generated, translated.2.symm, ?_, translated, wellFormed⟩
  exact translated.1.2.1.symm.trans (congrArg List.length levels)

private theorem insertedRecursorModelsHaveExactLookupsAndKeepOldEquations
    {safety : DefinitionSafety} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (isK : Bool) (reader : Context)
    (initial final : MLCtx) (checker : CheckerEnv safety reader.env env)
    (receipts : ∀ index, index < types.size →
      RecursorTypeModelReceipt env universes stats infos index reader initial final)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : initial.vlctx = []) :
    (declareRecursors stats types elimLevel infos lparams reader.lctx isK false reader).WF
      fun result => ∃ (models : Nat → VConstVal) (extended : VEnv),
        CheckerEnv safety result extended ∧ env ≤ extended ∧ extended.defeqs = env.defeqs ∧
        ∀ index, index < types.size →
          extended.constants (mkRecName types[index]!.name) = some (models index).toVConstant ∧
          (models index).toVConstant.WF env ∧
          ∀ rules, TrConstVal .safe env (.recInfo
            (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
              isK false index rules)) (models index) := by
  refine (declareRecursors.refinesChecker_of_typeReceipts stats types elimLevel infos lparams
    isK reader initial final checker receipts levels empty).mono ?_
  rintro result ⟨models, extended, properties, added, finalChecker⟩
  refine ⟨models, extended, finalChecker, VEnv.addConstructorHeaders.le added,
    VEnv.addConstructorHeaders.defeqs_eq added, ?_⟩
  intro index bound
  have member : models index ∈ (List.range types.size).map models :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩
  have name : (models index).name = mkRecName types[index]!.name :=
    (properties index bound []).1.2.symm
  refine ⟨?_, (properties index bound []).2, fun rules => (properties index bound rules).1⟩
  simpa only [name] using VEnv.addConstructorHeaders.constants added member

private theorem letOnlyContextIsNotAClosedNativeTranslationContext (identifier : FVarId) :
    let model := MLCtx.vlet identifier `alias (.sort (.succ .zero)) (.sort .zero)
      (.sort (.succ .zero)) (.sort .zero) .nil
    model.vlctx.toCtx = [] ∧ model.vlctx ≠ [] ∧ VLCtx.WF VEnv.empty 0 model.vlctx ∧
      TrExprS VEnv.empty [] model.vlctx (.fvar identifier) (.sort .zero) ∧
      ¬ ∃ semantic, TrExprS VEnv.empty [] [] (.fvar identifier) semantic := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro equality
    cases equality
  · refine ⟨trivial, ?_, .sortDF (by trivial) (by trivial) rfl⟩
    rintro fv dependencies equality
    cases equality
    simp [VLCtx.fvars, Expr.fvarsList]
  · exact .fvar (A := .sort (.succ .zero)) (by
      simp [MLCtx.vlctx, VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type])
  · rintro ⟨semantic, translated⟩
    cases translated with
    | fvar lookup => cases lookup

private theorem registeredAppliedGetterExposesCombinedTypehoodWithEnvironmentRegistration
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.2.1 result.2.2
            model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.2.1 result.2.2
            finalModel lparams isK isUnsafe rules)) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 :=
  mkRecInfos.registeredTranslatedAppliedInitialAndFinalTypehood stats types elimLevel lparams isK
    isUnsafe rules reader envWF constants definitions fieldOnly model modelWF native reserved nativeEnvWF
    mapped parentSupport minorSupport domainSupport

private theorem registeredScopedGetterPassesCombinedTypehoodToContinuation
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post :=
  mkRecInfos.registeredScopedTranslatedAppliedInitialAndFinalTypehood stats types elimLevel
    lparams isK isUnsafe rules reader next post envWF constants definitions fieldOnly model modelWF native
    reserved nativeEnvWF mapped parentSupport minorSupport domainSupport nextWF

private def captureFull (stats : InductiveStats) (types : Array InductiveType) :
    M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos stats types (.succ .zero) fun infos =>
    return (infos, ← readThe Context)
  return (result, ← readThe Context)

private def checkSameReader (before after : Context) : MetaM Unit := do
  unless before.ngen.curr == after.ngen.curr && before.lctx.decls.size == after.lctx.decls.size do
    throwError "recursor-application outer reader allocation state changed"
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "recursor-application original outer declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "recursor-application original outer declaration changed"

private def requireCDecl (reader : Context) (expression : Expr) : MetaM LocalDecl := do
  let .fvar identifier := expression
    | throwError "recursor-application selected expression is not an original fvar"
  let some declaration@(.cdecl _ original _ _ _ .default) := reader.lctx.find? identifier
    | throwError "recursor-application selected original default cdecl is missing"
  unless original == identifier do throwError "recursor-application original cdecl identifier changed"
  return declaration

private def requireSort (reader : Context) (expression : Expr) : MetaM Expr := do
  let .ok sort@(.sort _) := ((monadLift (TypeChecker.checkType expression) : M Expr) reader)
    | throwError "recursor-application fully checked expression is not a type"
  return sort

private def checkInstantiatedDomains (reader : Context) (motiveDomain : Expr)
    (arguments : Array Expr) : MetaM Unit := do
  let mut current := motiveDomain
  for argument in arguments do
    let declaration ← requireCDecl reader argument
    let .forallE name domain body binder := current
      | throwError "recursor-application motive domain lost a selected index/major binder"
    unless name == declaration.userName && domain == declaration.type && binder == declaration.binderInfo do
      throwError "recursor-application instantiated motive binder disagrees with the actual original cdecl"
    discard <| requireSort reader domain
    let .ok checked := ((monadLift (TypeChecker.checkType argument) : M Expr) reader)
      | throwError "recursor-application original selected argument failed full checking"
    unless checked == domain do throwError "recursor-application actual selected argument type changed"
    current := body.instantiate1 argument
  unless current == .sort (.succ .zero) do
    throwError "recursor-application exact indices/major self-application did not reach the elimination sort"

private def projectSelected (full : Context) (binders : Array Expr) : MetaM Context := do
  let mut projected := { full with lctx := {} }
  let mut changedPhysicalIndex := false
  for ordinal in [:binders.size] do
    let original ← requireCDecl full binders[ordinal]!
    unless (projected.lctx.find? original.fvarId).isNone do
      throwError "recursor-application projection reused an original selected identifier"
    discard <| requireSort projected original.type
    let copiedLctx := projected.lctx.mkLocalDecl original.fvarId original.userName original.type
      original.binderInfo original.kind
    projected := { projected with lctx := copiedLctx }
    let copied ← requireCDecl projected original.toExpr
    unless copied.index == ordinal && copied.type == original.type &&
        copied.userName == original.userName && copied.binderInfo == original.binderInfo &&
        copied.deps == original.deps do
      throwError "recursor-application projection changed an actual domain/name/binder/dependency or dense physical index"
    changedPhysicalIndex := changedPhysicalIndex || copied.index != original.index
  unless changedPhysicalIndex do
    throwError "recursor-application projection fixture did not change original physical declaration indices"
  return projected

private def checkProjectedApplication (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (full : Context) : MetaM Unit := do
  let info := infos[parent]!
  let projected ← projectSelected full (recursorTypeBinders stats infos parent)
  let motive ← requireCDecl projected info.motive
  let major ← requireCDecl projected info.major
  unless motive.index < major.index do
    throwError "recursor-application projection did not reorder the selected original motive before its major"
  checkInstantiatedDomains projected motive.type (info.indices.push info.major)
  let .ok (.forallE _ domain body _) :=
      ((monadLift (TypeChecker.checkType (mkAppN info.motive info.indices)) : M Expr) projected)
    | throwError "recursor-application sparse/reordered projection lost the checked motive/indices major arrow"
  unless domain == major.type && body == .sort (.succ .zero) do
    throwError "recursor-application projected actual motive arrow no longer matches the original major domain"
  let sort ← requireSort projected (recursorTypeBody infos parent)
  unless sort == .sort (.succ .zero) do
    throwError "recursor-application sparse/reordered projected complete body has the wrong sort"

private def checkRetained (initial finalReader : Context) (infos : Array RecInfo)
    (parent : Nat) : MetaM Unit := do
  let own := infos[parent]!.indices ++ #[infos[parent]!.major, infos[parent]!.motive]
  let allParent := infos.flatMap fun info => info.indices ++ #[info.major, info.motive]
  let minors := infos.flatMap (·.minors)
  unless minors.size > 0 do throwError "recursor-application final full pass has no retained minor"
  let mut residual := 0
  for declaration in finalReader.lctx.decls.toList.filterMap id do
    if (initial.lctx.find? declaration.fvarId).isNone &&
        !allParent.contains declaration.toExpr && !minors.contains declaration.toExpr then
      residual := residual + 1
  unless residual > 0 do
    throwError "recursor-application full-reader fixture has no retained residual constructor field/hypothesis"
  for ordinal in [:infos.size] do
    if ordinal != parent then
      for expression in infos[ordinal]!.indices ++ #[infos[ordinal]!.major, infos[ordinal]!.motive] do
        discard <| requireCDecl finalReader expression
        unless !own.contains expression do
          throwError "recursor-application selected parent reused another parents original identifier"

private def checkApplication (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (initial finalReader : Context) : MetaM Unit := do
  let info := infos[parent]!
  let major ← requireCDecl finalReader info.major
  let motive ← requireCDecl finalReader info.motive
  unless major.type == recursorMajorDomain stats parent info.indices && major.index < motive.index do
    throwError "recursor-application original major domain or major-before-motive allocation changed"
  for index in info.indices do
    let declaration ← requireCDecl finalReader index
    unless declaration.index < major.index do
      throwError "recursor-application actual index was not allocated before its actual major"
  let reconstructed := finalReader.lctx.mkForall info.indices <|
    finalReader.lctx.mkForall #[info.major] (.sort (.succ .zero))
  unless motive.type == reconstructed do
    throwError "recursor-application recovered original motive domain differs from its actual nested index/major abstraction"
  discard <| requireSort finalReader major.type
  discard <| requireSort finalReader motive.type
  checkInstantiatedDomains finalReader motive.type (info.indices.push info.major)
  let appliedIndices := mkAppN info.motive info.indices
  let .ok (.forallE _ domain body _) := ((monadLift (TypeChecker.checkType appliedIndices) : M Expr) finalReader)
    | throwError "recursor-application fully checked motive/indices did not retain its actual major arrow"
  unless domain == major.type && body == .sort (.succ .zero) do
    throwError "recursor-application actual partial motive application has the wrong major type or result sort"
  let complete := recursorTypeBody infos parent
  unless complete == mkAppN info.motive (info.indices.push info.major) do
    throwError "recursor-application exact selected complete body differs from the actual ordered argument list"
  let sort ← requireSort finalReader complete
  unless sort == .sort (.succ .zero) do
    throwError "recursor-application full checked complete motive application has the wrong elimination sort"
  let metadata := MData.empty.setString `applicationReceipt "original payload"
  let metadataSort ← requireSort finalReader (.mdata metadata complete)
  unless metadataSort == sort do
    throwError "recursor-application metadata payload changed complete application typing"
  checkRetained initial finalReader infos parent

private def expectIllTyped (reader : Context) (expression : Expr) (label : String := "malformed") : MetaM Unit := do
  match ((monadLift (TypeChecker.checkType expression) : M Expr) reader) with
  | .error (.other _) | .error (.funExpected ..) | .error (.appTypeMismatch ..) |
      .error (.typeExpected ..) => pure ()
  | .ok domain => throwError "recursor-application {label} unexpectedly fully checked with type {repr domain}"
  | _ => throwError "recursor-application {label} failed with an unexpected non-typing exception"

private def checkNegativeApplications (reader : Context) (infos : Array RecInfo)
    (parent : Nat) : MetaM Unit := do
  let info := infos[parent]!
  let appliedIndices := mkAppN info.motive info.indices
  match ((monadLift (TypeChecker.checkType appliedIndices) : M Expr) reader) with
  | .ok (.forallE _ _ _ _) => pure ()
  | _ => throwError "recursor-application omitted-major control did not remain a function rather than a sort"
  expectIllTyped reader (.app (recursorTypeBody infos parent) info.major) "duplicate major"
  if info.indices.size == 1 then
    expectIllTyped reader (mkAppN info.motive #[info.major, info.indices[0]!]) "reordered index/major"
    expectIllTyped reader (mkAppN info.motive #[info.indices[0]!, info.indices[0]!]) "duplicate index"
  if info.indices.size == 3 then
    expectIllTyped reader (mkAppN info.motive
      #[info.indices[1]!, info.indices[0]!, info.indices[2]!, info.major]) "reordered dependent indices"
    expectIllTyped reader (mkAppN info.motive
      #[info.indices[0]!, info.indices[0]!, info.indices[2]!, info.major]) "duplicate dependent index"
  for ordinal in [:infos.size] do
    if ordinal != parent then
      expectIllTyped reader (.app appliedIndices infos[ordinal]!.major) "cross-parent major"

private def typeFor (name : Name) (constructors : List Name) : MetaM InductiveType := do
  let some information := (← getEnv).find? name
    | throwError "recursor-application genuine parent declaration missing: {name}"
  let mut ctors : List Constructor := []
  for constructor in constructors do
    let some declaration := (← getEnv).find? constructor
      | throwError "recursor-application genuine constructor declaration missing: {constructor}"
    ctors := ctors ++ [{ name := constructor, type := (declaration.type.instantiateLevelParams
      declaration.levelParams (declaration.levelParams.map fun _ => .zero)) }]
  return { name, ctors, type := (information.type.instantiateLevelParams information.levelParams
    (information.levelParams.map fun _ => .zero)) }

private def statsFor (reader : Context) (types : Array InductiveType) (counts : Array Nat)
    (params : Array Expr := #[]) (levels : List Level := []) : InductiveStats :=
  { lctx := reader.lctx, resultLevel := .succ .zero, levels, params, isNotZero := true,
    nindices := counts, indConsts := types.map fun type => .const type.name levels }

private def checkRegistrationNameControls (stats : InductiveStats)
    (types : Array InductiveType) (infos : Array RecInfo) (reader : Context) : MetaM Unit := do
  let renamed := types.map fun type => { type with name := type.name.appendAfter "_header_receipt" }
  let .ok registered := declareRecursors stats renamed (.succ .zero) infos [] reader.lctx
      false false reader
    | throwError "recursor-header actual registration with fresh recursor names failed"
  for parent in [:renamed.size] do
    let name := mkRecName renamed[parent]!.name
    let some (.recInfo info) := registered.find? name
      | throwError "recursor-header exact native recursor lookup absent"
    unless info.name == name && !info.isUnsafe do
      throwError "recursor-header native name or safety changed"
    let .ok (rules, offset) := mkRecRules renamed (.succ .zero) stats parent
        (infos.map (·.motive)) (infos.flatMap (·.minors))
        (recursorMinorOffset renamed parent) reader
      | throwError "recursor-header original rule generator failed"
    unless info.rules == rules && offset == recursorMinorOffset renamed (parent + 1) do
      throwError "recursor-header original generated rules or minor offset changed"
  if renamed.size > 0 then
    let firstName := mkRecName renamed[0]!.name
    let .error (.alreadyDeclared _ name) := declareRecursors stats renamed (.succ .zero)
        infos [] reader.lctx false false { reader with env := registered }
      | throwError "recursor-header preexisting recursor collision was accepted"
    unless name == firstName do throwError "recursor-header wrong preexisting collision"
    if renamed.size > 1 then
      let duplicate := renamed.map fun type => { type with name := renamed[0]!.name }
      let .error (.alreadyDeclared _ name) := declareRecursors stats duplicate (.succ .zero)
          infos [] reader.lctx false false reader
        | throwError "recursor-header repeated recursor name was accepted"
      unless name == firstName do throwError "recursor-header wrong duplicate collision"

private def checkFixture (reader : Context) (types : Array InductiveType) (counts : Array Nat)
    (params : Array Expr := #[]) (levels : List Level := []) : MetaM Unit := do
  let stats := statsFor reader types counts params levels
  let .ok ((infos, finalReader), returnedBase) := captureFull stats types reader
    | throwError "recursor-application actual full mkRecInfos capture failed"
  checkSameReader reader returnedBase
  unless infos.size == types.size do throwError "recursor-application actual parent count changed"
  for parent in [:types.size] do
    checkApplication stats infos parent reader finalReader
    checkProjectedApplication stats infos parent finalReader
    checkNegativeApplications finalReader infos parent
  checkRegistrationNameControls stats types infos finalReader

private def checkAllocationOnlyControl (reader : Context) (natural : InductiveType) : MetaM Unit := do
  let untyped := Expr.mvar ⟨`ApplicationUntypedIndex⟩
  let constructor : Constructor := {
    name := ``Nat.succ
    type := .forallE `invalid untyped (.app (.const ``Nat []) (.bvar 0)) .default }
  let malformed := { natural with
    type := .forallE `invalid untyped (.sort (.succ .zero)) .default
    ctors := [constructor] }
  let stats := statsFor reader #[malformed] #[1]
  let .ok ((infos, finalReader), _) := captureFull stats #[malformed] reader
    | throwError "recursor-application untyped index native allocation unexpectedly supplied a semantic guard"
  let motive ← requireCDecl finalReader infos[0]!.motive
  expectIllTyped finalReader motive.type "untyped allocated motive domain"

private def checkCancellationFixtures : MetaM Unit := do
  let identifier : FVarId := ⟨`ApplicationCancel⟩
  let other : FVarId := ⟨`ApplicationOther⟩
  let metadata := MData.empty.setString `applicationCancellation "retained payload"
  let expressions : Array Expr := #[.bvar 0, .bvar 9, .fvar identifier, .fvar other,
    .app (.bvar 2) (.fvar identifier),
    .forallE `carrier (.app (.bvar 4) (.fvar identifier)) (.app (.bvar 0) (.fvar identifier)) .implicit,
    .lam `value (.bvar 3) (.app (.fvar identifier) (.bvar 0)) .default,
    .letE `value (.bvar 1) (.fvar identifier) (.app (.bvar 0) (.bvar 5)) false,
    .mdata metadata (.app (.bvar 7) (.fvar identifier)), .proj ``Prod 0 (.fvar identifier)]
  for expression in expressions do
    for depth in [0, 1, 2, 5] do
      let restored := (expression.abstract1 identifier depth).instantiate1' (.fvar identifier) depth
      unless restored == expression do
        throwError "recursor-application abstraction/instantiation cancellation changed a preexisting bvar/binder/metadata payload"
  let head := Expr.fvar ⟨`ApplicationHead⟩
  let ordered := mkAppN head #[.fvar identifier, .fvar other]
  unless ordered == .app (.app head (.fvar identifier)) (.fvar other) &&
      ordered != mkAppN head #[.fvar other, .fvar identifier] &&
      ordered != mkAppN head #[.fvar identifier, .fvar identifier] do
    throwError "recursor-application ordered original fvar array was treated as an unordered or duplicate argument set"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let padding : FVarId := ⟨`ApplicationPadding⟩
  let carrier : FVarId := ⟨`ApplicationCarrier⟩
  let oldLet : FVarId := ⟨`ApplicationOldLet⟩
  let seeded := { reader with
    ngen := { namePrefix := `ApplicationSeed, idx := 219 }
    lctx := (reader.lctx.mkLocalDecl padding `padding (.const ``Nat []) .default
      |>.mkLocalDecl carrier `carrier (.sort (.succ .zero)) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 53)) false) }
  let natural ← typeFor ``Nat [``Nat.zero, ``Nat.succ]
  checkFixture seeded #[natural] #[0]
  let left ← typeFor ``ApplicationLeft [``ApplicationLeft.leaf, ``ApplicationLeft.right]
  let right ← typeFor ``ApplicationRight [``ApplicationRight.left, ``ApplicationRight.higher]
  checkFixture seeded #[left, right] #[0, 0]
  let indexed ← typeFor ``ApplicationIndexed [``ApplicationIndexed.leaf, ``ApplicationIndexed.direct]
  checkFixture seeded #[indexed] #[1]
  let dependent ← typeFor ``ApplicationDependent [``ApplicationDependent.leaf, ``ApplicationDependent.direct]
  checkFixture seeded #[dependent] #[3]
  checkFixture seeded #[indexed, natural] #[1, 0]
  let list ← typeFor ``List [``List.nil, ``List.cons]
  checkFixture seeded #[list] #[0] #[.fvar carrier] [.zero]
  let parameterized ← typeFor ``ApplicationParam [``ApplicationParam.leaf, ``ApplicationParam.direct]
  checkFixture seeded #[parameterized] #[1] #[.fvar carrier]
  checkAllocationOnlyControl seeded natural
  checkCancellationFixtures
  logInfo "recursor-header runtime: seven fresh registrations, nine exact recursor lookups and generated-rule offset checks; seven preexisting-name collisions and two duplicate-parent-name collisions rejected"
  logInfo "recursor-application runtime: seven actual full mkRecInfos captures and nine selected-parent complete applications; independent original motive/major/index cdecl lookups, exact nested motive domains and step-by-step instantiated actual argument domains; full domain/partial-arrow/complete-sort checking, seeded local/let base and retained mutual/other-parent residual fields/IHs/minors; original-parameter controls remain native-only; omitted-major stays a function, duplicate-major/reordered-dependent/duplicate-index/cross-parent-major applications rejected; one untyped-index allocation-only boundary"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name
    | throwError "recursor-application audited declaration absent: {name}"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "recursor-application unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "recursor-application audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "recursor-application new module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditProvenance (name moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "recursor-application foundation module absent: {moduleName}"
  unless environment.getModuleIdxFor? name == some moduleIndex do
    throwError "recursor-application foundation provenance changed: {name} from {moduleName}"

private def auditFoundation (name moduleName : Name) (expected : List Name) : MetaM Unit := do
  auditProvenance name moduleName
  auditDeclaration name expected
  let axioms ← collectAxioms name
  unless axioms.size == expected.length && expected.all axioms.contains do
    throwError "recursor-application foundation dependency set changed: {name}"
  logInfo m!"pinned inherited recursor-application foundation: {name} from {moduleName}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  auditFoundation ``TrProj `Lean4Lean.Verify.Typing.Expr [``sorryAx]
  auditFoundation ``TrProj.uniq `Lean4Lean.Verify.Typing.Lemmas
    [``propext, ``Quot.sound, ``sorryAx]
  for name in [``TrExprS.instN, ``TrExprS.uniq] do
    auditFoundation name `Lean4Lean.Verify.Typing.Lemmas inherited
  let allocation := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let abstraction := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  auditFoundation ``TypeChecker.MLCtx.WF.mkForall_eq `Lean4Lean.Verify.TypeChecker.Basic
    (inherited ++ allocation ++ abstraction)
  auditFoundation ``TypeChecker.MLCtx.WF.mkForall_tr `Lean4Lean.Verify.TypeChecker.Basic
    (inherited ++ allocation)
  auditFoundation ``TypeChecker.MLCtx.WF.mkForall_trS `Lean4Lean.Verify.TypeChecker.Basic inherited
  for name in nativeInterfaces do
    let some (.axiomInfo _) := (← getEnv).find? name
      | throwError "recursor-application native interface is not an existing axiom: {name}"
    auditProvenance name `Lean4Lean.Verify.Axioms
    auditDeclaration name (logical ++ [name])
    logInfo m!"pinned existing native recursor-application interface: {name}"

private def expectAuditRejection (label : String) (expectedPrefix : MessageData)
    (action : MetaM Unit) : MetaM Unit := do
  let failure ← try
    action
    pure none
  catch exception =>
    pure (some exception)
  let some exception := failure
    | throwError "recursor-application {label} audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    unless (← message.toString).startsWith (← expectedPrefix.toString) do
      throw exception
  | .internal .. => throw exception
  logInfo m!"recursor-application rejected audit control {label}: {exception.toMessageData}"

private def checkAuditRejections (logical : List Name) : MetaM Unit := do
  expectAuditRejection "forbidden range even when whitelisted"
    m!"recursor-application unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    (auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq]))
  expectAuditRejection "excluded inherited admission"
    m!"recursor-application unexpected or forbidden axiom {``sorryAx} in {``TrProj}"
    (auditDeclaration ``TrProj logical)
  expectAuditRejection "excluded native interface"
    m!"recursor-application unexpected or forbidden axiom {``Expr.instantiate1_eq} in {``Expr.instantiate1_eq}"
    (auditDeclaration ``Expr.instantiate1_eq logical)
  expectAuditRejection "absent declaration"
    m!"recursor-application audited declaration absent: {`InductiveRecursorApplicationTranslationTest.AbsentDeclaration}"
    (auditDeclaration `InductiveRecursorApplicationTranslationTest.AbsentDeclaration logical)
  expectAuditRejection "absent module"
    m!"recursor-application audited module absent: {`Lean4Lean.Verify.AbsentRecursorApplicationModule}"
    (auditModule `Lean4Lean.Verify.AbsentRecursorApplicationModule logical)
  expectAuditRejection "wrong existing foundation origin"
    m!"recursor-application foundation provenance changed: {``TrProj} from {`Lean4Lean.Verify.Typing.Lemmas}"
    (auditProvenance ``TrProj `Lean4Lean.Verify.Typing.Lemmas)
  expectAuditRejection "whole-module transitive dependency policy"
    "recursor-application unexpected or forbidden axiom "
    (auditModule `Lean4Lean.Verify.InductiveRecursorApplicationFacts logical)
  expectAuditRejection "exact inherited foundation dependency set"
    m!"recursor-application foundation dependency set changed: {``TrProj}"
    (auditFoundation ``TrProj `Lean4Lean.Verify.Typing.Expr [``sorryAx, ``Classical.choice])

#print axioms actualBodyHasExactlyTheSelectedMotiveIndicesAndMajor
#print axioms cancellationAllowsArbitraryPreexistingBoundVariablesWithoutAClosurePremise
#print axioms cancellationPreservesMetadataWithoutDiscardingItsPayload
#print axioms actualCDeclTranslationDerivesTheTypedArgumentFromMixedContextWellFormedness
#print axioms nativeForallSelfApplicationDerivesEveryAppliedArgumentInsteadOfAssumingBodyTyping
#print axioms actualSelectedForallSortApplicationUsesOnlyTheTranslatedNativeMotiveType
#print axioms actualSourceRecoversTheUnpeeledOriginalMotiveDomainAtTheCurrentReader
#print axioms selectedDomainHistoryDerivesMotiveAndMajorApplicationSupportInsteadOfReceivingIt
#print axioms domainOnlySupportDerivesWholeRawSupportFromTheSameActualSource
#print axioms actualEndpointDerivesRawStoredReceiptsFromDomainsWithoutWholeBodyTyping
#print axioms actualEndpointExposesFinalStoredTypehoodFromSelectedDomains
#print axioms actualEndpointExposesFinalRawTypehoodFromSelectedDomains
#print axioms actualEndpointExposesFinalMetadataTypehoodFromSelectedDomains
#print axioms actualEndpointExposesAllFinalTypehoodFromSelectedDomains
#print axioms actualEndpointExposesAllInitialTypehoodFromSelectedDomains
#print axioms actualEndpointExposesAllInitialAndFinalTypehoodFromSelectedDomains
#print axioms actualGetterRecoversSourcesAtItsSameSuccessAndNeedsOnlySelectedDomainSupport
#print axioms actualGetterExposesInitialTypehoodAtEveryBoundedParent
#print axioms actualGetterExposesInitialAndFinalTypehoodAtEveryBoundedParent
#print axioms actualGetterExposesFinalStoredTypehoodAtEveryBoundedParent
#print axioms actualGetterExposesFinalRawTypehoodAtEveryBoundedParent
#print axioms actualGetterExposesFinalMetadataTypehoodAtEveryBoundedParent
#print axioms scopedAppliedGetterPassesFinalMetadataTypehoodToContinuation
#print axioms scopedAppliedGetterPassesFinalStoredTypehoodToContinuation
#print axioms scopedAppliedGetterPassesFinalRawTypehoodToContinuation
#print axioms scopedAppliedGetterPassesAllFinalTypehoodToContinuation
#print axioms scopedAppliedGetterPassesAllInitialTypehoodToContinuation
#print axioms scopedAppliedGetterPassesAllInitialAndFinalTypehoodToContinuation
#print axioms scopedAppliedGetterKeepsOneDerivedModelAndLeavesRulesAndRegistrationSeparate
#print axioms registeredAppliedGetterKeepsReceiptsWithEnvironmentRegistration
#print axioms registeredAppliedGetterExposesCombinedTypehoodWithEnvironmentRegistration
#print axioms Lean4Lean.AddInductive.mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes
#print axioms Lean4Lean.AddInductive.RecursorRuleRhsScope.impRegistrationRuleSemantics
#print axioms Lean4Lean.AddInductive.mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults
#print axioms registeredScopedGetterPassesCombinedTypehoodToContinuation
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_closedTranslation
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_recursorTranslation
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_declaredRecursor
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWFOfDeclaredRecursors
#print axioms Lean4Lean.AddInductive.RecursorInfoModelEndpoint.initialStoredWF_of_declaredRecursorFromDomains
#print axioms Lean4Lean.AddInductive.RecursorInfoModelEndpoint.initialStoredWFOfDeclaredRecursorsFromDomains
#print axioms Lean4Lean.AddInductive.mkRecInfos.getTranslatedAppliedInitialStoredWFOfDeclaredRecursors
#print axioms Lean4Lean.AddInductive.RecursorTypeModelReceipt.existsDeclaredRecursor
#print axioms Lean4Lean.AddInductive.mkRecInfos.registeredTranslatedAppliedDeclaredRecursors
#print axioms actualRegisteredRecursorsHaveModelsAndGeneratedRules
#print axioms insertedRecursorModelsHaveExactLookupsAndKeepOldEquations
#print axioms Lean4Lean.AddInductive.declareRecursors.refinesChecker
#print axioms Lean4Lean.AddInductive.declareRecursors.refinesChecker_of_typeReceipts
#print axioms Lean4Lean.AddInductive.mkRecInfos.registeredTranslatedAppliedChecker
#print axioms letOnlyContextIsNotAClosedNativeTranslationContext
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let abstraction := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let allocation := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``PersistentHashMap.findAux_isSome]
  let nativeInterfaces := abstraction ++ allocation ++ [``Expr.instantiate1_eq]
  let native := logical ++ nativeInterfaces
  let inherited := native ++ [``sorryAx]
  let checkerInsertion := logical ++ [``sorryAx, ``PersistentHashMap.findAux_isSome,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  for name in [``actualBodyHasExactlyTheSelectedMotiveIndicesAndMajor,
      ``realDependentApplicationCannotReplaceCombinedSuffixLiftingWithIdentity,
      ``mismatchedCancellationDepthDoesNotRestoreTheOriginalBoundVariable,
      ``arrayApplicationPreservesOrderedOriginalFVarsNotASetOfArguments,
      ``captureFull, ``checkSameReader, ``requireCDecl, ``requireSort,
      ``checkInstantiatedDomains, ``projectSelected, ``checkProjectedApplication,
      ``checkRetained, ``checkApplication, ``expectIllTyped, ``checkNegativeApplications,
      ``typeFor, ``statsFor, ``checkFixture, ``checkRegistrationNameControls, ``checkAllocationOnlyControl,
      ``checkCancellationFixtures, ``runtimeFixtures, ``auditDeclaration, ``auditModule,
      ``auditProvenance, ``auditFoundation, ``auditFoundations,
      ``expectAuditRejection, ``checkAuditRejections] do
    auditDeclaration name logical
  for name in [``cancellationAllowsArbitraryPreexistingBoundVariablesWithoutAClosurePremise,
      ``cancellationKeepsNestedBindersAndBothSidesOfTheDepthBoundary,
      ``cancellationPreservesMetadataWithoutDiscardingItsPayload,
      ``actualSourceRecoversTheUnpeeledOriginalMotiveDomainAtTheCurrentReader] do
    auditDeclaration name (logical ++ abstraction ++ allocation)
  for name in [``actualCDeclTranslationDerivesTheTypedArgumentFromMixedContextWellFormedness,
      ``nativeForallSelfApplicationDerivesEveryAppliedArgumentInsteadOfAssumingBodyTyping,
      ``actualSelectedForallSortApplicationUsesOnlyTheTranslatedNativeMotiveType,
      ``selectedDomainHistoryDerivesMotiveAndMajorApplicationSupportInsteadOfReceivingIt,
      ``domainOnlySupportDerivesWholeRawSupportFromTheSameActualSource,
      ``actualEndpointDerivesRawStoredReceiptsFromDomainsWithoutWholeBodyTyping,
      ``actualEndpointExposesFinalStoredTypehoodFromSelectedDomains,
      ``actualEndpointExposesFinalRawTypehoodFromSelectedDomains,
      ``actualEndpointExposesFinalMetadataTypehoodFromSelectedDomains,
      ``actualEndpointExposesAllFinalTypehoodFromSelectedDomains,
      ``actualEndpointExposesAllInitialTypehoodFromSelectedDomains,
      ``actualEndpointExposesAllInitialAndFinalTypehoodFromSelectedDomains,
      ``actualGetterRecoversSourcesAtItsSameSuccessAndNeedsOnlySelectedDomainSupport,
      ``actualGetterExposesInitialTypehoodAtEveryBoundedParent,
      ``actualGetterExposesInitialAndFinalTypehoodAtEveryBoundedParent,
      ``actualGetterExposesFinalStoredTypehoodAtEveryBoundedParent,
      ``actualGetterExposesFinalRawTypehoodAtEveryBoundedParent,
      ``actualGetterExposesFinalMetadataTypehoodAtEveryBoundedParent,
      ``scopedAppliedGetterPassesFinalMetadataTypehoodToContinuation,
      ``scopedAppliedGetterPassesFinalStoredTypehoodToContinuation,
      ``scopedAppliedGetterPassesFinalRawTypehoodToContinuation,
      ``scopedAppliedGetterPassesAllFinalTypehoodToContinuation,
      ``scopedAppliedGetterPassesAllInitialTypehoodToContinuation,
      ``scopedAppliedGetterPassesAllInitialAndFinalTypehoodToContinuation,
      ``scopedAppliedGetterKeepsOneDerivedModelAndLeavesRulesAndRegistrationSeparate,
      ``registeredAppliedGetterKeepsReceiptsWithEnvironmentRegistration,
      ``registeredAppliedGetterExposesCombinedTypehoodWithEnvironmentRegistration,
      ``Lean4Lean.AddInductive.mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes,
      ``Lean4Lean.AddInductive.mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults,
      ``registeredScopedGetterPassesCombinedTypehoodToContinuation,
      ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF,
      ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_closedTranslation,
      ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_recursorTranslation,
      ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWF_of_declaredRecursor,
      ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.initialStoredWFOfDeclaredRecursors] do
    auditDeclaration name inherited
  auditDeclaration ``Lean4Lean.AddInductive.RecursorRuleRhsScope.impRegistrationRuleSemantics
    (logical ++ [``sorryAx])
  auditDeclaration ``actualEndpointDerivesInitialStoredWFOfDeclaredRecursorFromSelectedDomains inherited
  auditDeclaration ``actualEndpointDerivesInitialStoredWFForDeclaredRecursorsFromSelectedDomains inherited
  auditDeclaration ``actualGetterExposesInitialStoredWFOfDeclaredRecursors inherited
  auditDeclaration ``Lean4Lean.AddInductive.RecursorTypeModelReceipt.existsDeclaredRecursor
    (logical ++ [``sorryAx])
  auditDeclaration ``actualRegisteredRecursorsHaveModelsAndGeneratedRules inherited
  auditDeclaration ``insertedRecursorModelsHaveExactLookupsAndKeepOldEquations checkerInsertion
  auditDeclaration ``Lean4Lean.AddInductive.declareRecursors.refinesChecker checkerInsertion
  auditDeclaration ``Lean4Lean.AddInductive.declareRecursors.refinesChecker_of_typeReceipts
    checkerInsertion
  auditFoundation ``CheckerEnv.addConst `Lean4Lean.Verify.Environment.Checker checkerInsertion
  auditFoundation ``CheckerEnv.of_valueFrame `Lean4Lean.Verify.Environment.Checker (logical ++ [``sorryAx])
  auditDeclaration ``letOnlyContextIsNotAClosedNativeTranslationContext (logical ++ [``sorryAx])
  for name in [``Lean.Expr.instantiate1'_abstract1,
      ``Lean4Lean.AddInductive.mkForall_selected_cons] do
    auditDeclaration name native
  for name in [``Lean4Lean.AddInductive.SelectedRecursorTelescope.bodyApplicationSupport,
      ``Lean4Lean.AddInductive.RecursorSelectedDomainSupport.rawTypeSupport,
      ``Lean4Lean.AddInductive.RecursorInfoModelEndpoint.recursorTypeFromDomains,
      ``Lean4Lean.AddInductive.mkRecInfos.getTranslatedAppliedRecursorTypes] do
    auditDeclaration name inherited
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveRecursorApplicationFacts (logical ++ abstraction)
  auditModule `Lean4Lean.Verify.InductiveRecursorApplicationNative (logical ++ abstraction ++ allocation)
  auditModule `Lean4Lean.Verify.InductiveRecursorApplicationTranslation
    (logical ++ abstraction ++ allocation ++ [``sorryAx])
  auditModule `Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS inherited
  auditModule `Lean4Lean.Verify.RecursorHeaders inherited
  auditFoundations nativeInterfaces
  checkAuditRejections logical
  let reader : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "recursor-application audits: every module-owned declaration including private/generated helpers transitively checked; clean annotation/binder core and runtime helpers exclude sorryAx; facts/native exclude inherited admissions; semantic/CPS retain explicitly pinned inherited admissions; seven exact foundation dependency/provenance pins, two existing CheckerEnv pins and nine existing native-interface pins; eight negative audit controls including whole-module policy and forbidden range even if whitelisted"

end InductiveRecursorApplicationTranslationTest
