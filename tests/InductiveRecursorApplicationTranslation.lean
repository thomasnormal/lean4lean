import Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS
import Lean4Lean.Verify.InductiveRecursorApplicationTranslation
import Lean4Lean.Verify.InductiveRecursorApplicationNative
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
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
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats result.1 parent result.2 model finalModel :=
  mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport

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
  logInfo "recursor-application runtime: seven actual full mkRecInfos captures and nine selected-parent complete applications; independent original motive/major/index cdecl lookups, exact nested motive domains and step-by-step instantiated actual argument domains; full domain/partial-arrow/complete-sort checking, seeded local/let base and retained mutual/other-parent residual fields/IHs/minors; original-parameter controls remain native-only; omitted-major stays a function, duplicate-major/reordered-dependent/duplicate-index/cross-parent-major applications rejected; one untyped-index allocation-only boundary"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "recursor-application unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) : MetaM Unit := do
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
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations : MetaM Unit := do
  for name in [``TrProj, ``TrProj.uniq, ``TrExprS.instN, ``TrExprS.uniq] do
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  logInfo "recursor-application inherited translation foundations pinned separately"

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
#print axioms actualGetterRecoversSourcesAtItsSameSuccessAndNeedsOnlySelectedDomainSupport
#print axioms scopedAppliedGetterKeepsOneDerivedModelAndLeavesRulesAndRegistrationSeparate
#print axioms runtimeFixtures

run_meta
  let reader : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := logical ++ nativeInterfaces
  let inherited := native ++ [``sorryAx]
  for name in [``Lean.Expr.instantiate1'_abstract1,
      ``Lean4Lean.AddInductive.mkForall_selected_cons] do
    auditDeclaration name native
  for name in [``Lean4Lean.AddInductive.SelectedRecursorTelescope.bodyApplicationSupport,
      ``Lean4Lean.AddInductive.RecursorSelectedDomainSupport.rawTypeSupport,
      ``Lean4Lean.AddInductive.RecursorInfoModelEndpoint.recursorTypeFromDomains,
      ``Lean4Lean.AddInductive.mkRecInfos.getTranslatedAppliedRecursorTypes] do
    auditDeclaration name inherited
  for moduleName in [`Lean4Lean.Verify.InductiveRecursorApplicationFacts,
      `Lean4Lean.Verify.InductiveRecursorApplicationNative] do
    auditModule moduleName
  for moduleName in [`Lean4Lean.Verify.InductiveRecursorApplicationTranslation,
      `Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS] do
    auditModule moduleName
  auditFoundations
  logInfo "recursor-application audits: four new modules censused; module-owned axioms and Expr.looseBVarRange_eq forbidden; inherited uniqueness/instantiation foundations pinned"

end InductiveRecursorApplicationTranslationTest
