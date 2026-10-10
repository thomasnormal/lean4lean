import Lean4Lean.Verify.InductiveRecursorTypeNative
import Lean4Lean.Verify.InductiveRecursorImplicitTranslation
import Lean4Lean.Verify.InductiveRecursorTypeTranslation
import Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS
import Lean4Lean.Verify.InductiveMinorPassTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveRecursorTypeTranslationTest

mutual
  inductive RawLeft where
    | leaf : RawLeft
    | right (child : RawRight) : RawLeft
  inductive RawRight where
    | left (child : RawLeft) : RawRight
    | higher (children : Nat → RawLeft) : RawRight
end

inductive RawHigher where
  | leaf : RawHigher
  | higher (children : Nat → RawHigher) : RawHigher
  | dependent (children : (carrier : Type) → carrier → RawHigher) : RawHigher
  | pair (left right : RawHigher) : RawHigher

inductive RawIndexed : Nat → Type where
  | leaf (ordinal : Nat) : RawIndexed ordinal
  | direct (ordinal : Nat) (child : RawIndexed ordinal) : RawIndexed ordinal

inductive RawFamily (carrier : Type) : Nat → Type where
  | leaf (ordinal : Nat) (payload : carrier) : RawFamily carrier ordinal
  | direct (ordinal : Nat) (child : RawFamily carrier ordinal) : RawFamily carrier ordinal

private theorem rawBodyUsesOnlyTheSelectedParentsMotiveIndicesAndMajor
    (infos : Array RecInfo) (parent : Nat) :
    recursorTypeBody infos parent =
      Expr.app (mkAppN infos[parent]!.motive infos[parent]!.indices) infos[parent]!.major := rfl

private theorem exactMetadataTypeKeepsTheRealInferImplicitBoundary
    (stats : InductiveStats) (types : Array InductiveType) (infos : Array RecInfo)
    (reader : Context) (parent : Nat) :
    (declareRecursors.metadataVal stats types (.succ .zero) infos reader.lparams reader.lctx
      false false parent []).type = (recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false :=
  declareRecursors.metadataVal_type stats types (.succ .zero) infos reader.lparams reader.lctx
    false false parent []

private theorem fullReaderSemanticWeakeningCannotUseProjectionIdentity :
    (VExpr.forallE (.bvar 0) (.bvar 2)).liftN 4 = .forallE (.bvar 4) (.bvar 6) ∧
      (VExpr.forallE (.bvar 0) (.bvar 2)).liftN 4 ≠ .forallE (.bvar 0) (.bvar 2) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem nativeSelectionIgnoresOnlyOriginalPhysicalIndices
    (left right : LocalContext) (ids : List FVarId) (body : Expr)
    (leftScope : left.BindingScope) (rightScope : right.BindingScope)
    (bodyClosed : body.looseBVarRange' = 0) (distinct : ids.Nodup)
    (agreement : SelectedCDeclBindingAgreement left right ids) :
    left.mkForall (ids.map Expr.fvar).toArray body =
      right.mkForall (ids.map Expr.fvar).toArray body :=
  mkForall_congr_selected_cdecl ids leftScope rightScope bodyClosed distinct agreement

private theorem nestedActualRawGroupsEqualExactlyTheirSelectedConcatenation
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat) (full : LocalContext)
    (ids : List FVarId) (scope : full.BindingScope)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (selected : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings full ids) :
    recursorRawType stats infos parent full =
      full.mkForall (ids.map Expr.fvar).toArray (recursorTypeBody infos parent) :=
  recursorRawType_eq_flat_selected stats infos parent full ids scope bodyClosed
    selected distinct bindings

private theorem selectedProjectionDerivesItsWellFormednessFromOneInitialModel
    (env : VEnv) (universes : List Name) (full : LocalContext) (initial projected : MLCtx)
    (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes full initial ids projected)
    (initialWF : initial.WF env universes) : projected.WF env universes :=
  telescope.context initialWF

private theorem selectedProjectionKeepsOriginalDomainsNamesAndBinderInfosNotPhysicalIndices
    (env : VEnv) (universes : List Name) (full : LocalContext) (initial projected : MLCtx)
    (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes full initial ids projected)
    (initialWF : initial.WF env universes) :
    ∀ identifier ∈ ids, ∃ physicalIndex projectedIndex name domain binder,
      full.find? identifier = some (.cdecl physicalIndex identifier name domain binder .default) ∧
      projected.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) :=
  telescope.lookups initialWF

private theorem selectedProjectionDerivesDistinctnessInsteadOfAssumingAValidFinalContext
    (env : VEnv) (universes : List Name) (full : LocalContext) (initial projected : MLCtx)
    (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes full initial ids projected)
    (initialWF : initial.WF env universes) : ids.Nodup :=
  telescope.distinct initialWF

private theorem selectedProjectionExtendsByExactlyTheSelectedOriginalIdentifiers
    (env : VEnv) (universes : List Name) (full : LocalContext) (initial projected : MLCtx)
    (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes full initial ids projected) :
    IndexMLCtxExtension initial ids projected := telescope.extension

private theorem motiveAndMajorComponentsSupplyTheActualBodyApplicationNotWholeRawTyping
    (env : VEnv) (universes : List Name) (infos : Array RecInfo) (parent : Nat)
    (virtual : VLCtx)
    (support : RecursorTypeBodyApplicationSupport env universes infos parent virtual) :
    ∃ semantic level,
      TrExprS env universes virtual (recursorTypeBody infos parent) semantic ∧
      env.HasType universes.length virtual.toCtx semantic (.sort level) :=
  support.translated

private theorem abstractionReturnsToTheSameInitialSelectionBase
    (env : VEnv) (universes : List Name) (full : LocalContext) (initial projected : MLCtx)
    (ids : List FVarId)
    (telescope : SelectedRecursorTelescope env universes full initial ids projected)
    (envWF : env.WF) (initialWF : initial.WF env universes) (body : Expr) (semantic : VExpr)
    (translated : TrExprS env universes projected.vlctx body semantic)
    (typed : env.IsType universes.length projected.vlctx.toCtx semantic) :
    ∃ abstracted level,
      TrExprS env universes initial.vlctx
        (projected.lctx.mkForall (ids.map Expr.fvar).toArray body) abstracted ∧
      env.HasType universes.length initial.vlctx.toCtx abstracted (.sort level) :=
  telescope.typedAbstraction envWF initialWF translated typed

private theorem rawTypeUsesOnlySelectedDomainAndBodyComponentSupport
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (full : LocalContext) (initial : MLCtx)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent full initial)
    (envWF : env.WF) (initialWF : initial.WF env universes) (fullScope : full.BindingScope) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx (recursorRawType stats infos parent full) semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) :=
  support.rawTypeTranslation envWF initialWF fullScope

private theorem actualEndpointKeepsZeroParametersAndUsesRealCombinedSuffixLifting
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) ∧
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx)
        (semantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (semantic.liftN (final.length - initial.length)) (.sort level) :=
  endpoint.rawTypeAtFinal envWF initialWF parameterFree parent support

private theorem strictInferImplicitZeroKeepsTheSameSemanticAtBothRangePolicies
    (env : VEnv) (universes : List Name) (virtual : VLCtx) (expression : Expr)
    (semantic : VExpr) (translated : TrExprS env universes virtual expression semantic) :
    TrExprS env universes virtual (expression.inferImplicit 0 false) semantic ∧
      TrExprS env universes virtual (expression.inferImplicit 0 true) semantic :=
  ⟨translated.inferImplicit 0 false, translated.inferImplicit 0 true⟩

private theorem strictInferImplicitOneKeepsTheSameSemanticAtBothRangePolicies
    (env : VEnv) (universes : List Name) (virtual : VLCtx) (expression : Expr)
    (semantic : VExpr) (translated : TrExprS env universes virtual expression semantic) :
    TrExprS env universes virtual (expression.inferImplicit 1 false) semantic ∧
      TrExprS env universes virtual (expression.inferImplicit 1 true) semantic :=
  ⟨translated.inferImplicit 1 false, translated.inferImplicit 1 true⟩

private theorem strictInferImplicitThousandKeepsTheSameSemanticAtBothRangePolicies
    (env : VEnv) (universes : List Name) (virtual : VLCtx) (expression : Expr)
    (semantic : VExpr) (translated : TrExprS env universes virtual expression semantic) :
    TrExprS env universes virtual (expression.inferImplicit 1000 false) semantic ∧
      TrExprS env universes virtual (expression.inferImplicit 1000 true) semantic :=
  ⟨translated.inferImplicit 1000 false, translated.inferImplicit 1000 true⟩

private theorem nonStrictInferImplicitKeepsTheSameSemanticForEveryCountAndRangePolicy
    (env : VEnv) (universes : List Name) (virtual : VLCtx) (expression : Expr)
    (semantic : VExpr) (translated : TrExpr env universes virtual expression semantic)
    (count : Nat) (considerRange : Bool) :
    TrExpr env universes virtual (expression.inferImplicit count considerRange) semantic :=
  translated.inferImplicit count considerRange

private theorem storedMetadataTypeUsesTheSameSemanticAsTheActuallyProvedRawType
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (reader : Context) (parent : Nat) (initial : MLCtx)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent reader.lctx initial)
    (envWF : env.WF) (initialWF : initial.WF env universes) (fullScope : reader.lctx.BindingScope) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx (recursorRawType stats infos parent reader.lctx) semantic ∧
      TrExprS env universes initial.vlctx
        (declareRecursors.metadataVal stats types (.succ .zero) infos reader.lparams reader.lctx
          false false parent []).type semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) := by
  obtain ⟨semantic, level, translated, typed⟩ := support.rawTypeTranslation envWF initialWF fullScope
  exact ⟨semantic, level, translated, by
    rw [declareRecursors.metadataVal_type]
    exact translated.inferImplicit 1000 false, typed⟩

private theorem receiptRestrictsRawAndStoredFreeVariablesToTheSameInitialBase
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (reader : Context) (initial final : MLCtx)
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    Expr.FVarsIn (· ∈ initial.vlctx.fvars) (recursorRawType stats infos parent reader.lctx) ∧
      Expr.FVarsIn (· ∈ initial.vlctx.fvars)
        ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) :=
  receipt.sourceFVars

private theorem receiptDerivesRawAndStoredClosureWithoutTheGlobalNativeRangeAxiom
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (reader : Context) (initial final : MLCtx)
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    (recursorRawType stats infos parent reader.lctx).looseBVarRange' = 0 ∧
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false).looseBVarRange' = 0 :=
  receipt.sourceClosed

private theorem receiptMatchesTheActualMetadataTypeAtBothModelsWithRealSuffixLifting
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (reader : Context) (initial final : MLCtx)
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (types : Array InductiveType) (elimLevel : Level) (rules : List RecursorRule) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos reader.lparams reader.lctx
          false false parent rules).type semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) ∧
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos reader.lparams reader.lctx
          false false parent rules).type (semantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (semantic.liftN (final.length - initial.length)) (.sort level) :=
  receipt.metadataType types elimLevel reader.lparams false false rules

private theorem actualEndpointBuildsRawAndStoredReceiptsFromOnlyComponentSupports
    (env : VEnv) (universes : List Name) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (reader finalReader : Context) (infos : Array RecInfo)
    (initial final : MLCtx)
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final :=
  endpoint.recursorType envWF initialWF parameterFree parent support

private theorem actualFullGetterReturnsEachBoundedParentsReceiptAtItsActualSuccessCheckpoint
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
    (typeSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorRawTypeTranslationSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats result.1 parent result.2 model finalModel :=
  mkRecInfos.getTranslatedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport typeSupport

private theorem actualScopedCpsKeepsRuleAndRegistrationSoundnessAsLaterObligations
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
    (typeSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorRawTypeTranslationSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post :=
  mkRecInfos.scopedTranslatedRecursorTypes stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport typeSupport nextWF

private def captureFull (stats : InductiveStats) (types : Array InductiveType) :
    M ((Array RecInfo × Context) × Context) := do
  let result ← mkRecInfos stats types (.succ .zero) fun infos =>
    return (infos, ← readThe Context)
  return (result, ← readThe Context)

private def checkSameReader (before after : Context) : MetaM Unit := do
  unless before.ngen.curr == after.ngen.curr && before.lctx.decls.size == after.lctx.decls.size do
    throwError "recursor-type outer reader allocation state changed"
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "recursor-type original outer declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "recursor-type original outer declaration changed"

private def project (full : Context) (binders : Array Expr) : MetaM Context := do
  let mut projected := { full with lctx := {} }
  let mut changedPhysicalIndex := false
  for ordinal in [:binders.size] do
    let identifier := binders[ordinal]!.fvarId!
    let some (.cdecl physicalIndex _ name domain binder .default) := full.lctx.find? identifier
      | throwError "recursor-type selected original cdecl is missing"
    unless (projected.lctx.find? identifier).isNone do
      throwError "recursor-type selection reused an already selected original identifier"
    let .ok (.sort _) := ((monadLift (TypeChecker.checkType domain) : M Expr) projected)
      | throwError "recursor-type copied actual domain is not typeable at this selection step"
    projected := { projected with lctx := projected.lctx.mkLocalDecl identifier name domain binder }
    let copied := projected.lctx.get! identifier
    unless copied.index == ordinal && copied.type == domain && copied.userName == name &&
        copied.binderInfo == binder && copied.deps == domain.fvarsList do
      throwError "recursor-type copied cdecl domain/name/binder/dependencies or dense selection index changed"
    changedPhysicalIndex := changedPhysicalIndex || copied.index != physicalIndex
  unless changedPhysicalIndex do throwError "recursor-type fixture did not exercise changed physical declaration indices"
  return projected

private def checkScopeAndOrder (stats : InductiveStats) (infos : Array RecInfo)
    (parent : Nat) (initial finalReader : Context) (binders : Array Expr) : MetaM Unit := do
  let expected := stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors) ++
    infos[parent]!.indices ++ #[infos[parent]!.major]
  unless binders == expected do throwError "recursor-type exact selected binder group order changed"
  let mut reordered := false
  let mut previous := 0
  for ordinal in [:binders.size] do
    let declaration := finalReader.lctx.get! binders[ordinal]!.fvarId!
    if ordinal > 0 && declaration.index < previous then reordered := true
    previous := declaration.index
  unless reordered do throwError "recursor-type fixture did not exercise reordered original declaration indices"
  let allParent := infos.flatMap fun info => info.indices ++ #[info.major, info.motive]
  let retained := stats.params ++ allParent ++ infos.flatMap (·.minors)
  let mut residual := 0
  for declaration in finalReader.lctx.decls.toList.filterMap id do
    if (initial.lctx.find? declaration.fvarId).isNone && !retained.contains declaration.toExpr then
      residual := residual + 1
      unless !binders.contains declaration.toExpr do
        throwError "recursor-type selection included a residual constructor field or hypothesis"
  unless residual > 0 do throwError "recursor-type fixture has no excluded persistent constructor fields/hypotheses"
  for ordinal in [:infos.size] do
    if ordinal != parent then
      for value in infos[ordinal]!.indices ++ #[infos[ordinal]!.major] do
        unless !binders.contains value do
          throwError "recursor-type selection included another parents indices or major"

private def checkType (stats : InductiveStats) (types : Array InductiveType) (infos : Array RecInfo)
    (parent : Nat) (initial finalReader : Context) : MetaM Unit := do
  let binders := recursorTypeBinders stats infos parent
  checkScopeAndOrder stats infos parent initial finalReader binders
  let projected ← project finalReader binders
  let body := recursorTypeBody infos parent
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType body) : M Expr) projected)
    | throwError "recursor-type exact selected motive/indices/major application is not typeable"
  let raw := recursorRawType stats infos parent finalReader.lctx
  let projectedRaw := recursorRawType stats infos parent projected.lctx
  unless raw == projectedRaw && raw.fvarsList.isEmpty && !raw.hasLooseBVars do
    throwError "recursor-type sparse reordered projection changed raw abstraction or retained an unselected fvar"
  let flat := projected.lctx.mkForall binders body
  unless raw == flat do throwError "recursor-type nested selected group abstraction differs from its exact concatenation"
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType raw) : M Expr) finalReader)
    | throwError "recursor-type actual raw type is not typeable at the actual final reader"
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType projectedRaw) : M Expr) { projected with lctx := {} })
    | throwError "recursor-type selected abstraction did not return to its initial empty selection base"
  let stored := (declareRecursors.metadataVal stats types (.succ .zero) infos finalReader.lparams
    finalReader.lctx false false parent []).type
  unless stored == raw.inferImplicit 1000 false do
    throwError "recursor-type actual stored metadata no longer uses inferImplicit 1000 false"
  let .ok (.sort _) := ((monadLift (TypeChecker.checkType stored) : M Expr) finalReader)
    | throwError "recursor-type actual inferImplicit result does not fully type-check as a sort"

private def checkProjectionFailures (stats : InductiveStats) (infos : Array RecInfo)
    (finalReader : Context) : MetaM Unit := do
  let firstMinor := (infos.flatMap (·.minors))[0]!
  let empty := { finalReader with lctx := {} }
  let declaration := finalReader.lctx.get! firstMinor.fvarId!
  match ((monadLift (TypeChecker.checkType declaration.type) : M Expr) empty) with
  | .error (.other _) => pure ()
  | _ => throwError "recursor-type invalid forward minor-before-motive order was not rejected"
  let selected := recursorTypeBinders stats infos 0
  let omitted := selected.filter fun value => value != infos[0]!.major
  let projected ← project finalReader omitted
  match ((monadLift (TypeChecker.checkType (recursorTypeBody infos 0)) : M Expr) projected) with
  | .error (.other _) => pure ()
  | _ => throwError "recursor-type omitted-major projection must not supply body application typing"
  let duplicated := selected.push selected[0]!
  let accepted ← try
    discard <| project finalReader duplicated
    pure true
  catch _ => pure false
  unless !accepted do throwError "recursor-type duplicate original identifier was accepted as fresh"

private def typeFor (name : Name) (constructors : List Name) : MetaM InductiveType := do
  let some information := (← getEnv).find? name
    | throwError "recursor-type genuine parent declaration missing: {name}"
  let mut ctors : List Constructor := []
  for constructor in constructors do
    let some declaration := (← getEnv).find? constructor
      | throwError "recursor-type genuine constructor declaration missing: {constructor}"
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
    | throwError "recursor-type actual full mkRecInfos capture failed"
  checkSameReader reader returnedBase
  unless infos.size == types.size do throwError "recursor-type actual full parent count changed"
  for parent in [:types.size] do
    checkType stats types infos parent reader finalReader
  checkProjectionFailures stats infos finalReader

private def checkAllocationOnlyControl (reader : Context) (type : InductiveType) : MetaM Unit := do
  let constructor : Constructor := {
    name := ``Nat.succ
    type := .forallE `invalid (.mvar ⟨`RawUntypedField⟩) (.const ``Nat []) .default }
  let invalid := { type with ctors := [constructor] }
  let stats := statsFor reader #[invalid] #[0]
  let .ok ((infos, finalReader), _) := captureFull stats #[invalid] reader
    | throwError "recursor-type untyped field allocation unexpectedly supplied a semantic guard"
  let raw := recursorRawType stats infos 0 finalReader.lctx
  match ((monadLift (TypeChecker.checkType raw) : M Expr) finalReader) with
  | .error (.other _) => pure ()
  | _ => throwError "recursor-type raw native allocation must not justify projected domain typing"

private def checkFailures (reader : Context) (type : InductiveType) : MetaM Unit := do
  let stats := statsFor reader #[type] #[0]
  let noOpening := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match captureFull stats #[type] noOpening with
  | .error .deepRecursion => pure ()
  | _ => throwError "recursor-type actual parent opening-fuel failure must propagate"
  let noNormalization := { reader with fuel := { reader.fuel with whnf := 0 } }
  match captureFull stats #[type] noNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "recursor-type actual initial-WHNF failure must propagate"
  let message := "recursor-type callback failure"
  match mkRecInfos stats #[type] (.succ .zero) (fun _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "recursor-type post-allocation callback exception changed"
  | _ => throwError "recursor-type post-allocation callback failure must propagate"

private def binderInfos (expression : Expr) : List BinderInfo :=
  match expression with
  | .forallE _ _ body binder => binder :: binderInfos body
  | _ => []

private def checkImplicitFixtures : MetaM Unit := do
  let dependent := Expr.forallE `carrier (.sort (.succ .zero))
    (.forallE `value (.bvar 0) (.bvar 1) .default) .default
  unless binderInfos (dependent.inferImplicit 0 false) == [.default, .default] &&
      binderInfos (dependent.inferImplicit 1 false) == [.implicit, .default] &&
      binderInfos (dependent.inferImplicit 1000 false) == [.implicit, .default] do
    throwError "recursor-type inferImplicit count boundary or dependent binder promotion changed"
  let rangeOnly := Expr.forallE `carrier (.sort (.succ .zero)) (.bvar 0) .default
  unless binderInfos (rangeOnly.inferImplicit 1000 false) == [.default] &&
      binderInfos (rangeOnly.inferImplicit 1000 true) == [.implicit] do
    throwError "recursor-type inferImplicit considerRange polarity changed"
  let metadata := Expr.mdata {} dependent
  unless binderInfos (metadata.inferImplicit 1000 false) == [] &&
      metadata.inferImplicit 1000 false == metadata do
    throwError "recursor-type inferImplicit crossed a metadata non-forall barrier"
  let terminal := Expr.const ``Nat []
  unless terminal.inferImplicit 1000 true == terminal do
    throwError "recursor-type inferImplicit changed a non-forall terminal"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let padding := FVarId.mk `RawPadding
  let carrier := FVarId.mk `RawCarrier
  let oldLet := FVarId.mk `RawOldLet
  let seeded := { reader with
    ngen := { namePrefix := `RawSeed, idx := 137 }
    lctx := reader.lctx.mkLocalDecl padding `padding (.const ``Nat []) .default
      |>.mkLocalDecl carrier `carrier (.sort (.succ .zero)) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 41)) false }
  let natural ← typeFor ``Nat [``Nat.zero, ``Nat.succ]
  checkFixture seeded #[natural] #[0]
  let left ← typeFor ``RawLeft [``RawLeft.leaf, ``RawLeft.right]
  let right ← typeFor ``RawRight [``RawRight.left, ``RawRight.higher]
  checkFixture seeded #[left, right] #[0, 0]
  let higher ← typeFor ``RawHigher [``RawHigher.leaf, ``RawHigher.higher,
    ``RawHigher.dependent, ``RawHigher.pair]
  checkFixture seeded #[higher] #[0]
  let indexed ← typeFor ``RawIndexed [``RawIndexed.leaf, ``RawIndexed.direct]
  checkFixture seeded #[indexed] #[1]
  checkFixture seeded #[indexed, natural] #[1, 0]
  let list ← typeFor ``List [``List.nil, ``List.cons]
  checkFixture seeded #[list] #[0] #[.fvar carrier] [.zero]
  let family ← typeFor ``RawFamily [``RawFamily.leaf, ``RawFamily.direct]
  checkFixture seeded #[family] #[1] #[.fvar carrier]
  checkAllocationOnlyControl seeded natural
  checkFailures seeded natural
  checkImplicitFixtures
  logInfo "recursor-type runtime: seven actual full mkRecInfos captures and nine selected-parent raw/stored type checks; sparse/reordered original IDs with changed dense physical indices; actual copied domains type-checked step-by-step and raw selected body/base/final/stored types checked; residual fields/IHs and other-parent indices/majors excluded; mutual/indexed/dependent and original-parameter native controls; invalid forward-order/omitted-major/duplicate-ID controls, one allocation-only untyped field and three failure controls; inferImplicit zero/limited/full counts, both range polarities and metadata/non-forall barriers"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "recursor-type unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "recursor-type audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "recursor-type new module-owned axiom {name}"
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
      throwError "recursor-type inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "recursor-type inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited recursor-type foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "recursor-type inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context recursor-type abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "recursor-type native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "recursor-type native interface provenance changed: {name}"
    logInfo m!"pinned existing native recursor-type interface: {name}"

#print axioms nativeSelectionIgnoresOnlyOriginalPhysicalIndices
#print axioms nestedActualRawGroupsEqualExactlyTheirSelectedConcatenation
#print axioms selectedProjectionDerivesItsWellFormednessFromOneInitialModel
#print axioms selectedProjectionKeepsOriginalDomainsNamesAndBinderInfosNotPhysicalIndices
#print axioms motiveAndMajorComponentsSupplyTheActualBodyApplicationNotWholeRawTyping
#print axioms rawTypeUsesOnlySelectedDomainAndBodyComponentSupport
#print axioms actualEndpointKeepsZeroParametersAndUsesRealCombinedSuffixLifting
#print axioms strictInferImplicitThousandKeepsTheSameSemanticAtBothRangePolicies
#print axioms storedMetadataTypeUsesTheSameSemanticAsTheActuallyProvedRawType
#print axioms actualFullGetterReturnsEachBoundedParentsReceiptAtItsActualSuccessCheckpoint
#print axioms actualScopedCpsKeepsRuleAndRegistrationSoundnessAsLaterObligations
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := logical ++ nativeInterfaces
  let inherited := native ++ [``sorryAx]
  for name in [``rawBodyUsesOnlyTheSelectedParentsMotiveIndicesAndMajor,
      ``exactMetadataTypeKeepsTheRealInferImplicitBoundary,
      ``fullReaderSemanticWeakeningCannotUseProjectionIdentity,
      ``captureFull, ``checkSameReader, ``project, ``checkScopeAndOrder, ``checkType,
      ``checkProjectionFailures, ``typeFor, ``statsFor, ``checkFixture,
      ``checkAllocationOnlyControl, ``checkFailures, ``binderInfos,
      ``checkImplicitFixtures, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``nativeSelectionIgnoresOnlyOriginalPhysicalIndices,
      ``nestedActualRawGroupsEqualExactlyTheirSelectedConcatenation] do
    auditDeclaration name native
  for name in [``strictInferImplicitZeroKeepsTheSameSemanticAtBothRangePolicies,
      ``strictInferImplicitOneKeepsTheSameSemanticAtBothRangePolicies,
      ``strictInferImplicitThousandKeepsTheSameSemanticAtBothRangePolicies,
      ``nonStrictInferImplicitKeepsTheSameSemanticForEveryCountAndRangePolicy] do
    auditDeclaration name (logical ++ [``sorryAx])
  for name in [``selectedProjectionDerivesItsWellFormednessFromOneInitialModel,
      ``selectedProjectionKeepsOriginalDomainsNamesAndBinderInfosNotPhysicalIndices,
      ``selectedProjectionDerivesDistinctnessInsteadOfAssumingAValidFinalContext,
      ``selectedProjectionExtendsByExactlyTheSelectedOriginalIdentifiers,
      ``motiveAndMajorComponentsSupplyTheActualBodyApplicationNotWholeRawTyping,
      ``abstractionReturnsToTheSameInitialSelectionBase,
      ``rawTypeUsesOnlySelectedDomainAndBodyComponentSupport,
      ``actualEndpointKeepsZeroParametersAndUsesRealCombinedSuffixLifting,
      ``storedMetadataTypeUsesTheSameSemanticAsTheActuallyProvedRawType,
      ``receiptRestrictsRawAndStoredFreeVariablesToTheSameInitialBase,
      ``receiptDerivesRawAndStoredClosureWithoutTheGlobalNativeRangeAxiom,
      ``receiptMatchesTheActualMetadataTypeAtBothModelsWithRealSuffixLifting,
      ``actualEndpointBuildsRawAndStoredReceiptsFromOnlyComponentSupports,
      ``actualFullGetterReturnsEachBoundedParentsReceiptAtItsActualSuccessCheckpoint,
      ``actualScopedCpsKeepsRuleAndRegistrationSoundnessAsLaterObligations] do
    auditDeclaration name inherited
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveRecursorTypeNative native
  auditModule `Lean4Lean.Verify.InductiveRecursorImplicitTranslation (logical ++ [``sorryAx])
  auditModule `Lean4Lean.Verify.InductiveRecursorTypeTranslation inherited
  auditModule `Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS inherited
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "recursor-type translation: 24 proof controls; selected actual domains derive the sparse/reordered projection from one initial model; component motive/indices/major support supplies body typing, exact nested raw abstraction and real full-suffix semantic lifting; raw/stored inferImplicit 1000 false types share semantics; bounded-parent full CPS receipts retain genuine zero-original-parameter restriction; rule/environment/registration soundness remains separate; clean core and inherited projection/typing admissions/eight native interfaces pinned; global native range axiom forbidden even if whitelisted"

end InductiveRecursorTypeTranslationTest
