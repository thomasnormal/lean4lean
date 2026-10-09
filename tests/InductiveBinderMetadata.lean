import Lean4Lean.Verify.InductiveBinderMetadata
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderMetadataTest

private def sortType : Expr := .sort (.succ .zero)

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr :=
  .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`BinderMetadataTag, .ofNat 47)] }

private theorem peelingPreservesConstructorBound {value : Expr} (fits : BVarRangeFits value) :
    BVarRangeFits (peelTypeAnnotations value) := fits.peelTypeAnnotations

private theorem substitutionPreservesBoundAtArbitraryOffset {value replacement : Expr} {offset : Nat}
    (fits : BVarRangeFits value) (replacementFits : BVarRangeFits replacement)
    (replacementClosed : replacement.Closed 0) : BVarRangeFits (value.instantiate1' replacement offset) :=
  fits.instantiate1_offset replacementFits replacementClosed

private theorem nativeOpeningPreservesConstructorBound {value : Expr} (id : FVarId)
    (fits : BVarRangeFits value) : BVarRangeFits (value.instantiate1 (.fvar id)) :=
  fits.instantiate1_native (by trivial) (by trivial)

private theorem unclosedReplacementLiftCanOverflow :
    BVarRangeFits (.forallE `inner sortType (.bvar 1) .default) ∧
      BVarRangeFits (.bvar 1048574) ∧ ¬ (Expr.bvar 1048574).Closed 0 ∧
      ¬ BVarRangeFits ((Expr.forallE `inner sortType (.bvar 1) .default).instantiate1' (.bvar 1048574)) := by
  simp [BVarRangeFits, Closed, sortType, Expr.instantiate1', Expr.liftLooseBVars']

private theorem constructorBoundDoesNotExcludeExpressionMeta (metavar : MVarId) :
    BVarRangeFits (.mvar metavar) ∧ ¬ (Expr.mvar metavar).Closed 0 := by
  simp [BVarRangeFits, Closed]

private theorem constructorBoundDoesNotExcludeLooseBVar :
    BVarRangeFits (.bvar 1048574) ∧ ¬ (Expr.bvar 1048574).Closed 0 := by
  simp [BVarRangeFits, Closed]

private theorem universeMetaHasBoundAndClosureButNotIntegrity (metavar : LMVarId) :
    BVarRangeFits (.sort (.mvar metavar)) ∧ (Expr.sort (.mvar metavar)).Closed 0 ∧
      ¬ (Expr.sort (.mvar metavar)).FVarsIn (fun _ => False) := by
  simp [BVarRangeFits, Closed, FVarsIn, Level.hasMVar']

private theorem discardedDefaultDoesNotReflectBoundOrClosure :
    BVarRangeFits (peelTypeAnnotations (binary ``optParam [] (.const ``Nat []) (.bvar 1048575))) ∧
      (peelTypeAnnotations (binary ``optParam [] (.const ``Nat []) (.bvar 1048575))).Closed 0 ∧
      ¬ BVarRangeFits (binary ``optParam [] (.const ``Nat []) (.bvar 1048575)) ∧
      ¬ (binary ``optParam [] (.const ``Nat []) (.bvar 1048575)).Closed 0 := by
  simp [peelTypeAnnotations, binary, BVarRangeFits, Closed]

private theorem metadataBarrierRetainsBadBoundAndClosure :
    ¬ BVarRangeFits (peelTypeAnnotations (.mdata tagged (unary ``outParam [] (.bvar 1048575)))) ∧
      ¬ (peelTypeAnnotations (.mdata tagged (unary ``outParam [] (.bvar 1048575)))).Closed 0 := by
  simp [peelTypeAnnotations, unary, BVarRangeFits, Closed]

private theorem wrongArityRetainsBadBoundAndClosure :
    ¬ BVarRangeFits (peelTypeAnnotations (binary ``outParam [] (.const ``Nat []) (.bvar 1048575))) ∧
      ¬ (peelTypeAnnotations (binary ``outParam [] (.const ``Nat []) (.bvar 1048575))).Closed 0 := by
  simp [peelTypeAnnotations, binary, BVarRangeFits, Closed]

private theorem fittingClosedExpressionMaterializesNativeFlags {value : Expr}
    (fits : BVarRangeFits value) (closed : value.Closed 0) :
    value.looseBVarRange = 0 ∧ value.hasExprMVar = false := fits.nativeBinderClosed closed

private theorem universeMetaCanBeNativeClosed (metavar : LMVarId) :
    NativeBinderClosed (.sort (.mvar metavar)) ∧
      ¬ (Expr.sort (.mvar metavar)).FVarsIn (fun _ => False) := by
  refine ⟨BVarRangeFits.nativeBinderClosed (by trivial) (by trivial), ?_⟩
  simp [FVarsIn, Level.hasMVar']

private theorem actualOpenedRawDomainsRetainBound {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (fits : BVarRangeFits type)
    (valuesClosed : BinderValuesClosed steps) (valuesFits : BinderValuesRangeFits steps) :
    BinderRawDomainRangeFits steps := opened.rawDomainRangeFits fits valuesClosed valuesFits

private theorem actualDeclaredIndexTypesRetainBound {ctx : Context} {steps : List BinderStep}
    (fits : BinderRawDomainRangeFits steps) (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeRangeFits ctx steps := fits.storedIndexTypeRangeFits declared

private theorem actualDeclaredIndexTypesMaterializeNativeFlags {ctx : Context} {steps : List BinderStep}
    (closed : BinderStoredIndexTypeClosed ctx steps) (fits : BinderStoredIndexTypeRangeFits ctx steps) :
    BinderStoredIndexTypeNativeClosed ctx steps := closed.nativeClosed fits

private theorem nativeLookupFlagsAreUsable {ctx : Context} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (native : BinderStoredIndexTypeNativeClosed ctx steps)
    (selected : steps[position]? = some step) (index : step.role = .index)
    (lookup : ctx.lctx.find? step.value.fvarId! = some decl) :
    decl.type.looseBVarRange = 0 ∧ decl.type.hasExprMVar = false :=
  native position step decl selected index lookup

private theorem nativeLookupHasNoLooseBVarFlag {ctx : Context} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (native : BinderStoredIndexTypeNativeClosed ctx steps)
    (selected : steps[position]? = some step) (index : step.role = .index)
    (lookup : ctx.lctx.find? step.value.fvarId! = some decl) : decl.type.hasLooseBVars = false := by
  rw [Expr.hasLooseBVars, (native position step decl selected index lookup).1]
  rfl

private theorem parentMetadataRetainsStoredLookupTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderMetadata stats types parent checked current info) :
    ParentBinderStoredLookupTypes stats types parent checked current info :=
  receipt.toBinderClosure.toBinderStoredLookupTypes

private theorem recursorMetadataRetainsClosure {stats : InductiveStats} {types : Array InductiveType}
    {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderMetadata stats types checked current infos) :
    RecursorBinderClosure stats types checked current infos := receipt.toBinderClosure

private theorem sameWitnessFitsAndNativeFlags {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderMetadata stats types parent checkedRoot current info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧ OpenedTelescope normalized generated generatedTerminal ∧
      BinderStepsIndexDeclared checkedRoot checked ∧ BinderStepsIndexDeclared current generated ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧ BinderIndexAllocations current generatedStart generated ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!) (info.indices.toList.map Expr.fvarId!) ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      BVarRangeFits normalized ∧ BinderRawDomainRangeFits checked ∧ BinderRawDomainRangeFits generated ∧
      BinderStoredIndexDomainRangeFits checked ∧ BinderStoredIndexDomainRangeFits generated ∧
      BinderStoredIndexTypeRangeFits checkedRoot checked ∧ BinderStoredIndexTypeRangeFits current generated ∧
      BVarRangeFits checkedTerminal ∧ BVarRangeFits generatedTerminal ∧
      NativeBinderClosed normalized ∧ BinderRawDomainNativeClosed checked ∧ BinderRawDomainNativeClosed generated ∧
      BinderStoredIndexDomainNativeClosed checked ∧ BinderStoredIndexDomainNativeClosed generated ∧
      BinderStoredIndexTypeNativeClosed checkedRoot checked ∧ BinderStoredIndexTypeNativeClosed current generated ∧
      NativeBinderClosed checkedTerminal ∧ NativeBinderClosed generatedTerminal := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, _, _, _, _, hcheckedDeclared,
    hgeneratedDeclared, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, hpairs, _, _, _, hlookup,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, hnormalizedFits, hcheckedFits, hgeneratedFits,
    hcheckedStoredFits, hgeneratedStoredFits, hcheckedTypeFits, hgeneratedTypeFits,
    hcheckedTerminalFits, hgeneratedTerminalFits, hnormalizedNative, hcheckedNative, hgeneratedNative,
    hcheckedStoredNative, hgeneratedStoredNative, hcheckedTypeNative, hgeneratedTypeNative,
    hcheckedTerminalNative, hgeneratedTerminalNative⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedDeclared, hgeneratedDeclared,
    hcheckedAlloc, hgeneratedAlloc, hpairs, hlookup, hnormalizedFits, hcheckedFits, hgeneratedFits,
    hcheckedStoredFits, hgeneratedStoredFits, hcheckedTypeFits, hgeneratedTypeFits,
    hcheckedTerminalFits, hgeneratedTerminalFits, hnormalizedNative, hcheckedNative, hgeneratedNative,
    hcheckedStoredNative, hgeneratedStoredNative, hcheckedTypeNative, hgeneratedTypeNative,
    hcheckedTerminalNative, hgeneratedTerminalNative⟩

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def dependent : Expr :=
  .forallE `carrier sortType
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0))
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1)))
          sortType .strictImplicit) .instImplicit) .default) .implicit

private theorem dependentFits : BVarRangeFits dependent := by
  simp [dependent, BVarRangeFits, sortType, unary, binary, equalityDomain, mkApp2, mkApp3]

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0)) .default
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))) .instImplicit
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1))) .strictImplicit
          (.sort (.succ .zero)))))

private def wrappedLet (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private def wrappedBeta (data : MData) : Expr :=
  .mdata data (.app (.lam `unused (.const ``Nat []) dependent .implicit) (.lit (.natVal 0)))

private theorem wrappedLetFits (data : MData) : BVarRangeFits (wrappedLet data) :=
  ⟨True.intro, True.intro, dependentFits⟩

private theorem wrappedBetaFits (data : MData) : BVarRangeFits (wrappedBeta data) :=
  ⟨⟨True.intro, dependentFits⟩, True.intro⟩

private theorem wrappedLetTrace (data : MData) : WrappedSortTelescope (wrappedLet data) dependent := by
  unfold wrappedLet
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private theorem wrappedBetaTrace (data : MData) : WrappedSortTelescope (wrappedBeta data) dependent := by
  unfold wrappedBeta
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `BinderMetadataProvedLet (wrappedLet data), header `BinderMetadataProvedBeta (wrappedBeta data)]

private theorem provedSourceFits (data : MData) : HeaderSourceBVarRangeFits (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact wrappedLetFits data
  · exact wrappedBetaFits data

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem provedSafeWrappedMetadata (data : MData) (ctx : Context)
    (hwf : ctx.lctx.WF) (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderMetadata result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderMetadata 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf reserved (provedSourceFits data)

private theorem wrappedCheckedSourcesCarryMetadata {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checked recursorRoot current : Context}
    {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (wrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) (fits : HeaderSourceBVarRangeFits types) :
    RecursorBinderMetadata stats types checked current infos :=
  headers.wrappedBinderMetadata sources wrapped support hwf fits

private theorem normalizedMetadataRetainsExplicitFitsAndClosure {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {original checked recursorRoot current : Context}
    {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (normalized : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!))
    (closed : NormalizedHeaderClosed types) (fits : NormalizedHeaderRangeFits types) :
    RecursorBinderMetadata stats types checked current infos :=
  headers.normalizedBinderMetadata sources normalized support hwf within closed fits

private theorem wrappedGetterCarriesMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (original checked ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderMetadata stats types checked result.2 result.1 :=
  mkRecInfos.getWrappedBinderMetadata nparams stats types elimLevel original checked ctx
    headers wrapped hwf reserved support fits

private theorem wrappedCPSCarriesMetadata (ResultType : Type) (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (next : Array RecInfo → M ResultType)
    (original checked ctx : Context) (post : ResultType → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderMetadata stats types checked current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedWrappedBinderMetadata nparams stats types elimLevel next original checked ctx post
    headers wrapped hwf reserved support fits hnext

private theorem wrappedRegistrationCarriesFlagsAndMetadata (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checked ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderMetadata stats types checked result.2.2 result.2.1 :=
  mkRecInfos.registeredWrappedBinderMetadata nparams stats types elimLevel lparams isK isUnsafe original checked
    ctx headers wrapped hwf reserved henv support fits

private def boundsHold : Expr → Bool
  | .bvar index => index + 1 ≤ 2^20 - 1
  | .app function argument => boundsHold function && boundsHold argument
  | .lam _ domain body _ | .forallE _ domain body _ => boundsHold domain && boundsHold body
  | .letE _ domain value body _ => boundsHold domain && boundsHold value && boundsHold body
  | .mdata _ value | .proj _ _ value => boundsHold value
  | _ => true

private def checkNativeClosed (value : Expr) : MetaM Unit := do
  unless boundsHold value && value.looseBVarRange == value.looseBVarRange' &&
      value.looseBVarRange == 0 && !value.hasExprMVar do
    throwError "binder-metadata constructor bound/native zero range/expr-meta freedom failed"

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let generatorRoot ← readThe Context
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          generatorRoot.lparams false false
        return (stats, checked, generatorRoot, result)

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some declaration := ctx.lctx.getAt? (start + offset)
      | throwError "binder-metadata actual index points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkDeclaration (ctx : Context) (value : Expr) (domain : Expr)
    (position : Nat) : MetaM Unit := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "binder-metadata actual index lookup is missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations domain &&
      declaration.index == position do
    throwError "binder-metadata actual index stored-type/value/native-position anchor changed"
  checkNativeClosed declaration.type

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    checkNativeClosed left
    checkNativeClosed right
    let .forallE _ leftRaw leftBody _ := left
      | throwError "binder-metadata checked opening ended before actual values"
    let .forallE _ rightRaw rightBody _ := right
      | throwError "binder-metadata generated opening ended before actual values"
    checkNativeClosed leftRaw
    checkNativeClosed rightRaw
    checkNativeClosed (peelTypeAnnotations leftRaw)
    checkNativeClosed (peelTypeAnnotations rightRaw)
    if position ≥ nparams then
      checkDeclaration checkedCtx leftValues[position]! leftRaw (checkedStart + position - nparams)
      checkDeclaration generatedCtx rightValues[position]! rightRaw (generatedStart + position - nparams)
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  checkNativeClosed left
  checkNativeClosed right
  unless left == sortType && right == sortType do
    throwError "binder-metadata actual checked/generated terminal changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  for type in types do
    checkNativeClosed type.type
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "binder-metadata actual safe/header/recursor registration failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-metadata actual count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "binder-metadata actual checked source normalization failed"
    checkNativeClosed normalized
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-metadata registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-metadata registered recursor parameters/indices changed"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderMetadataSort sortType] #[0]
  for nparams in [0, 1, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderMetadataDependent nparams) dependent] #[4 - nparams]
    checkFixture ctx nparams #[header (Name.mkNum `BinderMetadataMutualFirst nparams) dependent,
      header (Name.mkNum `BinderMetadataMutualSecond nparams) dependent] #[4 - nparams, 4 - nparams]
  checkFixture ctx 1 #[header `BinderMetadataLet (wrappedLet tagged),
    header `BinderMetadataBeta (wrappedBeta tagged)] #[3, 3]
  let nat := Expr.const ``Nat []
  checkFixture ctx 0 #[
    header `BinderMetadataOut (.forallE `index (unary ``outParam [.succ .zero] nat) sortType .default),
    header `BinderMetadataAuto (.forallE `index
      (binary ``autoParam [.succ .zero] nat (.const ``Lean.Syntax.missing [])) sortType .default),
    header `BinderMetadataAnnotationBarrier (.forallE `index (.mdata tagged
      (unary ``outParam [.succ .zero] nat)) sortType .default)] #[1, 1, 1]

private def nativeBoundaryControls : MetaM Unit := do
  let largest := Expr.bvar 1048574
  unless boundsHold largest && largest.looseBVarRange == 1048575 && !largest.hasExprMVar &&
      largest.hasLooseBVars do
    throwError "binder-metadata fitting loose BVar boundary changed"
  let expressionMeta := Expr.mvar ⟨`BinderMetadataExprMeta⟩
  unless boundsHold expressionMeta && expressionMeta.looseBVarRange == 0 && expressionMeta.hasExprMVar do
    throwError "binder-metadata fitting expression meta no longer separates zero range from closure"
  let universeMeta := Expr.sort (.mvar ⟨`BinderMetadataLevelMeta⟩)
  unless boundsHold universeMeta && universeMeta.looseBVarRange == 0 && !universeMeta.hasExprMVar &&
      universeMeta.hasLevelMVar do
    throwError "binder-metadata native closure incorrectly excludes universe metas"
  logInfo "three native controls distinguish fitting loose BVars, zero-range expr metas and native-closed universe metas"

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless axiomName != ``Expr.looseBVarRange_eq && axiomName != ``sorryAx && allowed.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

private def auditModules (modules : List Name) (allowed : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut totalDeclarations := 0
  let mut totalTheorems := 0
  for moduleName in modules do
    let some moduleIndex := env.getModuleIdx? moduleName
      | throwError "binder-metadata audited module absent: {moduleName}"
    let mut declarations := 0
    let mut theorems := 0
    for (name, info) in env.constants do
      if env.getModuleIdxFor? name == some moduleIndex then
        declarations := declarations + 1
        if info matches .thmInfo _ then
          theorems := theorems + 1
        audit name allowed
    totalDeclarations := totalDeclarations + declarations
    totalTheorems := totalTheorems + theorems
    logInfo m!"{moduleName}: declarations = {declarations}; theorems = {theorems}"
  logInfo m!"binder-metadata module census incl private: declarations = {totalDeclarations}; theorems = {totalTheorems}"

private def auditNativeProvenance (nativeInterfaces nativeBitAxioms : List Name) : MetaM Unit := do
  let env ← getEnv
  for (moduleName, names) in [(`Lean4Lean.Verify.Axioms, nativeInterfaces),
      (`Lean4Lean.Verify.Expr, nativeBitAxioms)] do
    let some expectedModule := env.getModuleIdx? moduleName
      | throwError "binder-metadata native-axiom provenance module absent: {moduleName}"
    for name in names do
      let some (.axiomInfo _) := env.find? name
        | throwError "binder-metadata native provenance name is not an existing axiom: {name}"
      unless env.getModuleIdxFor? name == some expectedModule do
        throwError "binder-metadata native axiom originates outside its pinned existing module: {name}"
      logInfo m!"native provenance: {name} from {moduleName}"

#print axioms BVarRangeFits.peelTypeAnnotations
#print axioms BVarRangeFits.instantiate1_offset
#print axioms BVarRangeFits.instantiate1_native
#print axioms BVarRangeFits.nativeBinderClosed
#print axioms ParentBinderClosure.metadata
#print axioms checkInductiveTypes.safeRegisteredWrappedBinderMetadata

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.mkData_eq, ``Expr.mkAppData_eq]
  let nativeBitAxioms := [
    `Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9,
    `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7,
    `Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8]
  let native := nativeInterfaces ++ nativeBitAxioms
  auditNativeProvenance nativeInterfaces nativeBitAxioms
  let binding := [``Expr.instantiate1_eq, ``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  let expressions := [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``PersistentHashMap.findAux_isSome]
  for theoremName in [``peelingPreservesConstructorBound, ``substitutionPreservesBoundAtArbitraryOffset,
      ``unclosedReplacementLiftCanOverflow, ``constructorBoundDoesNotExcludeExpressionMeta,
      ``constructorBoundDoesNotExcludeLooseBVar, ``universeMetaHasBoundAndClosureButNotIntegrity,
      ``discardedDefaultDoesNotReflectBoundOrClosure, ``metadataBarrierRetainsBadBoundAndClosure,
      ``wrongArityRetainsBadBoundAndClosure, ``dependentFits, ``dependentShape, ``wrappedLetFits,
      ``wrappedBetaFits, ``provedSourceFits, ``actualDeclaredIndexTypesRetainBound,
      ``nativeLookupFlagsAreUsable, ``nativeLookupHasNoLooseBVarFlag,
      ``parentMetadataRetainsStoredLookupTypes, ``recursorMetadataRetainsClosure,
      ``sameWitnessFitsAndNativeFlags] do
    audit theoremName logical
  for theoremName in [``nativeOpeningPreservesConstructorBound, ``wrappedLetTrace, ``wrappedBetaTrace,
      ``provedHeaders, ``actualOpenedRawDomainsRetainBound] do
    audit theoremName (logical ++ binding)
  for theoremName in [``fittingClosedExpressionMaterializesNativeFlags, ``universeMetaCanBeNativeClosed,
      ``actualDeclaredIndexTypesMaterializeNativeFlags] do
    audit theoremName (logical ++ native ++ [``Expr.hasExprMVar_eq])
  for theoremName in [``provedSafeWrappedMetadata, ``wrappedCheckedSourcesCarryMetadata,
      ``normalizedMetadataRetainsExplicitFitsAndClosure, ``wrappedGetterCarriesMetadata,
      ``wrappedCPSCarriesMetadata, ``wrappedRegistrationCarriesFlagsAndMetadata] do
    audit theoremName (logical ++ native ++ binding ++ expressions ++ scope)
  auditModules [`Lean4Lean.Verify.InductiveAnnotationModelRangeFits,
    `Lean4Lean.Verify.InductiveBinderRangeFits, `Lean4Lean.Verify.InductiveBinderMetadata]
    (logical ++ native ++ binding ++ expressions ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderMetadataSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderMetadataSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderMetadataSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderMetadataSeed, idx := 71 } }] do
    fixtures reader
  nativeBoundaryControls
  logInfo "27 full registrations / 45 parent pairs / 141 paired raw domains / 90 paired index declarations / three readers preserve numeric bounds, native zero ranges and native expr-meta-free flags"

end InductiveBinderMetadataTest
