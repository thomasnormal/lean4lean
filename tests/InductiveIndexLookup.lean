import Lean4Lean.Verify.InductiveBinderSupportAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexLookupTest

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`IndexLookupTag, .ofNat 1)] }

private def dependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
      (.forallE `again
        (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
        sortType .default) .instImplicit) .strictImplicit) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) .instImplicit
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          .default (.sort (.succ .zero)))))

private def wrapped (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private theorem wrappedTrace (data : MData) : WrappedSortTelescope (wrapped data) dependent := by
  unfold wrapped
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `LookupWrapped (wrapped data), header `LookupAnnotated (.mdata data dependent)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedTrace data⟩
  · exact ⟨dependent, .mdata data (.telescope dependentShape)⟩

private theorem provedRegisteredSupport (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderSupportAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderSupport 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private theorem emptySupport (params : List FVarId) : IndexParameterSupport [] params := by
  simp [IndexParameterSupport]

private theorem emptyLookup (id : FVarId) : indexLookup [] id = id := rfl

private theorem listedLookup {pairs : List (FVarId × FVarId)} {source target : FVarId}
    (injection : IndexPairInjection pairs) (listed : (source, target) ∈ pairs) :
    indexLookup pairs source = target := indexLookup_of_mem injection listed

private theorem outsideLookup {pairs : List (FVarId × FVarId)} {id : FVarId}
    (outside : id ∉ pairs.map Prod.fst) : indexLookup pairs id = id :=
  indexLookup_eq_self_of_not_mem outside

private theorem fixedSupport {pairs : List (FVarId × FVarId)} {params : List FVarId}
    (support : IndexParameterSupport pairs params) {param : FVarId} (shared : param ∈ params) :
    indexLookup pairs param = param := indexLookup_fixedParameters support shared

private theorem singletonInjection (source target : FVarId) : IndexPairInjection [(source, target)] := by
  simp [IndexPairInjection]

private theorem singletonLookup (source target : FVarId) : indexLookup [(source, target)] source = target :=
  indexLookup_of_mem (singletonInjection source target) (by simp)

private theorem overlappingInjection (first second : FVarId) (different : first ≠ second) :
    IndexPairInjection [(first, second), (second, first)] := by
  simp [IndexPairInjection, different, Ne.symm different]

private theorem overlappingLookup (first second : FVarId) (different : first ≠ second) :
    indexLookup [(first, second), (second, first)] first = second ∧
      indexLookup [(first, second), (second, first)] second = first :=
  ⟨indexLookup_of_mem (overlappingInjection first second different) (by simp),
    indexLookup_of_mem (overlappingInjection first second different) (by simp)⟩

private theorem oldRelationStillAmbiguous (first second : FVarId) (different : first ≠ second) :
    IndexRenaming [(first, second)] (.fvar first) (.fvar first) ∧
      IndexRenaming [(first, second)] (.fvar first) (.fvar second) ∧ Expr.fvar first ≠ .fvar second :=
  ⟨IndexRenaming.refl _ _, .fvar (.inr (by simp)), fun equal => different (Expr.fvar.inj equal)⟩

private theorem listedIdentityRejected (first second : FVarId) (different : first ≠ second) :
    ¬ IndexLookupRenaming [(first, second)] (.fvar first) (.fvar first) := by
  intro related
  have mapped : IndexLookupRenaming [(first, second)] (.fvar first) (.fvar second) :=
    .fvar_of_mem (singletonInjection first second) (by simp)
  exact different (Expr.fvar.inj (related.functional mapped))

private theorem lookupFunctional {pairs : List (FVarId × FVarId)} {source first second : Expr}
    (firstImage : IndexLookupRenaming pairs source first) (secondImage : IndexLookupRenaming pairs source second) :
    first = second := firstImage.functional secondImage

private theorem lookupRetainsRelation {pairs : List (FVarId × FVarId)} {source target : Expr}
    (lookedUp : IndexLookupRenaming pairs source target) : IndexRenaming pairs source target := lookedUp.related

private theorem fixedParameterExpression {pairs : List (FVarId × FVarId)} {params : List FVarId}
    (support : IndexParameterSupport pairs params) {param : FVarId} (shared : param ∈ params) :
    IndexLookupRenaming pairs (.fvar param) (.fvar param) := .fixedParameter support shared

private theorem duplicateFirstMatch (source first second : FVarId) :
    indexLookup [(source, first), (source, second)] source = first := by
  simp [indexLookup]

private theorem duplicateReversedFirstMatch (source first second : FVarId) :
    indexLookup ([(source, first), (source, second)] : List (FVarId × FVarId)).reverse source = second := by
  simp [indexLookup]

private theorem duplicateNeedsNoInjection (source first second : FVarId) :
    ¬ IndexPairInjection [(source, first), (source, second)] := by
  simp [IndexPairInjection]

private theorem duplicateListingNeedsInjection (source first second : FVarId) (different : first ≠ second) :
    (source, second) ∈ ([(source, first), (source, second)] : List (FVarId × FVarId)) ∧
      indexLookup [(source, first), (source, second)] source ≠ second := by
  exact ⟨by simp, by rw [duplicateFirstMatch]; exact different⟩

private theorem parameterDomainCollision (param target : FVarId) :
    ¬ IndexParameterSupport [(param, target)] [param] := by
  intro support
  exact (support param (by simp)) (by simp)

private theorem fixedDoesNotImplySupport (param : FVarId) :
    indexLookup [(param, param)] param = param ∧ ¬ IndexParameterSupport [(param, param)] [param] :=
  ⟨singletonLookup param param, parameterDomainCollision param param⟩

private theorem targetParameterMayBeFixed (source target : FVarId) (different : source ≠ target) :
    IndexParameterSupport [(source, target)] [target] ∧
      indexLookup [(source, target)] target = target ∧
      target ∈ ([(source, target)] : List (FVarId × FVarId)).map Prod.snd := by
  have support : IndexParameterSupport [(source, target)] [target] := by
    simp [IndexParameterSupport, Ne.symm different]
  exact ⟨support, indexLookup_fixedParameters support (by simp), by simp⟩

private theorem unsupportedParameterMoves (param target : FVarId) (different : param ≠ target) :
    indexLookup [(param, target)] param ≠ param := by
  rw [singletonLookup]
  exact Ne.symm different

private theorem finiteLookupNotGloballyInjective (source target : FVarId) (different : source ≠ target) :
    source ≠ target ∧ indexLookup [(source, target)] source = indexLookup [(source, target)] target := by
  refine ⟨different, ?_⟩
  rw [singletonLookup, indexLookup_eq_self_of_not_mem]
  simpa using Ne.symm different

private def allConstructors (source param : FVarId) : Expr :=
  .app
    (.lam `local (.sort (.succ (.param `u)))
      (.forallE `index (.fvar param)
        (.letE `hidden (.const `LookupConstant [.param `u]) (.fvar source)
          (.mdata tagged (.proj `LookupStructure 2 (.app (.bvar 0) (.mvar ⟨`LookupMeta⟩)))) false)
        .strictImplicit) .instImplicit)
    (.app (.fvar source) (.lit (.natVal 7)))

private theorem constructorLookup (source target param : FVarId) (different : param ≠ source) :
    indexRenameExpr [(source, target)] (allConstructors source param) = allConstructors target param := by
  have outside : param ∉ ([(source, target)] : List (FVarId × FVarId)).map Prod.fst := by
    simpa using different
  simp [allConstructors, indexRenameExpr, singletonLookup, indexLookup_eq_self_of_not_mem outside]

private theorem constructorLookupRelated (source target param : FVarId) (different : param ≠ source) :
    IndexRenaming [(source, target)] (allConstructors source param) (allConstructors target param) :=
  (show IndexLookupRenaming [(source, target)] (allConstructors source param) (allConstructors target param)
    from constructorLookup source target param different).related

private def mixedSteps (param index : FVarId) : List BinderStep := [
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar param },
  { role := .index, name := `element, domain := .fvar param, bi := .default, value := .fvar index }]

private theorem emptyBinderSupport : BinderParameterIndexDisjoint [] := by
  simp [BinderParameterIndexDisjoint, BinderStep.parameterValues, BinderStep.indexValues]

private theorem distinctBinderSupport (param index : FVarId) (different : param ≠ index) :
    BinderParameterIndexDisjoint (mixedSteps param index) := by
  simp [BinderParameterIndexDisjoint, mixedSteps, BinderStep.parameterValues, BinderStep.indexValues,
    Expr.fvarId!, Ne.symm different]

private theorem sharedIndexRejected (id : FVarId) : ¬ BinderParameterIndexDisjoint (mixedSteps id id) := by
  simp [BinderParameterIndexDisjoint, mixedSteps, BinderStep.parameterValues, BinderStep.indexValues,
    Expr.fvarId!]

private theorem actualSupportFromPositions {ctx : Context} {start : Nat} {steps : List BinderStep}
    (allocated : BinderIndexAllocations ctx start steps)
    (parameters : BinderValuesBefore ctx start (BinderStep.parameterValues steps)) :
    BinderParameterIndexDisjoint steps := allocated.parameterDisjoint parameters

private theorem supportedSourceRetainsSource {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current) :
    CheckedHeaderSource nparams types parent original params count current := source.toSource

private theorem supportedSourcesRetainSources {nparams : Nat} {types : Array InductiveType}
    {original current : Context} {stats : InductiveStats}
    (sources : CheckedHeaderSupportSources nparams types original stats current) :
    CheckedHeaderSources nparams types original stats current := sources.toSources

private theorem parentRetainsAllocations {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked generated : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checked generated info) :
    ParentBinderAllocationAlignment stats types parent checked generated info := alignment.toBinderAllocations

private theorem recursorsRetainAllocations {stats : InductiveStats} {types : Array InductiveType}
    {checked generated : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderSupportAlignment stats types checked generated infos) :
    RecursorBinderAllocationAlignment stats types checked generated infos := alignment.toBinderAllocations

private theorem parentSameWitnessSupport {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot generatedRoot : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checkedRoot generatedRoot info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧
      OpenedTelescope normalized generated generatedTerminal ∧
      BinderStep.parameterValues checked = stats.params.toList ∧
      BinderStep.parameterValues generated = stats.params.toList ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧
      BinderIndexAllocations generatedRoot generatedStart generated ∧
      BinderParameterIndexDisjoint checked ∧ BinderParameterIndexDisjoint generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, hcheckedParams, hgeneratedParams,
    _, _, _, _, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, _, _, hcheckedSupport,
    hgeneratedSupport⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, hnormalized, hchecked, hgenerated, hcheckedParams, hgeneratedParams,
    hcheckedAlloc, hgeneratedAlloc, hcheckedSupport, hgeneratedSupport⟩

private theorem fullActualLookup {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked generated : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checked generated info) :
    ∃ checkedIds pairs,
      checkedIds.length = stats.nindices[parent]! ∧
      pairs = checkedIds.zip (info.indices.toList.map Expr.fvarId!) ∧
      pairs.map Prod.fst = checkedIds ∧ pairs.map Prod.snd = info.indices.toList.map Expr.fvarId! ∧
      IndexPairInjection pairs ∧ IndexParameterSupport pairs (stats.params.toList.map Expr.fvarId!) ∧
      (∀ id ∈ stats.params.toList.map Expr.fvarId!, id ∉ pairs.map Prod.snd) ∧
      (∀ id image, (id, image) ∈ pairs → indexLookup pairs id = image) ∧
      (∀ id ∈ stats.params.toList.map Expr.fvarId!, indexLookup pairs id = id) := alignment.injectiveIndexLookup

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

private def sameDecl (left right : LocalDecl) : Bool :=
  match left, right with
  | .cdecl leftIndex leftId leftName leftType leftBi leftKind,
      .cdecl rightIndex rightId rightName rightType rightBi rightKind =>
    leftIndex == rightIndex && leftId == rightId && leftName == rightName && leftType == rightType &&
      leftBi == rightBi && decide (leftKind = rightKind)
  | .ldecl leftIndex leftId leftName leftType leftValue leftNondep leftKind,
      .ldecl rightIndex rightId rightName rightType rightValue rightNondep rightKind =>
    leftIndex == rightIndex && leftId == rightId && leftName == rightName && leftType == rightType &&
      leftValue == rightValue && leftNondep == rightNondep && decide (leftKind = rightKind)
  | _, _ => false

private def foundDecl (found : Option LocalDecl) (expected : LocalDecl) : Bool :=
  match found with
  | some actual => sameDecl actual expected
  | none => false

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some decl := ctx.lctx.getAt? (start + offset)
      | throwError "index-lookup checked source allocation points at a hole"
    unless foundDecl (ctx.lctx.find? decl.fvarId) decl && decl.index == start + offset do
      throwError "index-lookup actual source find?/getAt? receipts disagree"
    values := values.push decl.toExpr
  return values

private def injectiveZip (pairs : List (FVarId × FVarId)) : Bool :=
  let sources := pairs.map Prod.fst
  let targets := pairs.map Prod.snd
  sources.eraseDups.length == sources.length && targets.eraseDups.length == targets.length

private def parameterSupport (pairs : List (FVarId × FVarId)) (params : Array Expr) : Bool :=
  params.all fun param => !(pairs.any (·.1 == param.fvarId!))

private def checkParameters (checked generated : Context) (params : Array Expr)
    (pairs : List (FVarId × FVarId)) : MetaM Unit := do
  unless parameterSupport pairs params && parameterSupport (pairs.map Prod.swap) params do
    throwError "index-lookup actual parameter IDs overlap an index allocation"
  for param in params do
    let some checkedDecl := checked.lctx.find? param.fvarId!
      | throwError "index-lookup checked shared parameter disappeared"
    let some generatedDecl := generated.lctx.find? param.fvarId!
      | throwError "index-lookup generated shared parameter disappeared"
    unless param.isFVar && sameDecl checkedDecl generatedDecl && indexLookup pairs param.fvarId! == param.fvarId! do
      throwError "index-lookup failed to preserve actual shared parameters"

private def checkParent (original checked generatorRoot generated : Context) (stats : InductiveStats)
    (parent : Nat) (info : RecInfo) : MetaM Unit := do
  let preceding := (stats.nindices.toList.take parent).sum
  let checkedStart := original.lctx.numIndices + stats.params.size + preceding
  let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
  let checkedValues ← valuesAt checked checkedStart stats.nindices[parent]!
  let generatedValues ← valuesAt generated generatedStart info.indices.size
  let pairs := checkedValues.toList.map Expr.fvarId! |>.zip (info.indices.toList.map Expr.fvarId!)
  unless generatedValues == info.indices && checkedValues.size == info.indices.size &&
      pairs.length == info.indices.size && injectiveZip pairs do
    throwError "index-lookup actual finite pair list lost exact injective source/target projections"
  for pair in pairs do
    unless indexLookup pairs pair.1 == pair.2 do
      throwError "index-lookup disagrees with an actual listed allocation pair"
  checkParameters checked generated stats.params pairs

private def checkPreserved (original checked generated : Context) : MetaM Unit := do
  for declaration in original.lctx.decls.toList.filterMap id do
    unless foundDecl (checked.lctx.find? declaration.fvarId) declaration &&
        foundDecl (generated.lctx.find? declaration.fvarId) declaration do
      throwError "index-lookup actual registration changed an old declaration"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "index-lookup successful registration fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size &&
      checked.lctx.numIndices == ctx.lctx.numIndices + nparams + expected.toList.sum &&
      generated.lctx.numIndices == generatorRoot.lctx.numIndices + expected.toList.sum + 2 * types.size do
    throwError "index-lookup actual registration allocation arithmetic changed"
  checkPreserved ctx checked generated
  for parent in [:types.size] do
    checkParent ctx checked generatorRoot generated stats parent infos[parent]!
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "index-lookup successful fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "index-lookup actual registered metadata changed"

private def multipleParams : Expr := .forallE `carrier sortType
  (.forallE `pivot (.bvar 0)
    (.forallE `element (.bvar 1)
      (.forallE `witness (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1))
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 3) (.bvar 1) (.bvar 2)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .default) .implicit

private def family (names : Name) (marked : Bool) : Expr :=
  let elementDomain := if marked then Expr.mdata tagged (.bvar 0) else .bvar 0
  .forallE (names ++ `carrier) sortType
    (.forallE (names ++ `element) elementDomain
      (.forallE (names ++ `witness) (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.forallE (names ++ `again)
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .implicit

private def natIndices : Expr := .forallE `first (.const ``Nat [])
  (.forallE `second (.const ``Nat []) sortType .default) .default

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `LookupEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `LookupDependent nparams) dependent] #[4 - nparams]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `LookupMultiple nparams) multipleParams] #[5 - nparams]
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `LookupMutualFirst nparams) (family `first false),
      header (Name.mkNum `LookupMutualSecond nparams) (family `second true)] #[4 - nparams, 4 - nparams]
  checkFixture ctx 0 #[header `LookupIndependentNat natIndices] #[2]
  checkFixture ctx 0 #[header `LookupEmptyLeading sortType, header `LookupDependentFollowing dependent] #[0, 4]
  checkFixture ctx 4 #[header `LookupAllParametersFirst dependent,
    header `LookupAllParametersSecond (family `shared false)] #[0, 0]
  checkFixture ctx 1 #[header `LookupWrappedDependent (wrapped tagged)] #[3]
  checkFixture ctx 1 #[header `LookupMetadata (family `marked true)] #[3]

private def lookupControls : MetaM Unit := do
  let first : FVarId := ⟨`LookupFirst⟩
  let second : FVarId := ⟨`LookupSecond⟩
  let third : FVarId := ⟨`LookupThird⟩
  let unknown : FVarId := ⟨`LookupUnknown⟩
  let overlapping := [(first, second), (second, first)]
  unless injectiveZip overlapping && indexLookup overlapping first == second &&
      indexLookup overlapping second == first && indexLookup overlapping unknown == unknown do
    throwError "index-lookup overlap control lost deterministic listed-pair priority"
  unless indexLookup [(first, first)] first == first && indexLookup [] unknown == unknown do
    throwError "index-lookup identity/empty controls failed"
  unless !(parameterSupport [(first, first)] #[.fvar first]) && indexLookup [(first, first)] first == first do
    throwError "index-lookup parameter support was incorrectly required for an identity mapping"
  let duplicate := [(first, second), (first, third)]
  unless !(injectiveZip duplicate) && indexLookup duplicate first == second &&
      indexLookup duplicate.reverse first == third do
    throwError "index-lookup generic duplicate-list control lost first-match behavior"
  let collision := [(first, second)]
  unless !(parameterSupport collision #[.fvar first]) && indexLookup collision first != first &&
      parameterSupport collision #[.fvar third] && indexLookup collision third == third do
    throwError "index-lookup fixed-parameter support boundary disappeared"
  unless parameterSupport collision #[.fvar second] && indexLookup collision second == second do
    throwError "index-lookup generic fixed-parameter lookup incorrectly required target-side disjointness"
  unless indexRenameExpr collision (allConstructors first third) == allConstructors second third do
    throwError "index-lookup expression traversal lost a constructor, wrapper, binder, or fixed parameter"
  unless indexLookup collision first == indexLookup collision second && first != second do
    throwError "index-lookup global noninjectivity control disappeared"

private def differentReaderBoundary (ctx : Context) : MetaM Unit := do
  let types := #[header `LookupDifferentReaders natIndices]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 0 types ctx
    | throwError "index-lookup different-reader setup failed"
  let other := { generatorRoot with lparams := [`DifferentLookupReader] }
  let .ok first := mkRecInfos stats types (.succ .zero) pure generatorRoot
    | throwError "index-lookup first independent helper failed"
  let .ok second := mkRecInfos stats types (.succ .zero) pure other
    | throwError "index-lookup second independent helper failed"
  let pairs := first[0]!.indices.toList.map Expr.fvarId! |>.zip (second[0]!.indices.toList.map Expr.fvarId!)
  unless generatorRoot.lparams != other.lparams && pairs.length == 2 && injectiveZip pairs &&
      pairs.all (fun pair => pair.1 == pair.2 && indexLookup pairs pair.1 == pair.2) do
    throwError "index-lookup distinct readers were incorrectly required to have disjoint IDs"

private def uncheckedSourceSupportBoundary (ctx : Context) : MetaM Unit := do
  let type := Expr.forallE `carrier sortType
    (.forallE `index (.const ``Nat []) sortType .default) .implicit
  let types := #[header `LookupUncheckedSupport type]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "index-lookup unchecked source-support setup failed"
  let collision : FVarId := ⟨generatorRoot.ngen.curr⟩
  let changed := { stats with params := #[.fvar collision] }
  unless (generatorRoot.lctx.find? collision).isNone do
    throwError "index-lookup unchecked source-support parameter was already declared"
  let .ok (infos, generated) := mkRecInfos changed types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) generatorRoot
    | throwError "index-lookup bare helper unexpectedly requires the parameter-before-allocation receipt"
  let actual := infos[0]!.indices.toList.map Expr.fvarId!
  let pairs := actual.zip actual
  unless actual == [collision] && (generated.lctx.find? collision).isSome && injectiveZip pairs &&
      !(parameterSupport pairs changed.params) && indexLookup pairs collision == collision do
    throwError "index-lookup unchecked successful helper incorrectly acquired actual parameter/index separation"
  logInfo "one unchecked helper accepts a future-ID parameter that aliases its allocated index; successful execution alone does not discharge parameter support"

private def holeBoundaries (ctx : Context) : MetaM Unit := do
  for erased in [ctx.lctx.erase ⟨.num `IndexLookupSeed 41⟩,
      (ctx.lctx.erase ⟨.num `IndexLookupSeed 40⟩).erase ⟨.num `IndexLookupSeed 41⟩] do
    let reader := { ctx with lctx := erased }
    unless reader.lctx.numIndices == 3 && (reader.lctx.decls.toList.filterMap id).length < 3 do
      throwError "index-lookup unchecked hole-reader setup failed"
    checkFixture reader 1 #[header `LookupUncheckedHole dependent] #[3]
    checkFixture reader 1 #[header `LookupUncheckedHoleFirst (family `first false),
      header `LookupUncheckedHoleSecond (family `second true)] #[3, 3]
  logInfo "four unchecked erased-slot registrations preserve actual parameter/index separation; these readers have no LocalContext.WF receipt"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let normalized := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  audit ``dependentShape
  audit ``wrappedTrace binding
  audit ``provedHeaders binding
  audit ``provedRegisteredSupport (normalized ++ scope)
  audit ``emptySupport
  audit ``emptyLookup
  audit ``listedLookup
  audit ``outsideLookup
  audit ``fixedSupport
  audit ``singletonInjection
  audit ``singletonLookup
  audit ``overlappingInjection
  audit ``overlappingLookup
  audit ``oldRelationStillAmbiguous
  audit ``listedIdentityRejected
  audit ``lookupFunctional
  audit ``lookupRetainsRelation
  audit ``fixedParameterExpression
  audit ``duplicateFirstMatch
  audit ``duplicateReversedFirstMatch
  audit ``duplicateNeedsNoInjection
  audit ``duplicateListingNeedsInjection
  audit ``parameterDomainCollision
  audit ``fixedDoesNotImplySupport
  audit ``targetParameterMayBeFixed
  audit ``unsupportedParameterMoves
  audit ``finiteLookupNotGloballyInjective
  audit ``constructorLookup
  audit ``constructorLookupRelated
  audit ``emptyBinderSupport
  audit ``distinctBinderSupport
  audit ``sharedIndexRejected
  audit ``actualSupportFromPositions
  audit ``supportedSourceRetainsSource
  audit ``supportedSourcesRetainSources
  audit ``parentRetainsAllocations
  audit ``recursorsRetainAllocations
  audit ``parentSameWitnessSupport
  audit ``fullActualLookup
  audit ``indexLookup_of_mem
  audit ``indexLookup_eq_self_of_not_mem
  audit ``indexLookup_fixedParameters
  audit ``indexLookup_mem_or_eq
  audit ``indexRenameExpr_related
  audit ``IndexLookupRenaming.functional
  audit ``IndexLookupRenaming.related
  audit ``IndexLookupRenaming.fvar_of_mem
  audit ``IndexLookupRenaming.fvar_of_not_mem
  audit ``IndexLookupRenaming.fixedParameter
  audit ``BinderValuesBefore.mono scope
  audit ``BinderValuesBefore.weaken
  audit ``BinderValuesBefore.push scope
  audit ``BinderValuesBefore.of_fieldsDeclared scope
  audit ``BinderValuesBefore.atSize scope
  audit ``BinderIndexAllocations.parameterDisjoint
  audit ``CheckedHeaderTrace.paramsUnchanged_of_complete
  audit ``CheckedHeaderTrace.paramsBefore scope
  audit ``CheckedHeaderTrace.parameterBase_le_size scope
  audit ``CheckedHeaderTrace.openedSupport (binding ++ scope)
  audit ``RecursorIndexTrace.openedSupport (binding ++ scope)
  audit ``CheckedHeaderSupportSource.toSource
  audit ``CheckedHeaderSupportSource.mono
  audit ``CheckedHeaderSupportSource.openedSupport_of_normalized (binding ++ scope)
  audit ``RecursorInfoIndexSource.openedSupport_of_normalized (binding ++ scope)
  audit ``CheckedHeaderSupportSources.toSources
  audit ``checkInductiveTypes.scopedHeaderSupportTraces (binding ++ scope)
  audit ``ParentBinderSupportAlignment.toBinderAllocations
  audit ``RecursorBinderSupportAlignment.toBinderAllocations
  audit ``ParentBinderSupportAlignment.injectiveIndexLookup
  audit ``CheckedHeaderSupportSources.normalizedBinderSupport (binding ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderSupport (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderSupport (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderSupport (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderSupport
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderSupport (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderSupport (normalized ++ scope)
  lookupControls
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let firstLocals := ctx.lctx.mkLocalDecl ⟨.num `IndexLookupSeed 40⟩ `oldNat (.const ``Nat []) .implicit
  let secondLocals := firstLocals.mkLocalDecl ⟨.num `IndexLookupSeed 41⟩ `oldBool (.const ``Bool []) .default
  let seeded := { ctx with
    ngen := { namePrefix := `IndexLookupSeed, idx := 43 }
    lctx := secondLocals.mkLetDecl ⟨.num `IndexLookupSeed 42⟩ `oldLet
      (.const ``Nat []) (.lit (.natVal 7)) false }
  let .ok (_, _, _, extendedEnv, _, _) := stage 0 #[header `LookupReaderExtension sortType] ctx
    | throwError "index-lookup reader-extension setup failed"
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherLookupSeed, idx := 71 } },
      { ctx with lparams := [`u] }, { ctx with env := extendedEnv }] do
    fixtures reader
  holeBoundaries seeded
  differentReaderBoundary ctx
  uncheckedSourceSupportBoundary ctx
  logInfo "100 dense-reader full registrations preserve fixed shared-parameter lookup and finite index mappings across 125 parent pairs/five readers"

end InductiveIndexLookupTest
