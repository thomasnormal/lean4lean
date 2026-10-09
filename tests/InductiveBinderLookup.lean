import Lean4Lean.Verify.InductiveBinderLookupAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderLookupTest

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`BinderLookupTag, .ofNat 1)] }

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

private def wrappedLet (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private theorem wrappedLetTrace (data : MData) : WrappedSortTelescope (wrappedLet data) dependent := by
  unfold wrappedLet
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def wrappedBeta (data : MData) : Expr :=
  .mdata data (.app (.lam `unused (.const ``Nat []) dependent .implicit) (.lit (.natVal 0)))

private theorem wrappedBetaTrace (data : MData) : WrappedSortTelescope (wrappedBeta data) dependent := by
  unfold wrappedBeta
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `BinderLookupLet (wrappedLet data), header `BinderLookupBeta (wrappedBeta data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem singletonInjection (source target : FVarId) : IndexPairInjection [(source, target)] := by
  simp [IndexPairInjection]

private theorem oldRelationNotDeterministic (source target : FVarId) (different : source ≠ target) :
    IndexRenaming [(source, target)] (.fvar source) (.fvar source) ∧
      ¬ IndexLookupRenaming [(source, target)] (.fvar source) (.fvar source) := by
  refine ⟨IndexRenaming.refl _ _, ?_⟩
  intro identity
  have mapped : IndexLookupRenaming [(source, target)] (.fvar source) (.fvar target) :=
    .fvar_of_mem (singletonInjection source target) (by simp)
  exact different (Expr.fvar.inj (identity.functional mapped))

private theorem parameterIndexAliasRejected (param target : FVarId) :
    ¬ IndexParameterSupport [(param, target)] [param] := by
  intro support
  exact (support param (by simp)) (by simp)

private theorem openHeaderNotFixed (source target : FVarId) (different : source ≠ target) :
    indexRenameExpr [(source, target)] (.forallE `index (.fvar source) sortType .default) ≠
      .forallE `index (.fvar source) sortType .default := by
  simp [indexRenameExpr, indexLookup, sortType, Ne.symm different]

private theorem futurePairChangesUnreservedDomain (source target : FVarId) (different : source ≠ target) :
    indexRenameExpr [] (.fvar source) = .fvar source ∧
      indexRenameExpr [(source, target)] (.fvar source) ≠ .fvar source := by
  simp [indexRenameExpr, indexLookup, Ne.symm different]

private def indexStep (name : Name) (domain : Expr) (id : FVarId) : BinderStep :=
  { role := .index, name, domain, bi := .default, value := .fvar id }

private def parameterStep (domain value : Expr) : BinderStep :=
  { role := .parameter, name := `shared, domain, bi := .implicit, value }

private theorem emptyCorrespondence (pairs : List (FVarId × FVarId)) :
    BinderLookupCorrespondence pairs [] [] pairs := .nil pairs

private theorem rawIndexCorrespondence (pairs : List (FVarId × FVarId)) (domain : Expr)
    (source target : FVarId) :
    BinderLookupCorrespondence pairs [indexStep `index domain source]
      [indexStep `index (indexRenameExpr pairs domain) target] (pairs ++ [(source, target)]) :=
  .index `index .default domain (indexRenameExpr pairs domain) source target rfl (.nil _)

private theorem rawParameterCorrespondence (pairs : List (FVarId × FVarId)) (domain value : Expr) :
    BinderLookupCorrespondence pairs [parameterStep domain value]
      [parameterStep (indexRenameExpr pairs domain) value] pairs :=
  .parameter `shared .implicit domain (indexRenameExpr pairs domain) value rfl (.nil _)

private theorem correspondenceRetainsOldRelation {pairs finalPairs : List (FVarId × FVarId)}
    {checked generated : List BinderStep} (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs) :
    BinderIndexCorrespondence pairs checked generated finalPairs := correspondence.toIndexCorrespondence

private theorem correspondenceExactZip {pairs finalPairs : List (FVarId × FVarId)}
    {checked generated : List BinderStep} (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs) :
    finalPairs = pairs ++ List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!) := correspondence.finalPairs

private theorem sequentialDependentRawDomains (first second targetFirst targetSecond : FVarId) :
    BinderLookupCorrespondence []
      [indexStep `first (.const ``Nat []) first, indexStep `second (.fvar first) second]
      [indexStep `first (.const ``Nat []) targetFirst, indexStep `second (.fvar targetFirst) targetSecond]
      [(first, targetFirst), (second, targetSecond)] := by
  apply BinderLookupCorrespondence.index `first .default (.const ``Nat []) (.const ``Nat []) first targetFirst rfl
  apply BinderLookupCorrespondence.index `second .default (.fvar first) (.fvar targetFirst) second targetSecond
  · change indexRenameExpr [(first, targetFirst)] (.fvar first) = .fvar targetFirst
    simp [indexRenameExpr, indexLookup]
  · exact .nil _

private theorem sequentialIdentityRawDomains (first second : FVarId) :
    BinderLookupCorrespondence []
      [indexStep `first (.const ``Nat []) first, indexStep `second (.fvar first) second]
      [indexStep `first (.const ``Nat []) first, indexStep `second (.fvar first) second]
      [(first, first), (second, second)] := sequentialDependentRawDomains first second first second

private theorem sequentialOverlappingRawDomains (first second third : FVarId) :
    BinderLookupCorrespondence []
      [indexStep `first (.const ``Nat []) first, indexStep `second (.fvar first) second]
      [indexStep `first (.const ``Nat []) second, indexStep `second (.fvar second) third]
      [(first, second), (second, third)] := sequentialDependentRawDomains first second second third

private theorem sharedPrefixRawDomains (param source target : FVarId) :
    BinderLookupCorrespondence []
      [parameterStep sortType (.fvar param), indexStep `index (.fvar param) source]
      [parameterStep sortType (.fvar param), indexStep `index (.fvar param) target]
      [(source, target)] := by
  apply BinderLookupCorrespondence.parameter `shared .implicit sortType sortType (.fvar param) rfl
  exact rawIndexCorrespondence [] (.fvar param) source target

private theorem constructorDoesNotSupplySourceSupport (source target : FVarId) :
    BinderLookupCorrespondence [] [indexStep `index (.fvar source) source]
      [indexStep `index (.fvar source) target] [(source, target)] :=
  rawIndexCorrespondence [] (.fvar source) source target

private theorem wrappedLetFreeVars (data : MData) : dependent.fvarsList ⊆ (wrappedLet data).fvarsList :=
  (wrappedLetTrace data).freeVarsSubset

private theorem wrappedBetaFreeVars (data : MData) : dependent.fvarsList ⊆ (wrappedBeta data).fvarsList :=
  (wrappedBetaTrace data).freeVarsSubset

private theorem wrappedLetClosed (data : MData) : dependent.hasFVar = false :=
  (wrappedLetTrace data).noFVars (fvarsList_eq_nil.mp rfl)

private theorem wrappedBetaClosed (data : MData) : dependent.hasFVar = false :=
  (wrappedBetaTrace data).noFVars (fvarsList_eq_nil.mp rfl)

private theorem unusedOpenLetTrace (id : FVarId) :
    WrappedSortTelescope (.letE `unused (.const ``Nat []) (.fvar id) sortType true) sortType := by
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  exact .telescope (.sort (.succ .zero))

private theorem normalizationDoesNotReflectClosedness (id : FVarId) :
    (.letE `unused (.const ``Nat []) (.fvar id) sortType true : Expr).hasFVar = true ∧
      sortType.hasFVar = false := by
  simp [Expr.hasFVar_eq, Expr.hasFVar', sortType]

private theorem normalizedSupportAtDepth {ids : List FVarId} {body replacement : Expr}
    (bodySupport : IndexFVarsWithin ids body) (replacementSupport : IndexFVarsWithin ids replacement) (depth : Nat) :
    IndexFVarsWithin ids (body.instantiate1' replacement depth) := bodySupport.instantiate1' replacementSupport depth

private theorem parentRetainsSupport {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checked generated : Context} {info : RecInfo}
    (alignment : ParentBinderLookupAlignment stats types parent checked generated info) :
    ParentBinderSupportAlignment stats types parent checked generated info := alignment.toBinderSupport

private theorem recursorsRetainSupport {stats : InductiveStats} {types : Array InductiveType}
    {checked generated : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderLookupAlignment stats types checked generated infos) :
    RecursorBinderSupportAlignment stats types checked generated infos := alignment.toBinderSupport

private theorem sameWitnessLookupHistories {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot generatedRoot : Context} {info : RecInfo}
    (alignment : ParentBinderLookupAlignment stats types parent checkedRoot generatedRoot info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧
      OpenedTelescope normalized generated generatedTerminal ∧
      BinderStep.parameterValues checked = stats.params.toList ∧
      BinderStep.parameterValues generated = stats.params.toList ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧
      BinderIndexAllocations generatedRoot generatedStart generated ∧
      BinderParameterIndexDisjoint checked ∧ BinderParameterIndexDisjoint generated ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
        (info.indices.toList.map Expr.fvarId!) ∧
      IndexLookupRenaming pairs checkedTerminal generatedTerminal := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, hcheckedParams, hgeneratedParams,
    _, _, _, _, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, hpairs, _, hcheckedSupport,
    hgeneratedSupport, hlookup, hterminal⟩ := alignment
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedParams, hgeneratedParams,
    hcheckedAlloc, hgeneratedAlloc, hcheckedSupport, hgeneratedSupport, hlookup, hpairs, hterminal⟩

private theorem normalizedSourcesNeedExplicitSupport {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (typesNormalized : NormalizedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF)
    (within : NormalizedHeaderFVarsWithin types (stats.params.toList.map Expr.fvarId!)) :
    RecursorBinderLookupAlignment stats types checkedRoot current infos :=
  headers.normalizedBinderLookup sources typesNormalized support hwf within

private theorem wrappedSourcesDischargeClosure {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (typesWrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) : RecursorBinderLookupAlignment stats types checkedRoot current infos :=
  headers.wrappedBinderLookup sources typesWrapped support hwf

private theorem provedRegisteredLookup (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderLookupAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderLookup 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private def constructors (source param : FVarId) : Array Expr := #[
  .bvar 2, .fvar source, .mvar ⟨`BinderLookupMeta⟩, .sort (.succ (.param `u)),
  .const `BinderLookupConstant [.param `u], .lit (.natVal 7),
  .app (.fvar source) (.fvar param),
  .lam `local (.fvar param) (.app (.fvar source) (.bvar 2)) .instImplicit,
  .forallE `index (.fvar param) (.app (.fvar source) (.bvar 3)) .strictImplicit,
  .letE `hidden (.fvar param) (.fvar source) (.app (.fvar source) (.bvar 3)) false,
  .mdata tagged (.app (.fvar source) (.fvar param)),
  .proj `BinderLookupStructure 2 (.app (.fvar source) (.fvar param))]

private def constructorControls : MetaM Unit := do
  let source : FVarId := ⟨`BinderLookupSource⟩
  let target : FVarId := ⟨`BinderLookupTarget⟩
  let param : FVarId := ⟨`BinderLookupParameter⟩
  for pairs in [[], [(source, target)], [(source, source)], [(source, target), (target, source)],
      [(source, target), (source, param)]] do
    for raw in constructors source param do
      let mapped := indexRenameExpr pairs raw
      unless Expr.binderSignature mapped == Expr.binderSignature raw do
        throwError "binder-lookup deterministic raw-domain mapping changed binder signatures"
      for depth in [0, 1, 3] do
        unless indexRenameExpr pairs (raw.instantiate1' (.fvar source) depth) ==
            mapped.instantiate1' (.fvar (indexLookup pairs source)) depth do
          throwError "binder-lookup deterministic raw-domain mapping changed incoming substitutions"
  logInfo "60 pure raw-domain checks/180 substitutions cover all 12 Expr constructors and five generic finite pair lists"

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
    let some decl := ctx.lctx.getAt? (start + offset)
      | throwError "binder-lookup checked source allocation points at a hole"
    let some byId := ctx.lctx.find? decl.fvarId
      | throwError "binder-lookup checked source allocation is absent from native find?"
    unless byId.index == decl.index && byId.toExpr == decl.toExpr && decl.index == start + offset do
      throwError "binder-lookup actual source find?/getAt? receipts disagree"
    values := values.push decl.toExpr
  return values

private def checkDeclaration (ctx : Context) (value : Expr) (name : Name) (rawDomain : Expr)
    (bi : BinderInfo) : MetaM Unit := do
  let some decl := ctx.lctx.find? value.fvarId!
    | throwError "binder-lookup opening refers to an undeclared actual local"
  unless decl.toExpr == value && decl.userName == name && decl.binderInfo == bi &&
      decl.type == rawDomain.consumeTypeAnnotations do
    throwError "binder-lookup actual own-plan consumed declaration anchor changed"

private def addIndexPair (pairs : List (FVarId × FVarId)) (leftBody leftValue rightValue : Expr) :
    MetaM (List (FVarId × FVarId)) := do
  let source := leftValue.fvarId!
  unless leftValue.isFVar && rightValue.isFVar && !(leftBody.containsFVar source) &&
      !(pairs.any (·.1 == source)) && !(pairs.any (·.2 == rightValue.fvarId!)) do
    throwError "binder-lookup actual raw-domain correspondence lacks fresh allocation/body support"
  return pairs ++ [(source, rightValue.fvarId!)]

private def checkOpening (checkedCtx generatedCtx : Context) (nparams parent : Nat) (type : Expr)
    (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut pairs : List (FVarId × FVarId) := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftDomain leftBody leftBi := left
      | throwError "binder-lookup checked plan ended before its actual substitutions"
    let .forallE rightName rightDomain rightBody rightBi := right
      | throwError "binder-lookup generated plan ended before its actual substitutions"
    unless leftName == rightName && leftBi == rightBi && indexRenameExpr pairs leftDomain == rightDomain &&
        indexRenameExpr pairs leftBody == rightBody do
      throwError "binder-lookup incoming chronological finite zip lost exact deterministic raw-domain equality"
    if position < nparams then
      unless leftValues[position]! == rightValues[position]! &&
          indexRenameExpr pairs leftValues[position]! == rightValues[position]! do
        throwError "binder-lookup actual shared-parameter replacement is not fixed"
    else
      pairs ← addIndexPair pairs leftBody leftValues[position]! rightValues[position]!
    if position ≥ nparams || parent = 0 then
      checkDeclaration checkedCtx leftValues[position]! leftName leftDomain leftBi
      checkDeclaration generatedCtx rightValues[position]! rightName rightDomain rightBi
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  unless left == sortType && right == sortType && pairs.length == checked.size &&
      pairs == List.zip (checked.toList.map Expr.fvarId!) (generated.toList.map Expr.fvarId!) do
    throwError "binder-lookup terminal equality or exact chronological native index zip changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, _, env, infos, generated) := stage nparams types ctx
    | throwError "binder-lookup successful registration fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-lookup actual registered counts changed"
  for parent in [:types.size] do
    let checkedStart := ctx.lctx.numIndices + nparams + (expected.toList.take parent).sum
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "binder-lookup source normalization failed"
    unless normalized.fvarsList.isEmpty do
      throwError "binder-lookup successful checked header normalized to an open raw telescope"
    checkOpening checked generated nparams parent normalized stats.params checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-lookup successful fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-lookup actual registered metadata changed"

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

private def natFancy : Expr :=
  let carrier := Expr.const ``Nat []
  let pair := mkApp4 (.const ``Prod.mk [.zero, .zero]) carrier carrier (.bvar 0) (.lit (.natVal 7))
  let projection := Expr.proj ``Prod 0 pair
  let beta := Expr.app (.lam `value carrier (.bvar 0) .default) (.bvar 1)
  let witness := Expr.letE `local carrier beta
    (equalityDomain carrier (.bvar 0) (.bvar 0)) false
  .forallE `first carrier
    (.forallE `second (equalityDomain carrier projection (.bvar 0))
      (.forallE `third witness sortType .instImplicit) .strictImplicit) .default

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderLookupEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderLookupDependent nparams) dependent] #[4 - nparams]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderLookupMultiple nparams) multipleParams] #[5 - nparams]
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderLookupMutualFirst nparams) (family `first false),
      header (Name.mkNum `BinderLookupMutualSecond nparams) (family `second true)] #[4 - nparams, 4 - nparams]
  checkFixture ctx 4 #[header `BinderLookupAllParamsFirst dependent,
    header `BinderLookupAllParamsSecond (family `shared false)] #[0, 0]
  checkFixture ctx 0 #[header `BinderLookupEmptyLeading sortType,
    header `BinderLookupDependentFollowing dependent] #[0, 4]
  checkFixture ctx 1 #[header `BinderLookupWrappedLet (wrappedLet tagged)] #[3]
  checkFixture ctx 1 #[header `BinderLookupWrappedBeta (wrappedBeta tagged)] #[3]
  checkFixture ctx 0 #[header `BinderLookupFancyNat natFancy] #[3]

private def missingSupportBoundary (ctx : Context) : MetaM Unit := do
  let type := Expr.forallE `carrier sortType
    (.forallE `index (.const ``Nat []) sortType .default) .implicit
  let types := #[header `BinderLookupUncheckedSupport type]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "binder-lookup unchecked support setup failed"
  let collision : FVarId := ⟨generatorRoot.ngen.curr⟩
  let changed := { stats with params := #[.fvar collision] }
  let .ok infos := mkRecInfos changed types (.succ .zero) pure generatorRoot
    | throwError "binder-lookup bare generator unexpectedly requires actual parameter support"
  unless infos[0]!.indices.toList.map Expr.fvarId! == [collision] && changed.params[0]!.fvarId! == collision do
    throwError "binder-lookup unchecked helper incorrectly acquired parameter/index separation"
  logInfo "one unchecked successful helper aliases a shared parameter and freshly allocated index; deterministic correspondence requires the support boundary"

private def independentReaderBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `BinderLookupIndependentReaders dependent]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "binder-lookup independent reader setup failed"
  let .ok (first, firstCtx) := mkRecInfos stats types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) generatorRoot
    | throwError "binder-lookup first independent helper failed"
  for offset in [0, 1] do
    let other := { generatorRoot with
      lparams := [`OtherBinderLookupReader]
      ngen := { generatorRoot.ngen with idx := generatorRoot.ngen.idx + offset } }
    let .ok (second, secondCtx) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) other
      | throwError "binder-lookup second independent helper failed"
    let sources := first[0]!.indices.toList.map Expr.fvarId!
    let targets := second[0]!.indices.toList.map Expr.fvarId!
    unless generatorRoot.lparams != other.lparams && sources.length == 3 && targets.length == 3 do
      throwError "binder-lookup independent-reader boundary setup changed"
    if offset = 0 then
      unless sources == targets do
        throwError "binder-lookup independent readers incorrectly require distinct source/target IDs"
    else
      unless (sources.any (targets.contains ·)) && sources != targets do
        throwError "binder-lookup shifted independent readers lost overlapping source/target ID sets"
    checkOpening firstCtx secondCtx 1 0 dependent stats.params first[0]!.indices second[0]!.indices
  logInfo "two independent-reader paired openings permit identity and overlapping source/target ID sets without global disjointness"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let expressions := binding ++ [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let normalized := expressions ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  audit ``dependentShape
  audit ``wrappedLetTrace binding
  audit ``wrappedBetaTrace binding
  audit ``provedHeaders binding
  audit ``singletonInjection
  audit ``oldRelationNotDeterministic
  audit ``parameterIndexAliasRejected
  audit ``openHeaderNotFixed
  audit ``futurePairChangesUnreservedDomain
  audit ``emptyCorrespondence
  audit ``rawIndexCorrespondence
  audit ``rawParameterCorrespondence
  audit ``correspondenceRetainsOldRelation
  audit ``correspondenceExactZip
  audit ``sequentialDependentRawDomains
  audit ``sequentialIdentityRawDomains
  audit ``sequentialOverlappingRawDomains
  audit ``sharedPrefixRawDomains
  audit ``constructorDoesNotSupplySourceSupport
  audit ``wrappedLetFreeVars binding
  audit ``wrappedBetaFreeVars binding
  audit ``wrappedLetClosed expressions
  audit ``wrappedBetaClosed expressions
  audit ``unusedOpenLetTrace binding
  audit ``normalizationDoesNotReflectClosedness expressions
  audit ``normalizedSupportAtDepth
  audit ``parentRetainsSupport
  audit ``recursorsRetainSupport
  audit ``sameWitnessLookupHistories
  audit ``normalizedSourcesNeedExplicitSupport (expressions ++ scope)
  audit ``wrappedSourcesDischargeClosure (normalized ++ scope)
  audit ``provedRegisteredLookup (normalized ++ scope)
  audit ``BinderLookupCorrespondence.toIndexCorrespondence
  audit ``BinderLookupCorrespondence.finalPairs
  audit ``OpenedTelescope.relatedLookupIndexCorrespondence binding
  audit ``OpenedTelescope.lookupIndexCorrespondence binding
  audit ``IndexFVarsWithin.mono
  audit ``IndexFVarsWithin.liftLooseBVars'
  audit ``IndexFVarsWithin.instantiate1'
  audit ``IndexFVarsWithin.instantiate1 binding
  audit ``instantiate1FreeVarsSubset binding
  audit ``WrappedSortTelescope.freeVarsSubset binding
  audit ``WrappedSortTelescope.fvars_nil binding
  audit ``WrappedSortTelescope.noFVars expressions
  audit ``CheckedHeaderSource.sourceNoFVars expressions
  audit ``CheckedHeaderSource.normalizedNoFVars_of_wrappedExact expressions
  audit ``CheckedHeaderSource.normalizedNoFVars_of_normalized_wrapped normalized
  audit ``CheckedHeaderSource.normalizedNoFVars_of_wrapped normalized
  audit ``CheckedHeaderSupportSource.normalizedNoFVars_of_wrapped normalized
  audit ``CheckedHeaderSupportSource.normalizedNoFVars_of_normalized_wrapped normalized
  audit ``ParentBinderLookupAlignment.toBinderSupport
  audit ``RecursorBinderLookupAlignment.toBinderSupport
  audit ``BinderValuesBefore.fvarValues
  audit ``CheckedHeaderSupportSources.wrappedFVarsWithin normalized
  audit ``ParentBinderSupportAlignment.toBinderLookup (expressions ++ scope)
  audit ``CheckedHeaderSupportSources.normalizedBinderLookup (expressions ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderLookup (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderLookup (expressions ++ scope)
  audit ``mkRecInfos.getNormalizedBinderLookup (expressions ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderLookup
    (expressions ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredBinderLookup (expressions ++ scope)
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderLookup (expressions ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderLookup (normalized ++ scope)
  constructorControls
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderLookupSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderLookupSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderLookupSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderLookupSeed, idx := 71 } },
      { ctx with lparams := [`u] }] do
    fixtures reader
  missingSupportBoundary ctx
  independentReaderBoundaries ctx
  logInfo "80 dense-reader full registrations preserve sequential deterministic raw-domain correspondence across 100 parent pairs/four readers"

end InductiveBinderLookupTest
