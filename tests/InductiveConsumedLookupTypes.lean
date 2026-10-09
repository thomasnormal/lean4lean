import Lean4Lean.Verify.InductiveBinderLookupTypes
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveConsumedLookupTypesTest

abbrev CarrierAlias := Type

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`ConsumedLookupTag, .ofNat 1)] }

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
  header `ConsumedLookupLet (wrappedLet data), header `ConsumedLookupBeta (wrappedBeta data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem missingIncomingPair (source target : FVarId) (different : source ≠ target) :
    indexRenameExpr [] (.fvar source) ≠ .fvar target := by
  simpa [indexRenameExpr, indexLookup] using different

private theorem ownPairIsNotIncoming (source target : FVarId) :
    indexRenameExpr [] (.const ``Nat []) = indexRenameExpr [(source, target)] (.const ``Nat []) ∧
      ([] : List (FVarId × FVarId)) ≠ [(source, target)] := ⟨rfl, by simp⟩

private theorem futurePairIsNotIncoming (first second targetFirst targetSecond : FVarId) :
    ([(first, targetFirst)] : List (FVarId × FVarId)) ≠
      [(first, targetFirst), (second, targetSecond)] := by
  intro equal
  have impossible := congrArg List.length equal
  simp at impossible

private theorem fakeStoredTypeRejected {ctx : Context} {value rawDomain : Expr} {name : Name}
    {bi : BinderInfo} {decl : LocalDecl}
    (declared : BinderDeclaredAt ctx value name (peelTypeAnnotations rawDomain) bi)
    (lookup : ctx.lctx.find? value.fvarId! = some decl) (fake : decl.type ≠ peelTypeAnnotations rawDomain) : False := by
  obtain ⟨actual, hlookup, _, htype, _, _⟩ := declared
  rw [lookup] at hlookup
  obtain rfl := Option.some.inj hlookup
  exact fake htype

private theorem consumedFromRaw {pairs : List (FVarId × FVarId)} {left right : Expr}
    (raw : IndexLookupRenaming pairs left right) :
    ConsumedIndexLookupRenaming pairs (peelTypeAnnotations left) (peelTypeAnnotations right) := .ofRaw raw

private theorem literalProvenanceWitnesses {pairs : List (FVarId × FVarId)} {left right : Expr}
    (provenance : ConsumedIndexLookupRenaming pairs left right) :
    ∃ rawLeft rawRight, IndexLookupRenaming pairs rawLeft rawRight ∧
      peelTypeAnnotations rawLeft = left ∧ peelTypeAnnotations rawRight = right := provenance

private theorem consumedRetainsOldProvenance {pairs : List (FVarId × FVarId)} {left right : Expr}
    (provenance : ConsumedIndexLookupRenaming pairs left right) : ConsumedIndexRenaming pairs left right :=
  provenance.toConsumedIndexRenaming

private theorem concreteMappedProvenance (pairs : List (FVarId × FVarId)) (domain : Expr) :
    ConsumedIndexLookupRenaming pairs (peelTypeAnnotations domain)
      (peelTypeAnnotations (indexRenameExpr pairs domain)) := .ofRaw rfl

private def outParamDomain (domain : Expr) : Expr := mkApp (.const ``outParam [.succ .zero]) domain

private theorem annotatedIndexDomainProvenance (source target : FVarId) :
    ConsumedIndexLookupRenaming [(source, target)] (peelTypeAnnotations (outParamDomain (.fvar source)))
      (peelTypeAnnotations (outParamDomain (.fvar target))) := by
  apply ConsumedIndexLookupRenaming.ofRaw
  simp [IndexLookupRenaming, outParamDomain, indexRenameExpr, indexLookup]

private theorem actualDeclaredProvenance {pairs : List (FVarId × FVarId)}
    {checkedCtx generatedCtx : Context} {checkedValue generatedValue checkedRaw generatedRaw : Expr}
    {name : Name} {bi : BinderInfo}
    (checkedDeclared : BinderDeclaredAt checkedCtx checkedValue name (peelTypeAnnotations checkedRaw) bi)
    (generatedDeclared : BinderDeclaredAt generatedCtx generatedValue name (peelTypeAnnotations generatedRaw) bi)
    (raw : IndexLookupRenaming pairs checkedRaw generatedRaw) :
    ∃ checkedDecl generatedDecl,
      checkedCtx.lctx.find? checkedValue.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedValue.fvarId! = some generatedDecl ∧
      ConsumedIndexLookupRenaming pairs checkedDecl.type generatedDecl.type :=
  checkedDeclared.lookupRenamingTypes generatedDeclared raw

private theorem indexHeadProvenance {pairs finalPairs : List (FVarId × FVarId)}
    {checkedFirst generatedFirst : BinderStep} {checkedTail generatedTail : List BinderStep}
    {checkedCtx generatedCtx : Context}
    (correspondence : BinderLookupCorrespondence pairs (checkedFirst :: checkedTail)
      (generatedFirst :: generatedTail) finalPairs)
    (index : checkedFirst.role = .index)
    (checkedDeclared : BinderStepsIndexDeclared checkedCtx (checkedFirst :: checkedTail))
    (generatedDeclared : BinderStepsIndexDeclared generatedCtx (generatedFirst :: generatedTail)) :
    ∃ checkedDecl generatedDecl,
      checkedCtx.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      ConsumedIndexLookupRenaming pairs checkedDecl.type generatedDecl.type :=
  correspondence.indexHeadTypes index checkedDeclared generatedDeclared

private theorem exactPrefixAtEveryPosition {pairs finalPairs : List (FVarId × FVarId)}
    {checked generated : List BinderStep}
    (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs)
    (position : Nat) (bound : position < checked.length) :
    ∃ checkedStep generatedStep priorPairs,
      checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
      checkedStep.role = generatedStep.role ∧ checkedStep.signature = generatedStep.signature ∧
      priorPairs = pairs ++ List.zip ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
      IndexLookupRenaming priorPairs checkedStep.domain generatedStep.domain := correspondence.atPosition position bound

private theorem storedPositionCountsIndicesOnly {ctx : Context} {start position : Nat}
    {steps : List BinderStep} {step : BinderStep} (allocated : BinderIndexAllocations ctx start steps)
    (selected : steps[position]? = some step) (index : step.role = .index) :
    BinderPositionedAt ctx step.value step.name step.localDomain step.bi
      (start + (BinderStep.indexValues (steps.take position)).length) := allocated.atPosition selected index

private def parameterStep (id : FVarId) : BinderStep :=
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar id }

private def indexStep (name : Name) (domain : Expr) (id : FVarId) : BinderStep :=
  { role := .index, name, domain, bi := .default, value := .fvar id }

private def sequentialSteps (param first second : FVarId) : List BinderStep := [
  parameterStep param, indexStep `first (.fvar param) first, indexStep `second (.fvar first) second]

private theorem sequentialCorrespondence (param first second targetFirst targetSecond : FVarId) :
    BinderLookupCorrespondence [] (sequentialSteps param first second)
      (sequentialSteps param targetFirst targetSecond) [(first, targetFirst), (second, targetSecond)] := by
  apply BinderLookupCorrespondence.parameter (pairs := []) `carrier .implicit sortType sortType (.fvar param) rfl
  apply BinderLookupCorrespondence.index (pairs := []) `first .default (.fvar param) (.fvar param) first targetFirst rfl
  apply BinderLookupCorrespondence.index (pairs := [(first, targetFirst)]) `second .default
    (.fvar first) (.fvar targetFirst) second targetSecond
  · change indexRenameExpr [(first, targetFirst)] (.fvar first) = .fvar targetFirst
    simp [indexRenameExpr, indexLookup]
  · exact .nil _

private theorem firstIndexSkipsParameterPair (param first second targetFirst targetSecond : FVarId) :
    List.zip ((BinderStep.indexValues ((sequentialSteps param first second).take 1)).map Expr.fvarId!)
      ((BinderStep.indexValues ((sequentialSteps param targetFirst targetSecond).take 1)).map Expr.fvarId!) = [] := rfl

private theorem laterIndexUsesOnlyEarlierPair (param first second targetFirst targetSecond : FVarId) :
    List.zip ((BinderStep.indexValues ((sequentialSteps param first second).take 2)).map Expr.fvarId!)
      ((BinderStep.indexValues ((sequentialSteps param targetFirst targetSecond).take 2)).map Expr.fvarId!) =
      [(first, targetFirst)] := rfl

private theorem parameterDoesNotRequireNativeTypeReceipt (checkedCtx generatedCtx : Context)
    (checkedStart generatedStart : Nat) (param : FVarId) :
    BinderLookupNativeTypes [] checkedCtx generatedCtx checkedStart generatedStart
      [parameterStep param] [parameterStep param] := by
  intro position step selected index
  cases position with
  | zero =>
    have equal : parameterStep param = step := Option.some.inj selected
    subst step
    cases index
  | succ position =>
    simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
    cases selected

private theorem nativeTypesFromSameHistories {pairs finalPairs : List (FVarId × FVarId)}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart : Nat} {checked generated : List BinderStep}
    (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs)
    (checkedAllocated : BinderIndexAllocations checkedCtx checkedStart checked)
    (generatedAllocated : BinderIndexAllocations generatedCtx generatedStart generated) :
    BinderLookupNativeTypes pairs checkedCtx generatedCtx checkedStart generatedStart checked generated :=
  correspondence.nativeIndexTypes checkedAllocated generatedAllocated

private theorem nativeProvenanceKeepsRawAnchors {pairs : List (FVarId × FVarId)}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeIndexTypeAt pairs checkedCtx generatedCtx checkedStart generatedStart checked generated position) :
    ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
      checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
      priorPairs = pairs ++ List.zip ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
      checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
      checkedDecl.type = peelTypeAnnotations checkedStep.domain ∧
      generatedDecl.type = peelTypeAnnotations generatedStep.domain ∧
      IndexLookupRenaming priorPairs checkedStep.domain generatedStep.domain ∧
      ConsumedIndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    _, _, _, hprior, hcheckedLookup, hgeneratedLookup, _, _, hcheckedType, hgeneratedType, _, _, _, _,
    _, _, hraw, hconsumed⟩ := receipt
  exact ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated, hprior,
    hcheckedLookup, hgeneratedLookup, hcheckedType, hgeneratedType, hraw, hconsumed⟩

private theorem parentNativeTypes {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedCtx generatedCtx : Context} {info : RecInfo}
    (alignment : ParentBinderLookupAlignment stats types parent checkedCtx generatedCtx info) :
    ParentBinderLookupTypes stats types parent checkedCtx generatedCtx info := alignment.nativeIndexTypes

private theorem recursorNativeTypes {stats : InductiveStats} {types : Array InductiveType}
    {checkedCtx generatedCtx : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderLookupAlignment stats types checkedCtx generatedCtx infos) :
    RecursorBinderLookupTypes stats types checkedCtx generatedCtx infos := alignment.nativeIndexTypes

private theorem parentRetainsLookup {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedCtx generatedCtx : Context} {info : RecInfo}
    (receipt : ParentBinderLookupTypes stats types parent checkedCtx generatedCtx info) :
    ParentBinderLookupAlignment stats types parent checkedCtx generatedCtx info := receipt.toBinderLookup

private theorem recursorRetainsLookup {stats : InductiveStats} {types : Array InductiveType}
    {checkedCtx generatedCtx : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderLookupTypes stats types checkedCtx generatedCtx infos) :
    RecursorBinderLookupAlignment stats types checkedCtx generatedCtx infos := receipt.toBinderLookup

private theorem nativeTypesKeepExactOpeningWitnesses {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedCtx generatedCtx : Context} {info : RecInfo}
    (receipt : ParentBinderLookupTypes stats types parent checkedCtx generatedCtx info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧
      OpenedTelescope normalized generated generatedTerminal ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      BinderIndexAllocations checkedCtx checkedStart checked ∧
      BinderIndexAllocations generatedCtx generatedStart generated ∧
      BinderLookupNativeTypes [] checkedCtx generatedCtx checkedStart generatedStart checked generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, _, _, _, _, _, _, _, _, _, _, _,
    hcheckedAllocated, hgeneratedAllocated, _, _, _, _, _, hlookup, _, hnative⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hlookup, hcheckedAllocated,
    hgeneratedAllocated, hnative⟩

private theorem provedRegisteredNativeTypes (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderLookupTypes result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderLookupTypes 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private theorem normalizedRegisteredNativeTypes (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (typesNormalized : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (closed : NormalizedHeaderFVarsWithin types []) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderLookupTypes result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedBinderLookupTypes nparams types numNested elimLevel lparams isK ctx
    typesNormalized hwf hreserved closed

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
      | throwError "consumed-lookup checked source allocation points at a hole"
    let some byId := ctx.lctx.find? decl.fvarId
      | throwError "consumed-lookup checked source allocation is absent from native find?"
    unless byId.index == decl.index && byId.toExpr == decl.toExpr && decl.index == start + offset do
      throwError "consumed-lookup actual source find?/getAt? receipts disagree"
    values := values.push decl.toExpr
  return values

private def nativeType (ctx : Context) (value : Expr) (name : Name) (rawDomain : Expr)
    (bi : BinderInfo) (position : Nat) : MetaM Expr := do
  let some decl := ctx.lctx.find? value.fvarId!
    | throwError "consumed-lookup exact source opening refers to an undeclared actual local"
  unless decl.toExpr == value && decl.userName == name && decl.binderInfo == bi &&
      decl.type == peelTypeAnnotations rawDomain && decl.index == position do
    throwError "consumed-lookup exact own-plan native declaration receipt changed"
  unless decl.type != .lit (.natVal 66) do
    throwError "consumed-lookup accepted a fake native declaration type"
  return decl.type

private def openingStep (role : BinderRole) (name : Name) (domain : Expr) (bi : BinderInfo)
    (value : Expr) : BinderStep := { role, name, domain, bi, value }

private def checkRawPrefix (checked generated : List BinderStep) (pairs : List (FVarId × FVarId)) : MetaM Unit := do
  let expected := List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
    ((BinderStep.indexValues generated).map Expr.fvarId!)
  unless pairs == expected do
    throwError "consumed-lookup incoming pair map is not the exact zip of preceding index steps"

private def checkIndexTypes (checkedCtx generatedCtx : Context) (checkedStart generatedStart ordinal : Nat)
    (leftValue rightValue : Expr) (name : Name) (leftRaw rightRaw : Expr) (bi : BinderInfo)
    (incoming : List (FVarId × FVarId)) : MetaM Unit := do
  let checkedType ← nativeType checkedCtx leftValue name leftRaw bi (checkedStart + ordinal)
  let generatedType ← nativeType generatedCtx rightValue name rightRaw bi (generatedStart + ordinal)
  unless indexRenameExpr incoming leftRaw == rightRaw && checkedType == peelTypeAnnotations leftRaw &&
      generatedType == peelTypeAnnotations rightRaw do
    throwError "consumed-lookup native types lost deterministic raw provenance or literal consumption equations"
  let extended := incoming ++ [(leftValue.fvarId!, rightValue.fvarId!)]
  unless incoming.length + 1 == extended.length && incoming != extended do
    throwError "consumed-lookup included the own/current index pair in its incoming receipt"

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut pairs : List (FVarId × FVarId) := []
  let mut checkedSteps : List BinderStep := []
  let mut generatedSteps : List BinderStep := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftRaw leftBody leftBi := left
      | throwError "consumed-lookup checked opening ended before the actual substitutions"
    let .forallE rightName rightRaw rightBody rightBi := right
      | throwError "consumed-lookup generated opening ended before the actual substitutions"
    checkRawPrefix checkedSteps generatedSteps pairs
    unless leftName == rightName && leftBi == rightBi && indexRenameExpr pairs leftRaw == rightRaw do
      throwError "consumed-lookup chronological raw binder matching failed"
    let role := if position < nparams then BinderRole.parameter else .index
    if role = .index then
      checkIndexTypes checkedCtx generatedCtx checkedStart generatedStart (position - nparams)
        leftValues[position]! rightValues[position]! leftName leftRaw rightRaw leftBi pairs
      pairs := pairs ++ [(leftValues[position]!.fvarId!, rightValues[position]!.fvarId!)]
    else
      unless leftValues[position]! == rightValues[position]! &&
          indexRenameExpr pairs leftValues[position]! == rightValues[position]! do
        throwError "consumed-lookup shared parameters are not fixed"
    checkedSteps := checkedSteps ++ [openingStep role leftName leftRaw leftBi leftValues[position]!]
    generatedSteps := generatedSteps ++ [openingStep role rightName rightRaw rightBi rightValues[position]!]
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  checkRawPrefix checkedSteps generatedSteps pairs
  unless left == sortType && right == sortType && pairs.length == checked.size do
    throwError "consumed-lookup native opening terminal/count changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "consumed-lookup actual successful registration fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "consumed-lookup actual registration count changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "consumed-lookup actual source normalization failed"
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "consumed-lookup actual registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "consumed-lookup actual registered recursor metadata changed"

private def multipleParams : Expr := .forallE `carrier sortType
  (.forallE `pivot (.bvar 0)
    (.forallE `element (.bvar 1)
      (.forallE `witness (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1))
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 3) (.bvar 1) (.bvar 2)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .default) .implicit

private def family (carrierDomain : Expr) (names : Name) (marked : Bool) : Expr :=
  let elementDomain := if marked then Expr.mdata tagged (.bvar 0) else .bvar 0
  .forallE (names ++ `carrier) carrierDomain
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

private def annotationHeaders : Array InductiveType :=
  let carrier := Expr.const ``Nat []
  let outDomain := outParamDomain carrier
  let semiDomain := mkApp (.const ``semiOutParam [.succ .zero]) carrier
  let optionalDomain := mkApp2 (.const ``optParam [.succ .zero]) carrier (.lit (.natVal 7))
  let automaticDomain := mkApp2 (.const ``autoParam [.succ .zero]) carrier (.const ``Lean.Syntax.missing [])
  let nestedDomain := Expr.forallE `inside carrier outDomain .default
  let metadataDomain := Expr.mdata tagged outDomain
  #[header `ConsumedLookupOut (.forallE `index outDomain sortType .default),
    header `ConsumedLookupSemi (.forallE `index semiDomain sortType .implicit),
    header `ConsumedLookupOptional (.forallE `index optionalDomain sortType .strictImplicit),
    header `ConsumedLookupAutomatic (.forallE `index automaticDomain sortType .instImplicit),
    header `ConsumedLookupNested (.forallE `index nestedDomain sortType .default),
    header `ConsumedLookupMetadata (.forallE `index metadataDomain sortType .default)]

private def annotatedDependent : Expr := .forallE `carrier sortType
  (.forallE `element (outParamDomain (.bvar 0))
    (.forallE `witness
      (mkApp (.const ``outParam [.zero]) (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
      sortType .instImplicit) .strictImplicit) .implicit

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `ConsumedLookupEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `ConsumedLookupDependent nparams) dependent] #[4 - nparams]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `ConsumedLookupMultiple nparams) multipleParams] #[5 - nparams]
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `ConsumedLookupMutualFirst nparams) (family sortType `first false),
      header (Name.mkNum `ConsumedLookupMutualSecond nparams) (family sortType `second true)] #[4 - nparams, 4 - nparams]
  checkFixture ctx 4 #[header `ConsumedLookupAllParamsFirst dependent,
    header `ConsumedLookupAllParamsSecond (family sortType `shared false)] #[0, 0]
  checkFixture ctx 0 #[header `ConsumedLookupEmptyLeading sortType,
    header `ConsumedLookupDependentFollowing dependent] #[0, 4]
  checkFixture ctx 1 #[header `ConsumedLookupWrappedLet (wrappedLet tagged)] #[3]
  checkFixture ctx 1 #[header `ConsumedLookupWrappedBeta (wrappedBeta tagged)] #[3]
  checkFixture ctx 1 #[header `ConsumedLookupAliasFirst (family (.const ``CarrierAlias []) `first false),
    header `ConsumedLookupAliasSecond (family sortType `second false)] #[3, 3]
  checkFixture ctx 0 #[header `ConsumedLookupFancyNat natFancy] #[3]
  checkFixture ctx 0 annotationHeaders #[1, 1, 1, 1, 1, 1]
  checkFixture ctx 1 #[header `ConsumedLookupAnnotatedDependent annotatedDependent] #[2]

private def annotationBoundaries (ctx : Context) : MetaM Unit := do
  let carrier := Expr.const ``Nat []
  let rawOut := outParamDomain carrier
  let nested := Expr.forallE `inside carrier rawOut .default
  let metadata := Expr.mdata tagged rawOut
  unless rawOut != carrier && peelTypeAnnotations rawOut == carrier &&
      peelTypeAnnotations nested == nested && peelTypeAnnotations metadata == metadata do
    throwError "consumed-lookup executable annotation stripping was incorrectly generalized to nested domains or metadata"
  unless rawOut != carrier && rawOut.consumeTypeAnnotations == carrier &&
      nested.consumeTypeAnnotations == nested && metadata.consumeTypeAnnotations == metadata do
    throwError "consumed-lookup annotation stripping was incorrectly generalized to nested domains or metadata"
  let .ok (_, checked, _, _, infos, generated) := stage 0 annotationHeaders ctx
    | throwError "consumed-lookup native annotation-boundary setup failed"
  let checkedValues ← valuesAt checked ctx.lctx.numIndices 6
  for parent in [:4] do
    let some checkedDecl := checked.lctx.find? checkedValues[parent]!.fvarId!
      | throwError "consumed-lookup checked annotation declaration missing"
    let some generatedDecl := generated.lctx.find? infos[parent]!.indices[0]!.fvarId!
      | throwError "consumed-lookup generated annotation declaration missing"
    let .forallE _ rawDomain _ _ := annotationHeaders[parent]!.type
      | throwError "consumed-lookup annotated index-domain setup changed"
    unless checkedDecl.type == peelTypeAnnotations rawDomain && generatedDecl.type == peelTypeAnnotations rawDomain &&
        checkedDecl.type == carrier && generatedDecl.type == carrier && rawDomain != checkedDecl.type do
      throwError "consumed-lookup total-consumer annotated index-domain type failed to differ from raw syntax"
  logInfo "four executable outParam/semiOutParam/optParam/autoParam index domains strip to Nat; native comparison is empirical and nested/metadata barriers remain unchanged"

private def reusedParameterBoundary (ctx : Context) : MetaM Unit := do
  let first := family (.const ``CarrierAlias []) `first false
  let second := Expr.forallE `changedCarrier sortType (.forallE `element (.bvar 0) sortType .default) .default
  let types := #[header `ConsumedLookupReusedFirst first, header `ConsumedLookupReusedSecond second]
  let .ok (stats, checked, _, _, _, _) := stage 1 types ctx
    | throwError "consumed-lookup reused parameter setup failed"
  let some declaration := checked.lctx.find? stats.params[0]!.fvarId!
    | throwError "consumed-lookup reused shared parameter disappeared"
  let raw := peelTypeAnnotations sortType
  let .ok equivalent := ((monadLift (TypeChecker.isDefEq declaration.type raw) : M Bool) checked)
    | throwError "consumed-lookup reused parameter definitional equality failed"
  unless equivalent && declaration.type != raw && declaration.userName != `changedCarrier &&
      declaration.binderInfo != .default do
    throwError "consumed-lookup reused parameter incorrectly acquired literal source-domain/name/binder-info equality"
  logInfo "one actual reused parameter is definitionally equal but not literally equal to the second raw consumed source domain; exact native-type receipts cover indices only"

private def independentReaderBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `ConsumedLookupIndependentReaders dependent]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 1 types ctx
    | throwError "consumed-lookup independent reader setup failed"
  let .ok (first, firstCtx) := mkRecInfos stats types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) generatorRoot
    | throwError "consumed-lookup first independent helper failed"
  for offset in [0, 1] do
    let other := { generatorRoot with
      lparams := [`OtherConsumedLookupReader]
      ngen := { generatorRoot.ngen with idx := generatorRoot.ngen.idx + offset } }
    let .ok (second, secondCtx) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) other
      | throwError "consumed-lookup second independent helper failed"
    let sources := first[0]!.indices.toList.map Expr.fvarId!
    let targets := second[0]!.indices.toList.map Expr.fvarId!
    unless sources.length == 3 && targets.length == 3 do
      throwError "consumed-lookup independent-reader boundary setup changed"
    if offset = 0 then
      unless sources == targets do
        throwError "consumed-lookup identity paired-reader type boundary disappeared"
    else
      unless (sources.any (targets.contains ·)) && sources != targets do
        throwError "consumed-lookup overlapping paired-reader type boundary disappeared"
    checkOpening firstCtx secondCtx 1 generatorRoot.lctx.numIndices generatorRoot.lctx.numIndices
      dependent stats.params first[0]!.indices second[0]!.indices
  logInfo "two independent-reader opening controls preserve native consumed-type provenance with identity/overlapping source and target IDs"

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
  let normalized := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``dependentShape
  audit ``wrappedLetTrace binding
  audit ``wrappedBetaTrace binding
  audit ``provedHeaders binding
  audit ``missingIncomingPair
  audit ``ownPairIsNotIncoming
  audit ``futurePairIsNotIncoming
  audit ``fakeStoredTypeRejected
  audit ``consumedFromRaw
  audit ``literalProvenanceWitnesses
  audit ``consumedRetainsOldProvenance
  audit ``concreteMappedProvenance
  audit ``annotatedIndexDomainProvenance
  audit ``actualDeclaredProvenance
  audit ``indexHeadProvenance
  audit ``exactPrefixAtEveryPosition
  audit ``storedPositionCountsIndicesOnly
  audit ``sequentialCorrespondence
  audit ``firstIndexSkipsParameterPair
  audit ``laterIndexUsesOnlyEarlierPair
  audit ``parameterDoesNotRequireNativeTypeReceipt
  audit ``nativeTypesFromSameHistories
  audit ``nativeProvenanceKeepsRawAnchors
  audit ``parentNativeTypes
  audit ``recursorNativeTypes
  audit ``parentRetainsLookup
  audit ``recursorRetainsLookup
  audit ``nativeTypesKeepExactOpeningWitnesses
  audit ``provedRegisteredNativeTypes (normalized ++ scope)
  audit ``normalizedRegisteredNativeTypes (binding ++ scope)
  audit ``ConsumedIndexLookupRenaming.ofRaw
  audit ``ConsumedIndexLookupRenaming.toConsumedIndexRenaming
  audit ``BinderDeclaredAt.lookupRenamingTypes
  audit ``BinderLookupCorrespondence.indexHeadTypes
  audit ``BinderLookupCorrespondence.length
  audit ``BinderLookupCorrespondence.roles
  audit ``BinderLookupCorrespondence.atPosition
  audit ``BinderLookupCorrespondence.atPosition_of_getElem?
  audit ``BinderIndexAllocations.atPosition
  audit ``BinderLookupCorrespondence.nativeIndexTypes
  audit ``ParentBinderLookupAlignment.nativeIndexTypes
  audit ``RecursorBinderLookupAlignment.nativeIndexTypes
  audit ``ParentBinderLookupTypes.toBinderLookup
  audit ``RecursorBinderLookupTypes.toBinderLookup
  audit ``CheckedHeaderSupportSources.normalizedBinderLookupTypes (binding ++ scope)
  audit ``CheckedHeaderSupportSources.wrappedBinderLookupTypes (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderLookupTypes (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderLookupTypes (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderLookupTypes
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredBinderLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderLookupTypes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderLookupTypes (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `ConsumedLookupSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `ConsumedLookupSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `ConsumedLookupSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherConsumedLookupSeed, idx := 71 } },
      { ctx with lparams := [`u] }] do
    fixtures reader
  reusedParameterBoundary ctx
  independentReaderBoundaries ctx
  annotationBoundaries ctx
  logInfo "92 dense-reader registrations retain exact incoming pair prefixes and native consumed-type provenance across 136 parent pairs/280 index-type pairs/four readers"

end InductiveConsumedLookupTypesTest
