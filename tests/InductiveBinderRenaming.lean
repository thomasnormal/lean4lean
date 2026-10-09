import Lean4Lean.Verify.InductiveBinderRenamingAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderRenamingTest

abbrev RenamingCarrierAlias := Type

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`BinderRenamingTag, .ofNat 1)] }

private def changedTag : MData := { entries := [(`BinderRenamingTag, .ofNat 2)] }

private def deepDependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
      (.forallE `again
        (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
        sortType .default) .instImplicit) .strictImplicit) .implicit

private theorem deepDependentShape : SortTelescope deepDependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) .instImplicit
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          .default (.sort (.succ .zero)))))

private def deepSteps (carrier element witness again : FVarId) : List BinderStep := [
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar carrier },
  { role := .index, name := `element, domain := .fvar carrier, bi := .strictImplicit, value := .fvar element },
  { role := .index, name := `witness, domain := equalityDomain (.fvar carrier) (.fvar element) (.fvar element),
    bi := .instImplicit, value := .fvar witness },
  { role := .index, name := `again,
    domain := proofEquality (equalityDomain (.fvar carrier) (.fvar element) (.fvar element))
      (.fvar witness) (.fvar witness), bi := .default, value := .fvar again }]

private theorem deepOpened (carrier element witness again : FVarId) :
    OpenedTelescope deepDependent (deepSteps carrier element witness again) sortType := by
  unfold deepDependent deepSteps
  apply OpenedTelescope.bind .parameter `carrier sortType .implicit (.fvar carrier)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `element (.fvar carrier)
      (.forallE `witness (equalityDomain (.fvar carrier) (.bvar 0) (.bvar 0))
        (.forallE `again
          (proofEquality (equalityDomain (.fvar carrier) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) _ sortType
  apply OpenedTelescope.bind .index `element (.fvar carrier) .strictImplicit (.fvar element)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `witness (equalityDomain (.fvar carrier) (.fvar element) (.fvar element))
      (.forallE `again
        (proofEquality (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) (.bvar 0) (.bvar 0))
        sortType .default) .instImplicit) _ sortType
  apply OpenedTelescope.bind .index `witness
    (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) .instImplicit (.fvar witness)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `again
      (proofEquality (equalityDomain (.fvar carrier) (.fvar element) (.fvar element))
        (.fvar witness) (.fvar witness)) sortType .default) _ sortType
  apply OpenedTelescope.bind .index `again
    (proofEquality (equalityDomain (.fvar carrier) (.fvar element) (.fvar element))
      (.fvar witness) (.fvar witness)) .default (.fvar again)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope sortType [] sortType
  exact .sort (.succ .zero)

private theorem eqRelated {pairs : List (FVarId × FVarId)} {left right leftFirst rightFirst leftSecond rightSecond : Expr}
    (level : Level) (carrier : IndexRenaming pairs left right)
    (first : IndexRenaming pairs leftFirst rightFirst) (second : IndexRenaming pairs leftSecond rightSecond) :
    IndexRenaming pairs (mkApp3 (.const ``Eq [level]) left leftFirst leftSecond)
      (mkApp3 (.const ``Eq [level]) right rightFirst rightSecond) :=
  .app (.app (.app (.const ``Eq [level]) carrier) first) second

private theorem deepCorrespondence (carrier leftElement rightElement leftWitness rightWitness leftAgain rightAgain : FVarId) :
    BinderIndexCorrespondence [] (deepSteps carrier leftElement leftWitness leftAgain)
      (deepSteps carrier rightElement rightWitness rightAgain)
      [(leftElement, rightElement), (leftWitness, rightWitness), (leftAgain, rightAgain)] := by
  let elementPair : IndexRenaming [(leftElement, rightElement)] (.fvar leftElement) (.fvar rightElement) :=
    .fvar (.inr (List.mem_cons_self ..))
  let witnessPair : IndexRenaming [(leftElement, rightElement), (leftWitness, rightWitness)]
      (.fvar leftWitness) (.fvar rightWitness) := .fvar (.inr (by simp))
  let elements : IndexRenaming [(leftElement, rightElement), (leftWitness, rightWitness)]
      (.fvar leftElement) (.fvar rightElement) := .fvar (.inr (by simp))
  let witnessDomain := eqRelated (.succ .zero) (IndexRenaming.refl _ (.fvar carrier)) elementPair elementPair
  let againDomain := eqRelated .zero
    (eqRelated (.succ .zero) (IndexRenaming.refl _ (.fvar carrier)) elements elements) witnessPair witnessPair
  exact .parameter `carrier .implicit sortType sortType (.fvar carrier) (.sort _) (.ofRaw (.sort _))
    (.index `element .strictImplicit (.fvar carrier) (.fvar carrier) leftElement rightElement
      (IndexRenaming.refl _ _) (.ofRaw (IndexRenaming.refl _ _))
      (.index `witness .instImplicit _ _ leftWitness rightWitness witnessDomain (.ofRaw witnessDomain)
        (.index `again .default _ _ leftAgain rightAgain againDomain (.ofRaw againDomain) (.nil _))))

private theorem deepFinalPairs (carrier leftElement rightElement leftWitness rightWitness leftAgain rightAgain : FVarId) :
    [(leftElement, rightElement), (leftWitness, rightWitness), (leftAgain, rightAgain)] =
      List.zip ((BinderStep.indexValues (deepSteps carrier leftElement leftWitness leftAgain)).map Expr.fvarId!)
        ((BinderStep.indexValues (deepSteps carrier rightElement rightWitness rightAgain)).map Expr.fvarId!) :=
  (deepCorrespondence carrier leftElement rightElement leftWitness rightWitness leftAgain rightAgain).finalPairs

private theorem deepDomainsUnequal (carrier leftElement rightElement leftWitness rightWitness leftAgain rightAgain : FVarId)
    (different : leftElement ≠ rightElement) :
    (deepSteps carrier leftElement leftWitness leftAgain).map BinderStep.domain ≠
      (deepSteps carrier rightElement rightWitness rightAgain).map BinderStep.domain := by
  intro equal
  have domain := (List.cons.inj (List.cons.inj (List.cons.inj equal).2).2).1
  exact different (Expr.fvar.inj (Expr.app.inj domain).2)

private theorem unpairedRejected (left right : FVarId) (different : left ≠ right) :
    ¬ IndexRenaming [] (.fvar left) (.fvar right) := by
  rw [IndexRenaming.fvar_iff]
  simp only [List.not_mem_nil, or_false]
  exact different

private theorem futurePairRejected (left right laterLeft laterRight : FVarId)
    (different : left ≠ right) (notLater : left ≠ laterLeft) :
    ¬ IndexRenaming [(laterLeft, laterRight)] (.fvar left) (.fvar right) := by
  rw [IndexRenaming.fvar_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  exact fun related => related.elim different (fun pair => notLater pair.1)

private theorem reversedPairRejected (left right : FVarId) (different : left ≠ right) :
    ¬ IndexRenaming [(right, left)] (.fvar left) (.fvar right) :=
  futurePairRejected left right right left different different

private theorem identityAlongsidePair (left right : FVarId) :
    IndexRenaming [(left, right)] (.fvar left) (.fvar left) := IndexRenaming.refl _ _

private theorem listedNonfunctional (source first second : FVarId) :
    IndexRenaming [(source, first), (source, second)] (.fvar source) (.fvar first) ∧
      IndexRenaming [(source, first), (source, second)] (.fvar source) (.fvar second) :=
  ⟨.fvar (.inr (by simp)), .fvar (.inr (by simp))⟩

private theorem changedConstantRejected (pairs : List (FVarId × FVarId)) :
    ¬ IndexRenaming pairs (.const ``Nat []) (.const ``Bool []) := by
  rw [IndexRenaming.const_iff]
  simp

private theorem changedLevelsRejected (pairs : List (FVarId × FVarId)) :
    ¬ IndexRenaming pairs (.const ``Eq [.zero]) (.const ``Eq [.succ .zero]) := by
  rw [IndexRenaming.const_iff]
  simp

private theorem changedSortRejected (pairs : List (FVarId × FVarId)) :
    ¬ IndexRenaming pairs (.sort .zero) (.sort (.succ .zero)) := by
  rw [IndexRenaming.sort_iff]
  exact Level.noConfusion

private theorem metadataAgreement {pairs : List (FVarId × FVarId)} {left right : Expr} {leftData rightData : MData}
    (related : IndexRenaming pairs (.mdata leftData left) (.mdata rightData right)) : leftData = rightData := by
  cases related
  rfl

private theorem changedMetadataRejected (pairs : List (FVarId × FVarId)) (type : Expr) :
    ¬ IndexRenaming pairs (.mdata tagged type) (.mdata changedTag type) := by
  intro related
  have entries := congrArg KVMap.entries (metadataAgreement related)
  have first := (Prod.mk.inj (List.cons.inj entries).1).2
  have impossible : (1 : Nat) = 2 := DataValue.ofNat.inj first
  omega

private def futureStep (domain value : FVarId) : BinderStep :=
  { role := .index, name := `future, domain := .fvar domain, bi := .default, value := .fvar value }

private theorem ownPairTooLate (left right : FVarId) (different : left ≠ right) :
    ¬ BinderIndexCorrespondence [] [futureStep left left] [futureStep right right] [(left, right)] := by
  intro correspondence
  cases correspondence with
  | index _ _ _ _ _ _ raw _ _ => exact unpairedRejected left right different raw

private theorem reversedDependenciesRejected (left right laterLeft laterRight : FVarId)
    (different : laterLeft ≠ laterRight) :
    ¬ BinderIndexCorrespondence [] [futureStep laterLeft left, futureStep left laterLeft]
      [futureStep laterRight right, futureStep right laterRight] [(left, right), (laterLeft, laterRight)] := by
  intro correspondence
  cases correspondence with
  | index _ _ _ _ _ _ raw _ _ => exact unpairedRejected laterLeft laterRight different raw

private def richDomain (data : MData) (value : Expr) : Expr :=
  .mdata data (.letE `selected sortType value
    (.forallE `function (.app (.lam `alias sortType (.bvar 0) .implicit) value)
      (.app (.proj ``Prod 0 value) (.app (.mvar ⟨`RenamingMeta⟩) (.lit (.natVal 0)))) .strictImplicit) false)

private theorem richDomainRelated {pairs : List (FVarId × FVarId)} {left right : Expr} (data : MData)
    (values : IndexRenaming pairs left right) : IndexRenaming pairs (richDomain data left) (richDomain data right) :=
  .mdata data (.letE `selected false (.sort _) values
    (.forallE `function .strictImplicit (.app (.lam `alias .implicit (.sort _) (.bvar 0)) values)
      (.app (.proj ``Prod 0 values) (.app (.mvar ⟨`RenamingMeta⟩) (.lit (.natVal 0))))))

private theorem richInstantiated (left right : FVarId) (data : MData) :
    IndexRenaming [(left, right)] ((richDomain data (.bvar 0)).instantiate1 (.fvar left))
      ((richDomain data (.bvar 0)).instantiate1 (.fvar right)) :=
  (IndexRenaming.refl _ (richDomain data (.bvar 0))).instantiate1 (.fvar (.inr (by simp)))

private theorem richLooseInstantiated (data : MData) :
    IndexRenaming [] ((richDomain data (.bvar 0)).instantiate1 (.bvar 7))
      ((richDomain data (.bvar 0)).instantiate1 (.bvar 7)) :=
  (IndexRenaming.refl _ (richDomain data (.bvar 0))).instantiate1 (.bvar 7)

private theorem richConsumed (left right : FVarId) (data : MData) :
    ConsumedIndexRenaming [(left, right)] (peelTypeAnnotations (richDomain data (.fvar left)))
      (peelTypeAnnotations (richDomain data (.fvar right))) :=
  ConsumedIndexRenaming.ofRaw (richDomainRelated data (.fvar (.inr (by simp))))

private def wrappedDeep (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) deepDependent true)

private theorem wrappedDeepTrace (data : MData) : WrappedSortTelescope (wrappedDeep data) deepDependent := by
  unfold wrappedDeep
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope deepDependent deepDependent
  exact .telescope deepDependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `RenamingWrapped (wrappedDeep data), header `RenamingAnnotated (.mdata data deepDependent)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨deepDependent, wrappedDeepTrace data⟩
  · exact ⟨deepDependent, .mdata data (.telescope deepDependentShape)⟩

private theorem provedRegisteredRenaming (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderRenamingAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderRenaming 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private theorem nativeDeclarationTypes {pairs : List (FVarId × FVarId)}
    {checkedRoot current : Context} {checkedValue generatedValue checkedDomain generatedDomain : Expr}
    {name : Name} {bi : BinderInfo}
    (checkedDeclared : BinderDeclaredAt checkedRoot checkedValue name (peelTypeAnnotations checkedDomain) bi)
    (generatedDeclared : BinderDeclaredAt current generatedValue name (peelTypeAnnotations generatedDomain) bi)
    (domains : IndexRenaming pairs checkedDomain generatedDomain) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedValue.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedValue.fvarId! = some generatedDecl ∧
      ConsumedIndexRenaming pairs checkedDecl.type generatedDecl.type :=
  checkedDeclared.renamingTypes generatedDeclared domains

private theorem nativeChronologicalHead {pairs finalPairs : List (FVarId × FVarId)}
    {checkedFirst generatedFirst : BinderStep} {checkedTail generatedTail : List BinderStep}
    {checkedRoot current : Context}
    (correspondence : BinderIndexCorrespondence pairs
      (checkedFirst :: checkedTail) (generatedFirst :: generatedTail) finalPairs)
    (index : checkedFirst.role = .index)
    (checkedDeclared : BinderStepsIndexDeclared checkedRoot (checkedFirst :: checkedTail))
    (generatedDeclared : BinderStepsIndexDeclared current (generatedFirst :: generatedTail)) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      ConsumedIndexRenaming pairs checkedDecl.type generatedDecl.type :=
  correspondence.indexHeadTypes index checkedDeclared generatedDeclared

private def sameBinder (leftName rightName : Name) (leftBi rightBi : BinderInfo) : Bool :=
  leftName == rightName && leftBi == rightBi

private def sameLet (leftName rightName : Name) (leftNondep rightNondep : Bool) : Bool :=
  leftName == rightName && leftNondep == rightNondep

private def sameProjection (leftName rightName : Name) (leftIndex rightIndex : Nat) : Bool :=
  leftName == rightName && leftIndex == rightIndex

private def structuralRelated (pairs : List (FVarId × FVarId)) : Expr → Expr → Bool
  | .bvar left, .bvar right => left == right
  | .sort left, .sort right => left == right
  | .const left leftLevels, .const right rightLevels => left == right && leftLevels == rightLevels
  | .lit left, .lit right => left == right
  | .mvar left, .mvar right => left == right
  | .fvar left, .fvar right => left == right || pairs.contains (left, right)
  | .app leftFn leftArg, .app rightFn rightArg =>
    structuralRelated pairs leftFn rightFn && structuralRelated pairs leftArg rightArg
  | .lam leftName leftDomain leftBody leftBi, .lam rightName rightDomain rightBody rightBi =>
    sameBinder leftName rightName leftBi rightBi && structuralRelated pairs leftDomain rightDomain &&
      structuralRelated pairs leftBody rightBody
  | .forallE leftName leftDomain leftBody leftBi, .forallE rightName rightDomain rightBody rightBi =>
    sameBinder leftName rightName leftBi rightBi && structuralRelated pairs leftDomain rightDomain &&
      structuralRelated pairs leftBody rightBody
  | .letE leftName leftDomain leftValue leftBody leftNondep, .letE rightName rightDomain rightValue rightBody rightNondep =>
    sameLet leftName rightName leftNondep rightNondep && structuralRelated pairs leftDomain rightDomain &&
      structuralRelated pairs leftValue rightValue && structuralRelated pairs leftBody rightBody
  | .mdata leftData left, .mdata rightData right =>
    leftData.entries == rightData.entries && structuralRelated pairs left right
  | .proj leftName leftIndex left, .proj rightName rightIndex right =>
    sameProjection leftName rightName leftIndex rightIndex && structuralRelated pairs left right
  | _, _ => false

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          (← readThe Context).lparams false false
        return (stats, checked, result)

private def opening (paramsLeft : Nat) (type : Expr) (values : List Expr) : List BinderStep × Expr :=
  match values with
  | [] => ([], type)
  | value :: values =>
    match type with
    | .forallE name domain body bi =>
      let role := if paramsLeft = 0 then BinderRole.index else .parameter
      let (steps, terminal) := opening (paramsLeft - 1) (body.instantiate1 value) values
      ({ role, name, domain, bi, value } :: steps, terminal)
    | _ => ([], type)

private def checkedIndices (original checked : Context) (stats : InductiveStats) (parent : Nat) : Array Expr :=
  let oldSize := (original.lctx.decls.toList.filterMap id).length
  let offset := stats.params.size + (stats.nindices.toList.take parent).sum
  ((checked.lctx.decls.toList.filterMap id).drop (oldSize + offset)).take stats.nindices[parent]! |>
    List.map LocalDecl.toExpr |>.toArray

private def checkOpening (ctx : Context) (nparams parent : Nat) (type : Expr)
    (params indices : Array Expr) : MetaM (List BinderStep) := do
  let .ok normalized := ((monadLift (TypeChecker.whnf type) : M Expr) ctx)
    | throwError "binder-renaming source normalization failed"
  let values := params.toList ++ indices.toList
  let (steps, terminal) := opening nparams normalized values
  unless steps.length == values.length && terminal == sortType &&
      (steps.take nparams).all (·.role = .parameter) && (steps.drop nparams).all (·.role = .index) &&
      BinderStep.parameterValues steps == params.toList && BinderStep.indexValues steps == indices.toList do
    throwError "binder-renaming opening lost exact ordered substitutions"
  for step in steps do
    let some decl := ctx.lctx.find? step.value.fvarId!
      | throwError "binder-renaming opening refers to undeclared actual binder"
    if parent = 0 || step.role = .index then
      unless structuralRelated [] decl.type step.localDomain &&
          decl.userName == step.name && decl.binderInfo == step.bi do
        throwError "binder-renaming opening lost actual native declaration provenance"
  return steps

private def indexPairs (checked generated : List BinderStep) : List (FVarId × FVarId) :=
  List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
    ((BinderStep.indexValues generated).map Expr.fvarId!)

private def checkDomainBoundary (pairs future : List (FVarId × FVarId)) (checked generated : BinderStep) : MetaM Unit := do
  unless structuralRelated pairs checked.domain generated.domain &&
      structuralRelated pairs checked.localDomain generated.localDomain do
    throwError "binder-renaming domain uses something beyond preceding actual index pairs"
  unless structuralRelated [] checked.domain generated.domain do
    unless !(structuralRelated future checked.domain generated.domain) &&
        !(structuralRelated (pairs.map Prod.swap) checked.domain generated.domain) do
      throwError "binder-renaming domain incorrectly accepts future-only or reversed index pairs"

private def checkCorrespondence (checked generated : List BinderStep) : MetaM Unit := do
  unless checked.length == generated.length do
    throwError "binder-renaming step lengths disagree"
  let mut pairs := []
  for ((first, second), position) in (checked.zip generated).zipIdx do
    unless first.role == second.role && first.name == second.name && first.bi == second.bi do
      throwError "binder-renaming changed a role, binder name or binder info"
    checkDomainBoundary pairs (indexPairs (checked.drop position) (generated.drop position)) first second
    if first.role = .parameter then
      unless structuralRelated [] first.domain second.domain && first.value == second.value do
        throwError "binder-renaming shared parameter record changed"
    else
      unless first.value.isFVar && second.value.isFVar && first.value != second.value do
        throwError "binder-renaming fixture collapsed fresh native index IDs"
      pairs := pairs ++ [(first.value.fvarId!, second.value.fvarId!)]
  unless pairs == indexPairs checked generated do
    throwError "binder-renaming final pairs do not exactly zip actual index histories"

private def checkParent (original checked source : Context) (stats : InductiveStats)
    (types : Array InductiveType) (parent : Nat) (info : RecInfo) : MetaM Unit := do
  let checkedValues := checkedIndices original checked stats parent
  unless checkedValues.size == stats.nindices[parent]! && info.indices.size == checkedValues.size do
    throwError "binder-renaming checked/generated index vectors disagree"
  let checkedSteps ← checkOpening checked stats.params.size parent types[parent]!.type stats.params checkedValues
  let generatedSteps ← checkOpening source stats.params.size parent types[parent]!.type stats.params info.indices
  checkCorrespondence checkedSteps generatedSteps

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, env, infos, source) := stage nparams types ctx
    | throwError "binder-renaming checked/registered fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-renaming fixture changed checked metadata"
  for parent in [:types.size] do
    checkParent ctx checked source stats types parent infos[parent]!
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-renaming fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-renaming fixture changed registered metadata"

private def shapedFamily (elementDomain : Expr) (names : Name) : Expr :=
  .forallE (names ++ `carrier) sortType
    (.forallE (names ++ `element) elementDomain
      (.forallE (names ++ `witness) (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.forallE (names ++ `again)
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .implicit

private def multipleParams : Expr := .forallE `carrier sortType
  (.forallE `pivot (.bvar 0)
    (.forallE `element (.bvar 1)
      (.forallE `witness (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1))
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 3) (.bvar 1) (.bvar 2)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .default) .implicit

private def functionFamily : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `function
      (.forallE `chosen (.bvar 1) (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1)) .implicit)
      (.forallE `again
        (proofEquality
          (.forallE `chosen (.bvar 2) (equalityDomain (.bvar 3) (.bvar 0) (.bvar 2)) .implicit)
          (.bvar 0) (.bvar 0)) sortType .default) .instImplicit) .strictImplicit) .implicit

private def projectionDomain : Expr :=
  .proj ``Prod 0 (mkAppN (.const ``Prod.mk [.succ .zero, .succ .zero])
    #[sortType, sortType, .bvar 0, .bvar 0])

private def actualDependentTypes (ctx : Context) : MetaM Unit := do
  let types := #[header `RenamingActualDependent deepDependent]
  let .ok (stats, checked, _, infos, source) := stage 1 types ctx
    | throwError "binder-renaming actual dependent-type setup failed"
  let checkedValues := checkedIndices ctx checked stats 0
  let generatedValues := infos[0]!.indices
  let allPairs := List.zip (checkedValues.toList.map Expr.fvarId!) (generatedValues.toList.map Expr.fvarId!)
  unless checkedValues.size == 3 && generatedValues.size == 3 do
    throwError "binder-renaming actual dependent-type vectors changed"
  for position in [1, 2] do
    let some first := checked.lctx.find? checkedValues[position]!.fvarId!
      | throwError "binder-renaming actual checked dependent declaration missing"
    let some second := source.lctx.find? generatedValues[position]!.fvarId!
      | throwError "binder-renaming actual generated dependent declaration missing"
    unless !(structuralRelated [] first.type second.type) &&
        structuralRelated (allPairs.take position) first.type second.type &&
        !(structuralRelated (allPairs.drop position) first.type second.type) do
      throwError "binder-renaming native later domains lost unequal IDs or exact prior-pair dependency"

private def shapeFixtures (ctx : Context) : MetaM Unit := do
  let shapes := [
    ("let", Expr.letE `alias sortType (.bvar 0) (.bvar 0) false),
    ("lambda", Expr.app (.lam `alias sortType (.bvar 0) .implicit) (.bvar 0)),
    ("projection", projectionDomain),
    ("metadata", Expr.mdata tagged (mkApp (.const ``outParam [.succ .zero]) (.bvar 0)))]
  for (shape, domain) in shapes do
    for nparams in [0, 1, 2] do
      checkFixture ctx nparams #[header (Name.mkNum (Name.mkSimple ("RenamingShape_" ++ shape)) nparams)
        (shapedFamily domain (Name.mkSimple shape))] #[4 - nparams]
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `RenamingFunctions nparams) functionFamily] #[4 - nparams]

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `RenamingEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `RenamingDeep nparams) deepDependent] #[4 - nparams]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `RenamingMultiple nparams) multipleParams] #[5 - nparams]
  let first := shapedFamily (.bvar 0) `first
  let second := shapedFamily (.mdata tagged (.bvar 0)) `second
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `RenamingMutualFirst nparams) first,
      header (Name.mkNum `RenamingMutualSecond nparams) second] #[4 - nparams, 4 - nparams]
  checkFixture ctx 1 #[header `RenamingWrappedDeep (wrappedDeep tagged)] #[3]
  checkFixture ctx 2 #[header `RenamingWrappedMultiple
    (.mdata tagged (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) multipleParams true))] #[3]
  shapeFixtures ctx
  actualDependentTypes ctx

private def structuralControls : MetaM Unit := do
  let left : FVarId := ⟨`CheckedRenamingIndex⟩
  let right : FVarId := ⟨`GeneratedRenamingIndex⟩
  let laterLeft : FVarId := ⟨`CheckedLaterRenamingIndex⟩
  let laterRight : FVarId := ⟨`GeneratedLaterRenamingIndex⟩
  let pairs := [(left, right)]
  unless structuralRelated pairs (richDomain tagged (.fvar left)) (richDomain tagged (.fvar right)) do
    throwError "binder-renaming all-constructor positive control failed"
  let negatives := [
    ([], Expr.fvar left, Expr.fvar right),
    ([(laterLeft, laterRight)], Expr.fvar left, Expr.fvar right),
    ([(right, left)], Expr.fvar left, Expr.fvar right),
    (pairs, Expr.const ``Nat [], Expr.const ``Bool []),
    (pairs, Expr.const ``Eq [.zero], Expr.const ``Eq [.succ .zero]),
    (pairs, Expr.sort .zero, Expr.sort (.succ .zero)),
    (pairs, Expr.mdata tagged (.fvar left), Expr.mdata changedTag (.fvar right)),
    (pairs, Expr.proj ``Prod 0 (.fvar left), Expr.proj ``Prod 1 (.fvar right)),
    (pairs, Expr.lam `same sortType (.fvar left) .implicit, Expr.lam `same sortType (.fvar right) .default),
    (pairs, Expr.letE `same sortType (.fvar left) (.bvar 0) false,
      Expr.letE `same sortType (.fvar right) (.bvar 0) true)]
  for (context, first, second) in negatives do
    if structuralRelated context first second then
      throwError "binder-renaming structural negative control accepted"

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
  audit ``deepDependentShape
  audit ``deepOpened binding
  audit ``eqRelated
  audit ``deepCorrespondence
  audit ``deepFinalPairs
  audit ``deepDomainsUnequal
  audit ``unpairedRejected
  audit ``futurePairRejected
  audit ``reversedPairRejected
  audit ``identityAlongsidePair
  audit ``listedNonfunctional
  audit ``changedConstantRejected
  audit ``changedLevelsRejected
  audit ``changedSortRejected
  audit ``metadataAgreement
  audit ``changedMetadataRejected
  audit ``ownPairTooLate
  audit ``reversedDependenciesRejected
  audit ``richDomainRelated
  audit ``richInstantiated binding
  audit ``richLooseInstantiated binding
  audit ``richConsumed
  audit ``wrappedDeepTrace binding
  audit ``provedHeaders binding
  audit ``nativeDeclarationTypes
  audit ``nativeChronologicalHead
  audit ``IndexRenaming.refl
  audit ``IndexRenaming.mono
  audit ``IndexRenaming.liftLooseBVars'
  audit ``IndexRenaming.instantiate1'
  audit ``IndexRenaming.instantiate1 binding
  audit ``IndexRenaming.binderSignature
  audit ``IndexRenaming.fvar_iff
  audit ``IndexRenaming.const_iff
  audit ``IndexRenaming.sort_iff
  audit ``ConsumedIndexRenaming.ofRaw
  audit ``ConsumedIndexRenaming.mono
  audit ``BinderDeclaredAt.fvar
  audit ``BinderIndexCorrespondence.finalPairs
  audit ``OpenedTelescope.relatedIndexCorrespondence binding
  audit ``OpenedTelescope.pairedIndices binding
  audit ``OpenedTelescope.indexCorrespondence binding
  audit ``BinderDeclaredAt.renamingTypes
  audit ``BinderIndexCorrespondence.indexHeadTypes
  audit ``ParentBinderPrefixAlignment.toBinderRenaming binding
  audit ``RecursorBinderPrefixAlignment.toBinderRenaming binding
  audit ``ParentBinderRenamingAlignment.toBinderPrefixes
  audit ``RecursorBinderRenamingAlignment.toBinderPrefixes
  audit ``CheckedHeaderSources.normalizedBinderRenaming (binding ++ scope)
  audit ``CheckedHeaderSources.wrappedBinderRenaming (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderRenaming (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderRenaming (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderRenaming
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderRenaming (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderRenaming (normalized ++ scope)
  audit ``provedRegisteredRenaming (normalized ++ scope)
  structuralControls
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderRenamingSeed, idx := 43 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderRenamingSeed 42⟩ `old (.const ``Bool []) .implicit }
  let .ok (_, _, extendedEnv, _, _) := stage 0 #[header `RenamingReaderExtension sortType] ctx
    | throwError "binder-renaming reader-extension setup failed"
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherRenamingSeed, idx := 71 } },
      { ctx with lparams := [`u] }, { ctx with env := extendedEnv }] do
    fixtures reader
  logInfo "160 full registration fixtures preserve exact preceding actual index pairs and native consumed-domain provenance across 175 parent pairs/five readers; five additional registered boundaries retain ten actual unequal later-domain types"

end InductiveBinderRenamingTest
