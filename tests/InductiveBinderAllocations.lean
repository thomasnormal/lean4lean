import Lean4Lean.Verify.InductiveBinderAllocationAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.recursorIndexSize from Lean4Lean.Verify.InductiveBinderAllocations

namespace InductiveBinderAllocationsTest

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def tagged : MData := { entries := [(`BinderAllocationTag, .ofNat 1)] }

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
  header `AllocationWrapped (wrappedDeep data), header `AllocationAnnotated (.mdata data deepDependent)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨deepDependent, wrappedDeepTrace data⟩
  · exact ⟨deepDependent, .mdata data (.telescope deepDependentShape)⟩

private theorem provedRegisteredAllocations (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderAllocationAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderAllocations 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private def indexStep (name : Name) (domain value : Expr) : BinderStep :=
  { role := .index, name, domain, bi := .default, value }

private def parameterStep (value : Expr) : BinderStep :=
  { role := .parameter, name := `shared, domain := sortType, bi := .implicit, value }

private theorem emptyAllocations (ctx : Context) (start : Nat) : BinderIndexAllocations ctx start [] := trivial

private theorem parameterSkipsPosition (ctx : Context) (start : Nat) (value : Expr) :
    BinderIndexAllocations ctx start [parameterStep value] := trivial

private theorem parametersKeepIndexBase (ctx : Context) (start : Nat) (first second : Expr) (steps : List BinderStep)
    (allocated : BinderIndexAllocations ctx start steps) :
    BinderIndexAllocations ctx start (parameterStep first :: parameterStep second :: steps) := allocated

private theorem repeatedIndexRejected (ctx : Context) (start : Nat) (id : FVarId) :
    ¬ BinderIndexAllocations ctx start
      [indexStep `first (.const ``Nat []) (.fvar id), indexStep `second (.const ``Nat []) (.fvar id)] := by
  intro allocated
  have distinct := allocated.indexIdsNodup
  simp [indexStep, BinderStep.indexValues, Expr.fvarId!] at distinct

private theorem fakePositionRejected {ctx : Context} {value domain : Expr} {name : Name}
    {bi : BinderInfo} {position : Nat}
    (positioned : BinderPositionedAt ctx value name domain bi position) :
    ¬ BinderPositionedAt ctx value name domain bi (position + 1) := by
  intro fake
  have impossible := positioned.index_eq_of_id_eq fake rfl
  omega

private theorem chronologicalPosition {ctx : Context} {start ordinal : Nat}
    {steps : List BinderStep} {value : Expr} (allocated : BinderIndexAllocations ctx start steps)
    (atOrdinal : (BinderStep.indexValues steps)[ordinal]? = some value) :
    ∃ step ∈ steps, step.role = .index ∧ step.value = value ∧
      BinderPositionedAt ctx step.value step.name step.localDomain step.bi (start + ordinal) :=
  allocated.positioned atOrdinal

private def firstReader (ctx : Context) : Context :=
  recursorIndexContext ctx `first .default (Expr.const ``Nat []).consumeTypeAnnotations

private def secondReader (ctx : Context) : Context :=
  recursorIndexContext (firstReader ctx) `second .default (Expr.const ``Nat []).consumeTypeAnnotations

private def nativeSteps (ctx : Context) : List BinderStep := [
  indexStep `first (.const ``Nat []) (.fvar ⟨ctx.ngen.curr⟩),
  indexStep `second (.const ``Nat []) (.fvar ⟨(firstReader ctx).ngen.curr⟩)]

private theorem nativeTwoIndexAllocations (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    BinderIndexAllocations (secondReader ctx) ctx.lctx.decls.size (nativeSteps ctx) := by
  let firstFrame := Context.RecursorScopeFrame.push ctx hwf hreserved `first .default
    (Expr.const ``Nat []).consumeTypeAnnotations
  let secondFrame := Context.RecursorScopeFrame.push (firstReader ctx) firstFrame.wf firstFrame.reserved
    `second .default (Expr.const ``Nat []).consumeTypeAnnotations
  have firstPosition := newlyAllocatedBinderPositioned ctx `first (.const ``Nat []) .default hwf hreserved
  have secondPosition := newlyAllocatedBinderPositioned (firstReader ctx) `second (.const ``Nat [])
    .default firstFrame.wf firstFrame.reserved
  change BinderPositionedAt (secondReader ctx) (.fvar ⟨ctx.ngen.curr⟩) `first
      (Expr.const ``Nat []).consumeTypeAnnotations .default ctx.lctx.decls.size ∧
    BinderPositionedAt (secondReader ctx) (.fvar ⟨(firstReader ctx).ngen.curr⟩) `second
      (Expr.const ``Nat []).consumeTypeAnnotations .default (ctx.lctx.decls.size + 1) ∧ True
  refine ⟨firstPosition.mono firstFrame.wf secondFrame, ?_, trivial⟩
  simpa only [firstReader, Lean4Lean.AddInductive.recursorIndexSize] using secondPosition

private theorem nativeIndexIdsDistinct (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ((BinderStep.indexValues (nativeSteps ctx)).map Expr.fvarId!).Nodup :=
  (nativeTwoIndexAllocations ctx hwf hreserved).indexIdsNodup

private theorem actualPairZipInjection {checkedRoot generatedRoot : Context} {checkedStart generatedStart : Nat}
    {checked generated : List BinderStep}
    (checkedAllocations : BinderIndexAllocations checkedRoot checkedStart checked)
    (generatedAllocations : BinderIndexAllocations generatedRoot generatedStart generated) :
    IndexPairInjection (List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
      ((BinderStep.indexValues generated).map Expr.fvarId!)) :=
  .of_zip checkedAllocations.indexIdsNodup generatedAllocations.indexIdsNodup

private theorem exactZipProjections {left right : List FVarId} (sameLength : left.length = right.length) :
    (left.zip right).map Prod.fst = left ∧ (left.zip right).map Prod.snd = right :=
  indexZipExactProjections sameLength

private theorem unequalZipTruncates (first second target : FVarId) :
    ([first, second].zip [target]).map Prod.fst = [first] ∧
      ([first, second].zip [target]).map Prod.snd = [target] := ⟨rfl, rfl⟩

private theorem zipFunctional {pairs : List (FVarId × FVarId)} {left first second : FVarId}
    (injection : IndexPairInjection pairs) (firstPair : (left, first) ∈ pairs)
    (secondPair : (left, second) ∈ pairs) : first = second := injection.functional firstPair secondPair

private theorem zipInjective {pairs : List (FVarId × FVarId)} {first second right : FVarId}
    (injection : IndexPairInjection pairs) (firstPair : (first, right) ∈ pairs)
    (secondPair : (second, right) ∈ pairs) : first = second := injection.injective firstPair secondPair

private theorem duplicateSourceRejected (source first second : FVarId) :
    ¬ IndexPairInjection [(source, first), (source, second)] := by
  simp [IndexPairInjection]

private theorem duplicateTargetRejected (first second target : FVarId) :
    ¬ IndexPairInjection [(first, target), (second, target)] := by
  simp [IndexPairInjection]

private theorem duplicatePairRejected (source target : FVarId) :
    ¬ IndexPairInjection [(source, target), (source, target)] := duplicateSourceRejected source target target

private theorem singletonInjection (source target : FVarId) : IndexPairInjection [(source, target)] := by
  simp [IndexPairInjection]

private theorem overlappingInjection (left right : FVarId) (different : left ≠ right) :
    IndexPairInjection [(left, right), (right, left)] ∧
      left ∈ ([(left, right), (right, left)] : List (FVarId × FVarId)).map Prod.fst ∧
      left ∈ ([(left, right), (right, left)] : List (FVarId × FVarId)).map Prod.snd := by
  simp [IndexPairInjection, different, Ne.symm different]

private theorem injectiveZipNotGlobalDeterminism (left right : FVarId) (different : left ≠ right) :
    IndexPairInjection [(left, right)] ∧ IndexRenaming [(left, right)] (.fvar left) (.fvar left) ∧
      IndexRenaming [(left, right)] (.fvar left) (.fvar right) ∧ Expr.fvar left ≠ .fvar right := by
  exact ⟨singletonInjection left right, IndexRenaming.refl _ _, .fvar (.inr (by simp)),
    fun equal => different (Expr.fvar.inj equal)⟩

private theorem parentRetainsRenaming {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedRoot generatedRoot : Context} {info : RecInfo}
    (alignment : ParentBinderAllocationAlignment stats types parent checkedRoot generatedRoot info) :
    ParentBinderRenamingAlignment stats types parent checkedRoot generatedRoot info := alignment.toBinderRenaming

private theorem recursorsRetainRenaming {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot generatedRoot : Context} {infos : Array RecInfo}
    (alignment : RecursorBinderAllocationAlignment stats types checkedRoot generatedRoot infos) :
    RecursorBinderRenamingAlignment stats types checkedRoot generatedRoot infos := alignment.toBinderRenaming

private theorem fullActualZipProjections {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedRoot generatedRoot : Context} {info : RecInfo}
    (alignment : ParentBinderAllocationAlignment stats types parent checkedRoot generatedRoot info) :
    ∃ checkedIds pairs,
      checkedIds.length = stats.nindices[parent]! ∧
      pairs = checkedIds.zip (info.indices.toList.map Expr.fvarId!) ∧
      pairs.map Prod.fst = checkedIds ∧ pairs.map Prod.snd = info.indices.toList.map Expr.fvarId! ∧
      IndexPairInjection pairs := alignment.injectiveIndexZip

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

private def hasPosition (ctx : Context) (value : Expr) (position : Nat) : Bool :=
  if position < ctx.lctx.numIndices then
    match ctx.lctx.find? value.fvarId!, ctx.lctx.getAt? position with
    | some byId, some byPosition =>
      value.isFVar && byId.toExpr == value && byId.index == position &&
        byPosition.index == position && byPosition.fvarId == byId.fvarId
    | _, _ => false
  else false

private def checkPosition (ctx : Context) (value : Expr) (position : Nat) : MetaM LocalDecl := do
  unless hasPosition ctx value position do
    throwError "binder-allocation actual find?/getAt? position disagrees"
  let some decl := ctx.lctx.find? value.fvarId!
    | throwError "binder-allocation actual declaration missing"
  unless !(hasPosition ctx value (position + 1)) do
    throwError "binder-allocation accepted an incorrect native position"
  return decl

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    unless start + offset < ctx.lctx.numIndices do
      throwError "binder-allocation checked allocation exceeds reader"
    let some decl := ctx.lctx.getAt? (start + offset)
      | throwError "binder-allocation checked allocation points at a hole"
    discard <| checkPosition ctx decl.toExpr (start + offset)
    values := values.push decl.toExpr
  return values

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

private def checkOpening (ctx : Context) (parameterStart indexStart nparams parent : Nat) (type : Expr)
    (params indices : Array Expr) : MetaM (List BinderStep) := do
  let .ok normalized := ((monadLift (TypeChecker.whnf type) : M Expr) ctx)
    | throwError "binder-allocation source normalization failed"
  let (steps, terminal) := opening nparams normalized (params.toList ++ indices.toList)
  unless steps.length == params.size + indices.size && terminal == sortType &&
      BinderStep.parameterValues steps == params.toList && BinderStep.indexValues steps == indices.toList &&
      (steps.take nparams).all (·.role = .parameter) && (steps.drop nparams).all (·.role = .index) do
    throwError "binder-allocation opening lost exact ordered substitutions"
  let mut parameterOffset := 0
  let mut indexOffset := 0
  for step in steps do
    let position := if step.role = .parameter then parameterStart + parameterOffset else indexStart + indexOffset
    let decl ← checkPosition ctx step.value position
    if step.role = .parameter then
      parameterOffset := parameterOffset + 1
    else
      indexOffset := indexOffset + 1
    if parent = 0 || step.role = .index then
      unless decl.type == step.localDomain && decl.userName == step.name && decl.binderInfo == step.bi do
        throwError "binder-allocation actual domain/name/binder-info anchor changed"
  unless parameterOffset == nparams && indexOffset == indices.size do
    throwError "binder-allocation parameter skips or index increments changed"
  return steps

private def injectiveZip (pairs : List (FVarId × FVarId)) : Bool :=
  let first := pairs.map Prod.fst
  let second := pairs.map Prod.snd
  first.eraseDups.length == first.length && second.eraseDups.length == second.length

private def checkPairZip (checked generated : Array Expr) : MetaM Unit := do
  let pairs := List.zip (checked.toList.map Expr.fvarId!) (generated.toList.map Expr.fvarId!)
  unless checked.size == generated.size && pairs.length == checked.size && injectiveZip pairs do
    throwError "binder-allocation actual pair zip is not injective in both coordinates"
  for (first, second) in pairs do
    unless (pairs.filter (·.1 == first)).all (·.2 == second) &&
        (pairs.filter (·.2 == second)).all (·.1 == first) do
      throwError "binder-allocation actual pair zip is not functional in both directions"
    unless first != second do
      throwError "binder-allocation same-CPS fixture collapsed actual fresh IDs"

private def checkPreservedSlots (original checked generated : Context) : MetaM Unit := do
  for position in [:original.lctx.numIndices] do
    match original.lctx.getAt? position with
    | none =>
      unless (checked.lctx.getAt? position).isNone && (generated.lctx.getAt? position).isNone do
        throwError "binder-allocation filled an old erased slot"
    | some old =>
      discard <| checkPosition checked old.toExpr position
      discard <| checkPosition generated old.toExpr position

private def checkParent (original checked generatorRoot generated : Context) (stats : InductiveStats)
    (types : Array InductiveType) (parent : Nat) (info : RecInfo) : MetaM Unit := do
  let preceding := (stats.nindices.toList.take parent).sum
  let checkedStart := original.lctx.numIndices + stats.params.size + preceding
  let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
  let checkedValues ← valuesAt checked checkedStart stats.nindices[parent]!
  let checkedSteps ← checkOpening checked original.lctx.numIndices checkedStart stats.params.size parent
    types[parent]!.type stats.params checkedValues
  let generatedSteps ← checkOpening generated original.lctx.numIndices generatedStart stats.params.size parent
    types[parent]!.type stats.params info.indices
  unless (checkedSteps.take stats.params.size).map BinderStep.value ==
      (generatedSteps.take stats.params.size).map BinderStep.value do
    throwError "binder-allocation reused shared parameter values changed"
  checkPairZip checkedValues info.indices
  discard <| checkPosition generated info.major (generatedStart + info.indices.size)
  discard <| checkPosition generated info.motive (generatedStart + info.indices.size + 1)

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "binder-allocation checked/registered fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size &&
      checked.lctx.numIndices == ctx.lctx.numIndices + nparams + expected.toList.sum &&
      generatorRoot.lctx.numIndices == checked.lctx.numIndices &&
      generated.lctx.numIndices == generatorRoot.lctx.numIndices + expected.toList.sum + 2 * types.size do
    throwError "binder-allocation native dense allocation arithmetic changed"
  unless stats.lctx.numIndices == ctx.lctx.numIndices + nparams + expected[0]! do
    throwError "binder-allocation first-parent snapshot changed"
  checkPreservedSlots ctx checked generated
  for parent in [:types.size] do
    checkParent ctx checked generatorRoot generated stats types parent infos[parent]!
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-allocation fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-allocation registered metadata changed"

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
  checkFixture ctx 0 #[header `AllocationEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `AllocationDeep nparams) deepDependent] #[4 - nparams]
  for nparams in [0, 1, 2, 3, 4, 5] do
    checkFixture ctx nparams #[header (Name.mkNum `AllocationMultiple nparams) multipleParams] #[5 - nparams]
  for nparams in [0, 1, 2] do
    checkFixture ctx nparams #[header (Name.mkNum `AllocationMutualFirst nparams) (family `first false),
      header (Name.mkNum `AllocationMutualSecond nparams) (family `second true)] #[4 - nparams, 4 - nparams]
  checkFixture ctx 0 #[header `AllocationIndependentNat natIndices] #[2]
  checkFixture ctx 0 #[header `AllocationEmptyLeading sortType, header `AllocationDeepFollowing deepDependent] #[0, 4]
  checkFixture ctx 4 #[header `AllocationAllParametersFirst deepDependent,
    header `AllocationAllParametersSecond (family `shared false)] #[0, 0]
  checkFixture ctx 1 #[header `AllocationWrappedDeep (wrappedDeep tagged)] #[3]
  checkFixture ctx 1 #[header `AllocationMetadata (family `marked true)] #[3]

private def holeBoundaries (ctx : Context) : MetaM Unit := do
  for erased in [ctx.lctx.erase ⟨.num `BinderAllocationSeed 41⟩,
      (ctx.lctx.erase ⟨.num `BinderAllocationSeed 40⟩).erase ⟨.num `BinderAllocationSeed 41⟩] do
    let reader := { ctx with lctx := erased }
    unless reader.lctx.numIndices == 3 && (reader.lctx.decls.toList.filterMap id).length < 3 do
      throwError "binder-allocation unchecked hole-reader setup failed"
    checkFixture reader 1 #[header `AllocationUncheckedHole deepDependent] #[3]
    checkFixture reader 1 #[header `AllocationUncheckedHoleFirst (family `first false),
      header `AllocationUncheckedHoleSecond (family `second true)] #[3, 3]
  logInfo "four unchecked erased-slot registrations preserve native size-based positions; these readers have no LocalContext.WF receipt"

private def differentReaderBoundary (ctx : Context) : MetaM Unit := do
  let types := #[header `AllocationDifferentReaders natIndices]
  let .ok (stats, _, generatorRoot, _, _, _) := stage 0 types ctx
    | throwError "binder-allocation different-reader setup failed"
  let other := { generatorRoot with lparams := [`DifferentAllocationReader] }
  let .ok first := mkRecInfos stats types (.succ .zero) pure generatorRoot
    | throwError "binder-allocation first independent helper failed"
  let .ok second := mkRecInfos stats types (.succ .zero) pure other
    | throwError "binder-allocation second independent helper failed"
  let pairs := List.zip (first[0]!.indices.toList.map Expr.fvarId!) (second[0]!.indices.toList.map Expr.fvarId!)
  unless generatorRoot.lparams != other.lparams && pairs.length == 2 &&
      injectiveZip pairs && pairs.all (fun pair => pair.1 == pair.2) do
    throwError "binder-allocation different readers incorrectly imply disjoint ID sets"

private def duplicateControls : MetaM Unit := do
  let first : FVarId := ⟨`AllocationFirst⟩
  let second : FVarId := ⟨`AllocationSecond⟩
  let third : FVarId := ⟨`AllocationThird⟩
  unless injectiveZip [(first, second), (second, first)] && injectiveZip [(first, first)] do
    throwError "binder-allocation injective overlapping/identity pair controls failed"
  for pairs in [[(first, second), (first, third)], [(first, third), (second, third)],
      [(first, second), (first, second)]] do
    if injectiveZip pairs then
      throwError "binder-allocation duplicate source/target/pair control accepted"

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
  audit ``wrappedDeepTrace binding
  audit ``provedHeaders binding
  audit ``provedRegisteredAllocations (normalized ++ scope)
  audit ``emptyAllocations
  audit ``parameterSkipsPosition
  audit ``parametersKeepIndexBase
  audit ``repeatedIndexRejected
  audit ``fakePositionRejected
  audit ``chronologicalPosition
  audit ``nativeTwoIndexAllocations scope
  audit ``nativeIndexIdsDistinct scope
  audit ``actualPairZipInjection
  audit ``exactZipProjections
  audit ``unequalZipTruncates
  audit ``zipFunctional
  audit ``zipInjective
  audit ``duplicateSourceRejected
  audit ``duplicateTargetRejected
  audit ``duplicatePairRejected
  audit ``singletonInjection
  audit ``overlappingInjection
  audit ``injectiveZipNotGlobalDeterminism
  audit ``parentRetainsRenaming
  audit ``recursorsRetainRenaming
  audit ``fullActualZipProjections
  audit ``BinderPositionedAt.declared
  audit ``BinderPositionedAt.mono scope
  audit ``BinderPositionedAt.index_eq_of_id_eq
  audit ``newlyAllocatedBinderPositioned scope
  audit ``BinderIndexAllocations.mono scope
  audit ``BinderIndexAllocations.declared
  audit ``BinderIndexAllocations.positioned
  audit ``BinderIndexAllocations.indexIdsNodup
  audit ``indexZipProjections
  audit ``indexZipExactProjections
  audit ``IndexPairInjection.of_zip
  audit ``IndexPairInjection.functional
  audit ``IndexPairInjection.injective
  audit ``CheckedHeaderTrace.openedAllocations (binding ++ scope)
  audit ``RecursorIndexTrace.openedAllocations (binding ++ scope)
  audit ``CheckedHeaderSource.openedAllocations_of_normalized (binding ++ scope)
  audit ``RecursorInfoIndexSource.openedAllocations_of_normalized (binding ++ scope)
  audit ``ParentBinderAllocationAlignment.toBinderRenaming
  audit ``RecursorBinderAllocationAlignment.toBinderRenaming
  audit ``ParentBinderAllocationAlignment.injectiveIndexZip
  audit ``CheckedHeaderSources.normalizedBinderAllocations (binding ++ scope)
  audit ``CheckedHeaderSources.wrappedBinderAllocations (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderAllocations (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderAllocations (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderAllocations
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderAllocations (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderAllocations (normalized ++ scope)
  duplicateControls
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let firstLocals := ctx.lctx.mkLocalDecl ⟨.num `BinderAllocationSeed 40⟩ `oldNat (.const ``Nat []) .implicit
  let secondLocals := firstLocals.mkLocalDecl ⟨.num `BinderAllocationSeed 41⟩ `oldBool (.const ``Bool []) .default
  let seeded := { ctx with
    ngen := { namePrefix := `BinderAllocationSeed, idx := 43 }
    lctx := secondLocals.mkLetDecl ⟨.num `BinderAllocationSeed 42⟩ `oldLet
      (.const ``Nat []) (.lit (.natVal 7)) false }
  let .ok (_, _, _, extendedEnv, _, _) := stage 0 #[header `AllocationReaderExtension sortType] ctx
    | throwError "binder-allocation reader-extension setup failed"
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherAllocationSeed, idx := 71 } },
      { ctx with lparams := [`u] }, { ctx with env := extendedEnv }] do
    fixtures reader
  holeBoundaries seeded
  differentReaderBoundary ctx
  logInfo "100 dense-reader full registration fixtures preserve ordered native allocation positions and injective actual index-ID zips across 125 parent pairs/250 opening plans/five readers"

end InductiveBinderAllocationsTest
