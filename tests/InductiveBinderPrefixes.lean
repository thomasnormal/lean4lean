import Lean4Lean.Verify.InductiveBinderPrefixAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderPrefixesTest

abbrev PrefixCarrierAlias := Type

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def dependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) sortType .instImplicit)
      .strictImplicit) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) .instImplicit (.sort (.succ .zero))))

private def dependentSteps (carrier element witness : FVarId) : List BinderStep := [
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar carrier },
  { role := .index, name := `element, domain := .fvar carrier, bi := .strictImplicit, value := .fvar element },
  { role := .index, name := `witness, domain := equalityDomain (.fvar carrier) (.fvar element) (.fvar element),
    bi := .instImplicit, value := .fvar witness }]

private theorem dependentOpened (carrier element witness : FVarId) :
    OpenedTelescope dependent (dependentSteps carrier element witness) sortType := by
  unfold dependent dependentSteps
  apply OpenedTelescope.bind .parameter `carrier sortType .implicit (.fvar carrier)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `element (.fvar carrier)
      (.forallE `witness (equalityDomain (.fvar carrier) (.bvar 0) (.bvar 0)) sortType .instImplicit)
        .strictImplicit) _ sortType
  apply OpenedTelescope.bind .index `element (.fvar carrier) .strictImplicit (.fvar element)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `witness (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) sortType .instImplicit)
    _ sortType
  apply OpenedTelescope.bind .index `witness
    (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) .instImplicit (.fvar witness)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope sortType [] sortType
  exact .sort (.succ .zero)

private theorem concretePrefixAgreement (carrier first second firstWitness secondWitness : FVarId) :
    (dependentSteps carrier first firstWitness).take 1 = (dependentSteps carrier second secondWitness).take 1 ∧
      (((dependentSteps carrier first firstWitness).drop 1).head?).map BinderStep.domain =
        (((dependentSteps carrier second secondWitness).drop 1).head?).map BinderStep.domain :=
  (dependentOpened carrier first firstWitness).samePrefixAndNextDomain
    (dependentOpened carrier second secondWitness) 1 rfl rfl

private theorem concreteFirstLocalDomain (carrier first second firstWitness secondWitness : FVarId) :
    (((dependentSteps carrier first firstWitness).drop 1).head?).map BinderStep.localDomain =
      (((dependentSteps carrier second secondWitness).drop 1).head?).map BinderStep.localDomain :=
  (dependentOpened carrier first firstWitness).sameNextLocalDomain
    (dependentOpened carrier second secondWitness) 1 rfl rfl

private theorem concreteOrderedPrefix (carrier first second firstWitness secondWitness : FVarId) :
    (dependentSteps carrier first firstWitness).take 1 = (dependentSteps carrier second secondWitness).take 1 ∧
      (((dependentSteps carrier first firstWitness).drop 1).head?).map BinderStep.domain =
        (((dependentSteps carrier second secondWitness).drop 1).head?).map BinderStep.domain :=
  OpenedTelescope.sameParameterPrefix (count := 1) (leftIndices := 2) (rightIndices := 2)
    (dependentOpened carrier first firstWitness) (dependentOpened carrier second secondWitness) rfl rfl rfl

example (carrier element witness : FVarId) :
    ((dependentSteps carrier element witness).take 1).map BinderStep.value =
      BinderStep.parameterValues (dependentSteps carrier element witness) ∧
    ((dependentSteps carrier element witness).take 1).map BinderStep.role = List.replicate 1 .parameter :=
  BinderStep.parameterPrefix (dependentSteps carrier element witness) 1 2 rfl

private theorem secondDomainDifferent (carrier first second firstWitness secondWitness : FVarId)
    (hdifferent : first ≠ second) :
    (((dependentSteps carrier first firstWitness).drop 2).head?).map BinderStep.domain ≠
      (((dependentSteps carrier second secondWitness).drop 2).head?).map BinderStep.domain := by
  intro hequal
  change some (equalityDomain (.fvar carrier) (.fvar first) (.fvar first)) =
    some (equalityDomain (.fvar carrier) (.fvar second) (.fvar second)) at hequal
  exact hdifferent (Expr.fvar.inj (Expr.app.inj (Option.some.inj hequal)).2)

private def interleavedSteps (carrier element witness : FVarId) : List BinderStep := [
  { role := .index, name := `carrier, domain := sortType, bi := .implicit, value := .fvar carrier },
  { role := .parameter, name := `element, domain := .fvar carrier, bi := .strictImplicit, value := .fvar element },
  { role := .index, name := `witness, domain := equalityDomain (.fvar carrier) (.fvar element) (.fvar element),
    bi := .instImplicit, value := .fvar witness }]

private theorem interleavedOpened (carrier element witness : FVarId) :
    OpenedTelescope dependent (interleavedSteps carrier element witness) sortType := by
  unfold dependent interleavedSteps
  apply OpenedTelescope.bind .index `carrier sortType .implicit (.fvar carrier)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `element (.fvar carrier)
      (.forallE `witness (equalityDomain (.fvar carrier) (.bvar 0) (.bvar 0)) sortType .instImplicit)
        .strictImplicit) _ sortType
  apply OpenedTelescope.bind .parameter `element (.fvar carrier) .strictImplicit (.fvar element)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `witness (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) sortType .instImplicit)
    _ sortType
  apply OpenedTelescope.bind .index `witness
    (equalityDomain (.fvar carrier) (.fvar element) (.fvar element)) .instImplicit (.fvar witness)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope sortType [] sortType
  exact .sort (.succ .zero)

example (carrier element witness : FVarId) :
    (interleavedSteps carrier element witness).map BinderStep.role ≠ [.parameter, .index, .index] := by
  intro hequal
  change [BinderRole.index, .parameter, .index] = [.parameter, .index, .index] at hequal
  cases (List.cons.inj hequal).1

example {type leftTerminal rightTerminal : Expr} {left right : List BinderStep}
    (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal) (count : Nat)
    (hvalues : (left.take count).map BinderStep.value = (right.take count).map BinderStep.value)
    (hroles : (left.take count).map BinderStep.role = (right.take count).map BinderStep.role) :
    left.take count = right.take count := leftOpened.samePrefix rightOpened count hvalues hroles

example {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderPrefixAlignment stats types parent checkedRoot current info) :
    ParentBinderDomainAlignment stats types parent checkedRoot current info := alignment.toBinderDomains

example {stats : InductiveStats} {types : Array InductiveType} {checkedRoot current : Context}
    {infos : Array RecInfo} (alignment : RecursorBinderPrefixAlignment stats types checkedRoot current infos) :
    RecursorBinderDomainAlignment stats types checkedRoot current infos := alignment.toBinderDomains

example {checkedRoot current : Context} {checked generated : List BinderStep}
    {nparams checkedCount generatedCount : Nat} {checkedFirst generatedFirst : BinderStep}
    (hcheckedDeclared : BinderStep.IndexDomainsDeclared checkedRoot checked)
    (hgeneratedDeclared : BinderStep.IndexDomainsDeclared current generated)
    (hcheckedRoles : checked.map BinderStep.role = List.replicate nparams .parameter ++
      List.replicate checkedCount .index)
    (hgeneratedRoles : generated.map BinderStep.role = List.replicate nparams .parameter ++
      List.replicate generatedCount .index)
    (hcheckedFirst : (checked.drop nparams).head? = some checkedFirst)
    (hgeneratedFirst : (generated.drop nparams).head? = some generatedFirst)
    (hdomains : ((checked.drop nparams).head?).map BinderStep.localDomain =
      ((generated.drop nparams).head?).map BinderStep.localDomain) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      checkedDecl.type = generatedDecl.type :=
  hcheckedDeclared.firstIndexTypeAgreement hgeneratedDeclared hcheckedRoles hgeneratedRoles
    hcheckedFirst hgeneratedFirst hdomains

private def tagged : MData := ({} : MData).insert `BinderPrefixTag (.ofString "first-index")

private def wrappedDependent (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private theorem wrappedDependentTrace (data : MData) :
    WrappedSortTelescope (wrappedDependent data) dependent := by
  unfold wrappedDependent
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

example (data : MData) : declareConstructors.arity 0 (wrappedDependent data) = 0 := rfl

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `PrefixWrapped (wrappedDependent data), header `PrefixAnnotated (.mdata data dependent)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent hparent
  have hcases : parent = 0 ∨ parent = 1 := by
    have hbound : parent < 2 := by simpa [provedTypes] using hparent
    omega
  rcases hcases with rfl | rfl
  · exact ⟨dependent, wrappedDependentTrace data⟩
  · exact ⟨dependent, .mdata data (.telescope dependentShape)⟩

private theorem provedRegisteredPrefixes (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderPrefixAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderPrefixes 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

private def family (firstDomain : Expr) (names : Name) (marked : Bool) : Expr :=
  let elementDomain := if marked then .mdata tagged
    (mkApp (.const ``outParam [.succ .zero]) (.bvar 0)) else .bvar 0
  let witnessDomain := if marked then .mdata tagged
    (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) else equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)
  .forallE (names ++ `carrier) firstDomain
    (.forallE (names ++ `element) elementDomain
      (.forallE (names ++ `witness) witnessDomain sortType .instImplicit) .strictImplicit) .implicit

private def multipleParams (firstDomain : Expr) (names : Name) : Expr :=
  .forallE (names ++ `carrier) firstDomain
    (.forallE (names ++ `pivot) (.bvar 0)
      (.forallE (names ++ `element) (.bvar 1)
        (.forallE (names ++ `witness) (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1)) sortType .instImplicit)
          .strictImplicit) .default) .implicit

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

private def rolesOrdered (nparams : Nat) (steps : List BinderStep) : Bool :=
  (steps.take nparams).all (·.role = .parameter) && (steps.drop nparams).all (·.role = .index)

private def checkOpening (ctx : Context) (nparams parent : Nat) (type : Expr)
    (params indices : Array Expr) : MetaM (List BinderStep) := do
  let .ok normalized := ((monadLift (TypeChecker.whnf type) : M Expr) ctx)
    | throwError "binder-prefix source normalization failed"
  let values := params.toList ++ indices.toList
  let (steps, terminal) := opening nparams normalized values
  unless steps.length == values.length && terminal == sortType && rolesOrdered nparams steps &&
      BinderStep.parameterValues steps == params.toList && BinderStep.indexValues steps == indices.toList do
    throwError "binder-prefix opening lost exact ordered substitutions"
  for step in steps do
    let some decl := ctx.lctx.find? step.value.fvarId!
      | throwError "binder-prefix opening refers to undeclared actual binder"
    if parent = 0 || step.role = .index then
      unless decl.type == step.localDomain && decl.userName == step.name && decl.binderInfo == step.bi do
        throwError "binder-prefix opening lost its own local declaration anchor"
  return steps

private def checkParameterSteps (nparams : Nat) (checked generated : List BinderStep) : MetaM Unit := do
  let checkedPrefix := checked.take nparams
  let generatedPrefix := generated.take nparams
  unless checkedPrefix.length == nparams && generatedPrefix.length == nparams do
    throwError "binder-prefix parameter steps are incomplete"
  for (first, second) in checkedPrefix.zip generatedPrefix do
    unless first.role = second.role && first.name == second.name && first.domain == second.domain &&
        first.bi == second.bi && first.value == second.value do
      throwError "binder-prefix shared parameter records disagree"

private def checkParent (original checked source : Context) (stats : InductiveStats)
    (types : Array InductiveType) (parent : Nat) (info : RecInfo) : MetaM Unit := do
  let checkedValues := checkedIndices original checked stats parent
  unless checkedValues.size == stats.nindices[parent]! && info.indices.size == checkedValues.size do
    throwError "binder-prefix checked/generated vector lengths disagree"
  let checkedSteps ← checkOpening checked stats.params.size parent types[parent]!.type stats.params checkedValues
  let generatedSteps ← checkOpening source stats.params.size parent types[parent]!.type stats.params info.indices
  checkParameterSteps stats.params.size checkedSteps generatedSteps
  let checkedFirst := (checkedSteps.drop stats.params.size).head?
  let generatedFirst := (generatedSteps.drop stats.params.size).head?
  unless checkedFirst.map BinderStep.domain == generatedFirst.map BinderStep.domain &&
      checkedFirst.map BinderStep.localDomain == generatedFirst.map BinderStep.localDomain do
    throwError "binder-prefix first-index raw/consumed domains disagree"
  for index in [:checkedValues.size] do
    unless checkedValues[index]! != info.indices[index]! do
      throwError "binder-prefix fixture incorrectly equates checked/generated index IDs"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, env, infos, source) := stage nparams types ctx
    | throwError "binder-prefix checked/registered fixture failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-prefix fixture changed checked metadata"
  for parent in [:types.size] do
    checkParent ctx checked source stats types parent infos[parent]!
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-prefix fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-prefix fixture changed registered metadata"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `PrefixEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3] do
    checkFixture ctx nparams #[header (Name.mkNum `PrefixDependent nparams) dependent] #[3 - nparams]
  let multiple := multipleParams sortType `multiple
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `PrefixMultiple nparams) multiple] #[4 - nparams]
  let independent := Expr.forallE `carrier sortType
    (.forallE `first (.bvar 0) (.forallE `second (.bvar 1) sortType .default) .default) .implicit
  checkFixture ctx 1 #[header `PrefixIndependent independent] #[2]
  let natIndices := Expr.forallE `first (.const ``Nat [])
    (.forallE `second (.const ``Nat []) sortType .default) .default
  checkFixture ctx 0 #[header `PrefixNat natIndices] #[2]
  checkFixture ctx 1 #[header `PrefixMetadata (family (.mdata tagged sortType) `marked true)] #[2]
  checkFixture ctx 1 #[header `PrefixAlias
    (family (.const ``PrefixCarrierAlias []) `aliased false)] #[2]
  checkFixture ctx 1 #[header `PrefixMutualFirst
    (family (.const ``PrefixCarrierAlias []) `first false),
    header `PrefixMutualSecond (family sortType `second true)] #[2, 2]
  checkFixture ctx 2 #[header `PrefixMutualMultipleFirst
    (multipleParams (.const ``PrefixCarrierAlias []) `first),
    header `PrefixMutualMultipleSecond (multipleParams sortType `second)] #[2, 2]
  checkFixture ctx 1 #[header `PrefixWrappedDependent (wrappedDependent tagged)] #[2]
  checkFixture ctx 2 #[header `PrefixWrappedMultiple
    (.mdata tagged (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) multiple true))] #[2]
  unless declareConstructors.arity 0 (wrappedDependent tagged) == 0 &&
      declareConstructors.arity 0 dependent == 3 do
    throwError "binder-prefix fixtures collapsed raw/normalized arity"

private def laterDomainBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `PrefixLaterDependent dependent]
  let .ok (stats, checked, _, infos, source) := stage 1 types ctx
    | throwError "binder-prefix later-domain boundary setup failed"
  let checkedValues := checkedIndices ctx checked stats 0
  let some first := checked.lctx.find? checkedValues[0]!.fvarId!
    | throwError "checked first index missing"
  let some second := source.lctx.find? infos[0]!.indices[0]!.fvarId!
    | throwError "generated first index missing"
  let some checkedLater := checked.lctx.find? checkedValues[1]!.fvarId!
    | throwError "checked second index missing"
  let some generatedLater := source.lctx.find? infos[0]!.indices[1]!.fvarId!
    | throwError "generated second index missing"
  unless first.type == second.type && !(checkedLater.type == generatedLater.type) do
    throwError "binder-prefix boundary incorrectly extends first-domain agreement to dependent later domains"
  let (steps, _) := opening 1 dependent (stats.params.toList ++ checkedValues.toList)
  let shuffled := steps.zipIdx.map fun (step, index) =>
    if index = 0 then { step with role := .index }
    else if index = 1 then { step with role := .parameter } else step
  unless !(rolesOrdered 1 shuffled) && (BinderStep.parameterValues shuffled).length == 1 do
    throwError "binder-prefix boundary incorrectly infers ordering from counts alone"

private def arbitrarySubstitutionBoundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `PrefixUnchecked dependent]
  let .ok (stats, checked, _, _, source) := stage 1 types ctx
    | throwError "binder-prefix arbitrary-substitution setup failed"
  let checkedValues := checkedIndices ctx checked stats 0
  let some checkedFirst := checked.lctx.find? checkedValues[0]!.fvarId!
    | throwError "binder-prefix checked first index missing"
  for replacement in [.const ``Nat [], Expr.fvar ⟨`UndeclaredPrefixParameter⟩] do
    let changed := { stats with params := #[replacement], nindices := #[99] }
    let .ok (infos, current) := mkRecInfos changed types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) source
      | throwError "bare binder generator no longer accepts arbitrary substitutions"
    let some first := current.lctx.find? infos[0]!.indices[0]!.fvarId!
      | throwError "arbitrary-substitution first index missing"
    unless infos[0]!.indices.size == 2 && first.type == replacement && !(first.type == checkedFirst.type) do
      throwError "binder-prefix first-domain agreement incorrectly ignores changed parameter values"
  let extra := { stats with params := #[.const ``Nat [], .const ``Nat [], .const ``Nat [], .const ``Nat []] }
  let .ok infos := mkRecInfos extra types (.succ .zero) pure source
    | throwError "bare binder generator no longer accepts extra parameters"
  unless infos[0]!.indices.isEmpty && extra.params.size == 4 do
    throwError "binder-prefix arbitrary source incorrectly acquired complete parameter consumption"

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
  audit ``dependentOpened binding
  audit ``concretePrefixAgreement binding
  audit ``concreteFirstLocalDomain binding
  audit ``concreteOrderedPrefix binding
  audit ``secondDomainDifferent
  audit ``interleavedOpened binding
  audit ``OpenedTelescope.samePrefixAndNextDomain
  audit ``OpenedTelescope.samePrefix
  audit ``OpenedTelescope.sameNextLocalDomain
  audit ``BinderStep.parameterPrefix
  audit ``OpenedTelescope.sameParameterPrefix
  audit ``CheckedHeaderTrace.openedPrefix (binding ++ scope)
  audit ``RecursorIndexTrace.openedPrefix (binding ++ scope)
  audit ``CheckedHeaderSource.openedPrefix_of_normalized (binding ++ scope)
  audit ``RecursorInfoIndexSource.openedPrefix_of_normalized (binding ++ scope)
  audit ``BinderStep.IndexDomainsDeclared.firstIndexTypeAgreement
  audit ``wrappedDependentTrace binding
  audit ``provedHeaders binding
  audit ``ParentBinderPrefixAlignment.toBinderDomains
  audit ``RecursorBinderPrefixAlignment.toBinderDomains
  audit ``CheckedHeaderSources.normalizedBinderPrefixes (binding ++ scope)
  audit ``CheckedHeaderSources.wrappedBinderPrefixes (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderPrefixes (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderPrefixes (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderPrefixes
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderPrefixes (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderPrefixes (normalized ++ scope)
  audit ``provedRegisteredPrefixes (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderPrefixSeed, idx := 43 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderPrefixSeed 42⟩ `old (.const ``Bool []) .implicit }
  let .ok (_, _, extendedEnv, _, _) := stage 0 #[header `PrefixReaderExtension sortType] ctx
    | throwError "binder-prefix reader-extension setup failed"
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherPrefixSeed, idx := 71 } },
      { ctx with lparams := [`u] }, { ctx with env := extendedEnv }] do
    fixtures reader
  laterDomainBoundaries ctx
  arbitrarySubstitutionBoundaries ctx
  logInfo "90 checked/registered prefix fixtures preserve ordered roles, complete shared parameter records, and exact first-index domains across 100 parent pairs/five readers; later dependent domains and changed arbitrary substitutions remain unequal"

end InductiveBinderPrefixesTest
