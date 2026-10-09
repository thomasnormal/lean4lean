import Lean4Lean.Verify.InductiveBinderAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderDomainsTest

abbrev CarrierDomainAlias := Type

abbrev ElementDomainAlias := Nat

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier element : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier element element

private def dependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0)) sortType .instImplicit) .strictImplicit) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0)) .instImplicit (.sort (.succ .zero))))

private def dependentSteps (carrier element witness : FVarId) : List BinderStep := [
  { role := .parameter, name := `carrier, domain := sortType, bi := .implicit, value := .fvar carrier },
  { role := .index, name := `element, domain := .fvar carrier, bi := .strictImplicit, value := .fvar element },
  { role := .index, name := `witness, domain := equalityDomain (.fvar carrier) (.fvar element),
    bi := .instImplicit, value := .fvar witness }]

private theorem dependentOpened (carrier element witness : FVarId) :
    OpenedTelescope dependent (dependentSteps carrier element witness) sortType := by
  unfold dependent dependentSteps
  apply OpenedTelescope.bind .parameter `carrier sortType .implicit (.fvar carrier)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `element (.fvar carrier)
      (.forallE `witness (equalityDomain (.fvar carrier) (.bvar 0)) sortType .instImplicit) .strictImplicit) _ sortType
  apply OpenedTelescope.bind .index `element (.fvar carrier) .strictImplicit (.fvar element)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope
    (.forallE `witness (equalityDomain (.fvar carrier) (.fvar element)) sortType .instImplicit) _ sortType
  apply OpenedTelescope.bind .index `witness (equalityDomain (.fvar carrier) (.fvar element)) .instImplicit
    (.fvar witness)
  rw [Expr.instantiate1_eq]
  change OpenedTelescope sortType [] sortType
  exact .sort (.succ .zero)

example (carrier element witness : FVarId) :
    BinderStep.parameterValues (dependentSteps carrier element witness) = [.fvar carrier] := rfl

example (carrier element witness : FVarId) :
    BinderStep.indexValues (dependentSteps carrier element witness) = [.fvar element, .fvar witness] := rfl

example (carrier first second firstWitness secondWitness : FVarId) :
    (dependentSteps carrier first firstWitness).map BinderStep.signature =
      (dependentSteps carrier second secondWitness).map BinderStep.signature :=
  (dependentOpened carrier first firstWitness).sameSignature
    (dependentOpened carrier second secondWitness) dependentShape

example (first second : FVarId) (hdifferent : first ≠ second) : Expr.fvar first ≠ .fvar second := by
  intro hequal
  exact hdifferent (Expr.fvar.inj hequal)

private theorem dependentDomainsDifferent (carrier first second firstWitness secondWitness : FVarId)
    (hdifferent : first ≠ second) :
    (dependentSteps carrier first firstWitness).map BinderStep.domain ≠
      (dependentSteps carrier second secondWitness).map BinderStep.domain := by
  intro hequal
  change [sortType, .fvar carrier, equalityDomain (.fvar carrier) (.fvar first)] =
    [sortType, .fvar carrier, equalityDomain (.fvar carrier) (.fvar second)] at hequal
  have hdomain := (List.cons.inj (List.cons.inj (List.cons.inj hequal).2).2).1
  exact hdifferent (Expr.fvar.inj (Expr.app.inj hdomain).2)

example (step : BinderStep) : step.localDomain = peelTypeAnnotations step.domain := rfl

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

private theorem wrappedDependentNormalized (data : MData) :
    NormalizedSortTelescope (wrappedDependent data) dependent := (wrappedDependentTrace data).normalized

private def tagged : MData :=
  ({} : MData).insert `BinderDomainTag (.ofString "source-domain")

private def family (firstDomain : Expr) (names : Name) (marked : Bool) : Expr :=
  let elementDomain := if marked then .mdata tagged
    (mkApp (.const ``outParam [.succ .zero]) (.bvar 0)) else .bvar 0
  let witnessDomain := if marked then .mdata tagged (equalityDomain (.bvar 1) (.bvar 0))
    else equalityDomain (.bvar 1) (.bvar 0)
  .forallE (names ++ `carrier) firstDomain
    (.forallE (names ++ `element) elementDomain
      (.forallE (names ++ `witness) witnessDomain sortType .instImplicit) .strictImplicit) .implicit

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams) :
    ∃ steps, OpenedTelescope type steps terminal := by
  obtain ⟨steps, hopened⟩ := trace.openedTelescope htype hwf hreserved hparams
  exact ⟨steps, hopened.1⟩

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ∃ steps, OpenedTelescope type steps terminal ∧
      stats.params.toList.drop index = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      finalIndices.toList = indices.toList ++ BinderStep.indexValues steps ∧ BinderStepsIndexDeclared finalCtx steps :=
  trace.openedTelescope htype hwf hreserved

example {original current : Context} {params : Array Expr} {count : Nat}
    (source : CheckedHeaderSource 1 #[header `ProvedBinder (wrappedDependent tagged)] 0
      original params count current) : ∃ steps terminal, OpenedTelescope dependent steps terminal ∧
      BinderStep.parameterValues steps = params.toList ∧ (BinderStep.indexValues steps).length = count ∧
      BinderStepsIndexDeclared current steps :=
  source.opened_of_normalized (wrappedDependentNormalized tagged)

example {stats : InductiveStats} {elimLevel : Level} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats #[header `ProvedBinder (wrappedDependent tagged)] elimLevel 0
      original info current) : ∃ steps terminal finalIndex, OpenedTelescope dependent steps terminal ∧
      stats.params.toList = BinderStep.parameterValues steps ++ stats.params.toList.drop finalIndex ∧
      info.indices.toList = BinderStep.indexValues steps ∧
      finalIndex = min (declareConstructors.arity 0 dependent) stats.params.size ∧
      BinderStepsIndexDeclared current steps :=
  source.opened_of_normalized (wrappedDependentNormalized tagged)

private def provedTypes (data : MData) : Array InductiveType :=
  #[header `ProvedBinder (wrappedDependent data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent hparent
  have hzero : parent = 0 := by simpa [provedTypes] using hparent
  subst parent
  exact ⟨dependent, wrappedDependentTrace data⟩

example {stats : InductiveStats} {original checkedRoot recursorRoot current : Context}
    {elimLevel : Level} {infos : Array RecInfo} (data : MData)
    (headers : CheckedHeaderSources 1 (provedTypes data) original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats (provedTypes data) elimLevel recursorRoot infos current) :
    RecursorBinderDomainAlignment stats (provedTypes data) checkedRoot current infos :=
  headers.wrappedBinderDomains sources (provedHeaders data)

private theorem provedRegisteredDomains (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderDomainAlignment result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderDomains 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

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
    | throwError "binder-domain source normalization failed"
  let values := params.toList ++ indices.toList
  let (steps, terminal) := opening nparams normalized values
  unless steps.length == values.length && terminal == sortType &&
      BinderStep.parameterValues steps == params.toList && BinderStep.indexValues steps == indices.toList do
    throwError "binder-domain opening lost exact parameter/index substitutions"
  for step in steps do
    let some decl := ctx.lctx.find? step.value.fvarId!
      | throwError "binder-domain opening refers to undeclared actual binder"
    if parent = 0 || step.role = .index then
      unless decl.type == step.localDomain && decl.userName == step.name && decl.binderInfo == step.bi do
        throwError "binder-domain opening lost its own literal local declaration receipt"
  return steps

private def checkParent (original checked source : Context) (stats : InductiveStats)
    (types : Array InductiveType) (parent : Nat) (info : RecInfo) : MetaM Unit := do
  let checkedValues := checkedIndices original checked stats parent
  unless checkedValues.size == stats.nindices[parent]! && info.indices.size == checkedValues.size do
    throwError "binder-domain checked/generated vector lengths disagree"
  let checkedSteps ← checkOpening checked stats.params.size parent types[parent]!.type stats.params checkedValues
  let generatedSteps ← checkOpening source stats.params.size parent types[parent]!.type stats.params info.indices
  unless checkedSteps.map BinderStep.signature == generatedSteps.map BinderStep.signature do
    throwError "binder-domain source binder names or binder infos changed"
  for index in [:checkedValues.size] do
    unless checkedValues[index]! != info.indices[index]! do
      throwError "binder-domain fixture unexpectedly equates checked/generated fresh IDs"
    if parent = 0 then
      unless (stats.lctx.find? checkedValues[index]!.fvarId!).isSome &&
          (stats.lctx.find? info.indices[index]!.fvarId!).isNone do
        throwError "binder-domain fixture changed first checked stats-local ownership"
  if 2 ≤ checkedValues.size then
    let checkedDomains := checkedSteps.filter (·.role = .index) |>.map BinderStep.localDomain
    let generatedDomains := generatedSteps.filter (·.role = .index) |>.map BinderStep.localDomain
    unless !(checkedDomains == generatedDomains) do
      throwError "dependent binder-domain fixture incorrectly equates different substitution plans"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) (wrapped := false) : MetaM Unit := do
  let .ok (stats, checked, env, infos, source) := stage nparams types ctx
    | throwError "binder-domain checked/registered fixture failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-domain fixture changed checked metadata"
  for parent in [:types.size] do
    checkParent ctx checked source stats types parent infos[parent]!
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-domain fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-domain fixture changed registered metadata"
  if wrapped then
    unless declareConstructors.arity 0 types[0]!.type == 0 && nparams + expected[0]! == 3 do
      throwError "binder-domain wrapped fixture collapsed raw/normalized arity"

private def fixtures (ctx : Context) : MetaM Unit := do
  for nparams in [0, 1, 2, 3] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderPlain nparams) dependent] #[3 - nparams]
  checkFixture ctx 1 #[header `BinderAnnotated (family (.mdata tagged sortType) `annotated true)] #[2]
  checkFixture ctx 1 #[header `BinderAlias
    (family (.const ``CarrierDomainAlias []) `aliased false)] #[2]
  checkFixture ctx 1 #[header `BinderMutualFirst
    (family (.const ``CarrierDomainAlias []) `first false),
    header `BinderMutualSecond (family sortType `second false)] #[2, 2]
  checkFixture ctx 0 #[header `BinderFreshFirst (family sortType `first false),
    header `BinderFreshSecond (family sortType `second true)] #[3, 3]
  checkFixture ctx 1 #[header `BinderMarkedFirst (family sortType `first true),
    header `BinderMarkedSecond (family (.mdata tagged sortType) `second false)] #[2, 2]
  checkFixture ctx 1 #[header `BinderWrapped (wrappedDependent tagged)] #[2] true
  let aliasElements := Expr.forallE `element (.const ``ElementDomainAlias [])
    (.forallE `witness (equalityDomain (.const ``Nat []) (.bvar 0)) sortType .default) .default
  checkFixture ctx 0 #[header `BinderElementAlias aliasElements] #[2]

private def reusedParameterBoundary (ctx : Context) : MetaM Unit := do
  let first := family (.const ``CarrierDomainAlias []) `first false
  let second := Expr.forallE `differentName sortType
    (.forallE `element (.bvar 0) sortType .default) .default
  let types := #[header `ReusedSourceFirst first, header `ReusedSourceSecond second]
  let .ok (stats, checked, _, _, _) := stage 1 types ctx
    | throwError "reused binder-domain boundary setup failed"
  let some decl := checked.lctx.find? stats.params[0]!.fvarId!
    | throwError "reused binder-domain shared parameter missing"
  unless decl.userName != `differentName && decl.binderInfo != .default && !(decl.type == sortType) do
    throwError "reused source binder syntax incorrectly overwrote the shared parameter declaration"

private def uncheckedParameterBoundary (ctx : Context) : MetaM Unit := do
  let types := #[header `UncheckedBinderDomains dependent]
  let .ok (stats, _, _, _, source) := stage 1 types ctx
    | throwError "unchecked binder-domain boundary setup failed"
  let missing : FVarId := ⟨`UndeclaredBinderParameter⟩
  for replacement in [.const ``Nat [], Expr.fvar missing] do
    let changed := { stats with params := #[replacement], nindices := #[99] }
    let .ok (infos, current) := mkRecInfos changed types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) source
      | throwError "bare binder generator no longer accepts unchecked parameter substitutions"
    unless infos[0]!.indices.size == 2 && changed.nindices[0]! == 99 do
      throwError "unchecked binder-domain statistics unexpectedly determined generated index count"
    let some first := current.lctx.find? infos[0]!.indices[0]!.fvarId!
      | throwError "unchecked binder-domain generator lost first index"
    unless first.type == replacement && (current.lctx.find? missing).isNone do
      throwError "unchecked binder-domain substitution incorrectly acquired a typing/declaration certificate"
  let extra := { stats with params := #[.const ``Nat [], .const ``Nat [], .const ``Nat [], .const ``Nat []] }
  let .ok infos := mkRecInfos extra types (.succ .zero) pure source
    | throwError "bare binder generator no longer retains unconsumed extra parameters"
  unless infos[0]!.indices.isEmpty && extra.params.size == 4 && stats.nindices[0]! == 2 do
    throwError "unchecked binder-domain generator incorrectly requires all parameters consumed"

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
  audit ``dependentDomainsDifferent
  audit ``SortTelescope.binderSignature_instantiate1' []
  audit ``SortTelescope.binderSignature_instantiate1 binding
  audit ``OpenedTelescope.signature binding
  audit ``OpenedTelescope.sameSignature binding
  audit ``BinderDeclaredAt.mono scope
  audit ``BinderStep.IndexDomainsDeclared.mono scope
  audit ``CheckedHeaderTrace.openedTelescope (binding ++ scope)
  audit ``RecursorIndexTrace.openedTelescope (binding ++ scope)
  audit ``CheckedHeaderSource.opened_of_normalized (binding ++ scope)
  audit ``RecursorInfoIndexSource.opened_of_normalized (binding ++ scope)
  audit ``wrappedDependentTrace binding
  audit ``wrappedDependentNormalized normalized
  audit ``provedHeaders binding
  audit ``CheckedHeaderSources.normalizedBinderDomains (binding ++ scope)
  audit ``CheckedHeaderSources.wrappedBinderDomains (normalized ++ scope)
  audit ``mkRecInfos.scopedNormalizedBinderDomains (binding ++ scope)
  audit ``mkRecInfos.getNormalizedBinderDomains (binding ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderDomains
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedBinderDomains (binding ++ scope)
  audit ``checkInductiveTypes.safeRegisteredWrappedBinderDomains (normalized ++ scope)
  audit ``provedRegisteredDomains (normalized ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderDomainSeed, idx := 37 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderDomainSeed 36⟩ `old (.const ``Bool []) .implicit }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderPrefix, idx := 71 } },
      { ctx with lparams := [`u] }] do
    fixtures reader
  reusedParameterBoundary ctx
  uncheckedParameterBoundary ctx
  logInfo "44 checked/registered dependent-domain fixtures retain exact own-plan domains and substitutions across four readers; reused source syntax, unequal fresh domains, raw arity, and unchecked parameters remain explicit"

end InductiveBinderDomainsTest
