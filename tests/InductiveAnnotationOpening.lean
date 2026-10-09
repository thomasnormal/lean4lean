import Lean4Lean.Verify.InductiveAnnotationModelOpening
import Lean4Lean.Verify.InductiveAnnotationOpeningShape
import Lean4Lean.Verify.InductiveAnnotationBinderOpening
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveAnnotationOpeningTest

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr :=
  .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`AnnotationOpeningTag, .ofNat 19)] }

private def sortType : Expr := .sort (.succ .zero)

private theorem arbitraryDepthFVarCommutation (value : Expr) (id : FVarId) (depth : Nat) :
    peelTypeAnnotations (value.instantiate1' (.fvar id) depth) =
      (peelTypeAnnotations value).instantiate1' (.fvar id) depth :=
  peelTypeAnnotations_instantiate1'_fvar value id depth

private theorem actualFVarOpeningCommutation (value : Expr) (id : FVarId) :
    peelTypeAnnotations (value.instantiate1 (.fvar id)) =
      (peelTypeAnnotations value).instantiate1 (.fvar id) :=
  peelTypeAnnotations_instantiate1_fvar value id

private theorem openingDoesNotNeedFreshness (id : FVarId) :
    peelTypeAnnotations
      ((binary ``optParam [] (.app (.fvar id) (.bvar 0)) (.fvar id)).instantiate1' (.fvar id)) =
      .app (.fvar id) (.fvar id) := by
  simp [peelTypeAnnotations, binary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem looseBoundVariablesShift (id : FVarId) (depth : Nat) :
    peelTypeAnnotations ((unary ``outParam [] (.bvar (depth + 2))).instantiate1' (.fvar id) depth) =
      .bvar (depth + 1) := by
  rw [peelTypeAnnotations_instantiate1'_fvar]
  change (Expr.bvar (depth + 2)).instantiate1' (.fvar id) depth = .bvar (depth + 1)
  have notLower : ¬ depth + 2 < depth := by omega
  have notEqual : depth + 2 ≠ depth := by omega
  simp only [Expr.instantiate1', notLower, notEqual, ite_false]
  congr 1

private theorem lowerBoundVariablesStay (id : FVarId) (index depth : Nat) (lower : index < depth) :
    peelTypeAnnotations ((unary ``semiOutParam [] (.bvar index)).instantiate1' (.fvar id) depth) =
      .bvar index := by
  simp [peelTypeAnnotations, unary, Expr.instantiate1', lower]

private theorem exactDepthBecomesFVar (id : FVarId) (depth : Nat) :
    peelTypeAnnotations ((binary ``autoParam [] (.bvar depth) (.bvar (depth + 1))).instantiate1' (.fvar id) depth) =
      .fvar id := by
  simp [peelTypeAnnotations, binary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem forallDomainAndBodyShift (id : FVarId) :
    (Expr.forallE `inner (unary ``outParam [] (.bvar 0))
      (binary ``optParam [] (.bvar 1) (.bvar 0)) .implicit).instantiate1' (.fvar id) =
    .forallE `inner (unary ``outParam [] (.fvar id))
      (binary ``optParam [] (.fvar id) (.bvar 0)) .implicit := by
  simp [unary, binary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem lambdaDomainAndBodyShift (id : FVarId) :
    (Expr.lam `inner (unary ``semiOutParam [] (.bvar 0))
      (binary ``autoParam [] (.bvar 1) (.bvar 0)) .strictImplicit).instantiate1' (.fvar id) =
    .lam `inner (unary ``semiOutParam [] (.fvar id))
      (binary ``autoParam [] (.fvar id) (.bvar 0)) .strictImplicit := by
  simp [unary, binary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem letDomainValueAndBodyShift (id : FVarId) :
    (Expr.letE `inner (unary ``outParam [] (.bvar 0))
      (binary ``optParam [] (.bvar 0) (.bvar 1))
      (binary ``autoParam [] (.bvar 1) (.bvar 0)) false).instantiate1' (.fvar id) =
    .letE `inner (unary ``outParam [] (.fvar id))
      (binary ``optParam [] (.fvar id) (.bvar 0))
      (binary ``autoParam [] (.fvar id) (.bvar 0)) false := by
  simp [unary, binary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem metadataBarrierSurvivesOpening (id : FVarId) :
    peelTypeAnnotations ((Expr.mdata tagged (unary ``outParam [] (.bvar 0))).instantiate1' (.fvar id)) =
      .mdata tagged (unary ``outParam [] (.fvar id)) := by
  simp [peelTypeAnnotations, unary, Expr.instantiate1', Expr.liftLooseBVars']

private theorem arbitraryReplacementCreatesAnnotationHead :
    peelTypeAnnotations ((Expr.app (.bvar 0) (.const ``Nat [])).instantiate1' (.const ``outParam [])) ≠
      (peelTypeAnnotations (.app (.bvar 0) (.const ``Nat []))).instantiate1' (.const ``outParam []) := by
  simp [peelTypeAnnotations, Expr.instantiate1', Expr.liftLooseBVars']

private theorem arbitraryAnnotatedReplacementAlsoFails :
    peelTypeAnnotations ((Expr.bvar 0).instantiate1' (unary ``outParam [] (.const ``Nat []))) ≠
      (peelTypeAnnotations (.bvar 0)).instantiate1' (unary ``outParam [] (.const ``Nat [])) := by
  simp [peelTypeAnnotations, unary, Expr.instantiate1', Expr.liftLooseBVars']

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def sourceType (dropped : FVarId) : Expr :=
  .forallE `carrier (unary ``outParam [.succ .zero] sortType)
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0))
      (.forallE `witness
        (binary ``optParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) (.fvar dropped))
        sortType .instImplicit) .default) .implicit

private def rawSteps (param element witness dropped : FVarId) : List BinderStep := [
  { role := .parameter, name := `carrier, domain := unary ``outParam [.succ .zero] sortType, bi := .implicit, value := .fvar param },
  { role := .index, name := `element, domain := unary ``semiOutParam [.succ .zero] (.fvar param), bi := .default, value := .fvar element },
  { role := .index, name := `witness, domain := binary ``optParam [.zero] (equalityDomain (.fvar param) (.fvar element) (.fvar element)) (.fvar dropped), bi := .instImplicit, value := .fvar witness }]

private theorem actualSequentialRawOpening (param element witness dropped : FVarId) :
    OpenedTelescope (sourceType dropped) (rawSteps param element witness dropped) sortType := by
  apply OpenedTelescope.bind
  simp only [unary, binary, equalityDomain, sortType, Expr.instantiate1_eq,
    Expr.instantiate1', Expr.liftLooseBVars']
  apply OpenedTelescope.bind
  simp only [Expr.instantiate1_eq, Expr.instantiate1']
  apply OpenedTelescope.bind
  rw [Expr.instantiate1_eq]
  exact .sort (.succ .zero)

private theorem allSequentialOpeningValuesAreFVars (param element witness dropped : FVarId) :
    ∀ step ∈ rawSteps param element witness dropped, ∃ id, step.value = .fvar id := by
  intro step member
  simp only [rawSteps, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl := member
  · exact ⟨param, rfl⟩
  · exact ⟨element, rfl⟩
  · exact ⟨witness, rfl⟩

private theorem sameSequentialWitnessHasModeledDomains (param element witness dropped : FVarId) :
    OpenedTelescope (peelTelescopeDomains (sourceType dropped))
      ((rawSteps param element witness dropped).map BinderStep.withModelDomain) sortType :=
  (actualSequentialRawOpening param element witness dropped).withModelDomains
    (allSequentialOpeningValuesAreFVars param element witness dropped)

private theorem duplicateOpeningValuesStillHaveModeledWitness (id dropped : FVarId) :
    OpenedTelescope (peelTelescopeDomains (sourceType dropped))
      ((rawSteps id id id dropped).map BinderStep.withModelDomain) sortType :=
  sameSequentialWitnessHasModeledDomains id id id dropped

private theorem modeledSequentialDomainsAreLiteral (param element witness dropped : FVarId) :
    ((rawSteps param element witness dropped).map BinderStep.withModelDomain).map (·.domain) =
      [sortType, .fvar param, equalityDomain (.fvar param) (.fvar element) (.fvar element)] := by
  simp [rawSteps, BinderStep.withModelDomain, peelTypeAnnotations, unary, binary, equalityDomain,
    mkApp3, mkAppB, mkApp, sortType]

private theorem telescopeModelAtArbitraryDepth (value : Expr) (id : FVarId) (depth : Nat) :
    peelTelescopeDomains (value.instantiate1' (.fvar id) depth) =
      (peelTelescopeDomains value).instantiate1' (.fvar id) depth :=
  peelTelescopeDomains_instantiate1'_fvar value id depth

private theorem telescopeModelAtActualOpening (value : Expr) (id : FVarId) :
    peelTelescopeDomains (value.instantiate1 (.fvar id)) =
      (peelTelescopeDomains value).instantiate1 (.fvar id) :=
  peelTelescopeDomains_instantiate1_fvar value id

private theorem telescopeModelStopsOutsideSyntacticForalls (data : MData) (domain body : Expr) :
    peelTelescopeDomains (.mdata data (.forallE `inner domain body .default)) =
      .mdata data (.forallE `inner domain body .default) ∧
    peelTelescopeDomains (.lam `inner domain body .implicit) = .lam `inner domain body .implicit ∧
    peelTelescopeDomains (.letE `inner domain body (.bvar 0) false) =
      .letE `inner domain body (.bvar 0) false ∧
    peelTelescopeDomains (unary ``outParam [] (.forallE `inner domain body .default)) =
      unary ``outParam [] (.forallE `inner domain body .default) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem arbitraryReplacementCreatesTelescopeShape :
    peelTelescopeDomains
      ((Expr.bvar 0).instantiate1' (.forallE `inner (unary ``outParam [] (.const ``Nat [])) sortType .default)) ≠
      (peelTelescopeDomains (.bvar 0)).instantiate1'
        (.forallE `inner (unary ``outParam [] (.const ``Nat [])) sortType .default) := by
  simp [peelTelescopeDomains, peelTypeAnnotations, unary, sortType, Expr.instantiate1', Expr.liftLooseBVars']

private theorem actualSourcesSupplyFVarOpeningValues {type terminal : Expr} {steps : List BinderStep}
    {ctx : Context} (opened : OpenedTelescope type steps terminal)
    (parameters : ∀ value ∈ BinderStep.parameterValues steps, ∃ id, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) :
    OpenedTelescope (peelTelescopeDomains type) (steps.map BinderStep.withModelDomain) terminal :=
  opened.withModelDomains_of_parameters_indices parameters declared

private theorem rawChronologyRetainedByModeledDomains {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) :
    BinderRawDomainScope params (steps.map BinderStep.withModelDomain) := scope.withModelDomains

private theorem deterministicCorrespondenceRetainedByModeledDomains
    {pairs finalPairs : List (FVarId × FVarId)} {checked generated : List BinderStep}
    (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs) :
    BinderLookupCorrespondence pairs (checked.map BinderStep.withModelDomain)
      (generated.map BinderStep.withModelDomain) finalPairs := correspondence.withModelDomains

private theorem sameActualHistoriesRetainRawAndModeledDomains
    {type checkedTerminal generatedTerminal : Expr} {checked generated : List BinderStep}
    {checkedCtx generatedCtx : Context} {params : List FVarId} {pairs finalPairs : List (FVarId × FVarId)}
    (checkedOpening : OpenedTelescope type checked checkedTerminal)
    (generatedOpening : OpenedTelescope type generated generatedTerminal)
    (checkedDeclared : BinderStepsIndexDeclared checkedCtx checked)
    (generatedDeclared : BinderStepsIndexDeclared generatedCtx generated)
    (checkedParameters : ∀ value ∈ BinderStep.parameterValues checked, ∃ id, value = .fvar id)
    (generatedParameters : ∀ value ∈ BinderStep.parameterValues generated, ∃ id, value = .fvar id)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated)
    (lookup : BinderLookupCorrespondence pairs checked generated finalPairs) :
    OpenedTelescope type checked checkedTerminal ∧ OpenedTelescope type generated generatedTerminal ∧
      BinderLookupCorrespondence pairs checked generated finalPairs ∧
      BinderRawDomainScope params checked ∧ BinderRawDomainScope params generated ∧
      OpenedTelescope (peelTelescopeDomains type) (checked.map BinderStep.withModelDomain) checkedTerminal ∧
      OpenedTelescope (peelTelescopeDomains type) (generated.map BinderStep.withModelDomain) generatedTerminal ∧
      BinderLookupCorrespondence pairs (checked.map BinderStep.withModelDomain)
        (generated.map BinderStep.withModelDomain) finalPairs ∧
      BinderRawDomainScope params (checked.map BinderStep.withModelDomain) ∧
      BinderRawDomainScope params (generated.map BinderStep.withModelDomain) :=
  ⟨checkedOpening, generatedOpening, lookup, checkedScope, generatedScope,
    checkedOpening.withModelDomains_of_parameters_indices checkedParameters checkedDeclared,
    generatedOpening.withModelDomains_of_parameters_indices generatedParameters generatedDeclared,
    lookup.withModelDomains, checkedScope.withModelDomains, generatedScope.withModelDomains⟩

private theorem modeledDomainsDoNotChangeParameters (steps : List BinderStep) :
    BinderStep.parameterValues (steps.map BinderStep.withModelDomain) = BinderStep.parameterValues steps :=
  BinderStep.parameterValues_withModelDomains steps

private theorem modeledDomainsDoNotChangeIndices (steps : List BinderStep) :
    BinderStep.indexValues (steps.map BinderStep.withModelDomain) = BinderStep.indexValues steps :=
  BinderStep.indexValues_withModelDomains steps

private theorem nativeOpeningRequiresBothExplicitModels (value : Expr) (id : FVarId)
    (before : NativeAnnotationModelAt value) (after : NativeAnnotationModelAt (value.instantiate1 (.fvar id))) :
    (value.instantiate1 (.fvar id)).consumeTypeAnnotations = value.consumeTypeAnnotations.instantiate1 (.fvar id) :=
  before.instantiate1_fvar_of_model id after

private theorem evaluationDoesNotAutomaticallyTransportNativeModel (id : FVarId) : True := by
  fail_if_success
    have reflected : NativeAnnotationModelAt ((unary ``outParam [] (.bvar 0)).instantiate1 (.fvar id)) := by
      rfl
  have used : id = id := rfl
  cases used
  trivial

private def pairFixtures (source target other : FVarId) : List (List (FVarId × FVarId)) := [
  [], [(source, source)], [(source, target)], [(source, target), (target, other)],
  [(source, target), (source, other)], [(source, target), (target, source)]]

private def expressionFixtures (carrier extra : Expr) : Array Expr := Id.run do
  let mut values := #[
    Expr.bvar 0, .bvar 1, .bvar 2, .bvar 5, .bvar 11, .fvar ⟨`AnnotationOpeningSource⟩,
    .mvar ⟨`AnnotationOpeningExprMeta⟩, .sort (.param `u), .const `AnnotationOpeningOrdinary [.param `u],
    .lit (.natVal 23), .app (.bvar 0) carrier,
    .lam `inner carrier (.app (.bvar 1) (.bvar 0)) .implicit,
    .forallE `inner carrier (.app (.bvar 1) (.bvar 0)) .instImplicit,
    .letE `inner carrier extra (.app (.bvar 1) (.bvar 0)) false,
    .mdata tagged carrier, .proj `AnnotationOpeningStructure 1 carrier]
  for levels in [[], [.succ .zero], [.param `u], [.mvar ⟨`AnnotationOpeningLevelMeta⟩]] do
    for name in [``outParam, ``semiOutParam, ``optParam, ``autoParam] do
      for arity in [:5] do
        values := values.push (mkAppN (.const name levels) (#[carrier, extra, carrier, extra].extract 0 arity))
    values := values ++ #[
      .mdata tagged (unary ``outParam levels carrier),
      .app (.mdata tagged (.const ``outParam levels)) carrier,
      .app (.app (.mdata tagged (.const ``optParam levels)) carrier) extra,
      unary ``outParam levels (binary ``optParam levels
        (unary ``semiOutParam levels (binary ``autoParam levels carrier extra)) extra),
      .forallE `inner (unary ``outParam levels carrier) (binary ``optParam levels (.bvar 1) extra) .implicit,
      .lam `inner (unary ``semiOutParam levels carrier) (binary ``autoParam levels (.bvar 1) extra) .strictImplicit,
      .letE `inner (unary ``outParam levels carrier) (binary ``optParam levels carrier extra)
        (binary ``autoParam levels (.bvar 1) extra) false]
  return values

private def checkDepthOpening (value : Expr) (id : FVarId) (depth : Nat)
    (pairs : List (List (FVarId × FVarId))) : MetaM Unit := do
  let replacement := Expr.fvar id
  let opened := value.instantiate1' replacement depth
  unless peelTypeAnnotations opened == (peelTypeAnnotations value).instantiate1' replacement depth do
    throwError "modeled annotation peeling failed tested FVar opening at arbitrary depth"
  unless peelTelescopeDomains opened == (peelTelescopeDomains value).instantiate1' replacement depth do
    throwError "modeled telescope-domain transformation failed tested FVar opening at arbitrary depth"
  unless opened.consumeTypeAnnotations == value.consumeTypeAnnotations.instantiate1' replacement depth do
    throwError "native annotation consumption failed empirical FVar-opening comparison"
  for incoming in pairs do
    let renamed := indexRenameExpr incoming value
    let image := indexLookup incoming id
    let renamedOpened := renamed.instantiate1' (.fvar image) depth
    unless peelTypeAnnotations renamedOpened ==
        (indexRenameExpr incoming (peelTypeAnnotations value)).instantiate1' (.fvar image) depth do
      throwError "modeled FVar opening failed tested arbitrary renaming comparison"
    unless renamedOpened.consumeTypeAnnotations ==
        (indexRenameExpr incoming value.consumeTypeAnnotations).instantiate1' (.fvar image) depth do
      throwError "native FVar opening failed empirical renamed consumption comparison"
  if depth = 0 then
    unless value.instantiate1 replacement == opened &&
        (value.instantiate1 replacement).consumeTypeAnnotations == value.consumeTypeAnnotations.instantiate1 replacement do
      throwError "actual native instantiate1 disagrees with tested opening/consumption model"

private def checkUnrestrictedReplacementBoundary : MetaM Unit := do
  let value := Expr.app (.bvar 0) (.const ``Nat [])
  let replacement := Expr.const ``outParam []
  let opened := value.instantiate1 replacement
  unless peelTypeAnnotations opened != (peelTypeAnnotations value).instantiate1 replacement &&
      opened.consumeTypeAnnotations != value.consumeTypeAnnotations.instantiate1 replacement do
    throwError "unrestricted replacement unexpectedly generalized FVar-only opening commutation"
  logInfo "unrestricted constant-headed substitution creates a new annotation and empirically breaks model/native opening commutation"

private def openingMatrix : MetaM Unit := do
  let source : FVarId := ⟨`AnnotationOpeningSource⟩
  let target : FVarId := ⟨`AnnotationOpeningTarget⟩
  let other : FVarId := ⟨`AnnotationOpeningOther⟩
  let pairs := pairFixtures source target other
  let carriers : List Expr := [.bvar 0, .bvar 1, .bvar 3, .bvar 9,
    .app (.bvar 0) (.fvar source), .mdata tagged (unary ``outParam [] (.bvar 0)),
    .forallE `inner (.bvar 0) (unary ``semiOutParam [] (.bvar 1)) .default]
  let extras : List Expr := [.fvar other, .bvar 0, .bvar 4,
    binary ``autoParam [] (.fvar source) (.bvar 2)]
  let mut compared := 0
  for carrier in carriers do
    for extra in extras do
      for value in expressionFixtures carrier extra do
        for depth in [0, 1, 2, 4, 8, 16] do
          for id in [source, target, other] do
            checkDepthOpening value id depth pairs
            compared := compared + 1
  logInfo m!"{compared} FVar-opening cases and {compared * pairs.length} renamed comparisons: arbitrary loose depths, all constructors/gadgets/wrong arities, domain/body shifts, metadata, identity/overlap/duplicate pairs, no freshness premise"

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def nativeSourceType : Expr :=
  .forallE `carrier sortType
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0))
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1)))
          (.forallE `automatic
            (binary ``autoParam [.zero] (equalityDomain (.bvar 3) (.bvar 2) (.bvar 2))
              (.const ``Lean.Syntax.missing []))
            sortType .default) .strictImplicit) .instImplicit) .default) .implicit

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
      | throwError "annotation-opening actual checked source points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkActualOpening (ctx : Context) (nparams : Nat) (type : Expr) (values : Array Expr) : MetaM Unit := do
  let mut raw := type
  let mut modeled := peelTelescopeDomains type
  let mut steps : List BinderStep := []
  for position in [:values.size] do
    let .forallE name rawDomain body bi := raw
      | throwError "annotation-opening actual source telescope ended before its values"
    let .forallE modelName modelDomain modelBody modelBi := modeled
      | throwError "annotation-opening modeled source telescope ended before its values"
    let .fvar id := values[position]!
      | throwError "annotation-opening actual source helper returned a non-FVar opening value"
    unless name == modelName && bi == modelBi && modelDomain == peelTypeAnnotations rawDomain do
      throwError "annotation-opening actual source domain and transformed model domain diverged"
    let role := if position < nparams then BinderRole.parameter else .index
    if role = .index then
      let some declaration := ctx.lctx.find? id
        | throwError "annotation-opening actual index declaration missing"
      unless declaration.type == modelDomain && declaration.type == rawDomain.consumeTypeAnnotations do
        throwError "annotation-opening modeled domain diverged empirically from actual consumed local type"
    steps := steps ++ [{ role, name, domain := rawDomain, bi, value := .fvar id }]
    raw := body.instantiate1 (.fvar id)
    modeled := modelBody.instantiate1 (.fvar id)
    unless modeled == peelTelescopeDomains raw do
      throwError "annotation-opening sequential actual FVar substitution lost transformed telescope commutation"
  unless raw == sortType && modeled == sortType &&
      (steps.map BinderStep.withModelDomain).map (·.value) == values.toList do
    throwError "annotation-opening transformed actual source lost terminal/value anchors"

private def actualSourcePlans : MetaM Unit := do
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let mut registrations := 0
  let mut domains := 0
  for nparams in [0, 1, 2, 5] do
    let types := #[header (Name.mkNum `AnnotationOpeningNativeFirst nparams) nativeSourceType,
      header (Name.mkNum `AnnotationOpeningNativeSecond nparams) nativeSourceType]
    let .ok (stats, checked, _, _, infos, generated) := stage nparams types ctx
      | throwError "annotation-opening actual checked/registered native source fixture failed"
    for parent in [:types.size] do
      let checkedValues ← valuesAt checked (nparams + parent * (5 - nparams)) (5 - nparams)
      checkActualOpening checked nparams nativeSourceType (stats.params ++ checkedValues)
      checkActualOpening generated nparams nativeSourceType (stats.params ++ infos[parent]!.indices)
      domains := domains + 5
    registrations := registrations + 1
  logInfo m!"{registrations} mutual full registrations / {registrations * 2} actual parent pairs / {domains} paired binder domains: parameter/index splits 0,1,2,5 retain exact source values, chronological transformed domains, empirical native stored types, and terminal anchors"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  audit ``arbitraryDepthFVarCommutation
  audit ``actualFVarOpeningCommutation binding
  audit ``openingDoesNotNeedFreshness
  audit ``looseBoundVariablesShift
  audit ``lowerBoundVariablesStay
  audit ``exactDepthBecomesFVar
  audit ``forallDomainAndBodyShift
  audit ``lambdaDomainAndBodyShift
  audit ``letDomainValueAndBodyShift
  audit ``metadataBarrierSurvivesOpening
  audit ``arbitraryReplacementCreatesAnnotationHead
  audit ``arbitraryAnnotatedReplacementAlsoFails
  audit ``actualSequentialRawOpening binding
  audit ``allSequentialOpeningValuesAreFVars
  audit ``sameSequentialWitnessHasModeledDomains binding
  audit ``duplicateOpeningValuesStillHaveModeledWitness binding
  audit ``modeledSequentialDomainsAreLiteral
  audit ``telescopeModelAtArbitraryDepth
  audit ``telescopeModelAtActualOpening binding
  audit ``telescopeModelStopsOutsideSyntacticForalls
  audit ``arbitraryReplacementCreatesTelescopeShape
  audit ``actualSourcesSupplyFVarOpeningValues binding
  audit ``rawChronologyRetainedByModeledDomains
  audit ``deterministicCorrespondenceRetainedByModeledDomains
  audit ``sameActualHistoriesRetainRawAndModeledDomains binding
  audit ``modeledDomainsDoNotChangeParameters
  audit ``modeledDomainsDoNotChangeIndices
  audit ``nativeOpeningRequiresBothExplicitModels binding
  audit ``evaluationDoesNotAutomaticallyTransportNativeModel
  audit ``peelTypeAnnotations_instantiate1'_fvar
  audit ``peelTypeAnnotations_instantiate1_fvar binding
  audit ``instantiate1'_fvar_isAppOfArity
  audit ``instantiate1'_fvar_eq_const_iff
  audit ``instantiate1'_fvar_app_inv
  audit ``instantiate1'_fvar_preservesUnaryHead
  audit ``instantiate1'_fvar_preservesBinaryHead
  audit ``arbitraryInstantiationMayCreateAnnotationHead
  audit ``peelTelescopeDomains
  audit ``BinderStep.withModelDomain
  audit ``BinderStep.parameterValues_withModelDomains
  audit ``BinderStep.indexValues_withModelDomains
  audit ``peelTelescopeDomains_instantiate1'_fvar
  audit ``peelTelescopeDomains_instantiate1_fvar binding
  audit ``OpenedTelescope.withModelDomains binding
  audit ``OpenedTelescope.withModelDomains_of_parameters_indices binding
  audit ``BinderStepsIndexDeclared.fvarValues
  audit ``BinderLookupCorrespondence.withModelDomains
  audit ``BinderRawDomainScope.withModelDomains
  audit ``NativeAnnotationModelAt.instantiate1_fvar_of_model binding
  openingMatrix
  checkUnrestrictedReplacementBoundary
  actualSourcePlans

end InductiveAnnotationOpeningTest
