import Lean4Lean.Theory.Typing.QuotReductionAutomatic
import Lean.Util.CollectAxioms

namespace QuotientInjectivityTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.VEnv

private abbrev quotient (levels : List VLevel) (domain relation : VExpr) : VExpr :=
  .app (.app (.const ``Quot levels) domain) relation

private abbrev constructor (levels : List VLevel) (domain relation value : VExpr) : VExpr :=
  .app (.app (.app (.const ``Quot.mk levels) domain) relation) value

private abbrev lift (levels : List VLevel) (domain relation target function respect major : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
    domain) relation) target) function) respect) major

private abbrev induction (levels : List VLevel) (domain relation motive minor major : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.ind levels) domain) relation) motive) minor) major

section
variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (registered : environment.defeqs quotDefEq)

example (equal : environment.IsDefEqU universes locals
    (quotient leftLevels leftDomain leftRelation) (quotient rightLevels rightDomain rightRelation)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      environment.IsDefEqU universes locals leftDomain rightDomain ∧
      environment.IsDefEqU universes locals leftRelation rightRelation :=
  equal.quot_inj environmentWF universes localsWF registered

example (equal : environment.IsDefEqU universes locals
    (quotient [leftUniverse] leftDomain leftRelation)
    (quotient [rightUniverse] rightDomain rightRelation)) : leftUniverse ≈ rightUniverse := by
  obtain ⟨levelsEqual, _⟩ := equal.quot_inj environmentWF universes localsWF registered
  cases levelsEqual with
  | cons universeEqual _ => exact universeEqual

example (typed : environment.HasType universes locals (quotient levels domain relation) resultType)
    (wrongArity : levels.length ≠ 1) : False := by
  obtain ⟨_, rfl, _⟩ := VEnv.quot_inv environmentWF localsWF
    (environmentWF.quotientObjects registered).2.2.2.2.1 typed
  exact wrongArity rfl

example (reduced : @ParRedS (environmentWF.reductionParams universes) locals
    (quotient levels domain relation) result) :
    ∃ domain' relation', result = quotient levels domain' relation' ∧
      @ParRedS (environmentWF.reductionParams universes) locals domain domain' ∧
      @ParRedS (environmentWF.reductionParams universes) locals relation relation' :=
  reduced.quot_type environmentWF universes registered

example (typed : environment.HasType universes locals
    (lift levels domain relation target function respect
      (constructor constructorLevels constructorDomain constructorRelation value)) resultType) :
    environment.IsDefEq universes locals
      (lift levels domain relation target function respect
        (constructor constructorLevels constructorDomain constructorRelation value))
      (.app function value) resultType :=
  quotLift_beta_of_typed environmentWF localsWF registered typed

example (typed : environment.HasType universes locals
    (induction levels domain relation motive minor
      (constructor constructorLevels constructorDomain constructorRelation value)) resultType) :
    environment.IsDefEq universes locals
      (induction levels domain relation motive minor
        (constructor constructorLevels constructorDomain constructorRelation value))
      (.app minor value) resultType :=
  quotInd_beta_of_typed environmentWF localsWF registered typed

example (typed : environment.HasType universes locals
    (lift levels domain relation target function respect major) resultType)
    (majorEqual : environment.IsDefEqU universes locals major
      (constructor constructorLevels constructorDomain constructorRelation value)) :
    environment.IsDefEq universes locals (lift levels domain relation target function respect major)
      (.app function value) resultType :=
  quotLift_beta_of_normalizedMajor environmentWF localsWF registered typed majorEqual

example (typed : environment.HasType universes locals
    (induction levels domain relation motive minor major) resultType)
    (majorEqual : environment.IsDefEqU universes locals major
      (constructor constructorLevels constructorDomain constructorRelation value)) :
    environment.IsDefEq universes locals (induction levels domain relation motive minor major)
      (.app minor value) resultType :=
  quotInd_beta_of_normalizedMajor environmentWF localsWF registered typed majorEqual

example (sourceUniverseWF : sourceUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero)))) :
    environment.IsDefEqU universes locals
      (.app (.lam (.sort sourceUniverse) (.bvar 0)) domain) domain := by
  have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
  have headTyped := HasType.const (ls := [sourceUniverse]) (U := universes) quotientRegistered
    (by simpa using sourceUniverseWF) (by rfl) (Γ := locals)
  simp [quotConst, VExpr.instL, VLevel.inst] at headTyped
  have domainBeta := IsDefEq.beta (HasType.bvar (.zero (ty := .sort sourceUniverse))) domainTyped
  simp [VExpr.inst, VExpr.instVar] at domainBeta
  have partialEqual := headTyped.appDF domainBeta
  have canonicalPartial := headTyped.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at canonicalPartial
  have quotientEqual := (partialEqual.toU.of_r environmentWF localsWF canonicalPartial).appDF relationTyped
  exact (quotientEqual.toU.quot_inj environmentWF universes localsWF registered).2.1

example (equal : environment.IsDefEqU universes locals
    (quotient [.zero] leftDomain leftRelation) (quotient [.succ level] rightDomain rightRelation)) :
    False := by
  obtain ⟨levelsEqual, _⟩ := equal.quot_inj environmentWF universes localsWF registered
  cases levelsEqual with
  | cons universeEqual _ => exact Nat.noConfusion (VLevel.equiv_def.mp universeEqual [])

end

run_meta
  let environment ← getEnv
  let baseline ← collectAxioms ``VEnv.IsDefEq.church_rosser
  let mut owned := 0
  let mut pending := #[]
  for moduleName in #[`Lean4Lean.Theory.Typing.QuotInjectivity,
      `Lean4Lean.Theory.Typing.QuotReductionAutomatic] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "quotient injectivity module absent: {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned quotient injectivity axiom: {name}"
        let some proof := information.value? (allowOpaque := true) | throwError "owned quotient injectivity proof/value absent: {name}"
        if proof.hasSorry then throwError "owned quotient injectivity direct admission: {name}"
        let dependencies ← collectAxioms name
        for dependency in dependencies do
          unless baseline.contains dependency do
            throwError "unexpected quotient injectivity dependency: {dependency} in {name}"
        logInfo m!"{name}: {repr dependencies}"
        pending := pending.push name
        owned := owned + 1
  unless owned >= 20 do throwError "quotient injectivity audit incomplete: {owned}"
  for name in #[``VEnv.quot_inv, ``VEnv.ParRed.quot_head, ``VEnv.ParRed.quot_domain,
      ``VEnv.ParRed.quot_type, ``VEnv.ParRedS.quot_type, ``VEnv.NormalEq.quot_head,
      ``VEnv.NormalEq.quot_domain, ``VEnv.NormalEq.quot_type] do
    let dependencies ← collectAxioms name
    if dependencies.contains ``Classical.choice then
      throwError "structural quotient inversion acquired choice: {name}"
  for name in #[``VEnv.quotMk_hasType, ``VEnv.quotInd_beta] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "constructor/induction beta lost its admission-free boundary: {dependency} in {name}"
  let mut visited : NameSet := {}
  for _ in [:100000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "quotient injectivity dependency traversal exceeded its bound"
  for name in #[``VEnv.IsDefEq.church_rosser, ``VEnv.NormalEq.parRed,
      ``VEnv.WF.reductionParams, ``VEnv.WF.rewriteMetadata, ``VEnv.IsDefEqU.sort_inv] do
    unless visited.contains name do throwError "expected inherited quotient dependency absent: {name}"
  logInfo m!"{owned} owned quotient injectivity/alignment values have no direct admission or new axiom; the concrete model protects registered Quot spines, telescope typing rules out every proof-irrelevance branch, and both typed/normalized-major beta rules infer parameters without caller checks; existing confluence and sort-injectivity admissions remain explicit: {repr baseline}"

end QuotientInjectivityTest
