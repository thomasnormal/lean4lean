import Lean4Lean.Theory.Typing.QuotBetaSimulation
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotBetaSimulationTest
open Lean Lean4Lean Lean4Lean.VEnv
open Lean4Lean.VEnv.QuotConfluenceObstruction
open Lean4Lean.VEnv.QuotPropReduction

def equalityEnvironment : VEnv := {
  constants name := if ``Eq = name then some eqConst else none
  defeqs _ := False }
def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem quotientEnvironmentWF : quotientEnvironment.WF := by
  have added : VEnv.empty.addConst ``Eq eqConst = some equalityEnvironment := rfl
  have equalityWF : equalityEnvironment.WF := by
    refine ⟨_, .decl (.axiom (ci := ⟨eqConst, ``Eq⟩) ?_ added) .empty⟩
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : equalityEnvironment.QuotReady := by simp [QuotReady, equalityEnvironment]
  obtain ⟨_, checked⟩ := equalityWF
  exact ⟨_, .decl (.quot ready (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)) checked⟩

theorem quotientRegistered : quotientEnvironment.defeqs quotDefEq :=
  addQuot_defeq (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)


local instance : Params := quotientEnvironmentWF.reductionParams 0

def delay (type value : VExpr) : VExpr := .app (.lam type (.bvar 0)) value

theorem delayEqual {context : List VExpr} {type value : VExpr}
    (typed : quotientEnvironment.HasType 0 context value type) :
    quotientEnvironment.IsDefEq 0 context (delay type value) value type := by
  simpa [delay, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) typed

theorem delayReduction {context : List VExpr} (type value : VExpr) : ParRed context (delay type value) value := by
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := type :: context)) (ParRed.rfl (e := value)))



theorem domainTyped : quotientEnvironment.HasType 0 locals (.bvar 5) (.sort .zero) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem selectedTyped : quotientEnvironment.HasType 0 locals
    (selector (.bvar 5) (.bvar 4) (.bvar 0)) (.bvar 5) := by
  obtain ⟨_, inductionRegistered, _, constructorRegistered, quotientObject, _⟩ :=
    quotientEnvironmentWF.quotientObjects quotientRegistered
  have relationTyped : quotientEnvironment.HasType 0 locals (.bvar 4)
      (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  exact selector_hasType quotientEnvironmentWF.ordered quotientObject constructorRegistered
    inductionRegistered domainTyped relationTyped majorTyped

def leftDomain : VExpr := delay (.sort .zero) (.bvar 5)
def rightDomain : VExpr := delay (.sort .zero) leftDomain
def baseBody : VExpr := .forallE (.app (.bvar 4) (.bvar 0)) (.app (.bvar 5) (.bvar 1))
def body : VExpr := delay (.sort .zero) baseBody
def leftArgument : VExpr := delay (.bvar 5) (selector (.bvar 5) (.bvar 4) (.bvar 0))
def rightArgument : VExpr := delay (.bvar 5) (.bvar 1)
def originalType : VExpr := delay (.sort (.succ .zero)) (.sort .zero)

theorem leftDomainEqual : quotientEnvironment.IsDefEq 0 locals (.bvar 5) leftDomain (.sort .zero) :=
  (delayEqual domainTyped).symm

theorem rightDomainEqual : quotientEnvironment.IsDefEq 0 locals (.bvar 5) rightDomain (.sort .zero) :=
  ((delayEqual (delayEqual domainTyped).hasType.1).trans (delayEqual domainTyped)).symm

theorem baseBodyTyped : quotientEnvironment.HasType 0 (.bvar 5 :: locals) baseBody (.sort .zero) := by
  have natural : quotientEnvironment.HasType 0 (.bvar 5 :: locals) baseBody (.sort (.imax .zero .zero)) := by
    unfold baseBody
    apply HasType.forallE
    · exact HasType.app' (B := .sort .zero) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) rfl
    · exact HasType.app' (B := .sort .zero) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) rfl
  exact IsDefEq.defeq (.sortDF (by trivial) (by trivial)
    (VLevel.equiv_def.mpr (by intro values; rfl))) natural

theorem bodyTyped : quotientEnvironment.HasType 0 (.bvar 5 :: locals) body (.sort .zero) :=
  (delayEqual baseBodyTyped).hasType.1

theorem leftArgumentTyped : quotientEnvironment.HasType 0 locals leftArgument (.bvar 5) :=
  (delayEqual selectedTyped).hasType.1

theorem rightArgumentTyped : quotientEnvironment.HasType 0 locals rightArgument (.bvar 5) := by
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  exact (delayEqual witness).hasType.1

theorem argumentSimulation : CoreSimulates quotientEnvironmentWF 0 locals leftArgument rightArgument := by
  intro result reduction
  exact ⟨_, .tail .rfl (.core (delayReduction _ _)),
    .proofIrrel domainTyped selectedTyped
      (reduction.hasType (localsWF quotientEnvironmentWF quotientRegistered) rightArgumentTyped)⟩

theorem originalTyped : quotientEnvironment.HasType 0 locals
    (.app (.lam leftDomain body) leftArgument) originalType := by
  have domainConverted := bodyTyped.defeqDFC quotientEnvironmentWF.ordered (.succ .zero leftDomainEqual)
  have argumentConverted := leftDomainEqual.defeq leftArgumentTyped
  have applied := leftDomainEqual.hasType.2.lam domainConverted |>.app argumentConverted
  have sortTyped : quotientEnvironment.HasType 0 locals (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  exact (delayEqual sortTyped).symm.defeq (by simpa [VExpr.inst] using applied)

-- Body beta, argument beta, different converted lambda domains, and two copies
-- of the changed proof underneath a dependent forall all occur in this branch.
theorem betaControl : ∃ result,
    ParRed locals (.app (.lam rightDomain body) rightArgument) (baseBody.inst (.bvar 1)) ∧
    Steps quotientEnvironmentWF 0 locals (.app (.lam leftDomain body) leftArgument) result ∧
    NormalEq locals result (baseBody.inst (.bvar 1)) ∧
    quotientEnvironment.HasType 0 locals result originalType ∧
    quotientEnvironment.HasType 0 locals (baseBody.inst (.bvar 1)) originalType := by
  have extendedWF : OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) :=
    ⟨localsWF quotientEnvironmentWF quotientRegistered, _, domainTyped⟩
  have converted := bodyTyped.defeqDFC quotientEnvironmentWF.ordered (.succ .zero rightDomainEqual)
  exact CoreSimulates.lam_beta quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    leftDomainEqual rightDomainEqual leftArgumentTyped originalTyped
    (CoreSimulates.refl extendedWF bodyTyped) argumentSimulation
    (delayReduction _ _) converted (delayReduction _ _)

example : leftDomain ≠ rightDomain := by intro equal; cases equal
example : originalType ≠ .sort .zero := by intro equal; cases equal
example : baseBody.inst (.bvar 1) =
    .forallE (.app (.bvar 3) (.bvar 1)) (.app (.bvar 4) (.bvar 2)) := rfl

-- The argument path itself can contain new unfolding, duplicated in a domain
-- and beneath its dependent binder.
theorem unfoldingArgument : ∃ result,
    QuotPropReduction.unfold neutral = some result ∧
    Steps quotientEnvironmentWF 0 locals
      ((.forallE (.bvar 0) (.bvar 1) : VExpr).inst neutral)
      ((.forallE (.bvar 0) (.bvar 1) : VExpr).inst result) ∧
    quotientEnvironment.HasType 0 locals
      ((.forallE (.bvar 0) (.bvar 1) : VExpr).inst result) (.sort .zero) := by
  have computed : QuotPropReduction.unfold neutral =
      some (.app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))) := rfl
  have path : Steps quotientEnvironmentWF 0 locals neutral
      (.app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))) := .tail .rfl (.unfold computed)
  have substituted := path.instN_argument (expression := .forallE (.bvar 0) (.bvar 1))
    (Ctx.InstN.zero (A₀ := .sort .zero))
  have bodyTyped : quotientEnvironment.HasType 0 (.sort .zero :: locals)
      (.forallE (.bvar 0) (.bvar 1)) (.sort (.imax .zero .zero)) :=
    .forallE (.bvar .zero) (.bvar (.succ .zero))
  have typed := bodyTyped.instN quotientEnvironmentWF.ordered Ctx.InstN.zero
    (neutralTyped quotientEnvironmentWF quotientRegistered)
  exact ⟨_, computed, substituted,
    IsDefEq.defeq (.sortDF (by trivial) (by trivial)
      (VLevel.equiv_def.mpr (by intro values; rfl)))
      (substituted.hasType quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered) typed)⟩

def etaUseBody : VExpr := .forallE (.app (.bvar 0) (.bvar 2)) (.app (.bvar 1) (.bvar 3))

theorem etaArgument :
    Steps quotientEnvironmentWF 0 locals (etaUseBody.inst (.bvar 3))
      (etaUseBody.inst (.lam (.bvar 5) (.app (VExpr.bvar 3).lift (.bvar 0)))) ∧
    quotientEnvironment.HasType 0 locals
      (etaUseBody.inst (.lam (.bvar 5) (.app (VExpr.bvar 3).lift (.bvar 0)))) (.sort .zero) := by
  have typed : quotientEnvironment.HasType 0 locals (.bvar 3) (.forallE (.bvar 5) (.sort .zero)) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  have path : Steps quotientEnvironmentWF 0 locals (.bvar 3)
      (.lam (.bvar 5) (.app (VExpr.bvar 3).lift (.bvar 0))) := .tail .rfl (.funEta typed)
  have substituted := path.instN_argument (expression := etaUseBody)
    (Ctx.InstN.zero (A₀ := .forallE (.bvar 5) (.sort .zero)))
  have bodyTyped : quotientEnvironment.HasType 0 (.forallE (.bvar 5) (.sort .zero) :: locals)
      etaUseBody (.sort (.imax .zero .zero)) := by
    unfold etaUseBody
    apply HasType.forallE
    · exact HasType.app' (B := .sort .zero) (HasType.bvar .zero) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) rfl
    · exact HasType.app' (B := .sort .zero) (HasType.bvar (.succ .zero)) (by unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient; type_tac) rfl
  have originalTyped := bodyTyped.instN quotientEnvironmentWF.ordered Ctx.InstN.zero typed
  exact ⟨substituted, IsDefEq.defeq (.sortDF (by trivial) (by trivial)
    (VLevel.equiv_def.mpr (by intro values; rfl)))
    (substituted.hasType quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered) originalTyped)⟩

theorem retainedDependentBinder : ∃ result,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals)
      (VExpr.app (.lam leftDomain body) leftArgument).lift result.lift ∧
    NormalEq (.bvar 5 :: locals) result.lift (baseBody.inst (.bvar 1)).lift ∧
    Steps quotientEnvironmentWF 0 locals (.app (.lam leftDomain body) leftArgument) result ∧
    NormalEq locals result (baseBody.inst (.bvar 1)) := by
  obtain ⟨result, _, path, normal, _, _⟩ := betaControl
  have retainedPath := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  exact ⟨result, retainedPath, retainedNormal,
    by simpa only [VExpr.inst_lift] using retainedPath.instN Ctx.InstN.zero witness,
    by simpa only [VExpr.inst_lift] using retainedNormal.instN witness Ctx.InstN.zero⟩

run_meta
  let environment ← getEnv
  let roots := [``Steps.lam_congr, ``Steps.instN_argument, ``Steps.instN_both, ``CoreSimulates.lam_beta, ``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual, ``delayReduction, ``domainTyped, ``selectedTyped, ``leftDomainEqual, ``rightDomainEqual, ``baseBodyTyped, ``bodyTyped, ``leftArgumentTyped, ``rightArgumentTyped, ``argumentSimulation, ``originalTyped, ``betaControl, ``unfoldingArgument, ``etaArgument, ``retainedDependentBinder]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC,
    ``ParRed.weakN_inv, ``NormalEq.trans,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.Steps.lam_congr, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.Steps.instN_argument, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.Steps.instN_both, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.lam_beta, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.quotientEnvironmentWF, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.quotientRegistered, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.delayEqual, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.delayReduction, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.domainTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.selectedTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.leftDomainEqual, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.rightDomainEqual, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.baseBodyTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.bodyTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.leftArgumentTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.rightArgumentTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.argumentSimulation, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.originalTyped, [], [`propext, `Quot.sound]),
    (`QuotBetaSimulationTest.betaControl, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.unfoldingArgument, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.etaArgument, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotBetaSimulationTest.retainedDependentBinder, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new axiom {root}"
    let some proof := info.value? | throwError "missing proof {root}"
    if proof.hasSorry then throwError "direct admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then
          throwError "admitted declaration type {name} in {root}"
        if let some value := declaration.value? then
          if value.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unapproved admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``Steps.instN_argument then [``Steps.weakN, ``Steps.lam_congr, ``Steps.forallE, ``Steps.app]
      else if root == ``Steps.instN_both then [``Steps.instN, ``Steps.instN_argument]
      else if root == ``CoreSimulates.lam_beta then [``NormalEq.instDF, ``Steps.instN_both, ``ParRed.beta, ``ParRed.defeqDFC, ``Steps.hasType]
      else if root == ``betaControl then [``CoreSimulates.lam_beta, ``argumentSimulation, ``delayReduction, ``NormalEq.proofIrrel]
      else if root == ``unfoldingArgument then [``Step.unfold, ``Steps.instN_argument, ``Steps.hasType]
      else if root == ``etaArgument then [``Step.funEta, ``Steps.instN_argument, ``Steps.hasType]
      else if root == ``retainedDependentBinder then [``betaControl, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN, ``NormalEq.instN]
      else []
    unless required.all visited.contains do
      throwError "control bypassed a required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"

end QuotBetaSimulationTest
