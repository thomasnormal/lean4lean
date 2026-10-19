import Lean4Lean.Theory.Typing.QuotNormalBeta
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotNormalBetaTest
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

theorem functionTyped : quotientEnvironment.HasType 0 locals (.bvar 3)
    (.forallE (.bvar 5) (.sort .zero)) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem witnessTyped : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem argumentsNormal : NormalEq locals
    (selector (.bvar 5) (.bvar 4) (.bvar 0)) (.bvar 1) :=
  .proofIrrel domainTyped selectedTyped witnessTyped

-- The source function is a VARIABLE, not a lambda or a proof-valued function.
theorem neutralEtaRight : ∃ result,
    Steps quotientEnvironmentWF 0 locals
      (.app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))) result ∧
    NormalEq locals result (.app (.bvar 3) (.bvar 1)) := by
  have normal : NormalEq locals (.bvar 3)
      (.lam (.bvar 5) (.app (VExpr.bvar 3).lift (.bvar 0))) :=
    .etaR functionTyped (.refl (etaBody_hasType quotientEnvironmentWF.ordered functionTyped))
  simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
    normal_beta_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered) normal
      argumentsNormal (functionTyped.app selectedTyped)

-- Explicit application congruence at the leaves exercises the spine
-- classifier rather than using reflexivity of the whole application.
theorem explicitNormal {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) : NormalEq context expression expression := by
  cases expression with
  | app function argument =>
    obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv quotientEnvironmentWF.ordered contextWF
    exact .appDF functionTyped functionTyped argumentTyped argumentTyped (.refl functionTyped) (.refl argumentTyped)
  | _ => exact .refl typed

def etaTree : Nat → VExpr → VExpr → VExpr
  | 0, expression, _ => expression
  | depth + 1, expression, .forallE domain body =>
    .lam domain (etaTree depth (.app expression.lift (.bvar 0)) body)
  | _ + 1, expression, _ => expression

theorem etaTreeNormal {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) (depth : Nat) :
    NormalEq context (etaTree depth expression type) expression := by
  induction depth generalizing context expression type with
  | zero => exact explicitNormal contextWF typed
  | succ depth induction =>
    cases type <;> try exact .refl typed
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := typed.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    exact .etaL typed (induction ⟨contextWF, _, domainTyped⟩
      (etaBody_hasType quotientEnvironmentWF.ordered typed))

theorem etaTreeSimulation {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) (depth : Nat) :
    CoreSimulates quotientEnvironmentWF 0 context (etaTree depth expression type) expression := by
  induction depth generalizing context expression type with
  | zero => exact CoreSimulates.refl contextWF typed
  | succ depth induction =>
    cases type <;> try exact CoreSimulates.refl contextWF typed
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := typed.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    have extendedWF : OnCtx (domain :: context) (quotientEnvironment.IsType 0) :=
      ⟨contextWF, _, domainTyped⟩
    intro result reduction
    exact CoreSimulates.etaL contextWF typed (induction extendedWF
      (etaBody_hasType quotientEnvironmentWF.ordered typed)) reduction

def binaryType : VExpr := .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
def binaryLevel : VLevel := .imax .zero (.imax .zero (.succ .zero))

theorem binaryTypeTyped : quotientEnvironment.HasType 0 locals binaryType (.sort binaryLevel) := by
  apply HasType.forallE domainTyped
  exact HasType.forallE (domainTyped.weak quotientEnvironmentWF.ordered) (HasType.sort (by trivial))

def plainArgument : VExpr := .lam (.bvar 5) (.bvar 4)
def expandedArgument : VExpr := .lam (.bvar 5) (.lam (.bvar 6) (.app (.bvar 5) (.bvar 0)))

theorem plainArgumentTyped : quotientEnvironment.HasType 0 locals plainArgument binaryType := by
  have lifted := functionTyped.weak quotientEnvironmentWF.ordered (B := .bvar 5)
  exact domainTyped.lam (by simpa [HasType, VExpr.lift, VExpr.liftN, liftVar] using lifted)

theorem changedArguments : NormalEq locals plainArgument expandedArgument := by
  have lifted : quotientEnvironment.HasType 0 (.bvar 5 :: locals) (.bvar 4)
      (.forallE (.bvar 6) (.sort .zero)) := by
    simpa [HasType, VExpr.lift, VExpr.liftN, liftVar] using
      functionTyped.weak quotientEnvironmentWF.ordered (B := .bvar 5)
  exact .lamDF domainTyped domainTyped (.etaR lifted (.refl (etaBody_hasType quotientEnvironmentWF.ordered lifted)))

theorem expandedArgumentTyped : quotientEnvironment.HasType 0 locals expandedArgument binaryType :=
  ((changedArguments.defeq (localsWF quotientEnvironmentWF quotientRegistered)).of_l
    quotientEnvironmentWF (localsWF quotientEnvironmentWF quotientRegistered) plainArgumentTyped).hasType.2

def delayedIdentity : VExpr := .lam binaryType (delay binaryType.lift (.bvar 0))
def identityType : VExpr := .forallE binaryType binaryType.lift

theorem delayedIdentityTyped : quotientEnvironment.HasType 0 locals delayedIdentity identityType :=
  binaryTypeTyped.lam (delayEqual (HasType.bvar .zero)).hasType.1

def deepEta : VExpr := etaTree 3 delayedIdentity identityType

theorem deepEtaTyped : quotientEnvironment.HasType 0 locals deepEta identityType :=
  (((etaTreeNormal (localsWF quotientEnvironmentWF quotientRegistered) delayedIdentityTyped 3).defeq
    (localsWF quotientEnvironmentWF quotientRegistered)).symm.of_l quotientEnvironmentWF
      (localsWF quotientEnvironmentWF quotientRegistered) delayedIdentityTyped).hasType.2

-- Three nested eta binders, application congruence beneath them, and different
-- NONPROPOSITIONAL function arguments exercise both retained-spine cases.
theorem deepNormalBeta : ∃ result,
    Steps quotientEnvironmentWF 0 locals (.app deepEta plainArgument) result ∧
    NormalEq locals result (delay binaryType expandedArgument) := by
  simpa [deepEta, delayedIdentity, delay, VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
    normal_beta_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
      (etaTreeNormal (localsWF quotientEnvironmentWF quotientRegistered) delayedIdentityTyped 3)
      changedArguments (deepEtaTyped.app plainArgumentTyped)

example : plainArgument ≠ expandedArgument := by intro equal; cases equal
example : deepEta ≠ delayedIdentity := by intro equal; cases equal
example : deepEta = .lam binaryType
    (.lam (.bvar 6) (.lam (.bvar 7)
      (.app (.app (.app delayedIdentity.lift.lift.lift (.bvar 2)) (.bvar 1)) (.bvar 0)))) := rfl

def originalType : VExpr := delay (.sort binaryLevel) binaryType

theorem originalTyped : quotientEnvironment.HasType 0 locals
    (.app deepEta (delay binaryType expandedArgument)) originalType := by
  have natural := deepEtaTyped.app (delayEqual expandedArgumentTyped).hasType.1
  exact (delayEqual binaryTypeTyped).symm.defeq (by simpa only [VExpr.inst_lift] using natural)

-- The universal application clause consumes only the function/argument IHs.
-- Both the ACTUAL target body and its argument take nontrivial beta steps.
theorem generalBeta : ∃ result,
    ParRed locals (.app delayedIdentity (delay binaryType expandedArgument)) expandedArgument ∧
    Steps quotientEnvironmentWF 0 locals (.app deepEta (delay binaryType expandedArgument)) result ∧
    NormalEq locals result expandedArgument ∧
    quotientEnvironment.HasType 0 locals result originalType ∧
    quotientEnvironment.HasType 0 locals expandedArgument originalType := by
  simpa [delayedIdentity, VExpr.inst, VExpr.instVar_zero] using
    CoreSimulates.app_beta quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered) originalTyped
      (etaTreeSimulation (localsWF quotientEnvironmentWF quotientRegistered) delayedIdentityTyped 3)
      (CoreSimulates.refl (localsWF quotientEnvironmentWF quotientRegistered)
        (delayEqual expandedArgumentTyped).hasType.1)
      (delayReduction _ _) (delayReduction _ _)

example : originalType ≠ binaryType := by intro equal; cases equal
example : delay binaryType.lift (.bvar 0) ≠ VExpr.bvar 0 := by intro equal; cases equal
example : delay binaryType expandedArgument ≠ expandedArgument := by intro equal; cases equal

theorem retainedDependentBinder : ∃ result,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals)
      (VExpr.app deepEta (delay binaryType expandedArgument)).lift result.lift ∧
    NormalEq (.bvar 5 :: locals) result.lift expandedArgument.lift ∧
    Steps quotientEnvironmentWF 0 locals (.app deepEta (delay binaryType expandedArgument)) result ∧
    NormalEq locals result expandedArgument := by
  obtain ⟨result, _, path, normal, _, _⟩ := generalBeta
  have retainedPath := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  exact ⟨result, retainedPath, retainedNormal,
    by simpa only [VExpr.inst_lift] using retainedPath.instN Ctx.InstN.zero witnessTyped,
    by simpa only [VExpr.inst_lift] using retainedNormal.instN witnessTyped Ctx.InstN.zero⟩

-- Function proof irrelevance: the result is a proof even though source and
-- target functions, and their arguments, differ. This quantifies over every
-- actual core successor, not just a hand-picked beta.
def proofLocals : List VExpr := .forallE (.bvar 5) (.bvar 6) :: locals

theorem proofLocalsWF : OnCtx proofLocals (quotientEnvironment.IsType 0) :=
  ⟨localsWF quotientEnvironmentWF quotientRegistered, _, HasType.forallE domainTyped
    (domainTyped.weak quotientEnvironmentWF.ordered)⟩

theorem proofFunctionTyped : quotientEnvironment.HasType 0 proofLocals (.bvar 0)
    (.forallE (.bvar 6) (.bvar 7)) := by unfold proofLocals; type_tac

theorem proofFunctionProposition : quotientEnvironment.HasType 0 proofLocals
    (.forallE (.bvar 6) (.bvar 7)) (.sort .zero) := by
  have natural : quotientEnvironment.HasType 0 proofLocals
      (.forallE (.bvar 6) (.bvar 7)) (.sort (.imax .zero .zero)) := by
    unfold proofLocals locals respectType functionType relationType QuotConfluenceObstruction.quotient
    apply HasType.forallE <;> type_tac
  exact IsDefEq.defeq (.sortDF (by trivial) (by trivial)
    (VLevel.equiv_def.mpr (by intro values; rfl))) natural

theorem proofFunctionSimulation : CoreSimulates quotientEnvironmentWF 0 proofLocals
    (.app (.bvar 0) (delay (.bvar 6) (.bvar 2))) (.app (.lam (.bvar 6) (.bvar 3)) (.bvar 2)) := by
  have domainTyped' : quotientEnvironment.HasType 0 proofLocals (.bvar 6) (.sort .zero) := by
    unfold proofLocals locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  have rightFunction : quotientEnvironment.HasType 0 proofLocals (.lam (.bvar 6) (.bvar 3))
      (.forallE (.bvar 6) (.bvar 7)) := by
    unfold proofLocals locals respectType functionType relationType QuotConfluenceObstruction.quotient
    exact HasType.lam (by type_tac) (by type_tac)
  have rightArgument : quotientEnvironment.HasType 0 proofLocals (.bvar 2) (.bvar 6) := by
    unfold proofLocals locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  have leftArgument := (delayEqual rightArgument).hasType.1
  intro result reduction
  exact CoreSimulates.proof_application proofLocalsWF proofFunctionProposition proofFunctionTyped
    rightFunction proofFunctionTyped leftArgument (.proofIrrel domainTyped' leftArgument rightArgument) reduction

theorem proofApplicationTyped : quotientEnvironment.HasType 0 proofLocals
    (.app (.bvar 0) (delay (.bvar 6) (.bvar 2))) (.bvar 6) := by
  have argumentTyped : quotientEnvironment.HasType 0 proofLocals (.bvar 2) (.bvar 6) := by
    unfold proofLocals locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  simpa [VExpr.inst, VExpr.instVar] using proofFunctionTyped.app (delayEqual argumentTyped).hasType.1

theorem proofBetaControl :
    ParRed proofLocals (.app (.lam (.bvar 6) (.bvar 3)) (.bvar 2)) (.bvar 2) ∧
    ∃ result, Steps quotientEnvironmentWF 0 proofLocals
        (.app (.bvar 0) (delay (.bvar 6) (.bvar 2))) result ∧
      NormalEq proofLocals result (.bvar 2) ∧
      quotientEnvironment.HasType 0 proofLocals result (.bvar 6) ∧
      quotientEnvironment.HasType 0 proofLocals (.bvar 2) (.bvar 6) := by
  have beta : ParRed proofLocals (.app (.lam (.bvar 6) (.bvar 3)) (.bvar 2)) (.bvar 2) := by
    simpa [VExpr.inst, VExpr.instVar] using
      (ParRed.beta (A := .bvar 6) (Γ := proofLocals) (ParRed.bvar (i := 3)) (ParRed.bvar (i := 2)))
  exact ⟨beta, CoreSimulates.typed quotientRegistered proofLocalsWF proofApplicationTyped
    (fun reduction => proofFunctionSimulation reduction) beta⟩

run_meta
  let environment ← getEnv
  let roots := [``CoreSimulates.proof_application, ``ParRedExt.beta_forward, ``normal_beta_join, ``CoreSimulates.app_beta, ``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual, ``delayReduction, ``domainTyped, ``selectedTyped, ``functionTyped, ``witnessTyped, ``argumentsNormal, ``neutralEtaRight, ``explicitNormal, ``etaTreeNormal, ``etaTreeSimulation, ``binaryTypeTyped, ``plainArgumentTyped, ``changedArguments, ``expandedArgumentTyped, ``delayedIdentityTyped, ``deepEtaTyped, ``deepNormalBeta, ``originalTyped, ``generalBeta, ``retainedDependentBinder, ``proofLocalsWF, ``proofFunctionTyped, ``proofFunctionProposition, ``proofFunctionSimulation, ``proofApplicationTyped, ``proofBetaControl]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``HasType.weakN_iff,
    ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC, ``NormalEq.trans,
    ``ParRed.weakN_inv, ``ParRedExt.parRed_beta, ``hasType_app_bvar0,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.proof_application, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.ParRedExt.beta_forward, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_beta_join, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_beta, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.quotientEnvironmentWF, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.quotientRegistered, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.delayEqual, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.delayReduction, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.domainTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.selectedTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.functionTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.witnessTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.argumentsNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.neutralEtaRight, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.explicitNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.etaTreeNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.etaTreeSimulation, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.binaryTypeTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.plainArgumentTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.changedArguments, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.expandedArgumentTyped, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.delayedIdentityTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.deepEtaTyped, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.deepNormalBeta, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.originalTyped, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.generalBeta, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.retainedDependentBinder, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.proofLocalsWF, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.proofFunctionTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.proofFunctionProposition, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.proofFunctionSimulation, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalBetaTest.proofApplicationTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalBetaTest.proofBetaControl, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing beta manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new beta axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing beta proof {root}"
    if proof.hasSorry then throwError "direct beta admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "beta axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden beta dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then throwError "admitted type {name} in {root}"
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved beta admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "beta traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "beta admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``CoreSimulates.proof_application then [``NormalEq.proofIrrel, ``ParRed.hasType, ``IsDefEq.uniqU]
      else if root == ``ParRedExt.beta_forward then [``ParRed.beta, ``ParRed.weakN, ``ParRed.app]
      else if root == ``normal_beta_join then [``ParRedExt.beta_forward, ``NormalEq.instDF, ``CoreSimulates.proof_application, ``Steps.instN, ``Steps.hasType, ``Steps.app, ``Steps.lam, ``VExpr.brecOn]
      else if root == ``CoreSimulates.app_beta then [``normal_beta_join, ``ParRed.lam, ``ParRed.beta, ``Steps.app, ``Steps.hasType]
      else if root == ``neutralEtaRight then [``normal_beta_join, ``NormalEq.etaR, ``argumentsNormal]
      else if root == ``deepNormalBeta then [``normal_beta_join, ``etaTreeNormal, ``changedArguments, ``explicitNormal]
      else if root == ``generalBeta then [``CoreSimulates.app_beta, ``etaTreeSimulation, ``delayReduction, ``originalTyped]
      else if root == ``retainedDependentBinder then [``generalBeta, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN, ``NormalEq.instN]
      else if root == ``proofFunctionSimulation then [``CoreSimulates.proof_application]
      else if root == ``proofBetaControl then [``proofFunctionSimulation, ``ParRed.beta, ``CoreSimulates.typed]
      else []
    unless required.all visited.contains do
      throwError "beta control bypassed a required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"

end QuotNormalBetaTest
