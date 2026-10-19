import Lean4Lean.Theory.Typing.QuotEtaSimulation
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotEtaSimulationTest
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


def domain : VExpr := delay (.sort .zero) (.bvar 5)
def function : VExpr := .lam domain (.bvar 6)
def functionType : VExpr := .forallE domain (.sort .zero)
def etaFunction : VExpr := .lam domain (.app function.lift (.bvar 0))
def plainFunction : VExpr := .lam (.bvar 5) (.bvar 6)

theorem domainTyped : quotientEnvironment.HasType 0 locals domain (.sort .zero) := by
  unfold domain
  apply (delayEqual ?_).hasType.1
  unfold locals respectType Lean4Lean.VEnv.QuotConfluenceObstruction.functionType relationType Lean4Lean.VEnv.QuotConfluenceObstruction.quotient
  type_tac

theorem plainDomainTyped : quotientEnvironment.HasType 0 locals (.bvar 5) (.sort .zero) := by
  unfold locals respectType Lean4Lean.VEnv.QuotConfluenceObstruction.functionType relationType
    Lean4Lean.VEnv.QuotConfluenceObstruction.quotient
  type_tac

theorem bodyTyped : quotientEnvironment.HasType 0 (.bvar 5 :: locals) (.bvar 6) (.sort .zero) := by
  simpa [HasType, VExpr.lift, VExpr.liftN, liftVar] using plainDomainTyped.weak quotientEnvironmentWF.ordered

theorem functionTyped : quotientEnvironment.HasType 0 locals function functionType := by
  have lifted := plainDomainTyped.weak quotientEnvironmentWF.ordered (B := domain)
  exact domainTyped.lam (by simpa [HasType, VExpr.lift, VExpr.liftN, liftVar] using lifted)

theorem functionReduces : ParRed locals function plainFunction :=
  .lam (delayReduction _ _) .bvar

theorem etaReduces : ParRed locals etaFunction plainFunction := by
  refine .lam (delayReduction _ _) ?_
  simpa [function, VExpr.lift, VExpr.liftN, liftVar, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (A := domain.lift) (Γ := domain :: locals)
      (ParRed.rfl (e := .bvar 7)) (ParRed.bvar (i := 0)))

example : domain ≠ .bvar 5 := by intro equal; cases equal
example : etaFunction ≠ plainFunction := by intro equal; cases equal

theorem etaRSimulation : CoreSimulates quotientEnvironmentWF 0 locals function etaFunction := by
  intro result reduction
  have extendedWF : OnCtx (domain :: locals) (quotientEnvironment.IsType 0) :=
    ⟨localsWF quotientEnvironmentWF quotientRegistered, _, domainTyped⟩
  exact CoreSimulates.etaR (localsWF quotientEnvironmentWF quotientRegistered) functionTyped
    (CoreSimulates.refl extendedWF (etaBody_hasType quotientEnvironmentWF.ordered functionTyped)) reduction

-- This quantifies over the ACTUAL reduction of the target lambda, including
-- beta in its body and simultaneous domain reduction. No inverse is supplied.
theorem arbitraryEtaR {result : VExpr} (reduction : ParRed locals etaFunction result) :
    ∃ leftResult, Steps quotientEnvironmentWF 0 locals function leftResult ∧
      NormalEq locals leftResult result ∧
      quotientEnvironment.HasType 0 locals leftResult functionType ∧
      quotientEnvironment.HasType 0 locals result functionType :=
  etaRSimulation.typed quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    functionTyped reduction

theorem concreteEtaR : ∃ leftResult, Steps quotientEnvironmentWF 0 locals function leftResult ∧
    NormalEq locals leftResult plainFunction ∧
    quotientEnvironment.HasType 0 locals leftResult functionType ∧
    quotientEnvironment.HasType 0 locals plainFunction functionType := arbitraryEtaR etaReduces

theorem etaLSimulation : CoreSimulates quotientEnvironmentWF 0 locals etaFunction function := by
  intro result reduction
  have extendedWF : OnCtx (domain :: locals) (quotientEnvironment.IsType 0) :=
    ⟨localsWF quotientEnvironmentWF quotientRegistered, _, domainTyped⟩
  exact CoreSimulates.etaL (localsWF quotientEnvironmentWF quotientRegistered) functionTyped
    (CoreSimulates.refl extendedWF (etaBody_hasType quotientEnvironmentWF.ordered functionTyped)) reduction

theorem concreteEtaL : ∃ leftResult, Steps quotientEnvironmentWF 0 locals etaFunction leftResult ∧
    NormalEq locals leftResult plainFunction ∧
    quotientEnvironment.HasType 0 locals leftResult functionType ∧
    quotientEnvironment.HasType 0 locals plainFunction functionType :=
  etaLSimulation.typed quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    (IsDefEq.eta functionTyped).hasType.1 functionReduces

theorem lambdaSimulation : CoreSimulates quotientEnvironmentWF 0 locals plainFunction function := by
  intro result reduction
  have commonWF : OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) :=
    ⟨localsWF quotientEnvironmentWF quotientRegistered, _, plainDomainTyped⟩
  exact CoreSimulates.lamDF quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    plainDomainTyped (delayEqual plainDomainTyped).symm (.refl bodyTyped) (CoreSimulates.refl commonWF bodyTyped) reduction

theorem lambdaControl : ∃ leftResult, Steps quotientEnvironmentWF 0 locals plainFunction leftResult ∧
    NormalEq locals leftResult plainFunction ∧
    quotientEnvironment.HasType 0 locals leftResult (.forallE (.bvar 5) (.sort .zero)) ∧
    quotientEnvironment.HasType 0 locals plainFunction (.forallE (.bvar 5) (.sort .zero)) :=
  lambdaSimulation.typed quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    (plainDomainTyped.lam bodyTyped) functionReduces

def forallSource : VExpr := .forallE domain (.bvar 6)

theorem forallSimulation : CoreSimulates quotientEnvironmentWF 0 locals forallSource forallSource := by
  intro result reduction
  have commonWF : OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) :=
    ⟨localsWF quotientEnvironmentWF quotientRegistered, _, plainDomainTyped⟩
  exact CoreSimulates.forallEDF quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    (delayEqual plainDomainTyped).symm (.refl domainTyped) bodyTyped (.refl bodyTyped)
    (CoreSimulates.refl (localsWF quotientEnvironmentWF quotientRegistered) domainTyped) (CoreSimulates.refl commonWF bodyTyped) reduction

theorem forallControl : ∃ leftResult, Steps quotientEnvironmentWF 0 locals forallSource leftResult ∧
    NormalEq locals leftResult (.forallE (.bvar 5) (.bvar 6)) :=
  forallSimulation (.forallE (delayReduction _ _) .bvar)

-- The finite candidate path contains ALL THREE root kinds: original core,
-- canonical unfolding under a lambda, and another typed eta expansion.
def wrapper : VExpr := .lam domain neutral.lift
def unfoldedNeutral : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))
def unfoldedWrapper : VExpr := .lam (.bvar 5) unfoldedNeutral.lift

theorem wrapperTyped : quotientEnvironment.HasType 0 locals wrapper functionType :=
  domainTyped.lam ((neutralTyped quotientEnvironmentWF quotientRegistered).weak quotientEnvironmentWF.ordered)

theorem allKindsPath : Steps quotientEnvironmentWF 0 locals wrapper
    (.lam domain (.app unfoldedWrapper.lift (.bvar 0))) := by
  have unfolded : QuotPropReduction.unfold neutral = some unfoldedNeutral := rfl
  have initial : Steps quotientEnvironmentWF 0 locals wrapper unfoldedWrapper :=
    .tail (.tail .rfl (.core (.lam (delayReduction _ _) .rfl)))
      (.lam (.core .rfl) (.unfold (unfold_liftN unfolded 1 0)))
  exact .tail initial (.funEta (initial.hasType quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered) wrapperTyped))

theorem allKindsEtaJoin : ∃ result,
    Steps quotientEnvironmentWF 0 locals wrapper result ∧
    Steps quotientEnvironmentWF 0 locals (.lam domain (.app wrapper.lift (.bvar 0)))
      (.lam domain (.app result.lift (.bvar 0))) ∧
    Step quotientEnvironmentWF 0 locals result (.lam domain (.app result.lift (.bvar 0))) ∧
    quotientEnvironment.HasType 0 locals (.lam domain (.app result.lift (.bvar 0))) functionType := by
  obtain ⟨path, eta, typed⟩ := eta_steps_join quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered) wrapperTyped wrapperTyped allKindsPath
  exact ⟨_, allKindsPath, path, eta, typed⟩

-- Both paths of the eta/application diamond change the function AND argument.
def delayedProof : VExpr := delay (.bvar 5) (.bvar 1)

theorem delayedProofTyped : quotientEnvironment.HasType 0 locals delayedProof domain := by
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType Lean4Lean.VEnv.QuotConfluenceObstruction.functionType relationType
      Lean4Lean.VEnv.QuotConfluenceObstruction.quotient
    type_tac
  exact (delayEqual plainDomainTyped).symm.defeq (delayEqual witness).hasType.1

theorem applicationJoin :
    Step quotientEnvironmentWF 0 locals (.app function delayedProof) (.app etaFunction delayedProof) ∧
    Steps quotientEnvironmentWF 0 locals (.app etaFunction delayedProof) (.app plainFunction (.bvar 1)) ∧
    Steps quotientEnvironmentWF 0 locals (.app function delayedProof) (.app plainFunction (.bvar 1)) ∧
    quotientEnvironment.HasType 0 locals (.app plainFunction (.bvar 1)) (.sort .zero) := by
  exact eta_apply_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    functionTyped (by simpa [functionType, VExpr.inst] using functionTyped.app delayedProofTyped)
    (ReflTransGen.tail .rfl (.core functionReduces))
    (ReflTransGen.tail .rfl (.core (delayReduction _ _)))

theorem applicationCongruence : ∃ leftResult,
    Steps quotientEnvironmentWF 0 locals (.app function delayedProof) leftResult ∧
    NormalEq locals leftResult (.app plainFunction (.bvar 1)) :=
  CoreSimulates.app_congr quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    functionTyped functionTyped delayedProofTyped delayedProofTyped
    (CoreSimulates.refl (localsWF quotientEnvironmentWF quotientRegistered) functionTyped)
    (CoreSimulates.refl (localsWF quotientEnvironmentWF quotientRegistered) delayedProofTyped)
    functionReduces (delayReduction _ _)

theorem retainedDependentBinder : ∃ leftResult,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) function.lift leftResult.lift ∧
    NormalEq (.bvar 5 :: locals) leftResult.lift plainFunction.lift ∧
    Steps quotientEnvironmentWF 0 locals function leftResult ∧ NormalEq locals leftResult plainFunction := by
  obtain ⟨result, steps, normal, _, _⟩ := concreteEtaR
  have retainedSteps := steps.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType Lean4Lean.VEnv.QuotConfluenceObstruction.functionType relationType
      Lean4Lean.VEnv.QuotConfluenceObstruction.quotient
    type_tac
  exact ⟨result, retainedSteps, retainedNormal,
    by simpa only [VExpr.inst_lift] using retainedSteps.instN Ctx.InstN.zero witness,
    by simpa only [VExpr.inst_lift] using retainedNormal.instN witness Ctx.InstN.zero⟩


-- The dependent result really changes syntactically with the reduced argument.
-- The theorem must preserve its ORIGINAL delayed result type.
def dependentType : VExpr := .forallE (.sort .zero) (.bvar 0)
def dependentLocals : List VExpr := dependentType :: locals
def dependentFunction : VExpr := delay dependentType (.bvar 0)
def dependentArgument : VExpr := delay (.sort .zero) (.bvar 6)

theorem dependentApplicationJoin :
    Step quotientEnvironmentWF 0 dependentLocals (.app dependentFunction dependentArgument)
      (.app (.lam (.sort .zero) (.app dependentFunction.lift (.bvar 0))) dependentArgument) ∧
    Steps quotientEnvironmentWF 0 dependentLocals
      (.app (.lam (.sort .zero) (.app dependentFunction.lift (.bvar 0))) dependentArgument)
      (.app (.bvar 0) (.bvar 6)) ∧
    Steps quotientEnvironmentWF 0 dependentLocals (.app dependentFunction dependentArgument)
      (.app (.bvar 0) (.bvar 6)) ∧
    quotientEnvironment.HasType 0 dependentLocals (.app (.bvar 0) (.bvar 6)) dependentArgument := by
  have extendedWF : OnCtx dependentLocals (quotientEnvironment.IsType 0) := by
    have typeTyped : quotientEnvironment.HasType 0 locals dependentType
        (.sort (.imax (.succ .zero) .zero)) := by
      exact HasType.forallE (HasType.sort (show VLevel.zero.WF 0 from trivial)) (HasType.bvar .zero)
    exact ⟨localsWF quotientEnvironmentWF quotientRegistered, _, typeTyped⟩
  have headTyped : quotientEnvironment.HasType 0 dependentLocals (.bvar 0) dependentType := by
    simpa [HasType, dependentLocals, dependentType, VExpr.lift, VExpr.liftN, liftVar] using
      (HasType.bvar (env := quotientEnvironment) (U := 0)
        (Lookup.zero (Γ := locals) (ty := dependentType)))
  have delayedHeadTyped := (delayEqual headTyped).hasType.1
  have argumentTyped : quotientEnvironment.HasType 0 dependentLocals dependentArgument (.sort .zero) := by
    simpa [HasType, dependentArgument, dependentLocals, VExpr.lift, VExpr.liftN, liftVar] using
      (delayEqual (plainDomainTyped.weak quotientEnvironmentWF.ordered (B := dependentType))).hasType.1
  have applicationTyped : quotientEnvironment.HasType 0 dependentLocals
      (.app dependentFunction dependentArgument) dependentArgument := by
    simpa [HasType, dependentFunction, dependentArgument, dependentLocals, dependentType,
      VExpr.lift, VExpr.liftN, liftVar, VExpr.inst, VExpr.instVar] using
      delayedHeadTyped.app argumentTyped
  exact eta_apply_join quotientRegistered extendedWF delayedHeadTyped applicationTyped
    (ReflTransGen.tail .rfl (.core (delayReduction _ _)))
    (ReflTransGen.tail .rfl (.core (delayReduction _ _)))

example : dependentArgument ≠ .bvar 6 := by intro equal; cases equal

theorem proofSimulation : CoreSimulates quotientEnvironmentWF 0 locals (.bvar 0) constructor := by
  intro result reduction
  exact CoreSimulates.proofIrrel (localsWF quotientEnvironmentWF quotientRegistered)
    (majorTypeTyped quotientEnvironmentWF quotientRegistered) majorTyped
    (constructorTyped quotientEnvironmentWF quotientRegistered) reduction

theorem sortSimulation : CoreSimulates quotientEnvironmentWF 0 locals
    (.sort .zero) (.sort (.max .zero .zero)) := by
  intro result reduction
  exact CoreSimulates.sortDF (by trivial) (by simp [VLevel.WF])
    (VLevel.equiv_def.mpr (by intro values; rfl)) reduction

theorem constantSimulation : CoreSimulates quotientEnvironmentWF 0 locals
    (.const ``Quot.lift [.zero, .succ .zero])
    (.const ``Quot.lift [.max .zero .zero, .succ .zero]) := by
  intro result reduction
  obtain ⟨_, _, liftRegistered, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact CoreSimulates.constDF (localsWF quotientEnvironmentWF quotientRegistered) liftRegistered
    (by simp [VLevel.WF]) (by simp [VLevel.WF]) (by rfl)
    (.cons (VLevel.equiv_def.mpr (by intro values; rfl)) (.cons rfl .nil)) reduction

run_meta
  let environment ← getEnv
  let roots := [``Step.etaCongr, ``Steps.etaCongr, ``Steps.forallE, ``eta_steps_join,
    ``eta_apply_join, ``CoreSimulates.refl, ``CoreSimulates.sortDF,
    ``CoreSimulates.constDF, ``CoreSimulates.proofIrrel, ``CoreSimulates.etaL,
    ``CoreSimulates.etaR, ``CoreSimulates.lamDF, ``CoreSimulates.forallEDF,
    ``CoreSimulates.app_congr, ``CoreSimulates.typed,
    ``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual, ``delayReduction,
    ``domainTyped, ``plainDomainTyped, ``bodyTyped, ``functionTyped, ``functionReduces,
    ``etaReduces, ``etaRSimulation, ``arbitraryEtaR, ``concreteEtaR,
    ``etaLSimulation, ``concreteEtaL, ``lambdaSimulation, ``lambdaControl, ``forallSimulation,
    ``forallControl, ``wrapperTyped, ``allKindsPath, ``allKindsEtaJoin,
    ``delayedProofTyped, ``applicationJoin, ``applicationCongruence,
    ``retainedDependentBinder, ``dependentApplicationJoin, ``proofSimulation,
    ``sortSimulation, ``constantSimulation]
  let noAdmissions := [``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual,
    ``domainTyped, ``plainDomainTyped, ``bodyTyped, ``functionTyped, ``wrapperTyped,
    ``delayedProofTyped]
  let typingAdmissions : List Name := []
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC,
    ``ParRed.weakN_inv, ``NormalEq.trans,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  for root in roots do
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new eta-simulation axiom {root}"
    let some proof := info.value? | throwError "missing eta-simulation proof {root}"
    if proof.hasSorry then throwError "direct eta-simulation admission {root}"
    let expectedAdmissions := if noAdmissions.contains root then [] else typingAdmissions
    let expectedAxioms := if noAdmissions.contains root then [``propext, ``Quot.sound]
      else [``propext, ``Quot.sound]
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "eta-simulation axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden eta-simulation dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let some value := declaration.value? then
          if value.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unapproved eta-simulation admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "eta-simulation traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "eta-simulation admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``eta_steps_join then [``Steps.etaCongr, ``Step.funEta, ``Steps.hasType]
      else if root == ``eta_apply_join then
        [``Step.funEta, ``Steps.etaCongr, ``Steps.app, ``ParRed.beta, ``Steps.hasType]
      else if root == ``CoreSimulates.constDF then [``NormalEq.parRed_constDF, ``Steps.core]
      else if root == ``CoreSimulates.etaL then
        [``ParRed.weakN, ``Steps.lam, ``NormalEq.etaL, ``ParRed.hasType]
      else if root == ``CoreSimulates.etaR then
        [``Step.funEta, ``Steps.lam, ``NormalEq.lamDF, ``ParRed.defeq]
      else if root == ``CoreSimulates.lamDF then
        [``Steps.defeqDFC, ``ParRed.defeqDFC, ``NormalEq.lamDF]
      else if root == ``CoreSimulates.forallEDF then
        [``Steps.defeqDFC, ``ParRed.defeqDFC, ``Steps.forallE, ``NormalEq.forallEDF]
      else if root == ``CoreSimulates.app_congr then [``Steps.app, ``NormalEq.appDF]
      else if root == ``CoreSimulates.typed then [``Steps.hasType, ``NormalEq.defeq]
      else if root == ``concreteEtaR then [``CoreSimulates.etaR, ``etaReduces, ``CoreSimulates.typed]
      else if root == ``concreteEtaL then [``CoreSimulates.etaL, ``functionReduces, ``CoreSimulates.typed]
      else if root == ``lambdaControl then [``CoreSimulates.lamDF, ``functionReduces, ``CoreSimulates.typed]
      else if root == ``forallControl then [``CoreSimulates.forallEDF, ``delayReduction]
      else if root == ``allKindsPath then [``Step.core, ``Step.unfold, ``Step.funEta, ``unfold_liftN]
      else if root == ``allKindsEtaJoin then [``eta_steps_join, ``allKindsPath]
      else if root == ``applicationJoin then [``eta_apply_join, ``functionReduces, ``delayReduction]
      else if root == ``applicationCongruence then [``CoreSimulates.app_congr, ``functionReduces, ``delayReduction]
      else if root == ``dependentApplicationJoin then [``eta_apply_join, ``delayEqual, ``delayReduction]
      else if root == ``retainedDependentBinder then
        [``concreteEtaR, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN, ``NormalEq.instN]
      else []
    unless required.all visited.contains do
      throwError "eta-simulation control bypassed a required proof in {root}: {repr required}"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}; exact axioms {repr axioms}"

end QuotEtaSimulationTest
