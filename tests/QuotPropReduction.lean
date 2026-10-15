import Lean4Lean.Theory.Typing.QuotPropReduction
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotPropReductionTest
open Lean Lean4Lean Lean4Lean.VEnv
open Lean4Lean.VEnv.QuotConfluenceObstruction

def equalityEnvironment : VEnv := {
  constants name := if ``Eq = name then some eqConst else none
  defeqs _ := False }

def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem quotientEnvironmentWF : quotientEnvironment.WF := by
  have equalityAdded : VEnv.empty.addConst ``Eq eqConst = some equalityEnvironment := rfl
  have equalityWF : equalityEnvironment.WF := by
    refine ⟨_, .decl (.axiom (ci := ⟨eqConst, ``Eq⟩) ?_ equalityAdded) .empty⟩
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : equalityEnvironment.QuotReady := by
    simp [QuotReady, equalityEnvironment]
  have added : equalityEnvironment.addQuot = some quotientEnvironment := rfl
  obtain ⟨_, checked⟩ := equalityWF
  exact ⟨_, .decl (.quot ready added) checked⟩

theorem quotientRegistered : quotientEnvironment.defeqs quotDefEq :=
  addQuot_defeq (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)

local instance : Params := quotientEnvironmentWF.reductionParams 0

def selected : VExpr := QuotPropReduction.selector (.bvar 5) (.bvar 4) (.bvar 0)

def unfolded : VExpr := .app (.bvar 3) selected

theorem computes : QuotPropReduction.unfold neutral = some unfolded := rfl

theorem neutralStep : QuotPropReduction.Step quotientEnvironmentWF 0 locals neutral unfolded :=
  .unfold computes

theorem neutralStepSound : quotientEnvironment.IsDefEq 0 locals neutral unfolded (.sort .zero) :=
  neutralStep.defeq quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    (neutralTyped quotientEnvironmentWF quotientRegistered)

theorem joins : @NormalEq (quotientEnvironmentWF.reductionParams 0) locals unfolded reduced := by
  have domainTyped : quotientEnvironment.HasType 0 locals (.bvar 5) (.sort .zero) := by
    unfold locals respectType functionType relationType quotient
    type_tac
  have relationTyped : quotientEnvironment.HasType 0 locals (.bvar 4)
      (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
    unfold locals respectType functionType relationType quotient
    type_tac
  have functionTyped : quotientEnvironment.HasType 0 locals (.bvar 3)
      (.forallE (.bvar 5) (.sort .zero)) := by
    unfold locals respectType functionType relationType quotient
    type_tac
  have valueTyped : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType quotient
    type_tac
  exact QuotPropReduction.unfolding_join (target := .sort .zero)
    quotientEnvironmentWF quotientRegistered
    domainTyped relationTyped majorTyped functionTyped valueTyped

theorem obstruction_simulated :
    ∃ result, QuotPropReduction.Steps quotientEnvironmentWF 0 locals neutral result ∧
      @NormalEq (quotientEnvironmentWF.reductionParams 0) locals result reduced :=
  ⟨unfolded, .tail .rfl neutralStep, joins⟩

example : QuotPropReduction.unfold (.bvar 0) = none := rfl

example : QuotPropReduction.unfold (.const ``Quot.lift [.zero, .succ .zero]) = none := rfl

example : QuotPropReduction.unfold
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [.succ .zero, .succ .zero])
      (.bvar 5)) (.bvar 4)) (.sort .zero)) (.bvar 3)) (.bvar 2)) (.bvar 0)) = none := rfl

example : QuotPropReduction.unfold redex =
    some (.app (.bvar 3) (QuotPropReduction.selector (.bvar 5) (.bvar 4) constructor)) := rfl

example : QuotPropReduction.unfold
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [.imax (.param 0) .zero, .succ .zero])
      (.bvar 5)) (.bvar 4)) (.sort .zero)) (.bvar 3)) (.bvar 2)) (.bvar 0)) =
    some unfolded := rfl

example : QuotPropReduction.unfold
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [.max .zero .zero, .succ .zero])
      (.bvar 5)) (.bvar 4)) (.sort .zero)) (.bvar 3)) (.bvar 2)) (.bvar 0)) =
    some unfolded := rfl

example : QuotPropReduction.Step quotientEnvironmentWF 0 locals (.app neutral (.bvar 0))
    (.app unfolded (.bvar 0)) := .app neutralStep (.core .rfl)

example : QuotPropReduction.Step quotientEnvironmentWF 0 locals redex reduced :=
  .core (reduction quotientEnvironmentWF quotientRegistered)

example : QuotPropReduction.unfold (neutral.liftN 3 2) = some (unfolded.liftN 3 2) :=
  QuotPropReduction.unfold_liftN computes 3 2

example : QuotPropReduction.unfold (neutral.inst constructor 0) =
    some (unfolded.inst constructor 0) := QuotPropReduction.unfold_inst computes constructor 0

example : QuotPropReduction.Step quotientEnvironmentWF 0 locals
    (.lam (.sort .zero) neutral.lift) (.lam (.sort .zero) unfolded.lift) :=
  .lam (.core .rfl) (neutralStep.weakN .one)

example : QuotPropReduction.Steps quotientEnvironmentWF 0 locals redex reduced :=
  QuotPropReduction.Steps.core (.tail .rfl (reduction quotientEnvironmentWF quotientRegistered))

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotPropReduction
    | throwError "quotient proof reduction module absent"
  let mut pending : Array Name := #[``neutralStepSound, ``joins, ``obstruction_simulated]
  let mut owned : Nat := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new proof-reduction axiom {name}"
      if let some proof := information.value? then
        if proof.hasSorry then throwError "direct proof-reduction admission {name}"
      for dependency in (← collectAxioms name) do
        unless [``propext, ``Quot.sound, ``sorryAx].contains dependency do
          throwError "unexpected proof-reduction axiom {dependency} in {name}"
      pending := pending.push name
      owned := owned + 1
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff]
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden proof-reduction dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? then pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "proof-reduction dependency traversal exceeded its bound"
  for theoremName in [``QuotPropReduction.quotient_hasType, ``QuotPropReduction.selector_hasType,
      ``QuotPropReduction.zeroLike_iff,
      ``QuotPropReduction.selector_normalEq_of_params, ``QuotPropReduction.unfolding_join_of_params,
      ``quotientEnvironmentWF] do
    for dependency in (← collectAxioms theoremName) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "constructive selector/join theorem {theoremName} gained {dependency}"
  for theoremName in [``QuotPropReduction.selector_hasType, ``QuotPropReduction.unfold_sound,
      ``QuotPropReduction.Step.defeq, ``neutralStepSound, ``joins, ``obstruction_simulated] do
    logInfo m!"{theoremName}: axioms = {repr (← collectAxioms theoremName)}"
  logInfo m!"{owned} owned declarations: constructive Quot.ind proof selection and generic normal-equality joins have no admissions or choice; actual model instantiation and general unfolding inherit the independent typing baseline; compatible finite reduction preserves the original type without confluence or strengthening; the prior obstruction now simulates in the extended relation"

end QuotPropReductionTest
