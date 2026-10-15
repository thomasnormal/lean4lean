import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotConfluenceObstructionTest
open Lean Lean4Lean Lean4Lean.VEnv
open Lean4Lean.VEnv.QuotConfluenceObstruction

def equalityEnvironment : VEnv := {
  constants name := if ``Eq = name then some eqConst else none
  defeqs _ := False }

def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem equalityAdded : VEnv.empty.addConst ``Eq eqConst = some equalityEnvironment := rfl

theorem equalityEnvironmentWF : equalityEnvironment.WF := by
  refine ⟨_, .decl (.axiom (ci := ⟨eqConst, ``Eq⟩) ?_ equalityAdded) .empty⟩
  exact ⟨_, by unfold eqConst; type_tac⟩

theorem quotientReady : equalityEnvironment.QuotReady := by
  simp [QuotReady, equalityEnvironment]

theorem quotientAdded : equalityEnvironment.addQuot = some quotientEnvironment := by rfl

theorem quotientEnvironmentWF : quotientEnvironment.WF := by
  obtain ⟨declarations, checked⟩ := equalityEnvironmentWF
  exact ⟨_, .decl (.quot quotientReady quotientAdded) checked⟩

theorem quotientRegistered : quotientEnvironment.defeqs quotDefEq :=
  addQuot_defeq quotientAdded

theorem concreteCounterexample :
    OnCtx locals (quotientEnvironment.IsType 0) ∧
      @NormalEq (quotientEnvironmentWF.reductionParams 0) locals neutral redex ∧
      @ParRed (quotientEnvironmentWF.reductionParams 0) locals redex reduced ∧
      ¬∃ target, @ParRedS (quotientEnvironmentWF.reductionParams 0) locals neutral target ∧
        @NormalEq (quotientEnvironmentWF.reductionParams 0) locals target reduced :=
  counterexample quotientEnvironmentWF quotientRegistered

theorem nativeMajor (proposition : Prop) (relation : proposition → proposition → Prop)
    (value : proposition) (major : Quot relation) : major = Quot.mk relation value := rfl

theorem nativeFirst (proposition : Prop) (relation : proposition → proposition → Prop)
    (function : proposition → Prop)
    (respect : ∀ first second, relation first second → function first = function second)
    (value : proposition) (major : Quot relation) :
    Quot.lift function respect major = Quot.lift function respect (Quot.mk relation value) := by
  fail_if_success rfl
  exact congrArg (Quot.lift function respect) (nativeMajor proposition relation value major)

theorem nativeSecond (proposition : Prop) (relation : proposition → proposition → Prop)
    (function : proposition → Prop)
    (respect : ∀ first second, relation first second → function first = function second)
    (value : proposition) :
    Quot.lift function respect (Quot.mk relation value) = function value := rfl

theorem nativeTransitive (proposition : Prop) (relation : proposition → proposition → Prop)
    (function : proposition → Prop)
    (respect : ∀ first second, relation first second → function first = function second)
    (value : proposition) (major : Quot relation) :
    Quot.lift function respect major = function value := by
  fail_if_success rfl
  exact (nativeFirst proposition relation function respect value major).trans
    (nativeSecond proposition relation function respect value)

run_meta
  let environment ← getEnv
  let baseline ← collectAxioms ``VEnv.IsDefEqU.forallE_inv
  let mut allowed := baseline ++ #[``propext, ``Quot.sound, ``Classical.choice]
  allowed := allowed ++ (← collectAxioms ``VEnv.IsDefEqU.sort_inv)
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotConfluenceObstruction
    | throwError "quotient confluence obstruction module absent"
  let mut pending : Array Name := #[]
  let mut owned : Nat := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new obstruction axiom {name}"
      if let some proof := information.value? then
        if proof.hasSorry then throwError "direct obstruction admission {name}"
      for dependency in (← collectAxioms name) do
        unless allowed.contains dependency do throwError "unexpected obstruction dependency {dependency}"
      pending := pending.push name
      owned := owned + 1
  pending := pending.push ``concreteCounterexample
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff]
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden confluence obstruction dependency: {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? then pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "obstruction dependency traversal exceeded its bound"
  for theoremName in [``nativeMajor, ``nativeFirst, ``nativeSecond, ``nativeTransitive] do
    for dependency in (← collectAxioms theoremName) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "native minimal reproducer gained a nonstandard dependency {dependency}"
  for theoremName in [``equalityRegistered, ``counterexample, ``quotientEnvironmentWF,
      ``concreteCounterexample, ``nativeMajor, ``nativeFirst, ``nativeSecond, ``nativeTransitive] do
    logInfo m!"{theoremName}: axioms = {repr (← collectAxioms theoremName)}"
  logInfo m!"{owned} owned obstruction declarations and the closed reachable Eq/Quot model have no direct admission or new interface axiom; non-simulation uses only independent inherited typing/injectivity foundations, not the contradicted NormalEq.parRed, confluence/quotient-injectivity consequences, or IsDefEqU.weakN_iff (issue #50); native major proof-irrelevance and quotient beta rfl controls pass, while lifted congruence and final endpoint equalities require explicit congrArg/trans proofs rather than rfl"

end QuotConfluenceObstructionTest
