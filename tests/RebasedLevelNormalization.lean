import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace RebasedLevelNormalizationTest
open Lean
open Lean4Lean

example (valuation : Name → Nat) (level : Level) :
    Level.evalLevel valuation (level.normalizeCore) = Level.evalLevel valuation level :=
  Level.normalizeCore_eval level

example {names : List Name} {first second : Level} {firstModel secondModel : VLevel}
    (firstTranslation : VLevel.ofLevel names first = some firstModel)
    (secondTranslation : VLevel.ofLevel names second = some secondModel) :
    first.geq' second ↔ secondModel ≤ firstModel :=
  Level.geq'_complete firstTranslation secondTranslation

example {names : List Name} {first second : Level} {firstModel secondModel : VLevel}
    (firstTranslation : VLevel.ofLevel names first = some firstModel)
    (secondTranslation : VLevel.ofLevel names second = some secondModel) :
    first.isEquiv' second ↔ firstModel ≈ secondModel :=
  Level.isEquiv'_complete firstTranslation secondTranslation

theorem completeComparisonRegression :
    (Level.imax (.max (.param `left) (.param `right)) (.param `condition)).geq'
      (.imax (.param `left) (.param `condition)) := by
  apply (Level.geq'_complete (ls := [`left, `right, `condition])
    (u' := .imax (.max (.param 0) (.param 1)) (.param 2))
    (v' := .imax (.param 0) (.param 2)) (by rfl) (by rfl)).2
  intro valuation
  simp only [VLevel.eval, Nat.imax, Nat.max_eq_max]
  by_cases zeroCondition : valuation.getD 2 0 = 0
  · simp only [zeroCondition, if_true]
    exact Nat.le_refl 0
  · simp only [zeroCondition, if_false]
    omega

theorem completeEquivalenceRegression :
    (Level.max (.param `left) (.imax (.param `right) (.param `left))).isEquiv'
      (.imax (.param `right) (.param `left)) := by
  apply (Level.isEquiv'_complete (ls := [`left, `right])
    (u' := .max (.param 0) (.imax (.param 1) (.param 0)))
    (v' := .imax (.param 1) (.param 0)) (by rfl) (by rfl)).2
  rw [VLevel.equiv_def]
  intro valuation
  simp only [VLevel.eval, Nat.imax, Nat.max_eq_max]
  by_cases zeroLeft : valuation.getD 0 0 = 0
  · simp only [zeroLeft, if_true]
    rfl
  · simp only [zeroLeft, if_false]
    omega

run_meta
  let allowed ← collectAxioms ``Lean4Lean.TypeChecker.checkType.WF
  let canonicalBaseline := allowed.push ``Std.TreeMap.any_eq_any_toList
  let totalContracts := #[``Level.normalizeIMax_eval, ``Level.evalLevel_addOffset,
    ``Level.NormalizeCore.accMax_eval, ``Level.NormalizeCore.max_eval,
    ``Level.NormalizeCore.addOffset_eval, ``Level.NormalizeCore.normalize_eval,
    ``Level.normalizeCore_eval, ``Level.geqCore_eq_go, ``Level.geqCore_sound]
  for theoremName in #[``Level.normalizeIMax_eval, ``Level.evalLevel_addOffset,
      ``Level.NormalizeCore.accMax_eval, ``Level.NormalizeCore.max_eval,
      ``Level.NormalizeCore.addOffset_eval, ``Level.NormalizeCore.normalize_eval,
      ``Level.normalizeCore_eval, ``Level.geqCore_eq_go, ``Level.geqCore_sound,
      ``Level.normalize'_eval, ``Level.normalize'_complete,
      ``Level.geq'_wf, ``Level.geq'_complete, ``Level.isEquiv'_complete,
      ``completeComparisonRegression, ``completeEquivalenceRegression] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "level contract is an axiom"
    let some proof := information.value? (allowOpaque := true)
      | throwError "level proof absent"
    if proof.hasSorry then throwError "level direct admission: {theoremName}"
    let dependencies ← collectAxioms theoremName
    if dependencies.contains ``sorryAx then
      throwError "level contract inherits an admission: {theoremName}"
    for dependency in dependencies do
      let baseline := if totalContracts.contains theoremName then allowed else canonicalBaseline
      unless baseline.contains dependency do
        throwError "level dependency outside its pre-existing checker/canonical baseline: {dependency}"
    logInfo m!"{theoremName}: {repr dependencies}"

end RebasedLevelNormalizationTest
