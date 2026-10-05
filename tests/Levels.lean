import Lean4Lean.Level

open Lean

private def checkNormalization (level : Level) : IO Unit := do
  let expected := level.normalize
  let actual := level.normalizeCore
  if expected != actual then
    throw <| IO.userError s!"normalization mismatch: {level}: native={expected}, total={actual}"

def main : IO Unit := do
  let left := Level.param `left
  let right := Level.param `right
  let condition := Level.param `condition
  let cases := [
    (Level.imax left .zero, Level.zero),
    (Level.succ (.max left right), Level.max (.succ left) (.succ right)),
    (Level.imax (.max left right) condition, Level.imax (.max right left) condition)]
  for (first, second) in cases do
    unless first.isEquiv second && first.isEquiv' second do
      throw <| IO.userError s!"level equivalence regression: {first} == {second}"
  unless (Level.max (.succ (.succ .zero)) right).geq' (.imax (.succ (.succ .zero)) right) do
    throw <| IO.userError "level comparison regression: max 2 right >= imax 2 right"
  let redundant := Level.max left (.imax right left)
  let absorbed := Level.imax right left
  unless !redundant.isEquiv absorbed && redundant.isEquiv' absorbed do
    throw <| IO.userError "complete equivalence fallback was replaced by the incomplete native check"
  let larger := Level.imax (.max left right) condition
  let smaller := Level.imax left condition
  unless !larger.geq smaller && larger.geq' smaller do
    throw <| IO.userError "complete comparison fallback was replaced by the incomplete native check"
  let mut levels := #[Level.zero, Level.succ .zero, left, right]
  for _ in [:2] do
    let previous := levels
    for first in previous do
      levels := levels.push (.succ first)
      for second in previous do
        levels := (levels.push (.max first second)).push (.imax first second)
  for level in levels do
    checkNormalization level
  IO.println s!"{levels.size} small normalizations match the installed native normalizer"
  let metavariable := Level.mvar ⟨`left⟩
  for level in [metavariable, .max left metavariable, .max metavariable left,
      .imax left metavariable, .imax metavariable left,
      .succ (.max (.succ metavariable) left)] do
    checkNormalization level
  let mut seed : UInt64 := 42
  let mut randomLevels := #[Level.zero, Level.succ .zero, left, right, condition]
  let mut additionalComparisons := 0
  let mut additionalEquivalences := 0
  for _ in [:10000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let first := randomLevels[seed.toNat % randomLevels.size]!
    seed := seed * 6364136223846793005 + 1442695040888963407
    let second := randomLevels[seed.toNat % randomLevels.size]!
    seed := seed * 6364136223846793005 + 1442695040888963407
    let generated := match seed.toNat % 3 with
      | 0 => Level.succ first
      | 1 => Level.max first second
      | _ => Level.imax first second
    checkNormalization generated
    let nativeComparison := first.geq second
    let completeComparison := first.geq' second
    if nativeComparison && !completeComparison then
      throw <| IO.userError s!"complete comparison loses native acceptance: {first} >= {second}"
    if completeComparison && !nativeComparison then
      additionalComparisons := additionalComparisons + 1
    let nativeEquivalence := first.isEquiv second
    let completeEquivalence := first.isEquiv' second
    if nativeEquivalence && !completeEquivalence then
      throw <| IO.userError s!"complete equivalence loses native acceptance: {first} == {second}"
    if completeEquivalence && !nativeEquivalence then
      additionalEquivalences := additionalEquivalences + 1
    randomLevels := randomLevels.push generated
  IO.println s!"10000 generated normalizations match native; complete fallback additionally accepts {additionalComparisons} comparisons and {additionalEquivalences} equivalences"
