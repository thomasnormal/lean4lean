import Lean4Lean.Level

-- Run with: lake env lean --run tests/Levels.lean
open Lean

def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let cases := [
    (Level.imax u .zero, Level.zero),
    (Level.succ (.max u v), Level.max (.succ u) (.succ v)),
    (Level.imax (.max u v) (.param `w), Level.imax (.max v u) (.param `w))]
  for (a, b) in cases do
    unless a.isEquiv b && a.isEquiv' b do
      throw <| IO.userError s!"level equivalence regression: {a} == {b}"
  unless (Level.max (.succ (.succ .zero)) v).geq' (.imax (.succ (.succ .zero)) v) do
    throw <| IO.userError "level comparison regression: max 2 v >= imax 2 v"
  let mut levels := #[Level.zero, Level.succ .zero, u, v]
  for _ in [:2] do
    let previous := levels
    for a in previous do
      levels := levels.push (.succ a)
      for b in previous do
        levels := (levels.push (.max a b)).push (.imax a b)
  for a in levels do
    if a.normalize != a.normalizeCore then
      throw <| IO.userError s!"normalization mismatch: {a}: upstream={a.normalize}, fork={a.normalizeCore}"
  IO.println s!"{levels.size} small normalizations match upstream"
  let mut seed : UInt64 := 42
  let mut randomLevels := #[Level.zero, Level.succ .zero, u, v, .param `w]
  for _ in [:10000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let a := randomLevels[seed.toNat % randomLevels.size]!
    seed := seed * 6364136223846793005 + 1442695040888963407
    let b := randomLevels[seed.toNat % randomLevels.size]!
    seed := seed * 6364136223846793005 + 1442695040888963407
    let c := match seed.toNat % 3 with
      | 0 => Level.succ a
      | 1 => Level.max a b
      | _ => Level.imax a b
    if c.normalize != c.normalizeCore then
      throw <| IO.userError s!"normalization mismatch: {c}: upstream={c.normalize}, fork={c.normalizeCore}"
    if a.geq b != a.geq' b then
      throw <| IO.userError s!"comparison mismatch: {a} >= {b}"
    if a.isEquiv b != a.isEquiv' b then
      throw <| IO.userError s!"equivalence mismatch: {a} == {b}"
    randomLevels := randomLevels.push c
  IO.println "10000 generated normalizations, comparisons, and equivalence checks match upstream"
