import Lean4Lean.Primitive
import Lean.Meta

-- Run with: lake env lean tests/WellFoundedGap.lean
-- This characterizes a known validation gap, not desired acceptance behavior.
-- The acceptance checks must change when the validator is hardened.
open Lean Lean4Lean

namespace WellFoundedGap

opaque measureOffset : Nat := 0

def offsetGcd (k m n : Nat) : Nat :=
  if m = 0 then n else offsetGcd k (n % m) m
termination_by m + k
decreasing_by
  exact Nat.add_lt_add_right (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero ‹m ≠ 0›)) _

theorem offsetGcd_eq (k m n : Nat) : offsetGcd k m n = Nat.gcd m n := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    rw [offsetGcd]
    split
    · next hm => subst m; exact (Nat.gcd_zero_left n).symm
    · next hm =>
      rw [Nat.gcd_rec]
      exact ih _ (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero hm)) _

def measuredGcd (m n : Nat) : Nat :=
  if m = 0 then n else measuredGcd (n % m) m
termination_by m + measureOffset
decreasing_by
  exact Nat.add_lt_add_right (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero ‹m ≠ 0›)) _

theorem measuredGcd_eq (m n : Nat) : measuredGcd m n = Nat.gcd m n := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    rw [measuredGcd]
    split
    · next hm => subst m; exact (Nat.gcd_zero_left n).symm
    · next hm =>
      rw [Nat.gcd_rec]
      exact ih _ (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero hm)) _

def measuredBitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then
    if f false true then m else 0
  else if m = 0 then
    if f true false then n else 0
  else
    let n' := n / 2
    let m' := m / 2
    let b₁ := n % 2 = 1
    let b₂ := m % 2 = 1
    let r := measuredBitwise f n' m'
    if f b₁ b₂ then r + r + 1 else r + r
termination_by n + measureOffset
decreasing_by
  exact Nat.add_lt_add_right (Nat.bitwise_rec_lemma ‹n ≠ 0›) _

theorem measuredBitwise_eq (f : Bool → Bool → Bool) (n m : Nat) :
    measuredBitwise f n m = Nat.bitwise f n m := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    rw [measuredBitwise, Nat.bitwise]
    by_cases hn : n = 0
    · simp only [hn, if_true]
    · simp only [hn, if_false]
      by_cases hm : m = 0
      · simp only [hm, if_true]
      · simp only [hm, if_false]
        rw [ih _ (Nat.bitwise_rec_lemma hn)]

private def initialMeasure (e : Expr) (fvs : Array Expr) : TypeChecker.M Expr := do
  let e ← TypeChecker.whnfCore (mkAppN e fvs)
  let e ← TypeChecker.unfoldDefinition e
  (← TypeChecker.whnfCore e).withApp fun fix args => do
    let .const ``WellFounded.Nat.fix [_, _] := fix | throw <| .other "not Nat.fix"
    let #[_, _, measure, _, state] := args | throw <| .other "unexpected Nat.fix arguments"
    return mkApp measure state

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let checkAccepted (label : String) (v : DefinitionVal) := do
    match (Environment.checkPrimitiveDef v).run env with
    | .ok true => pure ()
    | .ok false => throwError "{label}: not recognized as a primitive"
    | .error e => throwError "{label}: rejected: {e.toMessageData {}}"
  let checkComparison (label : String) (e : Expr) (expected : Nat) := do
    match (TypeChecker.isDefEq e (mkNatLit expected)).run env with
    | .ok false => pure ()
    | .ok true => throwError "{label}: unexpectedly reduced the opaque measure"
    | .error e => throwError "{label}: comparison failed: {e.toMessageData {}}"
    if ← Lean.Meta.withTransparency .all <| Lean.Meta.isDefEq e (mkNatLit expected) then
      throwError "{label}: Lean unexpectedly reduced the opaque measure"

  let some (.defnInfo gcd) := env.find? ``Nat.gcd | throwError "missing Nat.gcd"
  let some (.defnInfo candidate) := env.find? ``measuredGcd | throwError "missing measuredGcd"
  let some (.defnInfo offset) := env.find? ``offsetGcd | throwError "missing offsetGcd"
  checkAccepted "reference gcd" gcd
  checkAccepted "opaque-measure gcd" { gcd with value := candidate.value }
  unless ((TypeChecker.checkType candidate.value).run env).isOk do
    throwError "opaque-measure gcd is ill-typed"
  for (m, n) in [(0, 5), (6, 9)] do
    checkComparison s!"gcd {m} {n}"
      (mkApp2 candidate.value (mkNatLit m) (mkNatLit n)) (Nat.gcd m n)

  -- The returned equation body reduces at zero, but the original candidate does not.
  let unfold : TypeChecker.M Expr :=
    Lean4Lean.withLocalDecl `m .default q(Nat) fun m =>
    Lean4Lean.withLocalDecl `n .default q(Nat) fun n =>
      Environment.unfoldNatWellFounded candidate.value #[m, n] q(type_of% Nat.gcd.eq_def)
        (throw <| .other "unfolding failed")
  let unfolded ← match unfold.run env with
    | .ok result => pure result
    | .error e => throwError "gcd unfolding failed: {e.toMessageData {}}"
  match (TypeChecker.isDefEq (mkApp2 unfolded (mkNatLit 0) (mkNatLit 5)) (mkNatLit 5)).run env with
  | .ok true => pure ()
  | _ => throwError "unfolded gcd body did not reduce at zero"

  let offsetZero := mkApp offset.value (mkNatLit 0)
  let offsetOne := mkApp offset.value (mkNatLit 1)
  for value in [offsetZero, offsetOne] do
    checkAccepted "computable-offset gcd" { gcd with value }
    for (m, n) in [(0, 5), (6, 9)] do
      match (TypeChecker.isDefEq (mkApp2 value (mkNatLit m) (mkNatLit n))
          (mkNatLit (Nat.gcd m n))).run env with
      | .ok true => pure ()
      | _ => throwError "computable-offset gcd did not reduce at {m}, {n}"

  let gcdMeasures : TypeChecker.M (Array Bool) :=
    Lean4Lean.withLocalDecl `m .default q(Nat) fun m =>
    Lean4Lean.withLocalDecl `n .default q(Nat) fun n => do
      let mut results := #[]
      for value in [gcd.value, offsetZero, offsetOne, candidate.value] do
        results := results.push (← TypeChecker.isDefEq (← initialMeasure value #[m, n]) m)
      return results
  match gcdMeasures.run env with
  | .ok #[true, true, false, false] => pure ()
  | _ => throwError "unexpected GCD measures"

  let some (.defnInfo bitwise) := env.find? ``Nat.bitwise | throwError "missing Nat.bitwise"
  let some (.defnInfo candidate) := env.find? ``measuredBitwise | throwError "missing measuredBitwise"
  checkAccepted "reference bitwise" bitwise
  checkAccepted "opaque-measure bitwise" { bitwise with value := candidate.value }
  unless ((TypeChecker.checkType candidate.value).run env).isOk do
    throwError "opaque-measure bitwise is ill-typed"
  for (n, m) in [(0, 5), (6, 9)] do
    for (f, expected) in [(q(Bool.and), Nat.land n m), (q(Bool.or), Nat.lor n m),
        (q(Bool.xor), Nat.xor n m)] do
      checkComparison s!"bitwise {n} {m}"
        (mkApp3 candidate.value f (mkNatLit n) (mkNatLit m)) expected

  let bitwiseMeasures : TypeChecker.M (Array Bool) :=
    Lean4Lean.withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
    Lean4Lean.withLocalDecl `n .default q(Nat) fun n =>
    Lean4Lean.withLocalDecl `m .default q(Nat) fun m => do
      let mut results := #[]
      for value in [bitwise.value, candidate.value] do
        results := results.push (← TypeChecker.isDefEq (← initialMeasure value #[f, n, m]) n)
      return results
  match bitwiseMeasures.run env with
  | .ok #[true, false] => pure ()
  | _ => throwError "unexpected bitwise measures"

end WellFoundedGap
