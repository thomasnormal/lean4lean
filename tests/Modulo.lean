import Lean4Lean.Verify.Primitive

-- Run with: lake env lean tests/Modulo.lean
open Lean Lean4Lean

run_meta
  let env := (← Lean.getEnv).toKernelEnv
  let some (.defnInfo mod) := env.find? ``Nat.mod | throwError "missing Nat.mod"
  match (Environment.checkPrimitiveDef mod).run env with
  | .ok _ => pure ()
  | .error e => throwError "rejected the reference Nat.mod implementation: {e.toMessageData {}}"
  for value in [q(fun (_ _ : Nat) => Nat.zero), q(fun (a : Nat) (_ : Nat) => a)] do
    if ((Environment.checkPrimitiveDef { mod with value }).run env).isOk then
      throwError "accepted an incorrect Nat.mod implementation"

  -- The large dividends require native reduction at this low fuel.
  let fuel : FuelConfig := { recDepth := 16, whnf := 8, lazyDelta := 8 }
  for (a, y) in [(0, 0), (17, 0), (0, 17), (17, 1), (17, 17), (31, 7), (7, 31),
      (1208925819614629174706177, 3),
      (1208925819614629174706177, 1208925819614629174706175)] do
    let e := mkApp2 q(Nat.mod) (mkNatLit a) (mkNatLit y)
    match (TypeChecker.whnf e).run env (fuel := fuel) with
    | .ok r =>
      unless r.rawNatLit? == some (a % y) do
        throwError "Nat.mod {a} {y}: expected literal {a % y}"
    | .error _ => throwError "Nat.mod {a} {y}: reduction failed"

  -- Exercise both nested entry conditions and the supplied recursion witness.
  for (a, y) in [(0, 0), (0, 1), (1, 5), (5, 2), (5, 6), (5, 7),
      (17, 3), (17, 18), (17, 19)] do
    let sx := mkApp q(Nat.succ) (mkNatLit a)
    let bound := mkApp q(Nat.lt_succ_self) sx
    let e := Environment.natModEntryAt q(@LE.le Nat _) q(Nat.decLe) q(Nat.modCore.go)
      (mkNatLit a) (mkNatLit y) bound
    let openEntry := (Environment.natModEntryBody.instantiate1' (mkNatLit a) 1).instantiate1'
      (mkNatLit y)
    unless openEntry == e do
      throwError "incorrect modulo entry substitution for dividend {a + 1}, divisor {y}"
    match (TypeChecker.isDefEq e (mkNatLit ((a + 1) % y))).run env with
    | .ok true => pure ()
    | _ => throwError "incorrect modulo entry result for dividend {a + 1}, divisor {y}"

  -- Check only source substitution here; the proof placeholders are untyped.
  for (a, y, fuel) in [(0, 1, 0), (5, 2, 5), (5, 6, 5), (17, 3, 17)] do
    let py := q(True.intro)
    let pa := q(True.intro)
    let body := ((((Environment.natModLoopBody.instantiate1' (mkNatLit a) 4).instantiate1'
      (mkNatLit y) 3).instantiate1' py 2).instantiate1' (mkNatLit fuel) 1).instantiate1' pa
    let expected := Environment.Condition.natLE.dite #[mkNatLit y, mkNatLit a]
      (mkApp5 q(Nat.modCore.go) (mkNatLit y) py (mkNatLit fuel)
        (mkApp2 q(Nat.sub) (mkNatLit a) (mkNatLit y))
        (mkApp6 q(@Nat.div_rec_fuel_lemma) (mkNatLit a) (mkNatLit y)
          (mkNatLit fuel) py (.bvar 0) pa)) (mkNatLit a)
    unless body == expected do
      throwError "incorrect modulo recursion substitution for {a}, {y}, {fuel}"
