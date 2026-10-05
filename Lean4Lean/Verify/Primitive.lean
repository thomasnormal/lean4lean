import Lean4Lean.Primitive
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception

namespace VEnv

variable {env : VEnv}

theorem HasPrimitives.natSucc_type (hp : env.HasPrimitives) (hn : env.contains ``Nat) :
    env.HasType U Γ .natSucc (.forallE .nat .nat) := by
  let ⟨_, _, h⟩ := hp.nat hn
  cases hp.natSucc h
  exact .const h nofun rfl

theorem HasPrimitives.natLit_type (hp : env.HasPrimitives) (hn : env.contains ``Nat) (n : Nat) :
    env.HasType U Γ (.natLit n) .nat := by
  induction n with
  | zero =>
    let ⟨⟨_, h⟩, _⟩ := hp.nat hn
    cases hp.natZero h
    exact .const h nofun rfl
  | succ n ih => exact hp.natSucc_type hn |>.app ih

private theorem IsDefEq.lam_body (henv : env.Ordered)
    (h₁ : env.HasType U (A :: Γ) e₁ B) (h₂ : env.HasType U (A :: Γ) e₂ B)
    (h : env.IsDefEq U Γ (.lam A e₁) (.lam A e₂) (.forallE A B)) :
    env.IsDefEq U (A :: Γ) e₁ e₂ B := by
  have hv : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have h₁' := IsDefEq.beta (h₁.weakN henv Ctx.LiftN.one.succ) hv
  have h₂' := IsDefEq.beta (h₂.weakN henv Ctx.LiftN.one.succ) hv
  simpa only [VExpr.instN_bvar0] using
    h₁'.symm.trans ((h.weak henv).appDF hv) |>.trans h₂'

/-- The two open equations checked for a candidate implementation of `Nat.add`. -/
structure NatAddSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) (.bvar 0) .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0)))
    (.app .natSucc (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) .nat

theorem NatAddSpec.mono (h : NatAddSpec env f) (hle : env ≤ env') :
    NatAddSpec env' f := ⟨h.zero.mono hle, h.succ.mono hle⟩

theorem NatAddSpec.eval (h : NatAddSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b)) (.natLit (a + b)) .nat := by
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  induction b with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero,
      VExpr.natLit, Nat.add_zero] using h.zero.instN henv ha .zero
  | succ b ih =>
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    have hb' := hb.weak0 henv (Γ := [.nat])
    have hs := h.succ.instN henv hb' .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc] at hs
    have hs := hs.instN henv ha .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    exact hs.trans <| (hp.natSucc_type hn).appDF ih

theorem NatAddSpec.reflects (h : NatAddSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hdef : env.IsDefEq 0 [] (.const fc []) f (.forallE .nat (.forallE .nat .nat))) :
    env.ReflectsNatNatNat fc Nat.add := by
  intro _ a b
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  have hb := hp.natLit_type (U := 0) (Γ := []) hn b
  exact ((hdef.appDF ha |>.appDF hb).trans (h.eval henv hp hn a b)).toU

/-- The open equations checked for a candidate implementation of `Nat.mul`. -/
structure NatMulSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) .natZero .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0)))
    (.app (.app (.const ``Nat.add []) (.app (.app f.lift.lift (.bvar 1)) (.bvar 0)))
      (.bvar 1)) .nat

theorem NatMulSpec.eval (h : NatMulSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hadd : env.HasType 0 [] (.const ``Nat.add []) (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.add []) (.natLit a)) (.natLit b)) (.natLit (a + b)) .nat)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b)) (.natLit (a * b)) .nat := by
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  induction b with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero,
      VExpr.natLit, Nat.mul_zero] using h.zero.instN henv ha .zero
  | succ b ih =>
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    have hs := h.succ.instN henv (hb.weak0 henv (Γ := [.nat])) .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc] at hs
    have hs := hs.instN henv ha .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    exact hs.trans <| ((hadd.appDF ih).appDF ha).trans (heval (a * b) a)

/-- The open equations checked for a candidate implementation of `Nat.pow`. -/
structure NatPowSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) (.natLit 1) .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0)))
    (.app (.app (.const ``Nat.mul []) (.app (.app f.lift.lift (.bvar 1)) (.bvar 0)))
      (.bvar 1)) .nat

theorem NatPowSpec.eval (h : NatPowSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hmul : env.HasType 0 [] (.const ``Nat.mul []) (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.mul []) (.natLit a)) (.natLit b)) (.natLit (a * b)) .nat)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b)) (.natLit (a ^ b)) .nat := by
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  induction b with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero,
      VExpr.natLit, VExpr.natSucc, Nat.pow_zero] using h.zero.instN henv ha .zero
  | succ b ih =>
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    have hs := h.succ.instN henv (hb.weak0 henv (Γ := [.nat])) .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc] at hs
    have hs := hs.instN henv ha .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    exact hs.trans <| ((hmul.appDF ih).appDF ha).trans (heval (a ^ b) a)

/-- The equations checked for a candidate implementation of `Nat.pred`. -/
structure NatPredSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [] (.app f .natZero) .natZero .nat
  succ : env.IsDefEq 0 [.nat]
    (.app f.lift (.app .natSucc (.bvar 0))) (.bvar 0) .nat

theorem NatPredSpec.eval (h : NatPredSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a : Nat) :
    env.IsDefEq 0 [] (.app f (.natLit a)) (.natLit a.pred) .nat := by
  cases a with
  | zero => exact h.zero
  | succ a =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat,
      VExpr.natSucc] using h.succ.instN henv (hp.natLit_type hn a) .zero

/-- The open equations checked for a candidate implementation of `Nat.sub`. -/
structure NatSubSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) (.bvar 0) .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0)))
    (.app (.const ``Nat.pred []) (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) .nat

theorem NatSubSpec.eval (h : NatSubSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (hpred : env.contains ``Nat.pred)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b)) (.natLit (a - b)) .nat := by
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  induction b with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero,
      VExpr.natLit, Nat.sub_zero] using h.zero.instN henv ha .zero
  | succ b ih =>
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    have hs := h.succ.instN henv (hb.weak0 henv (Γ := [.nat])) .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc] at hs
    have hs := hs.instN henv ha .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    simpa only [Nat.sub_succ] using hs.trans <|
      ((hp.natPredType hpred).appDF ih).trans (hp.natPred hpred (a - b))

/-- The equations checked for natural-number comparisons. Equality and ordering
differ only in their result on zero and a successor. -/
structure NatComparisonSpec (env : VEnv) (f : VExpr) (zeroSucc : Bool) : Prop where
  zero_zero : env.IsDefEq 0 []
    (.app (.app f .natZero) .natZero) .boolTrue .bool
  zero_succ : env.IsDefEq 0 [.nat]
    (.app (.app f.lift .natZero) (.app .natSucc (.bvar 0))) (.boolLit zeroSucc) .bool
  succ_zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.app .natSucc (.bvar 0))) .natZero) .boolFalse .bool
  succ_succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
    (.app (.app f.lift.lift (.bvar 1)) (.bvar 0)) .bool

abbrev NatBeqSpec (env : VEnv) (f : VExpr) := NatComparisonSpec env f false
abbrev NatBleSpec (env : VEnv) (f : VExpr) := NatComparisonSpec env f true

theorem NatBeqSpec.eval (h : NatBeqSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b))
      (.boolLit (Nat.beq a b)) .bool := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact h.zero_zero
    | succ b =>
      simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat,
        VExpr.natZero, VExpr.natSucc, VExpr.bool, VExpr.boolFalse] using
        h.zero_succ.instN henv (hp.natLit_type hn b) .zero
  | succ a ih =>
    have ha := hp.natLit_type (U := 0) (Γ := []) hn a
    cases b with
    | zero =>
      simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat,
        VExpr.natZero, VExpr.natSucc, VExpr.bool, VExpr.boolFalse] using
        h.succ_zero.instN henv ha .zero
    | succ b =>
      have hb := hp.natLit_type (U := 0) (Γ := []) hn b
      have hs := h.succ_succ.instN henv (hb.weak0 henv (Γ := [.nat])) .zero
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
        VExpr.nat, VExpr.natSucc, VExpr.bool] at hs
      have hs := hs.instN henv ha .zero
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
        (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
      exact hs.trans (ih b)

theorem NatBleSpec.eval (h : NatBleSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b))
      (.boolLit (Nat.ble a b)) .bool := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact h.zero_zero
    | succ b =>
      simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat,
        VExpr.natZero, VExpr.natSucc, VExpr.bool, VExpr.boolLit, VExpr.boolTrue] using
        h.zero_succ.instN henv (hp.natLit_type hn b) .zero
  | succ a ih =>
    have ha := hp.natLit_type (U := 0) (Γ := []) hn a
    cases b with
    | zero =>
      simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat,
        VExpr.natZero, VExpr.natSucc, VExpr.bool, VExpr.boolFalse] using
        h.succ_zero.instN henv ha .zero
    | succ b =>
      have hb := hp.natLit_type (U := 0) (Γ := []) hn b
      have hs := h.succ_succ.instN henv (hb.weak0 henv (Γ := [.nat])) .zero
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
        VExpr.nat, VExpr.natSucc, VExpr.bool] at hs
      have hs := hs.instN henv ha .zero
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
        (hb.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
      exact hs.trans (ih b)

/-- The open equations checked for a candidate implementation of `Nat.shiftLeft`. -/
structure NatShiftLeftSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) (.bvar 0) .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 0)) (.app .natSucc (.bvar 1)))
    (.app (.app f.lift.lift (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
      (.bvar 1)) .nat

theorem NatShiftLeftSpec.eval (h : NatShiftLeftSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hf : env.HasType 0 [] f (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.mul []) (.natLit a)) (.natLit b)) (.natLit (a * b)) .nat)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b))
      (.natLit (Nat.shiftLeft a b)) .nat := by
  induction b generalizing a with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero]
      using h.zero.instN henv (hp.natLit_type hn a) .zero
  | succ b ih =>
    have ha := hp.natLit_type (U := 0) (Γ := []) hn a
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    -- The checked equation binds the value inside the shift count.
    have hs := h.succ.instN henv (ha.weak0 henv (Γ := [.nat])) .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc, VExpr.natLit, VExpr.natZero] at hs
    have hs := hs.instN henv hb .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (ha.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    exact hs.trans <| ((hf.appDF (heval 2 a)).appDF hb).trans (ih (2 * a))

def natLeExpr (le : VExpr) (a b : Nat) : VExpr :=
  .app (.app le (.natLit a)) (.natLit b)

def natDivLoopExpr (go : VExpr) (y : Nat) (hy : VExpr) (fuel a : Nat) (ha : VExpr) : VExpr :=
  .app (.app (.app (.app (.app go (.natLit y)) hy) (.natLit fuel)) (.natLit a)) ha

/-- The division loop equations after evaluating the checked conditional and
subtraction. The proof arguments remain explicit, including the new fuel witness
needed by the recursive call. Establishing this specification from
`checkPrimitiveDef` requires the correctness of `Condition.natLE.check`. -/
structure NatDivLoopSpec (env : VEnv) (go le : VExpr) : Prop where
  step : ∀ y fuel a hy ha, 0 < y → a < fuel + 1 → y ≤ a →
    env.HasType 0 [] hy (natLeExpr le 1 y) →
    env.HasType 0 [] ha (natLeExpr le (a + 1) (fuel + 1)) →
    ∃ ha', env.HasType 0 [] ha' (natLeExpr le (a - y + 1) fuel) ∧
      env.IsDefEq 0 [] (natDivLoopExpr go y hy (fuel + 1) a ha)
        (.app .natSucc (natDivLoopExpr go y hy fuel (a - y) ha')) .nat
  stop : ∀ y fuel a hy ha, 0 < y → a < fuel + 1 → a < y →
    env.HasType 0 [] hy (natLeExpr le 1 y) →
    env.HasType 0 [] ha (natLeExpr le (a + 1) (fuel + 1)) →
    env.IsDefEq 0 [] (natDivLoopExpr go y hy (fuel + 1) a ha) .natZero .nat

theorem NatDivLoopSpec.eval (h : NatDivLoopSpec env go le)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (hy : 0 < y)
    (hpos : env.HasType 0 [] py (natLeExpr le 1 y)) (ha : a < fuel)
    (hbound : env.HasType 0 [] pa (natLeExpr le (a + 1) fuel)) :
    env.IsDefEq 0 [] (natDivLoopExpr go y py fuel a pa) (.natLit (a / y)) .nat := by
  induction fuel generalizing a pa with
  | zero => omega
  | succ fuel ih =>
    by_cases hle : y ≤ a
    · obtain ⟨pa', hbound', hstep⟩ := h.step y fuel a py pa hy ha hle hpos hbound
      have ha' : a - y < fuel := by omega
      rw [Nat.div_eq_sub_div hy hle]
      exact hstep.trans <| (hp.natSucc_type hn).appDF (ih ha' hbound')
    · have hlt : a < y := Nat.lt_of_not_ge hle
      simpa only [Nat.div_eq_of_lt hlt, VExpr.natLit] using
        h.stop y fuel a py pa hy ha hlt hpos hbound

/-- The entry equations for division, together with the loop specification.
These are intermediate obligations, not an assumption added to `HasPrimitives`. -/
structure NatDivSpec (env : VEnv) (f go le : VExpr) : Prop where
  loop : NatDivLoopSpec env go le
  zero : ∀ a, env.IsDefEq 0 []
    (.app (.app f (.natLit a)) .natZero) .natZero .nat
  start : ∀ a y, 0 < y →
    ∃ py pa, env.HasType 0 [] py (natLeExpr le 1 y) ∧
      env.HasType 0 [] pa (natLeExpr le (a + 1) (a + 1)) ∧
      env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit y))
        (natDivLoopExpr go y py (a + 1) a pa) .nat

theorem NatDivSpec.eval (h : NatDivSpec env f go le)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a y : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit y)) (.natLit (a / y)) .nat := by
  cases y with
  | zero => simpa only [Nat.div_zero, VExpr.natLit] using h.zero a
  | succ y =>
    obtain ⟨py, pa, hpos, hbound, hstart⟩ := h.start a (y + 1) (Nat.succ_pos _)
    exact hstart.trans <| h.loop.eval hp hn (Nat.succ_pos _) hpos (Nat.lt_succ_self _) hbound

end VEnv

private theorem TrExprS.weakBV_closed (henv : env.Ordered)
    (W : VLCtx.BVLift [] Δ dn 0 n 0) (h : TrExprS env Us [] e e') :
    TrExprS env Us Δ e (e'.liftN n) := by
  have h' := h.weakBV henv W
  rwa [Expr.liftLooseBVars_eq_self (s := 0) h.closed.looseBVarRange_le] at h'

namespace Environment
open TypeChecker

private def checkExprType (e ty : Expr) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType e) ty do fail

private theorem checkExprType.WF {c : VContext} (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (he : e.FVarsIn (· ∈ c.vlctx.fvars)) (hty : c.TrExprS ty ty') :
    (checkExprType e ty fail).WF c s fun _ _ =>
      ∃ e', c.TrExprS e e' ∧ c.HasType e' ty' := by
  unfold checkExprType
  refine (checkType.WF he).bind fun _ _ _ ⟨e', _, _, htr, ht, hety⟩ => ?_
  refine (isDefEq.WF ht hty).bind fun b _ _ htype => ?_
  cases b
  · exact hfail.mono fun _ _ _ h => h.elim
  · exact .pure ⟨e', htr, hety.defeqU_r c.Ewf c.Δwf (htype rfl)⟩

theorem Reflection.check.WF {c : VContext} (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hr : r.type.FVarsIn (· ∈ c.vlctx.fvars)) (hb : c.venv.contains ``Bool) :
    (r.check fail).WF c s fun _ _ => ∃ r', c.TrExprS r.type r' ∧
      c.HasType r' (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) := by
  have ht := TrExprS.boolTrue (Us := c.lparams) (Δ := []) c.hasPrimitives hb
  obtain ⟨u, hBool⟩ := ht.2.isType c.Ewf.ordered trivial
  obtain ⟨ci, hci, _, hu⟩ := hBool.const_inv c.Ewf.ordered trivial
  have trBool {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Bool) .bool := .const hci rfl hu
  have trProp {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Prop) (.sort .zero) := .sort rfl
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have boolType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .bool :=
    ⟨u, hBool.weak0 c.Ewf.ordered⟩
  have trType : c.TrExprS q(Prop → Bool → Prop)
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) :=
    .forallE propType (boolType.forallE propType) trProp
      (.forallE boolType propType trBool trProp)
  exact checkExprType.WF fail hfail hr trType

def Reflection.ofTrueType (r : VExpr) : VExpr :=
  .forallE (.sort .zero) <|
    .forallE (.app (.app r (.bvar 0)) .boolTrue) (.bvar 1)

def Reflection.ofFalseType (r neg : VExpr) : VExpr :=
  .forallE (.sort .zero) <|
    .forallE (.app (.app r (.bvar 0)) .boolFalse) (.app neg (.bvar 1))

theorem Reflection.ofTrueType.apply {env : VEnv} {r : VExpr} (hr : r.ClosedN)
    (ht : env.HasType U Γ t (ofTrueType r))
    (hp : env.HasType U Γ p (.sort .zero))
    (hH : env.HasType U Γ H (.app (.app r p) .boolTrue)) :
    env.HasType U Γ (.app (.app t p) H) p := by
  have ht₁ := ht.app hp
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, VExpr.instVar_succ, VExpr.boolTrue] at ht₁
  simpa only [VExpr.inst_lift] using ht₁.app hH

theorem Reflection.ofFalseType.apply {env : VEnv} {r neg : VExpr}
    (hr : r.ClosedN) (hn : neg.ClosedN)
    (ht : env.HasType U Γ t (ofFalseType r neg))
    (hp : env.HasType U Γ p (.sort .zero))
    (hH : env.HasType U Γ H (.app (.app r p) .boolFalse)) :
    env.HasType U Γ (.app (.app t p) H) (.app neg p) := by
  have ht₁ := ht.app hp
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _),
    hn.instN_eq (Nat.zero_le _), VExpr.instVar_zero, VExpr.instVar_succ,
    VExpr.boolFalse] at ht₁
  simpa only [VExpr.inst, hn.instN_eq (Nat.zero_le _), VExpr.inst_lift] using ht₁.app hH

-- This is the pair of witness-conversion checks in `Reflection.checkNatDITE`.
private def checkReflectionProofs (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  checkExprType r.ofTrue (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) fail
  checkExprType r.ofFalse (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) fail

private theorem checkReflectionProofs.WF {c : VContext} {neg : VExpr} (hc : c.vlctx = [])
    (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hnot : TrExprS c.venv c.lparams [] q(Not) neg)
    (hnott : c.venv.HasType c.lparams.length [] neg
      (.forallE (.sort .zero) (.sort .zero)))
    (hb : c.venv.contains ``Bool) :
    (checkReflectionProofs r fail).WF c s fun _ _ =>
      (∃ t, c.TrExprS r.ofTrue t ∧ c.HasType t (Reflection.ofTrueType r')) ∧
      (∃ f, c.TrExprS r.ofFalse f ∧ c.HasType f (Reflection.ofFalseType r' neg)) := by
  have hrc := hrt.closedN c.Ewf.ordered trivial
  have hnc := hnott.closedN c.Ewf.ordered trivial
  let Δ₁ : VLCtx := [(none, .vlam (.sort .zero))]
  have trProp {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Prop) (.sort .zero) := .sort rfl
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have hr₁ : TrExprS c.venv c.lparams Δ₁ r.type r' := by
    simpa only [hrc.liftN_eq (Nat.zero_le _)] using
      hr.weakBV_closed c.Ewf.ordered (.skip (.vlam (.sort .zero)) .refl)
  have hrt₁ : c.venv.HasType c.lparams.length [.sort .zero] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) := hrt.weak0 c.Ewf.ordered
  have hp₁ : c.venv.HasType c.lparams.length [.sort .zero] (.bvar 0) (.sort .zero) :=
    .bvar .zero
  have tp₁ : TrExprS c.venv c.lparams Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
  have htrue := TrExprS.boolTrue (Us := c.lparams) (Δ := Δ₁) c.hasPrimitives hb
  have hfalse := TrExprS.boolFalse (Us := c.lparams) (Δ := Δ₁) c.hasPrimitives hb
  have trRef := TrExprS.app hrt₁ hp₁ hr₁ tp₁
  have tt := TrExprS.app (hrt₁.app hp₁) htrue.2 trRef htrue.1
  have tf := TrExprS.app (hrt₁.app hp₁) hfalse.2 trRef hfalse.1
  have hAt := (hrt₁.app hp₁).app htrue.2
  have hAf := (hrt₁.app hp₁).app hfalse.2
  have hp₂ {A : VExpr} : c.venv.HasType c.lparams.length [A, .sort .zero]
      (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have trTrueType : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) (Reflection.ofTrueType r') := by
    simp only [VContext.TrExprS, hc]
    exact .forallE propType (VEnv.IsType.forallE ⟨_, hAt⟩ ⟨_, hp₂⟩) trProp
      (.forallE ⟨_, hAt⟩ ⟨_, hp₂⟩ tt (.bvar rfl))
  let Δ₂ : VLCtx := (none, .vlam (.app (.app r' (.bvar 0)) .boolFalse)) :: Δ₁
  have tn₂ : TrExprS c.venv c.lparams Δ₂ q(Not) neg := by
    simpa only [hnc.liftN_eq (Nat.zero_le _)] using
      hnot.weakBV_closed c.Ewf.ordered
        (.skip (.vlam _) (.skip (.vlam (.sort .zero)) .refl))
  have hn₂ : c.venv.HasType c.lparams.length Δ₂.toCtx neg
      (.forallE (.sort .zero) (.sort .zero)) := hnott.weak0 c.Ewf.ordered
  have tp₂ : TrExprS c.venv c.lparams Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
  have tnApp := TrExprS.app hn₂ hp₂ tn₂ tp₂
  have trFalseType : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1)))
      (Reflection.ofFalseType r' neg) := by
    simp only [VContext.TrExprS, hc]
    exact .forallE propType (VEnv.IsType.forallE ⟨_, hAf⟩ ⟨_, hn₂.app hp₂⟩)
      trProp (.forallE ⟨_, hAf⟩ ⟨_, hn₂.app hp₂⟩ tf tnApp)
  unfold checkReflectionProofs
  refine (checkExprType.WF fail hfail ht trTrueType).bind fun _ _ _ htrue => ?_
  exact (checkExprType.WF fail hfail hf trFalseType).mono fun _ _ _ hfalse => ⟨htrue, hfalse⟩

def Reflection.natDITEType (r neg : VExpr) : VExpr :=
  .forallE (.sort .zero) <| .forallE .bool <|
    .forallE (.app (.app r (.bvar 1)) (.bvar 0)) <|
    .forallE (.forallE (.bvar 2) .nat) <|
    .forallE (.forallE (.app neg (.bvar 3)) .nat) .nat

private def natDITETypeExpr (r : Reflection) : Expr :=
  .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .arrow (.arrow (.bvar 2) q(Nat)) <|
    .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)

private theorem tr_natDITETypeExpr {c : VContext} {r : Reflection} {r' neg : VExpr}
    (hc : c.vlctx = [])
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hnot : TrExprS c.venv c.lparams [] q(Not) neg)
    (hnott : c.venv.HasType c.lparams.length [] neg
      (.forallE (.sort .zero) (.sort .zero)))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    c.TrExprS (natDITETypeExpr r) (Reflection.natDITEType r' neg) := by
  have hrc := hrt.closedN c.Ewf.ordered trivial
  have hnc := hnott.closedN c.Ewf.ordered trivial
  have ht := TrExprS.boolTrue (Us := c.lparams) (Δ := []) c.hasPrimitives hb
  obtain ⟨uBool, hBool⟩ := ht.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciBool, _, huBool⟩ := hBool.const_inv c.Ewf.ordered trivial
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨uNat, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trProp {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Prop) (.sort .zero) := .sort rfl
  have trBool {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Bool) .bool := .const hciBool rfl huBool
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have boolType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .bool :=
    ⟨uBool, hBool.weak0 c.Ewf.ordered⟩
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨uNat, hNat.weak0 c.Ewf.ordered⟩
  let Δ₂ : VLCtx := [(none, .vlam .bool), (none, .vlam (.sort .zero))]
  let A := VExpr.app (.app r' (.bvar 1)) (.bvar 0)
  let Δ₃ : VLCtx := (none, .vlam A) :: Δ₂
  let T := VExpr.forallE (.bvar 2) .nat
  let Δ₄ : VLCtx := (none, .vlam T) :: Δ₃
  have hr₂ : TrExprS c.venv c.lparams Δ₂ r.type r' := by
    simpa only [hrc.liftN_eq (Nat.zero_le _)] using
      hr.weakBV_closed c.Ewf.ordered (.skip (.vlam .bool) (.skip (.vlam (.sort .zero)) .refl))
  have hrt₂ : c.venv.HasType c.lparams.length Δ₂.toCtx r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) := hrt.weak0 c.Ewf.ordered
  have hp₂ : c.venv.HasType c.lparams.length Δ₂.toCtx (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have hb₂ : c.venv.HasType c.lparams.length Δ₂.toCtx (.bvar 0) .bool := .bvar .zero
  have tp₂ : TrExprS c.venv c.lparams Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
  have tb₂ : TrExprS c.venv c.lparams Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
  have tA := TrExprS.app (hrt₂.app hp₂) hb₂ (.app hrt₂ hp₂ hr₂ tp₂) tb₂
  have hA : c.venv.IsType c.lparams.length Δ₂.toCtx A := ⟨_, (hrt₂.app hp₂).app hb₂⟩
  have hp₃ : c.venv.HasType c.lparams.length Δ₃.toCtx (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  have tT : TrExprS c.venv c.lparams Δ₃ (.arrow (.bvar 2) q(Nat)) T :=
    .forallE ⟨_, hp₃⟩ natType (.bvar rfl) trNat
  have hT : c.venv.IsType c.lparams.length Δ₃.toCtx T :=
    VEnv.IsType.forallE ⟨_, hp₃⟩ natType
  have tn₄ : TrExprS c.venv c.lparams Δ₄ q(Not) neg := by
    simpa only [hnc.liftN_eq (Nat.zero_le _)] using
      hnot.weakBV_closed c.Ewf.ordered
        (.skip (.vlam T) (.skip (.vlam A) (.skip (.vlam .bool)
          (.skip (.vlam (.sort .zero)) .refl))))
  have hn₄ : c.venv.HasType c.lparams.length Δ₄.toCtx neg
      (.forallE (.sort .zero) (.sort .zero)) := hnott.weak0 c.Ewf.ordered
  have hp₄ : c.venv.HasType c.lparams.length Δ₄.toCtx (.bvar 3) (.sort .zero) :=
    .bvar (.succ (.succ (.succ .zero)))
  have tp₄ : TrExprS c.venv c.lparams Δ₄ (.bvar 3) (.bvar 3) := .bvar rfl
  have tF : TrExprS c.venv c.lparams Δ₄
      (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) (.forallE (.app neg (.bvar 3)) .nat) :=
    .forallE ⟨_, hn₄.app hp₄⟩ natType (.app hn₄ hp₄ tn₄ tp₄) trNat
  have hF := VEnv.IsType.forallE ⟨_, hn₄.app hp₄⟩ natType
  simp only [VContext.TrExprS, hc]
  exact .forallE propType (boolType.forallE (hA.forallE (hT.forallE (hF.forallE natType))))
    trProp (.forallE boolType (hA.forallE (hT.forallE (hF.forallE natType))) trBool
      (.forallE hA (hT.forallE (hF.forallE natType)) tA
        (.forallE hT (hF.forallE natType) tT (.forallE hF natType tF trNat))))

/-- The type-checking prefix of `checkNatDITE`; the computation equations are
checked separately. This definition is only a grouping of the existing checks. -/
def Reflection.checkNatDITETypes (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  checkExprType q(Not) q(Prop → Prop) fail
  checkExprType r.natDITE (natDITETypeExpr r) fail
  checkReflectionProofs r fail

theorem Reflection.checkNatDITE_eq (r : Reflection) (fail : ∀ {α}, M α) :
    r.checkNatDITE fail = (do
      r.checkNatDITETypes fail
      withLocalDecl `p .default q(Prop) fun p => do
      withLocalDecl `a .default (.arrow p q(Nat)) fun a => do
      withLocalDecl `b .default (.arrow (mkApp q(Not) p) q(Nat)) fun b => do
      withLocalDecl `H .default (mkApp2 r.type p q(true)) fun H => do
        unless ← isDefEq (mkApp5 r.natDITE p q(true) H a b)
          (mkApp a (mkApp2 r.ofTrue p H)) do fail
      withLocalDecl `H .default (mkApp2 r.type p q(false)) fun H => do
        unless ← isDefEq (mkApp5 r.natDITE p q(false) H a b)
          (mkApp b (mkApp2 r.ofFalse p H)) do fail) := by
  have bindIf (p : Prop) [Decidable p] (x y : M Unit) (f : Unit → M Unit) :
      ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by
    split <;> rfl
  simp only [checkNatDITE, checkNatDITETypes, checkExprType, natDITETypeExpr,
    checkReflectionProofs, bind_assoc, bindIf]

theorem Reflection.checkNatDITETypes.WF {c : VContext} (hc : c.vlctx = [])
    (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hd : r.natDITE.FVarsIn (· ∈ c.vlctx.fvars))
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (r.checkNatDITETypes fail).WF c s fun _ _ => ∃ neg,
      c.TrExprS q(Not) neg ∧ c.HasType neg (.forallE (.sort .zero) (.sort .zero)) ∧
      (∃ d, c.TrExprS r.natDITE d ∧ c.HasType d (Reflection.natDITEType r' neg)) ∧
      (∃ t, c.TrExprS r.ofTrue t ∧ c.HasType t (Reflection.ofTrueType r')) ∧
      (∃ f, c.TrExprS r.ofFalse f ∧ c.HasType f (Reflection.ofFalseType r' neg)) := by
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have trNotType : c.TrExprS q(Prop → Prop) (.forallE (.sort .zero) (.sort .zero)) :=
    .forallE propType propType (.sort rfl) (.sort rfl)
  unfold checkNatDITETypes
  refine (checkExprType.WF (e := q(Not)) fail hfail (fun _ => nofun) trNotType).bind
    fun _ _ _ ⟨neg, tn, hnt⟩ => ?_
  have tn₀ : TrExprS c.venv c.lparams [] q(Not) neg := by
    simpa only [VContext.TrExprS, hc] using tn
  have hnt₀ : c.venv.HasType c.lparams.length [] neg
      (.forallE (.sort .zero) (.sort .zero)) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hnt
  have trDType := tr_natDITETypeExpr hc hr hrt tn₀ hnt₀ hb hn
  refine (checkExprType.WF fail hfail hd trDType).bind fun _ _ _ hdt => ?_
  exact (checkReflectionProofs.WF hc r fail hfail ht hf hr hrt tn₀ hnt₀ hb).mono
    fun _ _ _ ⟨ht, hf⟩ => ⟨neg, tn, hnt, hdt, ht, hf⟩

private theorem tr_inContext {c : VContext}
    (he : TrExprS c.venv c.lparams [] e e') (hclosed : e'.ClosedN) :
    c.TrExprS e e' := by
  simpa only [hclosed.liftN_eq (Nat.zero_le _)] using
    he.weakFV c.Ewf.ordered (.from_nil c.mlctx.noBV) c.Δwf

def Reflection.natDITEApp (d p b H a f : VExpr) : VExpr :=
  .app (.app (.app (.app (.app d p) b) H) a) f

private theorem tr_natDITEApp {env : VEnv} {r neg : VExpr}
    (hr : r.ClosedN) (hn : neg.ClosedN)
    (hd : env.HasType Us.length Δ.toCtx d' (Reflection.natDITEType r neg))
    (hp : env.HasType Us.length Δ.toCtx p' (.sort .zero))
    (hb : env.HasType Us.length Δ.toCtx b' .bool)
    (hH : env.HasType Us.length Δ.toCtx H' (.app (.app r p') b'))
    (ha : env.HasType Us.length Δ.toCtx a' (.forallE p' .nat))
    (hf : env.HasType Us.length Δ.toCtx f' (.forallE (.app neg p') .nat))
    (td : TrExprS env Us Δ d d') (tp : TrExprS env Us Δ p p')
    (tb : TrExprS env Us Δ b b') (tH : TrExprS env Us Δ H H')
    (ta : TrExprS env Us Δ a a') (tf : TrExprS env Us Δ f f') :
    TrExprS env Us Δ (mkApp5 d p b H a f) (Reflection.natDITEApp d' p' b' H' a' f') ∧
      env.HasType Us.length Δ.toCtx (Reflection.natDITEApp d' p' b' H' a' f') .nat := by
  have td₁ := TrExprS.app hd hp td tp
  have hd₁ := hd.app hp
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower, VExpr.nat, VExpr.bool] at hd₁
  have td₂ := TrExprS.app hd₁ hb td₁ tb
  have hd₂ := hd₁.app hb
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, ← VExpr.lift_instN_lo, VExpr.inst_lift] at hd₂
  have td₃ := TrExprS.app hd₂ hH td₂ tH
  have hd₃ := hd₂.app hH
  simp only [VExpr.inst, hn.instN_eq (Nat.zero_le _), ← VExpr.lift_instN_lo,
    VExpr.inst_lift] at hd₃
  have td₄ := TrExprS.app hd₃ ha td₃ ta
  have hd₄ := hd₃.app ha
  simp only [VExpr.inst, hn.instN_eq (Nat.zero_le _), VExpr.inst_lift] at hd₄
  exact ⟨.app hd₄ hf td₄ tf, hd₄.app hf⟩

private theorem tr_reflectionProof {env : VEnv} {r neg : VExpr} (b : Bool)
    (hr : r.ClosedN) (hn : neg.ClosedN)
    (ht : env.HasType Us.length Δ.toCtx t'
      (if b then Reflection.ofTrueType r else Reflection.ofFalseType r neg))
    (hp : env.HasType Us.length Δ.toCtx p' (.sort .zero))
    (hH : env.HasType Us.length Δ.toCtx H' (.app (.app r p') (.boolLit b)))
    (tt : TrExprS env Us Δ t t') (tp : TrExprS env Us Δ p p')
    (tH : TrExprS env Us Δ H H') :
    TrExprS env Us Δ (mkApp2 t p H) (.app (.app t' p') H') ∧
      env.HasType Us.length Δ.toCtx (.app (.app t' p') H')
        (if b then p' else .app neg p') := by
  cases b <;>
    have tt₁ := TrExprS.app ht hp tt tp <;>
    have ht₁ := ht.app hp
  · simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
      VExpr.instVar_succ, VExpr.instVar_zero, VExpr.boolFalse] at ht₁
    exact ⟨.app ht₁ hH tt₁ tH, Reflection.ofFalseType.apply hr hn ht hp hH⟩
  · simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
      VExpr.instVar_zero, VExpr.boolTrue] at ht₁
    exact ⟨.app ht₁ hH tt₁ tH, Reflection.ofTrueType.apply hr ht hp hH⟩

private def checkNatDITEBranch (r : Reflection) (p a f : Expr) (b : Bool)
    (fail : ∀ {α}, M α) : M Unit :=
  withLocalDecl `H .default (mkApp2 r.type p (toExpr b)) fun H => do
    unless ← isDefEq (mkApp5 r.natDITE p (toExpr b) H a f)
      (mkApp (if b then a else f) (mkApp2 (if b then r.ofTrue else r.ofFalse) p H)) do fail

private theorem checkNatDITEBranch.WF {c : VContext} {r' neg d' t' : VExpr}
    (r : Reflection) (b : Bool) (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hn : neg.ClosedN)
    (td : TrExprS c.venv c.lparams [] r.natDITE d')
    (hd : c.venv.HasType c.lparams.length [] d' (Reflection.natDITEType r' neg))
    (tt : TrExprS c.venv c.lparams [] (if b then r.ofTrue else r.ofFalse) t')
    (ht : c.venv.HasType c.lparams.length [] t'
      (if b then Reflection.ofTrueType r' else Reflection.ofFalseType r' neg))
    (tp : c.TrExprS p p') (hp : c.HasType p' (.sort .zero))
    (ta : c.TrExprS a a') (ha : c.HasType a' (.forallE p' .nat))
    (tf : c.TrExprS f f') (hf : c.HasType f' (.forallE (.app neg p') .nat))
    (hb : c.venv.contains ``Bool) :
    (checkNatDITEBranch r p a f b fail).WF c s fun _ _ =>
      c.venv.IsDefEq c.lparams.length ((.app (.app r' p') (.boolLit b)) :: c.vlctx.toCtx)
        (Reflection.natDITEApp d' p'.lift (.boolLit b) (.bvar 0) a'.lift f'.lift)
        (.app (if b then a'.lift else f'.lift) (.app (.app t' p'.lift) (.bvar 0))) .nat := by
  have hrc := hrt.closedN c.Ewf.ordered trivial
  have hdc := hd.closedN c.Ewf.ordered trivial
  have htc := ht.closedN c.Ewf.ordered trivial
  have tr : c.TrExprS r.type r' := tr_inContext hr hrc
  have hrΓ := hrt.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
  have tb := TrExprS.boolLit (Us := c.lparams) (Δ := c.vlctx) c.hasPrimitives hb b
  let A := VExpr.app (.app r' p') (.boolLit b)
  have tA := TrExprS.app (hrΓ.app hp) tb.2 (.app hrΓ hp tr tp) tb.1
  have hA : c.IsType A := ⟨_, (hrΓ.app hp).app tb.2⟩
  unfold checkNatDITEBranch
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl tA hA (.rfl (s := s)) fun id cwf' s' _ _ => ?_
  let c' := c.withMLC (.vlam id `H (mkApp2 r.type p (toExpr b)) A .default c.mlctx)
  have W : VLCtx.FVLift c.vlctx c'.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tp₁ : c'.TrExprS p p'.lift := tp.weakFV c.Ewf.ordered W c'.Δwf
  have ta₁ : c'.TrExprS a a'.lift := ta.weakFV c.Ewf.ordered W c'.Δwf
  have tf₁ : c'.TrExprS f f'.lift := tf.weakFV c.Ewf.ordered W c'.Δwf
  have hp₁ : c'.HasType p'.lift (.sort .zero) := hp.weak c.Ewf.ordered
  have ha₁ : c'.HasType a'.lift (.forallE p'.lift .nat) := ha.weak c.Ewf.ordered
  have hf₁ : c'.HasType f'.lift (.forallE (.app neg p'.lift) .nat) := by
    simpa only [VExpr.lift, VExpr.liftN, hn.liftN_eq (Nat.zero_le _), VExpr.nat] using
      hf.weak c.Ewf.ordered
  have tH : c'.TrExprS (.fvar id) (.bvar 0) := .fvar (A := A.lift) (by simp [c', VContext.withMLC,
    MLCtx.vlctx, VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type])
  have hH : c'.HasType (.bvar 0) (.app (.app r' p'.lift) (.boolLit b)) := by
    have h : c'.HasType (.bvar 0) A.lift := .bvar .zero
    cases b <;> simpa only [A, VExpr.lift, VExpr.liftN, hrc.liftN_eq (Nat.zero_le _),
      VExpr.boolLit, VExpr.boolTrue, VExpr.boolFalse] using h
  have tb₁ := TrExprS.boolLit (Us := c.lparams) (Δ := c'.vlctx) c'.hasPrimitives hb b
  have td₁ : c'.TrExprS r.natDITE d' := tr_inContext td hdc
  have tt₁ : c'.TrExprS (if b then r.ofTrue else r.ofFalse) t' := tr_inContext tt htc
  have hleft := tr_natDITEApp hrc hn (hd.weak0 c.Ewf.ordered) hp₁ tb₁.2 hH ha₁ hf₁
    td₁ tp₁ tb₁.1 tH ta₁ tf₁
  have hproof := tr_reflectionProof b hrc hn (ht.weak0 c.Ewf.ordered) hp₁ hH tt₁ tp₁ tH
  have tbranch : c'.TrExprS (if b then a else f) (if b then a'.lift else f'.lift) := by
    cases b <;> assumption
  have hbranch : c'.HasType (if b then a'.lift else f'.lift)
      (.forallE (if b then p'.lift else .app neg p'.lift) .nat) := by
    cases b <;> assumption
  have tright := TrExprS.app hbranch hproof.2 tbranch hproof.1
  refine (isDefEq.WF hleft.1 tright).bind fun b' _ _ heq => ?_
  cases b'
  · exact hfail.mono fun _ _ _ h => h.elim
  · exact .pure ((heq rfl).of_r c'.Ewf c'.Δwf.toCtx (hbranch.app hproof.2))

private theorem checkNatDITE_eq_branches (r : Reflection) (fail : ∀ {α}, M α) :
    r.checkNatDITE fail = (do
      r.checkNatDITETypes fail
      withLocalDecl `p .default q(Prop) fun p => do
      withLocalDecl `a .default (.arrow p q(Nat)) fun a => do
      withLocalDecl `b .default (.arrow (mkApp q(Not) p) q(Nat)) fun f => do
        checkNatDITEBranch r p a f true fail
        checkNatDITEBranch r p a f false fail) := by
  rw [Reflection.checkNatDITE_eq]
  rfl

def Reflection.natDITEBranchCtx (r neg : VExpr) (b : Bool) : List VExpr :=
  [.app (.app r (.bvar 2)) (.boolLit b), .forallE (.app neg (.bvar 1)) .nat,
    .forallE (.bvar 0) .nat, .sort .zero]

/-- The two open computation equations checked for a reflected Nat-valued
dependent conditional. The context binds `p`, the two branches, and the witness. -/
structure Reflection.NatDITESpec (env : VEnv) (U : Nat) (r neg d t f : VExpr) : Prop where
  true_eq : env.IsDefEq U (natDITEBranchCtx r neg true)
    (natDITEApp d (.bvar 3) .boolTrue (.bvar 0) (.bvar 2) (.bvar 1))
    (.app (.bvar 2) (.app (.app t (.bvar 3)) (.bvar 0))) .nat
  false_eq : env.IsDefEq U (natDITEBranchCtx r neg false)
    (natDITEApp d (.bvar 3) .boolFalse (.bvar 0) (.bvar 2) (.bvar 1))
    (.app (.bvar 1) (.app (.app f (.bvar 3)) (.bvar 0))) .nat

theorem Reflection.NatDITESpec.apply {env : VEnv} (h : NatDITESpec env U r neg d t f)
    (henv : env.Ordered) (hr : r.ClosedN) (hn : neg.ClosedN) (hd : d.ClosedN)
    (ht : t.ClosedN) (hf : f.ClosedN) (b : Bool)
    (hp : env.HasType U [] p (.sort .zero))
    (ha : env.HasType U [] a (.forallE p .nat))
    (he : env.HasType U [] e (.forallE (.app neg p) .nat))
    (hH : env.HasType U [] H (.app (.app r p) (.boolLit b))) :
    env.IsDefEq U [] (natDITEApp d p (.boolLit b) H a e)
      (.app (if b then a else e) (.app (.app (if b then t else f) p) H)) .nat := by
  have hpc := hp.closedN henv trivial
  have hac := ha.closedN henv trivial
  have hec := he.closedN henv trivial
  have hc : (if b then t else f).ClosedN := by cases b <;> assumption
  have eq : env.IsDefEq U (natDITEBranchCtx r neg b)
      (natDITEApp d (.bvar 3) (.boolLit b) (.bvar 0) (.bvar 2) (.bvar 1))
      (.app (.bvar (if b then 2 else 1))
        (.app (.app (if b then t else f) (.bvar 3)) (.bvar 0))) .nat := by
    cases b
    · exact h.false_eq
    · exact h.true_eq
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at hc eq ⊢
  -- Instantiate the proposition and branches before the witness, whose type
  -- depends on the proposition.
  all_goals
    have eq := eq.instN henv hp (.succ (.succ (.succ .zero)))
    simp only [natDITEApp, VExpr.inst, VExpr.instVar_succ,
      VExpr.instVar_zero, VExpr.instVar_lower, VExpr.lift, VExpr.liftN, liftVar_base,
      hr.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _), hd.instN_eq (Nat.zero_le _),
      hc.instN_eq (Nat.zero_le _), hpc.liftN_eq (Nat.zero_le _), VExpr.nat, VExpr.boolLit,
      VExpr.boolTrue, VExpr.boolFalse] at eq
    have eq := eq.instN henv ha (.succ (.succ .zero))
    simp only [VExpr.inst, VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
      hr.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
      hd.instN_eq (Nat.zero_le _), hc.instN_eq (Nat.zero_le _),
      hpc.instN_eq (Nat.zero_le _), hac.liftN_eq (Nat.zero_le _),
      VExpr.lift, VExpr.liftN, liftVar_base] at eq
    have eq := eq.instN henv he (.succ .zero)
    simp only [VExpr.inst, VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
      hr.instN_eq (Nat.zero_le _), hd.instN_eq (Nat.zero_le _),
      hc.instN_eq (Nat.zero_le _), hpc.instN_eq (Nat.zero_le _),
      hac.instN_eq (Nat.zero_le _), hec.liftN_eq (Nat.zero_le _),
      VExpr.lift] at eq
    simpa only [natDITEApp, VExpr.inst, VExpr.instVar_zero,
      hd.instN_eq (Nat.zero_le _), hc.instN_eq (Nat.zero_le _),
      hpc.instN_eq (Nat.zero_le _), hac.instN_eq (Nat.zero_le _), hec.instN_eq (Nat.zero_le _),
      VExpr.nat, VExpr.boolLit, VExpr.boolTrue, VExpr.boolFalse] using eq.instN henv hH .zero

theorem Reflection.checkNatDITE.WF {c : VContext} (hc : c.vlctx = [])
    (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hd : r.natDITE.FVarsIn (· ∈ c.vlctx.fvars))
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (r.checkNatDITE fail).WF c s fun _ _ => ∃ neg d t f,
      c.TrExprS q(Not) neg ∧ c.HasType neg (.forallE (.sort .zero) (.sort .zero)) ∧
      c.TrExprS r.natDITE d ∧ c.HasType d (Reflection.natDITEType r' neg) ∧
      c.TrExprS r.ofTrue t ∧ c.HasType t (Reflection.ofTrueType r') ∧
      c.TrExprS r.ofFalse f ∧ c.HasType f (Reflection.ofFalseType r' neg) ∧
      Reflection.NatDITESpec c.venv c.lparams.length r' neg d t f := by
  rw [checkNatDITE_eq_branches]
  refine (Reflection.checkNatDITETypes.WF hc r fail hfail hd ht hf hr hrt hb hn).bind
    fun _ _ _ ⟨neg, tn, hnt, ⟨d, td, hdt⟩, ⟨t, tt, htt⟩, ⟨f, tf, hft⟩⟩ => ?_
  have tn₀ : TrExprS c.venv c.lparams [] q(Not) neg := by
    simpa only [VContext.TrExprS, hc] using tn
  have td₀ : TrExprS c.venv c.lparams [] r.natDITE d := by
    simpa only [VContext.TrExprS, hc] using td
  have tt₀ : TrExprS c.venv c.lparams [] r.ofTrue t := by
    simpa only [VContext.TrExprS, hc] using tt
  have tf₀ : TrExprS c.venv c.lparams [] r.ofFalse f := by
    simpa only [VContext.TrExprS, hc] using tf
  have hn₀ : c.venv.HasType c.lparams.length [] neg
      (.forallE (.sort .zero) (.sort .zero)) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hnt
  have hd₀ : c.venv.HasType c.lparams.length [] d (Reflection.natDITEType r' neg) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hdt
  have ht₀ : c.venv.HasType c.lparams.length [] t (Reflection.ofTrueType r') := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using htt
  have hf₀ : c.venv.HasType c.lparams.length [] f (Reflection.ofFalseType r' neg) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hft
  have hnc := hn₀.closedN c.Ewf.ordered trivial
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨uNat, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨uNat, hNat.weak0 c.Ewf.ordered⟩
  have propType : c.IsType (.sort .zero) := ⟨_, .sort trivial⟩
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl (c := c) (m := c.mlctx) (.sort rfl) propType .rfl
    fun pid pwf sp _ _ => ?_
  let cp := c.withMLC (.vlam pid `p q(Prop) (.sort .zero) .default c.mlctx) (wf := pwf)
  have tp : cp.TrExprS (.fvar pid) (.bvar 0) := .fvar (A := .sort .zero) (by
    simp [cp, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN])
  have hp : cp.HasType (.bvar 0) (.sort .zero) := .bvar .zero
  let A := VExpr.forallE (.bvar 0) .nat
  have tA : cp.TrExprS (.arrow (.fvar pid) q(Nat)) A :=
    .forallE ⟨_, hp⟩ natType tp trNat
  have hA : cp.IsType A := VEnv.IsType.forallE ⟨_, hp⟩ natType
  refine M.WF.withLocalDecl (c := c) (m := cp.mlctx) (cwf := pwf) tA hA (.rfl (s := sp))
    fun aid awf sa _ _ => ?_
  let ca := c.withMLC (.vlam aid `a (.arrow (.fvar pid) q(Nat)) A .default cp.mlctx) (wf := awf)
  have Wp : VLCtx.FVLift cp.vlctx ca.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tp₁ : ca.TrExprS (.fvar pid) (.bvar 1) := tp.weakFV c.Ewf.ordered Wp ca.Δwf
  have hp₁ : ca.HasType (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have ta : ca.TrExprS (.fvar aid) (.bvar 0) := .fvar (A := A.lift) (by
    simp [ca, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type])
  have tn₁ : ca.TrExprS q(Not) neg := tr_inContext tn₀ hnc
  have hn₁ : ca.HasType neg (.forallE (.sort .zero) (.sort .zero)) := hn₀.weak0 c.Ewf.ordered
  let B := VExpr.forallE (.app neg (.bvar 1)) .nat
  have tB : ca.TrExprS (.arrow (mkApp q(Not) (.fvar pid)) q(Nat)) B :=
    .forallE ⟨_, hn₁.app hp₁⟩ natType (.app hn₁ hp₁ tn₁ tp₁) trNat
  have hB : ca.IsType B := VEnv.IsType.forallE ⟨_, hn₁.app hp₁⟩ natType
  refine M.WF.withLocalDecl (c := c) (m := ca.mlctx) (cwf := awf) tB hB (.rfl (s := sa))
    fun fid fwf sf _ _ => ?_
  let cf := c.withMLC (.vlam fid `b (.arrow (mkApp q(Not) (.fvar pid)) q(Nat))
    B .default ca.mlctx) (wf := fwf)
  have Wa : VLCtx.FVLift ca.vlctx cf.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tp₂ : cf.TrExprS (.fvar pid) (.bvar 2) := tp₁.weakFV c.Ewf.ordered Wa cf.Δwf
  have ta₁ : cf.TrExprS (.fvar aid) (.bvar 1) := ta.weakFV c.Ewf.ordered Wa cf.Δwf
  have tf₁ : cf.TrExprS (.fvar fid) (.bvar 0) := .fvar (A := B.lift) (by
    simp [cf, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type])
  have hp₂ : cf.HasType (.bvar 2) (.sort .zero) := .bvar (.succ (.succ .zero))
  have ha₁ : cf.HasType (.bvar 1) (.forallE (.bvar 2) .nat) := .bvar (.succ .zero)
  have hf₁ : cf.HasType (.bvar 0) (.forallE (.app neg (.bvar 2)) .nat) := by
    have h : cf.HasType (.bvar 0) B.lift := .bvar .zero
    simpa only [B, VExpr.lift, VExpr.liftN, hnc.liftN_eq (Nat.zero_le _),
      liftVar, VExpr.nat] using h
  refine (checkNatDITEBranch.WF (c := cf) r true fail hfail hr hrt hnc td₀ hd₀ tt₀ ht₀
    tp₂ hp₂ ta₁ ha₁ tf₁ hf₁ hb).bind fun _ _ _ htrue => ?_
  refine (checkNatDITEBranch.WF (c := cf) r false fail hfail hr hrt hnc td₀ hd₀ tf₀ hf₀
    tp₂ hp₂ ta₁ ha₁ tf₁ hf₁ hb).mono fun _ _ _ hfalse => ?_
  refine ⟨neg, d, t, f, tn, hnt, td, hdt, tt, htt, tf, hft, ?_, ?_⟩
  · simpa only [cf, ca, cp, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, VLCtx.toCtx, hc]
      using htrue
  · simpa only [cf, ca, cp, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, VLCtx.toCtx, hc]
      using hfalse

private theorem contains_primitive (c : VContext) (hn : c.env.contains n)
    (hp : Kernel.Environment.primitives.contains n) : c.venv.contains n := by
  rw [Kernel.Environment.contains, SMap.find?_isSome] at hn
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hn
  have hci' : c.env.find? n = some ci := by
    simpa only [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?] using hci
  have hs := (c.safePrimitives hci' hp).1
  exact c.trenv.find?_iff.1 ⟨ci, hci', hs ▸ DefinitionSafety.le_safe⟩

theorem checkPrimitiveDef_natAdd.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatAddSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hn := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hz := TrExprS.natZero (Us := []) (Δ := []) c.hasPrimitives hn
    obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
          (.forallE .nat (.forallE .nat .nat)) := hf₁.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
        simpa only [VExpr.lift, VExpr.liftN_liftN] using
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
      have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value (.bvar 0) q(Nat.zero)))
          (.lam .nat (.app (.app f.lift (.bvar 0)) .natZero)) :=
        .lam natType trNat (.app (hf₁.app hx₁) hz₁.2 (.app hf₁ hx₁ hv₁ tx₁) hz₁.1)
      have tid : c.TrExprS (.lam0 q(Nat) (.bvar 0)) (.lam .nat (.bvar 0)) :=
        .lam natType trNat tx₁
      refine (isDefEq.WF (c := c) tzero tid).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have tadd := TrExprS.app hf₂ hy₂ hv₂ ty₂
        have tsucc := TrExprS.app hs₂.2 hx₂ hs₂.1 tx₂
        have tleft := TrExprS.app (hf₂.app hy₂) (hs₂.2.app hx₂) tadd tsucc
        have tright := TrExprS.app hs₂.2 ((hf₂.app hy₂).app hx₂) hs₂.1
          (.app (hf₂.app hy₂) hx₂ tadd tx₂)
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hx₁
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hx₁))
          · have hl : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
              (hf₂.app hy₂).app (hs₂.2.app hx₂)
            have hr : c.venv.HasType 0 [.nat, .nat]
                (.app .natSucc (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) .nat :=
              hs₂.2.app ((hf₂.app hy₂).app hx₂)
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

theorem checkPrimitiveDef_natMul.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧ (ves.venv .safe).contains ``Nat.add ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatMulSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hadd := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have haddTy := c.hasPrimitives.natAddType hadd
    obtain ⟨u, hNat⟩ := (haddTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hci⟩
    obtain ⟨_, haddci, _, haddUs⟩ := haddTy.const_inv c.Ewf.ordered trivial
    have trAdd {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat.add) (.const ``Nat.add []) :=
      .const haddci rfl haddUs
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
          (.forallE .nat (.forallE .nat .nat)) := hf₁.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
        simpa only [VExpr.lift, VExpr.liftN_liftN] using
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
      have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value (.bvar 0) q(Nat.zero)))
          (.lam .nat (.app (.app f.lift (.bvar 0)) .natZero)) :=
        .lam natType trNat (.app (hf₁.app hx₁) hz₁.2 (.app hf₁ hx₁ hv₁ tx₁) hz₁.1)
      have tz : c.TrExprS (.lam0 q(Nat) q(Nat.zero)) (.lam .nat .natZero) :=
        .lam natType trNat hz₁.1
      refine (isDefEq.WF (c := c) tzero tz).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have tadd := TrExprS.app hf₂ hy₂ hv₂ ty₂
        have tsucc := TrExprS.app hs₂.2 hx₂ hs₂.1 tx₂
        have tleft := TrExprS.app (hf₂.app hy₂) (hs₂.2.app hx₂) tadd tsucc
        have hadd₂ : c.venv.HasType 0 [.nat, .nat] (.const ``Nat.add [])
            (.forallE .nat (.forallE .nat .nat)) := haddTy.weak0 c.Ewf.ordered
        have hprod := (hf₂.app hy₂).app hx₂
        have tprod := TrExprS.app (hf₂.app hy₂) hx₂ tadd tx₂
        have tright := TrExprS.app (hadd₂.app hprod) hy₂
          (.app hadd₂ hprod (trAdd (Δ := Δ₂)) tprod) ty₂
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, hadd, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hz₁.2
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hz₁.2))
          · have hl : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
              (hf₂.app hy₂).app (hs₂.2.app hx₂)
            have hr : c.venv.HasType 0 [.nat, .nat]
                (.app (.app (.const ``Nat.add [])
                  (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) (.bvar 1)) .nat :=
              (hadd₂.app hprod).app hy₂
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

theorem checkPrimitiveDef_natPow.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧ (ves.venv .safe).contains ``Nat.mul ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatPowSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hmul := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hmulTy := c.hasPrimitives.natMulType hmul
    obtain ⟨u, hNat⟩ := (hmulTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hci⟩
    obtain ⟨_, hmulci, _, hmulUs⟩ := hmulTy.const_inv c.Ewf.ordered trivial
    have trMul {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat.mul) (.const ``Nat.mul []) :=
      .const hmulci rfl hmulUs
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
          (.forallE .nat (.forallE .nat .nat)) := hf₁.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
        simpa only [VExpr.lift, VExpr.liftN_liftN] using
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
      have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value (.bvar 0) q(Nat.zero)))
          (.lam .nat (.app (.app f.lift (.bvar 0)) .natZero)) :=
        .lam natType trNat (.app (hf₁.app hx₁) hz₁.2 (.app hf₁ hx₁ hv₁ tx₁) hz₁.1)
      have hs₁ := TrExprS.natSucc (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have hone := hs₁.2.app hz₁.2
      have tone : c.TrExprS (.lam0 q(Nat) (mkApp q(Nat.succ) q(Nat.zero)))
          (.lam .nat (.natLit 1)) :=
        .lam natType trNat (.app hs₁.2 hz₁.2 hs₁.1 hz₁.1)
      refine (isDefEq.WF (c := c) tzero tone).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have tpow := TrExprS.app hf₂ hy₂ hv₂ ty₂
        have tsucc := TrExprS.app hs₂.2 hx₂ hs₂.1 tx₂
        have tleft := TrExprS.app (hf₂.app hy₂) (hs₂.2.app hx₂) tpow tsucc
        have hmul₂ : c.venv.HasType 0 [.nat, .nat] (.const ``Nat.mul [])
            (.forallE .nat (.forallE .nat .nat)) := hmulTy.weak0 c.Ewf.ordered
        have hpow := (hf₂.app hy₂).app hx₂
        have tpowApp := TrExprS.app (hf₂.app hy₂) hx₂ tpow tx₂
        have tright := TrExprS.app (hmul₂.app hpow) hy₂
          (.app hmul₂ hpow (trMul (Δ := Δ₂)) tpowApp) ty₂
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, hmul, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hone
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hone))
          · have hl : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
              (hf₂.app hy₂).app (hs₂.2.app hx₂)
            have hr : c.venv.HasType 0 [.nat, .nat]
                (.app (.app (.const ``Nat.mul [])
                  (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) (.bvar 1)) .nat :=
              (hmul₂.app hpow).app hy₂
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

theorem checkPrimitiveDef_natPred.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat .nat) ∧
      VEnv.NatPredSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hn := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hz := TrExprS.natZero (Us := []) (Δ := []) c.hasPrimitives hn
    obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat) (.forallE .nat .nat) :=
      .forallE natType natType trNat trNat
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      have tzero := TrExprS.app hf hz.2 hv hz.1
      refine (isDefEq.WF (c := c) tzero hz.1).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        let Δ₁ : VLCtx := [(none, .vlam .nat)]
        have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat .nat) :=
          hf.weak c.Ewf.ordered
        have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
        have tx : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
        have hx : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
        have hs := TrExprS.natSucc (Us := []) (Δ := Δ₁) c.hasPrimitives hn
        have hleft := hf₁.app (hs.2.app hx)
        have tleft := TrExprS.app hf₁ (hs.2.app hx) hv₁ (.app hs.2 hx hs.1 tx)
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat tleft
        have tid : c.TrExprS (.lam0 q(Nat) (.bvar 0)) (.lam .nat (.bvar 0)) :=
          .lam natType trNat tx
        refine (isDefEq.WF (c := c) tleft' tid).bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, htype rfl, (hzero rfl).of_r c.Ewf c.Δwf hz.2, ?_⟩
          exact VEnv.IsDefEq.lam_body c.Ewf.ordered hleft hx
            ((hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy hx))
  · exact nofun

theorem checkPrimitiveDef_natSub.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧ (ves.venv .safe).contains ``Nat.pred ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatSubSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hpred := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hpredTy := c.hasPrimitives.natPredType hpred
    obtain ⟨u, hNat⟩ := (hpredTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hci⟩
    obtain ⟨_, hpredci, _, hpredUs⟩ := hpredTy.const_inv c.Ewf.ordered trivial
    have trPred {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat.pred) (.const ``Nat.pred []) :=
      .const hpredci rfl hpredUs
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
          (.forallE .nat (.forallE .nat .nat)) := hf₁.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
        simpa only [VExpr.lift, VExpr.liftN_liftN] using
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
      have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value (.bvar 0) q(Nat.zero)))
          (.lam .nat (.app (.app f.lift (.bvar 0)) .natZero)) :=
        .lam natType trNat (.app (hf₁.app hx₁) hz₁.2 (.app hf₁ hx₁ hv₁ tx₁) hz₁.1)
      have tid : c.TrExprS (.lam0 q(Nat) (.bvar 0)) (.lam .nat (.bvar 0)) :=
        .lam natType trNat tx₁
      refine (isDefEq.WF (c := c) tzero tid).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have tsub := TrExprS.app hf₂ hy₂ hv₂ ty₂
        have tsucc := TrExprS.app hs₂.2 hx₂ hs₂.1 tx₂
        have tleft := TrExprS.app (hf₂.app hy₂) (hs₂.2.app hx₂) tsub tsucc
        have hpred₂ : c.venv.HasType 0 [.nat, .nat] (.const ``Nat.pred [])
            (.forallE .nat .nat) := hpredTy.weak0 c.Ewf.ordered
        have tvalue := TrExprS.app (hf₂.app hy₂) hx₂ tsub tx₂
        have tright := TrExprS.app hpred₂ ((hf₂.app hy₂).app hx₂)
          (trPred (Δ := Δ₂)) tvalue
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, hpred, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hx₁
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hx₁))
          · have hl : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
              (hf₂.app hy₂).app (hs₂.2.app hx₂)
            have hr : c.venv.HasType 0 [.nat, .nat]
                (.app (.const ``Nat.pred []) (.app (.app f.lift.lift (.bvar 1)) (.bvar 0))) .nat :=
              hpred₂.app ((hf₂.app hy₂).app hx₂)
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

theorem checkPrimitiveDef_natShiftLeft.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧ (ves.venv .safe).contains ``Nat.mul ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatShiftLeftSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hmul := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hmulTy := c.hasPrimitives.natMulType hmul
    obtain ⟨u, hNat⟩ := (hmulTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hci⟩
    obtain ⟨_, hmulci, _, hmulUs⟩ := hmulTy.const_inv c.Ewf.ordered trivial
    have trMul {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat.mul) (.const ``Nat.mul []) :=
      .const hmulci rfl hmulUs
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
          (.forallE .nat (.forallE .nat .nat)) := hf₁.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
        simpa only [VExpr.lift, VExpr.liftN_liftN] using
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
      have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value (.bvar 0) q(Nat.zero)))
          (.lam .nat (.app (.app f.lift (.bvar 0)) .natZero)) :=
        .lam natType trNat (.app (hf₁.app hx₁) hz₁.2 (.app hf₁ hx₁ hv₁ tx₁) hz₁.1)
      have tid : c.TrExprS (.lam0 q(Nat) (.bvar 0)) (.lam .nat (.bvar 0)) :=
        .lam natType trNat tx₁
      refine (isDefEq.WF (c := c) tzero tid).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
        have hz₂ := TrExprS.natZero (Us := []) (Δ := Δ₂) c.hasPrimitives hn
        have htwo : c.venv.HasType 0 [.nat, .nat] (.natLit 2) .nat :=
          hs₂.2.app (hs₂.2.app hz₂.2)
        have ttwo := TrExprS.app hs₂.2 (hs₂.2.app hz₂.2) hs₂.1
          (.app hs₂.2 hz₂.2 hs₂.1 hz₂.1)
        have tsucc := TrExprS.app hs₂.2 hy₂ hs₂.1 ty₂
        have tleft := TrExprS.app (hf₂.app hx₂) (hs₂.2.app hy₂)
          (.app hf₂ hx₂ hv₂ tx₂) tsucc
        have hmul₂ : c.venv.HasType 0 [.nat, .nat] (.const ``Nat.mul [])
            (.forallE .nat (.forallE .nat .nat)) := hmulTy.weak0 c.Ewf.ordered
        have hdouble : c.venv.HasType 0 [.nat, .nat]
            (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)) .nat :=
          (hmul₂.app htwo).app hx₂
        have tdouble := TrExprS.app (hmul₂.app htwo) hx₂
          (.app hmul₂ htwo (trMul (Δ := Δ₂)) ttwo) tx₂
        have tright := TrExprS.app (hf₂.app hdouble) hy₂
          (.app hf₂ hdouble hv₂ tdouble) ty₂
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, hmul, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hx₁
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hx₁))
          · have hl : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 0)) (.app .natSucc (.bvar 1))) .nat :=
              (hf₂.app hx₂).app (hs₂.2.app hy₂)
            have hr : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift
                  (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) (.bvar 1)) .nat :=
              (hf₂.app hdouble).app hy₂
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

-- Both comparison branches are definitionally equal to this shared sequence of checks.
private def checkNatComparison (v : DefinitionVal) (zeroSucc : Bool) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let env ← getEnv
  unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Bool) do fail
  let cmp := mkApp2 v.value
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← isDefEq (cmp zero zero) q(true) do fail
  unless ← defeq1 (cmp zero (succ x)) (toExpr zeroSucc) do fail
  unless ← defeq1 (cmp (succ x) zero) q(false) do fail
  unless ← defeq2 (cmp (succ y) (succ x)) (cmp y x) do fail
  return true

private theorem checkNatComparison.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (zeroSucc : Bool)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkNatComparison v zeroSucc).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .bool)) ∧
      VEnv.NatComparisonSpec (ves.venv .safe) f zeroSucc := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkNatComparison
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hn := contains_primitive c hguard.1.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hb := contains_primitive c hguard.1.2
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hz := TrExprS.natZero (Us := []) (Δ := []) c.hasPrimitives hn
    have htBool := TrExprS.boolTrue (Us := []) (Δ := []) c.hasPrimitives hb
    obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
    obtain ⟨ci, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    obtain ⟨uBool, hBool⟩ := htBool.2.isType c.Ewf.ordered trivial
    obtain ⟨ciBool, hciBool, _, huBool⟩ := hBool.const_inv c.Ewf.ordered trivial
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hci rfl hu
    have trBool {Δ : VLCtx} : TrExprS c.venv [] Δ q(Bool) .bool :=
      .const hciBool rfl huBool
    have natTy {Γ : List VExpr} : c.venv.HasType 0 Γ .nat (.sort u) := hNat.weak0 c.Ewf.ordered
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat := ⟨u, natTy⟩
    have boolType {Γ : List VExpr} : c.venv.IsType 0 Γ .bool :=
      ⟨uBool, hBool.weak0 c.Ewf.ordered⟩
    have trType : c.TrExprS q(Nat → Nat → Bool) (.forallE .nat (.forallE .nat .bool)) :=
      .forallE natType (natType.forallE boolType) trNat
        (.forallE natType boolType trNat trBool)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      have tzz := TrExprS.app (hf.app hz.2) hz.2 (.app hf hz.2 hv hz.1) hz.1
      refine (isDefEq.WF (c := c) tzz htBool.1).bind fun b _ _ hzz => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        let Δ₁ : VLCtx := [(none, .vlam .nat)]
        let Δ₂ : VLCtx := (none, .vlam .nat) :: Δ₁
        have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .bool)) :=
          hf.weak c.Ewf.ordered
        have hf₂ : c.venv.HasType 0 [.nat, .nat] f.lift.lift
            (.forallE .nat (.forallE .nat .bool)) := hf₁.weak c.Ewf.ordered
        have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
          hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
        have hv₂ : TrExprS c.venv [] Δ₂ v.value f.lift.lift := by
          simpa only [VExpr.lift, VExpr.liftN_liftN] using
            hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
        have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
        have tx₂ : TrExprS c.venv [] Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
        have ty₂ : TrExprS c.venv [] Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
        have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
        have hx₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
        have hy₂ : c.venv.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
        have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
        have hs₁ := TrExprS.natSucc (Us := []) (Δ := Δ₁) c.hasPrimitives hn
        have hfalse := TrExprS.boolFalse (Us := []) (Δ := Δ₁) c.hasPrimitives hb
        have hzeroSucc := TrExprS.boolLit (Us := []) (Δ := Δ₁) c.hasPrimitives hb zeroSucc
        have tsx₁ := TrExprS.app hs₁.2 hx₁ hs₁.1 tx₁
        have tzs := TrExprS.app (hf₁.app hz₁.2) (hs₁.2.app hx₁)
          (.app hf₁ hz₁.2 hv₁ hz₁.1) tsx₁
        have tzs' := TrExprS.lam (name := `_) (bi := .default) natType trNat tzs
        have tf' := TrExprS.lam (name := `_) (bi := .default) natType trNat hfalse.1
        have tzsResult := TrExprS.lam (name := `_) (bi := .default) natType trNat hzeroSucc.1
        refine (isDefEq.WF (c := c) tzs' tzsResult).bind fun b _ _ hzs => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          have tsz := TrExprS.app (hf₁.app (hs₁.2.app hx₁)) hz₁.2
            (.app hf₁ (hs₁.2.app hx₁) hv₁ tsx₁) hz₁.1
          have tsz' := TrExprS.lam (name := `_) (bi := .default) natType trNat tsz
          refine (isDefEq.WF (c := c) tsz' tf').bind fun b _ _ hsz => ?_
          cases b
          · exact nofun
          · simp only [if_true]
            have hs₂ := TrExprS.natSucc (Us := []) (Δ := Δ₂) c.hasPrimitives hn
            have tsy := TrExprS.app hs₂.2 hy₂ hs₂.1 ty₂
            have tsx := TrExprS.app hs₂.2 hx₂ hs₂.1 tx₂
            have tleft := TrExprS.app (hf₂.app (hs₂.2.app hy₂)) (hs₂.2.app hx₂)
              (.app hf₂ (hs₂.2.app hy₂) hv₂ tsy) tsx
            have tright := TrExprS.app (hf₂.app hy₂) hx₂ (.app hf₂ hy₂ hv₂ ty₂) tx₂
            have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
              (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
            have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
              (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
            refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hss => ?_
            cases b
            · exact nofun
            · simp only [if_true]
              apply M.WF.pure
              refine ⟨hn, htype rfl, (hzz rfl).of_r c.Ewf c.Δwf htBool.2, ?_, ?_, ?_⟩
              · exact VEnv.IsDefEq.lam_body c.Ewf.ordered
                  ((hf₁.app hz₁.2).app (hs₁.2.app hx₁)) hzeroSucc.2
                  ((hzs rfl).of_r c.Ewf c.Δwf (.lam natTy hzeroSucc.2))
              · exact VEnv.IsDefEq.lam_body c.Ewf.ordered
                  ((hf₁.app (hs₁.2.app hx₁)).app hz₁.2) hfalse.2
                  ((hsz rfl).of_r c.Ewf c.Δwf (.lam natTy hfalse.2))
              · have hl : c.venv.HasType 0 [.nat, .nat]
                    (.app (.app f.lift.lift (.app .natSucc (.bvar 1)))
                      (.app .natSucc (.bvar 0))) .bool :=
                  (hf₂.app (hs₂.2.app hy₂)).app (hs₂.2.app hx₂)
                have hr : c.venv.HasType 0 [.nat, .nat]
                    (.app (.app f.lift.lift (.bvar 1)) (.bvar 0)) .bool :=
                  (hf₂.app hy₂).app hx₂
                have he := (hss rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hr))
                have he := VEnv.IsDefEq.lam_body c.Ewf.ordered (.lam natTy hl) (.lam natTy hr) he
                exact VEnv.IsDefEq.lam_body c.Ewf.ordered hl hr he
  · exact nofun

theorem checkPrimitiveDef_natBeq.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .bool)) ∧
      VEnv.NatBeqSpec (ves.venv .safe) f := by
  have heq : checkPrimitiveDef v = checkNatComparison v false := by
    unfold checkPrimitiveDef checkNatComparison
    simp only [hname]
    rfl
  rw [heq]
  exact checkNatComparison.WF wf v false ht hv hf

theorem checkPrimitiveDef_natBle.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .bool)) ∧
      VEnv.NatBleSpec (ves.venv .safe) f := by
  have heq : checkPrimitiveDef v = checkNatComparison v true := by
    unfold checkPrimitiveDef checkNatComparison
    simp only [hname]
    rfl
  rw [heq]
  exact checkNatComparison.WF wf v true ht hv hf

theorem checkPrimitiveDef_natBeq.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.beq []) f type) :
    env'.ReflectsNatNatBool ``Nat.beq Nat.beq := by
  have ⟨hn, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natBeq.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  intro _ a b
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have heval := (hspec.eval (wf.tr (safety := .safe)).wf.ordered wf.hasPrimitives hn a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natBle.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.ble []) f type) :
    env'.ReflectsNatNatBool ``Nat.ble Nat.ble := by
  have ⟨hn, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natBle.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  intro _ a b
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have heval := (hspec.eval (wf.tr (safety := .safe)).wf.ordered wf.hasPrimitives hn a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natAdd.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.add []) f type) :
    env'.HasType 0 [] (.const ``Nat.add []) (.forallE .nat (.forallE .nat .nat)) ∧
    env'.ReflectsNatNatNat ``Nat.add Nat.add := by
  have ⟨hn, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natAdd.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, ?_⟩
  intro _ a b
  have ha := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn a).2.mono hle
  have hb := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn b).2.mono hle
  have heval := (hspec.eval (wf.tr (safety := .safe)).wf.ordered wf.hasPrimitives hn a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natAdd.reflects {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.add []) f type) :
    env'.ReflectsNatNatNat ``Nat.add Nat.add := by
  exact (checkPrimitiveDef_natAdd.extension wf v hname ht hv hf hcheck henv' hle hdef).2

theorem checkPrimitiveDef_natMul.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.mul []) f type) :
    env'.HasType 0 [] (.const ``Nat.mul []) (.forallE .nat (.forallE .nat .nat)) ∧
    env'.ReflectsNatNatNat ``Nat.mul Nat.mul := by
  have ⟨hn, hadd, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natMul.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, ?_⟩
  intro _ a b
  have ha := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn a).2.mono hle
  have hb := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn b).2.mono hle
  have henv := (wf.tr (safety := .safe)).wf
  have hp := wf.hasPrimitives (safety := .safe)
  have heval := hspec.eval henv.ordered hp hn (hp.natAddType hadd)
    (fun a b => (hp.natAdd hadd a b).of_r henv trivial (hp.natLit_type hn (a + b))) a b
  have heval := heval.mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natPow.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.pow []) f type) :
    env'.ReflectsNatNatNat ``Nat.pow Nat.pow := by
  have ⟨hn, hmul, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natPow.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  intro _ a b
  have ha := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn a).2.mono hle
  have hb := (TrExprS.natLit (Us := []) (Δ := []) wf.hasPrimitives hn b).2.mono hle
  have henv := (wf.tr (safety := .safe)).wf
  have hp := wf.hasPrimitives (safety := .safe)
  have heval := hspec.eval henv.ordered hp hn (hp.natMulType hmul)
    (fun a b => (hp.natMul hmul a b).of_r henv trivial (hp.natLit_type hn (a * b))) a b
  have heval := heval.mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natPred.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.pred []) f type) :
    env'.HasType 0 [] (.const ``Nat.pred []) (.forallE .nat .nat) ∧
    ∀ a, env'.IsDefEq 0 [] (.app (.const ``Nat.pred []) (.natLit a)) (.natLit a.pred) .nat := by
  have ⟨hn, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natPred.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, fun a => ?_⟩
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have heval := (hspec.eval (wf.tr (safety := .safe)).wf.ordered wf.hasPrimitives hn a).mono hle
  exact (hdef'.appDF ha).trans heval

theorem checkPrimitiveDef_natSub.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.sub []) f type) :
    env'.HasType 0 [] (.const ``Nat.sub []) (.forallE .nat (.forallE .nat .nat)) ∧
    env'.ReflectsNatNatNat ``Nat.sub Nat.sub := by
  have ⟨hn, hpred, htype, hspec⟩ := M.WF.run wf (checkPrimitiveDef_natSub.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, fun _ a b => ?_⟩
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have heval :=
    (hspec.eval (wf.tr (safety := .safe)).wf.ordered wf.hasPrimitives hn hpred a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natShiftLeft.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.shiftLeft []) f type) :
    env'.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft := by
  have ⟨hn, hmul, htype, hspec⟩ :=
    M.WF.run wf (checkPrimitiveDef_natShiftLeft.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  intro _ a b
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have henv := (wf.tr (safety := .safe)).wf
  have hp := wf.hasPrimitives (safety := .safe)
  have hf' := hf.defeqU_r henv trivial htype
  have heval := hspec.eval henv.ordered hp hn hf'
    (fun a b => (hp.natMul hmul a b).of_r henv trivial (hp.natLit_type hn (a * b))) a b
  exact ((hdef'.appDF ha |>.appDF hb).trans (heval.mono hle)).toU

end Environment
end Lean4Lean
