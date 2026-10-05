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

/-- The open equations checked for a candidate implementation of `Nat.shiftRight`. -/
structure NatShiftRightSpec (env : VEnv) (f : VExpr) : Prop where
  zero : env.IsDefEq 0 [.nat]
    (.app (.app f.lift (.bvar 0)) .natZero) (.bvar 0) .nat
  succ : env.IsDefEq 0 [.nat, .nat]
    (.app (.app f.lift.lift (.bvar 0)) (.app .natSucc (.bvar 1)))
    (.app (.app (.const ``Nat.div []) (.app (.app f.lift.lift (.bvar 0)) (.bvar 1)))
      (.natLit 2)) .nat

theorem NatShiftRightSpec.eval (h : NatShiftRightSpec env f) (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hdiv : env.HasType 0 [] (.const ``Nat.div []) (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.div []) (.natLit a)) (.natLit b)) (.natLit (a / b)) .nat)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b))
      (.natLit (Nat.shiftRight a b)) .nat := by
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  induction b with
  | zero =>
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.nat, VExpr.natZero]
      using h.zero.instN henv ha .zero
  | succ b ih =>
    have hb := hp.natLit_type (U := 0) (Γ := []) hn b
    have hs := h.succ.instN henv (ha.weak0 henv (Γ := [.nat])) .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero, VExpr.instVar_upper,
      VExpr.nat, VExpr.natSucc, VExpr.natLit, VExpr.natZero] at hs
    have hs := hs.instN henv hb .zero
    simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
      (ha.closedN henv trivial).instN_eq (Nat.zero_le _)] at hs
    simpa only [Nat.shiftRight_succ] using hs.trans <|
      ((hdiv.appDF ih).appDF (hp.natLit_type hn 2)).trans (heval (Nat.shiftRight a b) 2)

def natLeExpr (le : VExpr) (a b : Nat) : VExpr :=
  .app (.app le (.natLit a)) (.natLit b)

def natDivLoopExpr (go : VExpr) (y : Nat) (hy : VExpr) (fuel a : Nat) (ha : VExpr) : VExpr :=
  .app (.app (.app (.app (.app go (.natLit y)) hy) (.natLit fuel)) (.natLit a)) ha

/-- The dependent type checked for the division loop, retaining positivity and
the bound on the remaining fuel. -/
def natDivLoopType (le : VExpr) : VExpr :=
  .forallE .nat <| .forallE (.app (.app le (.natLit 1)) (.bvar 0)) <|
    .forallE .nat <| .forallE .nat <|
    .forallE (.app (.app le (.app .natSucc (.bvar 0))) (.bvar 1)) .nat

theorem natDivLoopType.apply (hlc : le.ClosedN)
    (hgo : env.HasType U [] go (natDivLoopType le))
    (hy : env.HasType U [] (.natLit y) .nat)
    (hp : env.HasType U [] py (natLeExpr le 1 y))
    (hf : env.HasType U [] (.natLit fuel) .nat)
    (ha : env.HasType U [] (.natLit a) .nat)
    (hbound : env.HasType U [] pa (natLeExpr le (a + 1) fuel)) :
    env.HasType U [] (natDivLoopExpr go y py fuel a pa) .nat := by
  have hg₁ := hgo.app hy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
    VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd,
    VExpr.natLit, VExpr.natSucc, VExpr.natZero, VExpr.nat] at hg₁
  have hg₂ := hg₁.app hp
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ, VExpr.instVar_lower,
    VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd] at hg₂
  have hg₃ := hg₂.app hf
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_zero, VExpr.instVar_lower,
    VExpr.lift, Nat.reduceAdd] at hg₃
  have hg₄ := hg₃.app ha
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_zero,
    VExpr.inst_lift] at hg₄
  exact hg₄.app hbound

/-- The loop's result is independent of its positivity and fuel-bound proofs. -/
theorem natDivLoopExpr.proofIrrel (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hle : env.HasType U [] le (.forallE .nat (.forallE .nat (.sort .zero))))
    (hgo : env.HasType U [] go (natDivLoopType le))
    (hpy : env.HasType U [] py (natLeExpr le 1 y))
    (hpy' : env.HasType U [] py' (natLeExpr le 1 y))
    (hpa : env.HasType U [] pa (natLeExpr le (a + 1) fuel))
    (hpa' : env.HasType U [] pa' (natLeExpr le (a + 1) fuel)) :
    env.IsDefEq U [] (natDivLoopExpr go y py fuel a pa)
      (natDivLoopExpr go y py' fuel a pa') .nat := by
  have hlc := hle.closedN henv trivial
  have hy := hp.natLit_type (U := U) (Γ := []) hn y
  have hf := hp.natLit_type (U := U) (Γ := []) hn fuel
  have ha := hp.natLit_type (U := U) (Γ := []) hn a
  have hP₁ := hle.app (hp.natLit_type hn 1)
  have hP₂ := hle.app (hp.natLit_type hn (a + 1))
  simp only [VExpr.inst, VExpr.nat] at hP₁ hP₂
  have hpyEq := IsDefEq.proofIrrel (hP₁.app hy) hpy hpy'
  have hpaEq := IsDefEq.proofIrrel (hP₂.app hf) hpa hpa'
  have hg₁ := hgo.app hy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
    VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd,
    VExpr.natLit, VExpr.natSucc, VExpr.natZero, VExpr.nat] at hg₁
  have eq₂ := hg₁.appDF hpyEq
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_lower, VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd] at eq₂
  have eq₃ := eq₂.appDF hf
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_zero, VExpr.instVar_lower, VExpr.lift, Nat.reduceAdd] at eq₃
  have eq₄ := eq₃.appDF ha
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_zero,
    VExpr.inst_lift] at eq₄
  exact eq₄.appDF hpaEq

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

/-- The entry equations extracted independently of the division loop checks. -/
structure NatDivEntrySpec (env : VEnv) (f go le : VExpr) : Prop where
  zero : ∀ a, env.IsDefEq 0 []
    (.app (.app f (.natLit a)) .natZero) .natZero .nat
  start : ∀ a y, 0 < y →
    ∃ py pa, env.HasType 0 [] py (natLeExpr le 1 y) ∧
      env.HasType 0 [] pa (natLeExpr le (a + 1) (a + 1)) ∧
      env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit y))
        (natDivLoopExpr go y py (a + 1) a pa) .nat

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

theorem NatDivSpec.ofEntry (h : NatDivEntrySpec env f go le)
    (hloop : NatDivLoopSpec env go le) : NatDivSpec env f go le :=
  ⟨hloop, h.zero, h.start⟩

theorem NatDivSpec.eval (h : NatDivSpec env f go le)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (a y : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit y)) (.natLit (a / y)) .nat := by
  cases y with
  | zero => simpa only [Nat.div_zero, VExpr.natLit] using h.zero a
  | succ y =>
    obtain ⟨py, pa, hpos, hbound, hstart⟩ := h.start a (y + 1) (Nat.succ_pos _)
    exact hstart.trans <| h.loop.eval hp hn (Nat.succ_pos _) hpos (Nat.lt_succ_self _) hbound

/-- The modulo loop has the same dependent arguments as the division loop,
but returns the remaining dividend when subtraction stops. -/
structure NatModLoopSpec (env : VEnv) (go le : VExpr) : Prop where
  step : ∀ y fuel a hy ha, 0 < y → a < fuel + 1 → y ≤ a →
    env.HasType 0 [] hy (natLeExpr le 1 y) →
    env.HasType 0 [] ha (natLeExpr le (a + 1) (fuel + 1)) →
    ∃ ha', env.HasType 0 [] ha' (natLeExpr le (a - y + 1) fuel) ∧
      env.IsDefEq 0 [] (natDivLoopExpr go y hy (fuel + 1) a ha)
        (natDivLoopExpr go y hy fuel (a - y) ha') .nat
  stop : ∀ y fuel a hy ha, 0 < y → a < fuel + 1 → a < y →
    env.HasType 0 [] hy (natLeExpr le 1 y) →
    env.HasType 0 [] ha (natLeExpr le (a + 1) (fuel + 1)) →
    env.IsDefEq 0 [] (natDivLoopExpr go y hy (fuel + 1) a ha) (.natLit a) .nat

theorem NatModLoopSpec.eval (h : NatModLoopSpec env go le)
    (hy : 0 < y) (hpos : env.HasType 0 [] py (natLeExpr le 1 y)) (ha : a < fuel)
    (hbound : env.HasType 0 [] pa (natLeExpr le (a + 1) fuel)) :
    env.IsDefEq 0 [] (natDivLoopExpr go y py fuel a pa) (.natLit (a % y)) .nat := by
  induction fuel generalizing a pa with
  | zero => omega
  | succ fuel ih =>
    by_cases hle : y ≤ a
    · obtain ⟨pa', hbound', hstep⟩ := h.step y fuel a py pa hy ha hle hpos hbound
      have ha' : a - y < fuel := by omega
      rw [Nat.mod_eq_sub_mod hle]
      exact hstep.trans (ih ha' hbound')
    · have hlt : a < y := Nat.lt_of_not_ge hle
      simpa only [Nat.mod_eq_of_lt hlt] using
        h.stop y fuel a py pa hy ha hlt hpos hbound

/-- The entry equations after evaluating both checked conditionals. -/
structure NatModSpec (env : VEnv) (f go le : VExpr) : Prop where
  loop : NatModLoopSpec env go le
  zero : ∀ y, env.IsDefEq 0 [] (.app (.app f .natZero) (.natLit y)) .natZero .nat
  stop : ∀ a y, y = 0 ∨ a + 1 < y →
    env.IsDefEq 0 [] (.app (.app f (.natLit (a + 1))) (.natLit y)) (.natLit (a + 1)) .nat
  start : ∀ a y, 0 < y → y ≤ a + 1 →
    ∃ py pa, env.HasType 0 [] py (natLeExpr le 1 y) ∧
      env.HasType 0 [] pa (natLeExpr le (a + 2) (a + 2)) ∧
      env.IsDefEq 0 [] (.app (.app f (.natLit (a + 1))) (.natLit y))
        (natDivLoopExpr go y py (a + 2) (a + 1) pa) .nat

theorem NatModSpec.eval (h : NatModSpec env f go le) (a y : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit y)) (.natLit (a % y)) .nat := by
  cases a with
  | zero => simpa only [Nat.zero_mod, VExpr.natLit] using h.zero y
  | succ a =>
    by_cases hy : y = 0
    · subst y
      simpa only [Nat.mod_zero] using h.stop a 0 (.inl rfl)
    · by_cases hle : y ≤ a + 1
      · obtain ⟨py, pa, hpos, hbound, hstart⟩ := h.start a y (Nat.pos_of_ne_zero hy) hle
        exact hstart.trans <| h.loop.eval (Nat.pos_of_ne_zero hy) hpos
          (Nat.lt_succ_self _) hbound
      · have hlt : a + 1 < y := Nat.lt_of_not_ge hle
        simpa only [Nat.mod_eq_of_lt hlt] using h.stop a y (.inr hlt)

/-- The successor entry equation is checked separately from the zero equation
and the loop equation. -/
structure NatModEntrySpec (env : VEnv) (f go le : VExpr) : Prop where
  stop : ∀ a y, y = 0 ∨ a + 1 < y →
    env.IsDefEq 0 [] (.app (.app f (.natLit (a + 1))) (.natLit y)) (.natLit (a + 1)) .nat
  start : ∀ a y, 0 < y → y ≤ a + 1 →
    ∃ py pa, env.HasType 0 [] py (natLeExpr le 1 y) ∧
      env.HasType 0 [] pa (natLeExpr le (a + 2) (a + 2)) ∧
      env.IsDefEq 0 [] (.app (.app f (.natLit (a + 1))) (.natLit y))
        (natDivLoopExpr go y py (a + 2) (a + 1) pa) .nat

theorem NatModSpec.ofEntry (h : NatModEntrySpec env f go le)
    (hloop : NatModLoopSpec env go le)
    (hzero : ∀ y, env.IsDefEq 0 [] (.app (.app f .natZero) (.natLit y)) .natZero .nat) :
    NatModSpec env f go le := ⟨hloop, hzero, h.stop, h.start⟩

/-- Literal equations for the original GCD candidate. Equations about only the
body returned by `unfoldNatWellFounded` do not supply this specification. -/
structure NatGcdSpec (env : VEnv) (f : VExpr) : Prop where
  zero : ∀ b, env.IsDefEq 0 []
    (.app (.app f .natZero) (.natLit b)) (.natLit b) .nat
  succ : ∀ a b, env.IsDefEq 0 []
    (.app (.app f (.natLit (a + 1))) (.natLit b))
    (.app (.app f (.app (.app (.const ``Nat.mod []) (.natLit b)) (.natLit (a + 1))))
      (.natLit (a + 1))) .nat

theorem NatGcdSpec.mono (h : NatGcdSpec env f) (hle : env ≤ env') :
    NatGcdSpec env' f := ⟨fun b => (h.zero b).mono hle, fun a b => (h.succ a b).mono hle⟩

theorem NatGcdSpec.eval (h : NatGcdSpec env f)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hf : env.HasType 0 [] f (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.mod []) (.natLit a)) (.natLit b)) (.natLit (a % b)) .nat)
    (a b : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit a)) (.natLit b)) (.natLit (Nat.gcd a b)) .nat := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    cases a with
    | zero => simpa only [Nat.gcd_zero_left, VExpr.natLit] using h.zero b
    | succ a =>
      rw [Nat.gcd_succ]
      exact (h.succ a b).trans <|
        (((hf.appDF (heval b (a + 1))).appDF (hp.natLit_type hn (a + 1))).trans
          (ih _ (Nat.mod_lt b (Nat.succ_pos a)) (a + 1)))

theorem NatGcdSpec.reflects (h : NatGcdSpec env f)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hf : env.HasType 0 [] f (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.mod []) (.natLit a)) (.natLit b)) (.natLit (a % b)) .nat)
    (hle : env ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const fc []) f (.forallE .nat (.forallE .nat .nat))) :
    env'.ReflectsNatNatNat fc Nat.gcd := by
  intro _ a b
  have ha := (hp.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (hp.natLit_type (U := 0) (Γ := []) hn b).mono hle
  exact ((hdef.appDF ha |>.appDF hb).trans ((h.eval hp hn hf heval a b).mono hle)).toU

/-- Literal bitwise equations after evaluating the conditionals and recursive
arguments. These must hold for the original candidate, not only its unfolded body. -/
structure NatBitwiseSpec (env : VEnv) (f : VExpr) (g : Bool → Bool → Bool) : Prop where
  zero_left : ∀ m, env.IsDefEq 0 []
    (.app (.app f .natZero) (.natLit m)) (.natLit (if g false true then m else 0)) .nat
  zero_right : ∀ n, env.IsDefEq 0 []
    (.app (.app f (.natLit n)) .natZero) (.natLit (if g true false then n else 0)) .nat
  step : ∀ n m, 0 < n → 0 < m →
    let r := .app (.app f (.natLit (n / 2))) (.natLit (m / 2))
    let double := .app (.app (.const ``Nat.add []) r) r
    env.IsDefEq 0 [] (.app (.app f (.natLit n)) (.natLit m))
      (if g (decide (n % 2 = 1)) (decide (m % 2 = 1)) then
        .app (.app (.const ``Nat.add []) double) (.natLit 1) else double) .nat

theorem NatBitwiseSpec.eval (h : NatBitwiseSpec env f g)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hadd : env.HasType 0 [] (.const ``Nat.add []) (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.add []) (.natLit a)) (.natLit b)) (.natLit (a + b)) .nat)
    (n m : Nat) :
    env.IsDefEq 0 [] (.app (.app f (.natLit n)) (.natLit m))
      (.natLit (Nat.bitwise g n m)) .nat := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    cases n with
    | zero =>
      rw [Nat.bitwise]
      simpa only [if_true, VExpr.natLit] using h.zero_left m
    | succ n =>
      cases m with
      | zero =>
        rw [Nat.bitwise]
        simpa only [Nat.succ_ne_zero, if_false, if_true, VExpr.natLit] using
          h.zero_right (n + 1)
      | succ m =>
        have hrec := ih _ (Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)) ((m + 1) / 2)
        have hdouble := ((hadd.appDF hrec).appDF hrec).trans (heval _ _)
        have hs := h.step (n + 1) (m + 1) (Nat.succ_pos _) (Nat.succ_pos _)
        dsimp only at hs
        rw [Nat.bitwise]
        simp only [Nat.succ_ne_zero, if_false]
        split at hs <;> rename_i hg
        · simp only [hg, if_true]
          exact hs.trans <| ((hadd.appDF hdouble).appDF (hp.natLit_type hn 1)).trans (heval _ _)
        · simp only [hg]
          exact hs.trans hdouble

theorem NatBitwiseSpec.reflects (h : NatBitwiseSpec env f g)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hadd : env.HasType 0 [] (.const ``Nat.add []) (.forallE .nat (.forallE .nat .nat)))
    (heval : ∀ a b, env.IsDefEq 0 []
      (.app (.app (.const ``Nat.add []) (.natLit a)) (.natLit b)) (.natLit (a + b)) .nat)
    (hle : env ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const fc []) f (.forallE .nat (.forallE .nat .nat))) :
    env'.ReflectsNatNatNat fc (Nat.bitwise g) := by
  intro _ n m
  have hn' := (hp.natLit_type (U := 0) (Γ := []) hn n).mono hle
  have hm' := (hp.natLit_type (U := 0) (Γ := []) hn m).mono hle
  exact ((hdef.appDF hn' |>.appDF hm').trans ((h.eval hp hn hadd heval n m).mono hle)).toU

end VEnv

private theorem TrExprS.weakBV_closed (henv : env.Ordered)
    (W : VLCtx.BVLift [] Δ dn 0 n 0) (h : TrExprS env Us [] e e') :
    TrExprS env Us Δ e (e'.liftN n) := by
  have h' := h.weakBV henv W
  rwa [Expr.liftLooseBVars_eq_self (s := 0) h.closed.looseBVarRange_le] at h'

private theorem TrExprS.underLams_closed (henv : env.Ordered) (hc : e'.ClosedN)
    (he : TrExprS env Us [] e e') (Γ : List VExpr) :
    TrExprS env Us (Γ.map fun A => (none, .vlam A)) e e' := by
  induction Γ with
  | nil => exact he
  | cons A Γ ih =>
    have h := ih.weakBV henv (.skip (.vlam A) .refl)
    rw [Expr.liftLooseBVars_eq_self (s := 0) he.closed.looseBVarRange_le] at h
    simpa only [hc.liftN_eq (Nat.zero_le _)] using h

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

def Reflection.iteResultType : VExpr :=
  .forallE (.sort (.succ .zero)) <| .forallE (.bvar 0) <|
    .forallE (.bvar 1) (.bvar 2)

def Reflection.iteType (r : VExpr) : VExpr :=
  .forallE (.sort .zero) <| .forallE .bool <|
    .forallE (.app (.app r (.bvar 1)) (.bvar 0)) iteResultType

private theorem tr_iteResultType {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    TrExprS env Us Δ q(∀ α : Type, α → α → α) Reflection.iteResultType := by
  let Δ₁ : VLCtx := (none, .vlam (.sort (.succ .zero))) :: Δ
  let Δ₂ : VLCtx := (none, .vlam (.bvar 0)) :: Δ₁
  let Δ₃ : VLCtx := (none, .vlam (.bvar 1)) :: Δ₂
  have sortType : env.IsType Us.length Δ.toCtx (.sort (.succ .zero)) := ⟨_, .sort trivial⟩
  have hα₁ : env.HasType Us.length Δ₁.toCtx (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hα₂ : env.HasType Us.length Δ₂.toCtx (.bvar 1) (.sort (.succ .zero)) :=
    .bvar (.succ .zero)
  have hα₃ : env.HasType Us.length Δ₃.toCtx (.bvar 2) (.sort (.succ .zero)) :=
    .bvar (.succ (.succ .zero))
  exact .forallE sortType (VEnv.IsType.forallE ⟨_, hα₁⟩
    (VEnv.IsType.forallE ⟨_, hα₂⟩ ⟨_, hα₃⟩)) (.sort rfl)
    (.forallE ⟨_, hα₁⟩ (VEnv.IsType.forallE ⟨_, hα₂⟩ ⟨_, hα₃⟩) (.bvar rfl)
      (.forallE ⟨_, hα₂⟩ ⟨_, hα₃⟩ (.bvar rfl) (.bvar rfl)))

def Reflection.iteBranch (b : Bool) : VExpr :=
  .lam (.sort (.succ .zero)) <| .lam (.bvar 0) <|
    .lam (.bvar 1) (.bvar (if b then 1 else 0))

private theorem tr_inContext {c : VContext}
    (he : TrExprS c.venv c.lparams [] e e') (hclosed : e'.ClosedN) :
    c.TrExprS e e' := by
  simpa only [hclosed.liftN_eq (Nat.zero_le _)] using
    he.weakFV c.Ewf.ordered (.from_nil c.mlctx.noBV) c.Δwf

private theorem tr_iteBranch {env : VEnv} {Us : List Name} {Δ : VLCtx} (b : Bool) :
    TrExprS env Us Δ (Reflection.iteBranchExpr b) (Reflection.iteBranch b) ∧
    env.HasType Us.length Δ.toCtx (Reflection.iteBranch b) Reflection.iteResultType := by
  let Δ₁ : VLCtx := (none, .vlam (.sort (.succ .zero))) :: Δ
  let Δ₂ : VLCtx := (none, .vlam (.bvar 0)) :: Δ₁
  let Δ₃ : VLCtx := (none, .vlam (.bvar 1)) :: Δ₂
  have hSort : env.HasType Us.length Δ.toCtx (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) := .sort trivial
  have hα₁ : env.HasType Us.length Δ₁.toCtx (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hα₂ : env.HasType Us.length Δ₂.toCtx (.bvar 1) (.sort (.succ .zero)) :=
    .bvar (.succ .zero)
  have ha : env.HasType Us.length Δ₃.toCtx (.bvar 1) (.bvar 2) := .bvar (.succ .zero)
  have he : env.HasType Us.length Δ₃.toCtx (.bvar 0) (.bvar 2) := .bvar .zero
  cases b <;> refine ⟨.lam ⟨_, hSort⟩ (.sort rfl)
    (.lam ⟨_, hα₁⟩ (.bvar rfl) (.lam ⟨_, hα₂⟩ (.bvar rfl) (.bvar rfl))), ?_⟩
  · exact .lam hSort (.lam hα₁ (.lam hα₂ he))
  · exact .lam hSort (.lam hα₁ (.lam hα₂ ha))

private theorem iteResultType_isType {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.IsType U Γ Reflection.iteResultType := by
  have hSort : env.HasType U Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort trivial
  have hα₁ : env.HasType U ((.sort (.succ .zero)) :: Γ) (.bvar 0)
      (.sort (.succ .zero)) := .bvar .zero
  have hα₂ : env.HasType U ((.bvar 0) :: (.sort (.succ .zero)) :: Γ) (.bvar 1)
      (.sort (.succ .zero)) := .bvar (.succ .zero)
  have hα₃ : env.HasType U ((.bvar 1) :: (.bvar 0) :: (.sort (.succ .zero)) :: Γ) (.bvar 2)
      (.sort (.succ .zero)) := .bvar (.succ (.succ .zero))
  exact ⟨_, .forallE hSort (.forallE hα₁ (.forallE hα₂ hα₃))⟩

private def iteTypeExpr (r : Reflection) : Expr :=
  .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)

private theorem tr_iteTypeExpr {c : VContext} {r : Reflection} {r' : VExpr}
    (hc : c.vlctx = []) (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hb : c.venv.contains ``Bool) :
    c.TrExprS (iteTypeExpr r) (Reflection.iteType r') := by
  have hrc := hrt.closedN c.Ewf.ordered trivial
  have ht := TrExprS.boolTrue (Us := c.lparams) (Δ := []) c.hasPrimitives hb
  obtain ⟨uBool, hBool⟩ := ht.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciBool, _, huBool⟩ := hBool.const_inv c.Ewf.ordered trivial
  have trProp {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Prop) (.sort .zero) := .sort rfl
  have trBool {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Bool) .bool := .const hciBool rfl huBool
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have boolType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .bool :=
    ⟨uBool, hBool.weak0 c.Ewf.ordered⟩
  let Δ₂ : VLCtx := [(none, .vlam .bool), (none, .vlam (.sort .zero))]
  let A := VExpr.app (.app r' (.bvar 1)) (.bvar 0)
  have hr₂ := hr.underLams_closed c.Ewf.ordered hrc [.bool, .sort .zero]
  have hrt₂ : c.venv.HasType c.lparams.length Δ₂.toCtx r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) := hrt.weak0 c.Ewf.ordered
  have hp₂ : c.venv.HasType c.lparams.length Δ₂.toCtx (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have hb₂ : c.venv.HasType c.lparams.length Δ₂.toCtx (.bvar 0) .bool := .bvar .zero
  have tp₂ : TrExprS c.venv c.lparams Δ₂ (.bvar 1) (.bvar 1) := .bvar rfl
  have tb₂ : TrExprS c.venv c.lparams Δ₂ (.bvar 0) (.bvar 0) := .bvar rfl
  have tA := TrExprS.app (hrt₂.app hp₂) hb₂ (.app hrt₂ hp₂ hr₂ tp₂) tb₂
  have hA : c.venv.IsType c.lparams.length Δ₂.toCtx A := ⟨_, (hrt₂.app hp₂).app hb₂⟩
  simp only [VContext.TrExprS, hc]
  exact .forallE propType (boolType.forallE (hA.forallE iteResultType_isType)) trProp
    (.forallE boolType (hA.forallE iteResultType_isType) trBool
      (.forallE hA iteResultType_isType tA tr_iteResultType))

/-- Only the initial type check of `checkITE`, not its computation equations. -/
def Reflection.checkITETypes (r : Reflection) (fail : ∀ {α}, M α) : M Unit :=
  checkExprType r.ite (iteTypeExpr r) fail

theorem Reflection.checkITETypes.WF {c : VContext} (hc : c.vlctx = [])
    (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hi : r.ite.FVarsIn (· ∈ c.vlctx.fvars))
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hb : c.venv.contains ``Bool) :
    (r.checkITETypes fail).WF c s fun _ _ => ∃ i,
      c.TrExprS r.ite i ∧ c.HasType i (Reflection.iteType r') :=
  checkExprType.WF fail hfail hi (tr_iteTypeExpr hc hr hrt hb)

def Reflection.itePrefix (i p b H : VExpr) : VExpr := .app (.app (.app i p) b) H

private theorem tr_itePrefix {env : VEnv} {r' : VExpr}
    (hr : r'.ClosedN)
    (hi : env.HasType Us.length Δ.toCtx i' (Reflection.iteType r'))
    (hp : env.HasType Us.length Δ.toCtx p' (.sort .zero))
    (hb : env.HasType Us.length Δ.toCtx b' .bool)
    (hH : env.HasType Us.length Δ.toCtx H' (.app (.app r' p') b'))
    (ti : TrExprS env Us Δ i i') (tp : TrExprS env Us Δ p p')
    (tb : TrExprS env Us Δ b b') (tH : TrExprS env Us Δ H H') :
    TrExprS env Us Δ (mkApp3 i p b H) (Reflection.itePrefix i' p' b' H') ∧
    env.HasType Us.length Δ.toCtx (Reflection.itePrefix i' p' b' H')
      Reflection.iteResultType := by
  have hc : Reflection.iteResultType.ClosedN := by
    simp [Reflection.iteResultType, VExpr.ClosedN]
  have t₁ := TrExprS.app hi hp ti tp
  have h₁ := hi.app hp
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), hc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower, VExpr.bool] at h₁
  have t₂ := TrExprS.app h₁ hb t₁ tb
  have h₂ := h₁.app hb
  simp only [VExpr.inst, hr.instN_eq (Nat.zero_le _), hc.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, VExpr.inst_lift] at h₂
  exact ⟨.app h₂ hH t₂ tH, by simpa only [hc.instN_eq (Nat.zero_le _)] using h₂.app hH⟩

def Reflection.iteApp (i p b H A a e : VExpr) : VExpr :=
  .app (.app (.app (itePrefix i p b H) A) a) e

private theorem tr_iteApp {env : VEnv} {r' : VExpr}
    (hr : r'.ClosedN) (hAc : A'.ClosedN)
    (hi : env.HasType Us.length Δ.toCtx i' (Reflection.iteType r'))
    (hp : env.HasType Us.length Δ.toCtx p' (.sort .zero))
    (hb : env.HasType Us.length Δ.toCtx b' .bool)
    (hH : env.HasType Us.length Δ.toCtx H' (.app (.app r' p') b'))
    (hA : env.HasType Us.length Δ.toCtx A' (.sort (.succ .zero)))
    (ha : env.HasType Us.length Δ.toCtx a' A')
    (he : env.HasType Us.length Δ.toCtx e' A')
    (ti : TrExprS env Us Δ i i') (tp : TrExprS env Us Δ p p')
    (tb : TrExprS env Us Δ b b') (tH : TrExprS env Us Δ H H')
    (tA : TrExprS env Us Δ A A') (ta : TrExprS env Us Δ a a')
    (te : TrExprS env Us Δ e e') :
    TrExprS env Us Δ (mkApp6 i p b H A a e) (Reflection.iteApp i' p' b' H' A' a' e') ∧
      env.HasType Us.length Δ.toCtx (Reflection.iteApp i' p' b' H' A' a' e') A' := by
  obtain ⟨t₃, h₃⟩ := tr_itePrefix hr hi hp hb hH ti tp tb tH
  have t₄ := TrExprS.app h₃ hA t₃ tA
  have h₄ := h₃.app hA
  simp only [VExpr.inst, VExpr.instVar_zero,
    VExpr.instVar_succ, VExpr.lift, hAc.liftN_eq (Nat.zero_le _)] at h₄
  have t₅ := TrExprS.app h₄ ha t₄ ta
  have h₅ := h₄.app ha
  simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _)] at h₅
  exact ⟨.app h₅ he t₅ te, by simpa only [hAc.instN_eq (Nat.zero_le _)] using h₅.app he⟩

private def checkITEBranch (r : Reflection) (p : Expr) (b : Bool)
    (fail : ∀ {α}, M α) : M Unit :=
  withLocalDecl `H .default (mkApp2 r.type p (toExpr b)) fun H => do
    unless ← isDefEq (mkApp3 r.ite p (toExpr b) H) (Reflection.iteBranchExpr b) do fail

private theorem checkITEBranch.WF {c : VContext} {r' i' : VExpr}
    (r : Reflection) (b : Bool) (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (ti : TrExprS c.venv c.lparams [] r.ite i')
    (hi : c.venv.HasType c.lparams.length [] i' (Reflection.iteType r'))
    (tp : c.TrExprS p p') (hp : c.HasType p' (.sort .zero))
    (hb : c.venv.contains ``Bool) :
    (checkITEBranch r p b fail).WF c s fun _ _ =>
      c.venv.IsDefEq c.lparams.length ((.app (.app r' p') (.boolLit b)) :: c.vlctx.toCtx)
        (Reflection.itePrefix i' p'.lift (.boolLit b) (.bvar 0))
        (Reflection.iteBranch b) Reflection.iteResultType := by
  have hrc := hrt.closedN c.Ewf.ordered trivial
  have hic := hi.closedN c.Ewf.ordered trivial
  have tr : c.TrExprS r.type r' := tr_inContext hr hrc
  have hrΓ := hrt.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
  have tb := TrExprS.boolLit (Us := c.lparams) (Δ := c.vlctx) c.hasPrimitives hb b
  let A := VExpr.app (.app r' p') (.boolLit b)
  have tA := TrExprS.app (hrΓ.app hp) tb.2 (.app hrΓ hp tr tp) tb.1
  have hA : c.IsType A := ⟨_, (hrΓ.app hp).app tb.2⟩
  unfold checkITEBranch
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl tA hA (.rfl (s := s)) fun id cwf' s' _ _ => ?_
  let c' := c.withMLC (.vlam id `H (mkApp2 r.type p (toExpr b)) A .default c.mlctx)
  have W : VLCtx.FVLift c.vlctx c'.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tp₁ : c'.TrExprS p p'.lift := tp.weakFV c.Ewf.ordered W c'.Δwf
  have hp₁ : c'.HasType p'.lift (.sort .zero) := hp.weak c.Ewf.ordered
  have tH : c'.TrExprS (.fvar id) (.bvar 0) := .fvar (A := A.lift) (by
    simp [c', VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type])
  have hH : c'.HasType (.bvar 0) (.app (.app r' p'.lift) (.boolLit b)) := by
    have h : c'.HasType (.bvar 0) A.lift := .bvar .zero
    cases b <;> simpa only [A, VExpr.lift, VExpr.liftN, hrc.liftN_eq (Nat.zero_le _),
      VExpr.boolLit, VExpr.boolTrue, VExpr.boolFalse] using h
  have tb₁ := TrExprS.boolLit (Us := c.lparams) (Δ := c'.vlctx) c.hasPrimitives hb b
  have ti₁ : c'.TrExprS r.ite i' := tr_inContext ti hic
  have hleft := tr_itePrefix hrc (hi.weak0 c.Ewf.ordered) hp₁ tb₁.2 hH
    ti₁ tp₁ tb₁.1 tH
  have hright := tr_iteBranch (env := c.venv) (Us := c.lparams) (Δ := c'.vlctx) b
  refine (isDefEq.WF hleft.1 hright.1).bind fun b' _ _ heq => ?_
  cases b'
  · exact hfail.mono fun _ _ _ h => h.elim
  · exact .pure ((heq rfl).of_r c'.Ewf c'.Δwf.toCtx hright.2)

theorem Reflection.checkITE_eq (r : Reflection) (fail : ∀ {α}, M α) :
    r.checkITE fail = (do
      r.checkITETypes fail
      withLocalDecl `p .default q(Prop) fun p => do
        checkITEBranch r p true fail
        checkITEBranch r p false fail) := by
  have bindIf (p : Prop) [Decidable p] (x y : M Unit) (f : Unit → M Unit) :
      ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by
    split <;> rfl
  simp only [checkITE, checkITETypes, checkExprType, iteTypeExpr, checkITEBranch,
    bind_assoc, bindIf, pure_bind]
  rfl

/-- The two open polymorphic branch equations checked by `Reflection.checkITE`. -/
structure Reflection.ITESpec (env : VEnv) (U : Nat) (r i : VExpr) : Prop where
  true_eq : env.IsDefEq U [.app (.app r (.bvar 0)) .boolTrue, .sort .zero]
    (itePrefix i (.bvar 1) .boolTrue (.bvar 0)) (iteBranch true) iteResultType
  false_eq : env.IsDefEq U [.app (.app r (.bvar 0)) .boolFalse, .sort .zero]
    (itePrefix i (.bvar 1) .boolFalse (.bvar 0)) (iteBranch false) iteResultType

theorem Reflection.ITESpec.apply {env : VEnv} (h : ITESpec env U r i)
    (henv : env.Ordered) (hr : r.ClosedN) (hi : i.ClosedN) (b : Bool)
    (hp : env.HasType U [] p (.sort .zero))
    (hH : env.HasType U [] H (.app (.app r p) (.boolLit b))) :
    env.IsDefEq U [] (itePrefix i p (.boolLit b) H) (iteBranch b) iteResultType := by
  have ht : iteResultType.ClosedN := by simp [iteResultType, VExpr.ClosedN]
  have hs : (iteBranch b).ClosedN := by cases b <;> simp [iteBranch, VExpr.ClosedN]
  have eq : env.IsDefEq U [.app (.app r (.bvar 0)) (.boolLit b), .sort .zero]
      (itePrefix i (.bvar 1) (.boolLit b) (.bvar 0)) (iteBranch b) iteResultType := by
    cases b
    · exact h.false_eq
    · exact h.true_eq
  have eq := eq.instN henv hp (.succ .zero)
  simp only [itePrefix, VExpr.inst, VExpr.instVar_succ, VExpr.instVar_zero,
    VExpr.instVar_lower, hi.instN_eq (Nat.zero_le _), hr.instN_eq (Nat.zero_le _),
    hs.instN_eq (Nat.zero_le _), ht.instN_eq (Nat.zero_le _)] at eq
  cases b <;> simpa only [itePrefix, VExpr.inst, hi.instN_eq (Nat.zero_le _),
    hs.instN_eq (Nat.zero_le _), ht.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, VExpr.inst_lift, VExpr.boolLit, VExpr.boolFalse,
    VExpr.boolTrue] using eq.instN henv hH .zero

theorem Reflection.iteBranch.eval {env : VEnv} (henv : env.Ordered) (b : Bool)
    (hA : env.HasType U [] A (.sort (.succ .zero)))
    (ha : env.HasType U [] a A) (he : env.HasType U [] e A) :
    env.IsDefEq U [] (.app (.app (.app (iteBranch b) A) a) e)
      (if b then a else e) A := by
  have hAc := hA.closedN henv trivial
  have hac := ha.closedN henv trivial
  have hα₁ : env.HasType U [.sort (.succ .zero)] (.bvar 0)
      (.sort (.succ .zero)) := .bvar .zero
  have hα₂ : env.HasType U [.bvar 0, .sort (.succ .zero)] (.bvar 1)
      (.sort (.succ .zero)) := .bvar (.succ .zero)
  have hA₁ : env.HasType U [A] A (.sort (.succ .zero)) := hA.weak0 henv
  have ha₁ : env.HasType U [A] a A := ha.weak0 henv
  have hA₃ : env.HasType U [A, A] (.bvar 0) A := by
    have h : env.HasType U [A, A] (.bvar 0) A.lift := .bvar .zero
    simpa only [hAc.lift_eq] using h
  have ha₃ : env.HasType U [A, A] (.bvar 1) A := by
    have h : env.HasType U [A, A] (.bvar 1) A.lift.lift := .bvar (.succ .zero)
    simpa only [hAc.lift_eq] using h
  cases b
  · have hv : env.HasType U [.bvar 1, .bvar 0, .sort (.succ .zero)]
        (.bvar 0) (.bvar 2) := .bvar .zero
    have h₁ := VEnv.IsDefEq.beta (VEnv.HasType.lam hα₁ (.lam hα₂ hv)) hA
    simp only [VExpr.inst, VExpr.instVar_zero, VExpr.instVar_lower,
      VExpr.instVar_succ, VExpr.lift, hAc.liftN_eq (Nat.zero_le _)] at h₁
    have h₂ := VEnv.IsDefEq.beta (VEnv.HasType.lam hA₁ hA₃) ha
    simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _),
      VExpr.instVar_lower] at h₂
    have hv₁ : env.HasType U [A] (.bvar 0) A := by
      have h : env.HasType U [A] (.bvar 0) A.lift := .bvar .zero
      simpa only [hAc.lift_eq] using h
    have h₃ := VEnv.IsDefEq.beta hv₁ he
    have h₁a := h₁.appDF ha
    simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _)] at h₁a
    have h₁ae := h₁a.appDF he
    have h₂e := h₂.appDF he
    simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _), VExpr.instVar_zero]
      at h₁ae h₂e h₃
    simpa only [iteBranch, Bool.false_eq_true, if_false, VExpr.inst,
      hAc.instN_eq (Nat.zero_le _), VExpr.instVar_zero] using
      h₁ae.trans (h₂e.trans h₃)
  · have hv : env.HasType U [.bvar 1, .bvar 0, .sort (.succ .zero)]
        (.bvar 1) (.bvar 2) := .bvar (.succ .zero)
    have h₁ := VEnv.IsDefEq.beta (VEnv.HasType.lam hα₁ (.lam hα₂ hv)) hA
    simp only [VExpr.inst, VExpr.instVar_zero, VExpr.instVar_lower,
      VExpr.instVar_succ, VExpr.lift, hAc.liftN_eq (Nat.zero_le _)] at h₁
    have h₂ := VEnv.IsDefEq.beta (VEnv.HasType.lam hA₁ ha₃) ha
    simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _),
      VExpr.instVar_zero, VExpr.instVar_succ, hac.lift_eq] at h₂
    have h₃ := VEnv.IsDefEq.beta ha₁ he
    have h₁a := h₁.appDF ha
    simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _)] at h₁a
    have h₁ae := h₁a.appDF he
    have h₂e := h₂.appDF he
    simp only [hAc.instN_eq (Nat.zero_le _), hac.instN_eq (Nat.zero_le _)]
      at h₁ae h₂e h₃
    simpa only [iteBranch, if_true, VExpr.inst, hAc.instN_eq (Nat.zero_le _),
      hac.instN_eq (Nat.zero_le _), hac.lift_eq] using
      h₁ae.trans (h₂e.trans h₃)

/-- Evaluate the polymorphic selector, retaining both the carrier's universe
bound and the typing of its dependent reflection witness. -/
theorem Reflection.ITESpec.eval {env : VEnv} (h : ITESpec env U r i)
    (henv : env.Ordered)
    (hr : env.HasType U [] r (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hi : env.HasType U [] i (iteType r)) (b : Bool)
    (hp : env.HasType U [] p (.sort .zero))
    (hb : env.IsDefEq U [] value (.boolLit b) .bool)
    (hH : env.HasType U [] H (.app (.app r p) value))
    (hA : env.HasType U [] A (.sort (.succ .zero)))
    (ha : env.HasType U [] a A) (he : env.HasType U [] e A) :
    env.IsDefEq U [] (.app (.app (.app (itePrefix i p value H) A) a) e)
      (if b then a else e) A := by
  have hrc := hr.closedN henv trivial
  have hic := hi.closedN henv trivial
  have hAc := hA.closedN henv trivial
  have htc : iteResultType.ClosedN := by simp [iteResultType, VExpr.ClosedN]
  have hH' := ((hr.app hp).appDF hb).defeqDF hH
  have h₁ := hi.app hp
  simp only [VExpr.inst, hrc.instN_eq (Nat.zero_le _), htc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower, VExpr.bool] at h₁
  have h₂ := h₁.appDF hb
  simp only [VExpr.inst, hrc.instN_eq (Nat.zero_le _), htc.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, VExpr.inst_lift] at h₂
  have h₃ := h₂.appDF hH
  simp only [htc.instN_eq (Nat.zero_le _)] at h₃
  have h₄ := (h₃.trans (h.apply henv hrc hic b hp hH')).appDF hA
  simp only [VExpr.inst, VExpr.instVar_zero, VExpr.instVar_succ,
    VExpr.lift, hAc.liftN_eq (Nat.zero_le _)] at h₄
  have h₅ := h₄.appDF ha
  simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _)] at h₅
  have h₆ := h₅.appDF he
  simp only [hAc.instN_eq (Nat.zero_le _)] at h₆
  exact h₆.trans (iteBranch.eval henv b hA ha he)

theorem Reflection.checkITE.WF {c : VContext} (hc : c.vlctx = [])
    (r : Reflection) (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hi : r.ite.FVarsIn (· ∈ c.vlctx.fvars))
    (hr : TrExprS c.venv c.lparams [] r.type r')
    (hrt : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hb : c.venv.contains ``Bool) :
    (r.checkITE fail).WF c s fun _ _ => ∃ i,
      c.TrExprS r.ite i ∧ c.HasType i (Reflection.iteType r') ∧
      Reflection.ITESpec c.venv c.lparams.length r' i := by
  rw [Reflection.checkITE_eq]
  refine (Reflection.checkITETypes.WF hc r fail hfail hi hr hrt hb).bind
    fun _ _ _ ⟨i, ti, hit⟩ => ?_
  have ti₀ : TrExprS c.venv c.lparams [] r.ite i := by
    simpa only [VContext.TrExprS, hc] using ti
  have hi₀ : c.venv.HasType c.lparams.length [] i (Reflection.iteType r') := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hit
  have propType : c.IsType (.sort .zero) := ⟨_, .sort trivial⟩
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl (c := c) (m := c.mlctx) (.sort rfl) propType .rfl
    fun pid pwf sp _ _ => ?_
  let cp := c.withMLC (.vlam pid `p q(Prop) (.sort .zero) .default c.mlctx) (wf := pwf)
  have tp : cp.TrExprS (.fvar pid) (.bvar 0) := .fvar (A := .sort .zero) (by
    simp [cp, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN])
  have hp : cp.HasType (.bvar 0) (.sort .zero) := .bvar .zero
  refine (checkITEBranch.WF (c := cp) r true fail hfail hr hrt ti₀ hi₀ tp hp hb).bind
    fun _ _ _ ht => ?_
  exact (checkITEBranch.WF (c := cp) r false fail hfail hr hrt ti₀ hi₀ tp hp hb).mono
    fun _ _ _ hf => by
      refine ⟨i, ti, hit, ?_, ?_⟩
      · simpa only [cp, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
          VLCtx.toCtx, VExpr.lift, VExpr.liftN, liftVar_base, VExpr.boolLit] using ht
      · simpa only [cp, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
          VLCtx.toCtx, VExpr.lift, VExpr.liftN, liftVar_base, VExpr.boolLit] using hf

/-- A checked polymorphic selector, including its reflection-family translation. -/
def Reflection.ITEChecked (c : VContext) (r : Reflection) : Prop :=
  ∃ r' i, c.TrExprS r.type r' ∧
    c.HasType r' (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) ∧
    c.TrExprS r.ite i ∧ c.HasType i (iteType r') ∧
    ITESpec c.venv c.lparams.length r' i

structure Reflection.ITEInstance (env : VEnv) (U : Nat) (p b H : VExpr) where
  r : VExpr
  i : VExpr
  r_type : env.HasType U [] r (.forallE (.sort .zero) (.forallE .bool (.sort .zero)))
  i_type : env.HasType U [] i (iteType r)
  prop_type : env.HasType U [] p (.sort .zero)
  bool_type : env.HasType U [] b .bool
  proof_type : env.HasType U [] H (.app (.app r p) b)
  equations : ITESpec env U r i

theorem Reflection.ITEInstance.eval {env : VEnv} (v : ITEInstance env U p value H)
    (henv : env.Ordered) (b : Bool)
    (hb : env.IsDefEq U [] value (.boolLit b) .bool)
    (hA : env.HasType U [] A (.sort (.succ .zero)))
    (ha : env.HasType U [] a A) (he : env.HasType U [] e A) :
    env.IsDefEq U [] (iteApp v.i p value H A a e) (if b then a else e) A :=
  v.equations.eval henv v.r_type v.i_type b v.prop_type hb v.proof_type hA ha he

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

private theorem tr_boundApp_arg {env : VEnv} (henv : env.WF)
    (hA : env.IsType Us.length [] A) (hc : fn.Closed)
    (hbody : TrExprS env Us [(none, .vlam A)] (.app fn (.bvar 0)) body')
    (happ : TrExprS env Us [] (.app fn arg) app') :
    ∃ arg', TrExprS env Us [] arg arg' ∧ env.HasType Us.length [] arg' A := by
  let .app hfb hab tfb tab := hbody
  let .app hfa haa tfa taa := happ
  have hΔ : VLCtx.WF env Us.length [(none, .vlam A)] := ⟨trivial, nofun, hA⟩
  have tv : TrExprS env Us [(none, .vlam A)] (.bvar 0) (.bvar 0) := .bvar rfl
  cases TrExprS.unique (e := .bvar 0) trivial tab tv
  have habA := hab.uniqU henv hΔ.toCtx (.bvar .zero)
  have tfa₁ := tfa.weakBV henv.ordered (.skip (.vlam A) .refl)
  rw [Expr.liftLooseBVars_eq_self (s := 0) hc.looseBVarRange_le] at tfa₁
  have hfun := (hfb.defeqU_l henv hΔ.toCtx (tfb.uniq henv (.refl henv.ordered hΔ) tfa₁)).uniqU
    henv hΔ.toCtx (hfa.weak henv.ordered)
  have ⟨⟨_, hdom⟩, _⟩ := hfun.forallE_inv henv hΔ.toCtx
  have heq := VEnv.IsDefEqU.trans henv hΔ.toCtx ⟨_, hdom.symm⟩ habA
  -- The compared domains are closed over the witness binder.
  have heq := (VEnv.IsDefEqU.weakN_iff henv hΔ.toCtx (.one (A := A))).1 heq
  exact ⟨_, taa, haa.defeqU_r henv trivial heq⟩

theorem Reflection.ite_witness {env : VEnv} (henv : env.WF) (r : Reflection)
    (hrc : r.type.Closed) (hdc : r.toDec.Closed)
    (tr : TrExprS env Us [] r.type r')
    (hr : env.HasType Us.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (ti : TrExprS env Us [] r.ite i')
    (tp : TrExprS env Us [] p p') (hp : env.HasType Us.length [] p' (.sort .zero))
    (tb : TrExprS env Us [] b b') (hb : env.HasType Us.length [] b' .bool)
    (te : TrExprS env Us [] (mkApp3 r.toDec p b proof) e') :
    ∃ proof', TrExprS env Us [] proof proof' ∧
      env.HasType Us.length [] proof' (.app (.app r' p') b') := by
  have hinst (e : Expr) (hc : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans hc.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (hc : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self hc.looseBVarRange_le
  simp only [Reflection.ite, Expr.lam0] at ti
  let .lam _ tProp tBody := ti
  cases tProp with
  | sort hu =>
    cases hu
    have tBody := tBody.inst henv.ordered hp tp
    simp only [Expr.instantiate1', hinst _ hrc, hinst _ hdc, hlift _ tp.closed,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false] at tBody
    have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
    let .lam _ tBool tBody := tBody
    cases tBool with
    | const _ hu _ =>
      cases hu
      have tBody := tBody.inst henv.ordered hb tb
      simp only [Expr.instantiate1', hinst _ hrc, hinst _ hdc, hinst _ tp.closed,
        hlift _ tb.closed, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        if_true, if_false] at tBody
      have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
      let .lam hA tA tBody := tBody
      let .lam _ tType tBody := tBody
      cases tType with
      | sort hu =>
        cases hu
        -- Instantiate the unused carrier binder to expose the decision proof.
        have tBody := tBody.inst henv.ordered (VEnv.HasType.sort (l := .zero) trivial)
          (TrExprS.sort (u := .zero) rfl)
        simp only [Expr.instantiate1', hinst _ hdc, hinst _ tp.closed, hinst _ tb.closed,
          Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false] at tBody
        have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [(none, .vlam _)] _ out
          from ⟨_, tBody⟩)
        let .app _ _ _ tDec := tBody
        have hfn : (mkApp2 r.toDec p b).Closed := ⟨⟨hdc, tp.closed⟩, tb.closed⟩
        obtain ⟨proof', tproof, hproof⟩ := tr_boundApp_arg henv hA hfn tDec te
        have tApp := TrExprS.app (hr.app hp) hb (.app hr hp tr tp) tb
        exact ⟨proof', tproof, hproof.defeqU_r henv trivial
          (tA.uniq henv (.refl henv.ordered (show VLCtx.WF env Us.length [] from trivial)) tApp)⟩

/-- Recover the carrier's `Type` bound from the checked selector. Merely knowing
that the carrier is some type would not justify this universe-specific check. -/
theorem Reflection.ite_carrier {env : VEnv} (henv : env.WF) (r : Reflection)
    (hrc : r.type.Closed) (hdc : r.toDec.Closed)
    (tr : TrExprS env Us [] r.type r')
    (hr : env.HasType Us.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (ti : TrExprS env Us [] r.ite i')
    (tp : TrExprS env Us [] p p') (hp : env.HasType Us.length [] p' (.sort .zero))
    (tb : TrExprS env Us [] b b') (hb : env.HasType Us.length [] b' .bool)
    (tH : TrExprS env Us [] H H')
    (hH : env.HasType Us.length [] H' (.app (.app r' p') b'))
    (tactual : TrExprS env Us [] (mkApp q(@_root_.ite.{1}) A) out) :
    ∃ A', TrExprS env Us [] A A' ∧ env.HasType Us.length [] A' (.sort (.succ .zero)) := by
  have hinst (e : Expr) (hc : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans hc.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (hc : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self hc.looseBVarRange_le
  simp only [Reflection.ite, Expr.lam0] at ti
  let .lam _ tProp tBody := ti
  cases tProp with
  | sort hu =>
    cases hu
    have tBody := tBody.inst henv.ordered hp tp
    simp only [Expr.instantiate1', hinst _ hrc, hinst _ hdc, hlift _ tp.closed,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false] at tBody
    have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
    let .lam _ tBool tBody := tBody
    cases tBool with
    | const _ hu _ =>
      cases hu
      have tBody := tBody.inst henv.ordered hb tb
      simp only [Expr.instantiate1', hinst _ hrc, hinst _ hdc, hinst _ tp.closed,
        hlift _ tb.closed, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        if_true, if_false] at tBody
      have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
      let .lam _ tA tBody := tBody
      have tRef := TrExprS.app (hr.app hp) hb (.app hr hp tr tp) tb
      have hH := hH.defeqU_r henv trivial (tRef.uniq henv (.refl henv.ordered
        (show VLCtx.WF env Us.length [] from trivial)) tA)
      have tBody := tBody.inst henv.ordered hH tH
      simp only [Expr.instantiate1', hinst _ hdc, hinst _ tp.closed, hinst _ tb.closed,
        hlift _ tH.closed, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
        if_true, if_false] at tBody
      have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
      let .lam hType tType tBody := tBody
      cases tType with
      | sort hu =>
        cases hu
        let .app _ _ tFn _ := tBody
        let .app _ _ tFn _ := tFn
        exact tr_boundApp_arg henv hType (by simp [Closed]) tFn tactual

private theorem Reflection.ite_beta_core (r : Reflection) (hd : r.toDec.Closed)
    (hp : p.Closed) (hb : b.Closed) (hH : H.Closed) (hA : A.Closed) :
    BetaReduce (mkApp4 r.ite p b H A)
      (mkApp3 q(@_root_.ite.{1}) A p (mkApp3 r.toDec p b H)) := by
  let body := mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
    (mkApp3 r.toDec (.bvar 3) (.bvar 2) (.bvar 1))
  have hbody : LambdaBodyN 4 r.ite body := .succ (.succ (.succ (.succ .zero)))
  have hinst (e : Expr) (hc : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans hc.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (hc : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self hc.looseBVarRange_le
  have eq : body.instantiateList [A, H, b, p] =
      mkApp3 q(@_root_.ite.{1}) A p (mkApp3 r.toDec p b H) := by
    simp only [body, Expr.instantiateList, Expr.instantiate1', hinst _ hd,
      hinst _ hH, hinst _ hb, hinst _ hA, hlift _ hp, hlift _ hb, hlift _ hH, hlift _ hA,
      Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
    rfl
  have hargs : ∀ x ∈ [p, b, H, A], x.Closed := by simp [hp, hb, hH, hA]
  exact BetaReduce.inst_reduce hargs [] hbody eq

private theorem Reflection.ite_beta (r : Reflection) (hd : r.toDec.Closed)
    (hp : p.Closed) (hb : b.Closed) (hH : H.Closed) (hA : A.Closed) :
    BetaReduce (mkApp6 r.ite p b H A a e)
      (mkApp5 q(@_root_.ite.{1}) A p (mkApp3 r.toDec p b H) a e) :=
  .app (.app (r.ite_beta_core hd hp hb hH hA))

theorem Reflection.natDITE_witness {env : VEnv} (henv : env.WF) (r : Reflection)
    (hrc : r.type.Closed) (hdc : r.toDec.Closed)
    (tr : TrExprS env Us [] r.type r')
    (hr : env.HasType Us.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (td : TrExprS env Us [] r.natDITE d')
    (tp : TrExprS env Us [] p p') (hp : env.HasType Us.length [] p' (.sort .zero))
    (tb : TrExprS env Us [] b b') (hb : env.HasType Us.length [] b' .bool)
    (te : TrExprS env Us [] (mkApp3 r.toDec p b proof) e') :
    ∃ proof', TrExprS env Us [] proof proof' ∧
      env.HasType Us.length [] proof' (.app (.app r' p') b') := by
  have hri (a : Expr) (k : Nat) : r.type.instantiate1' a k = r.type :=
    Expr.instantiate1'_eq_self (Nat.le_trans hrc.looseBVarRange_le (Nat.zero_le _))
  have hdi (a : Expr) (k : Nat) : r.toDec.instantiate1' a k = r.toDec :=
    Expr.instantiate1'_eq_self (Nat.le_trans hdc.looseBVarRange_le (Nat.zero_le _))
  have hpl (k : Nat) : p.liftLooseBVars' 0 k = p :=
    Expr.liftLooseBVars_eq_self tp.closed.looseBVarRange_le
  have hbl (k : Nat) : b.liftLooseBVars' 0 k = b :=
    Expr.liftLooseBVars_eq_self tb.closed.looseBVarRange_le
  simp only [Reflection.natDITE, Expr.lam0] at td
  let .lam _ tProp tBody := td
  cases tProp with
  | sort hu =>
    cases hu
    have tBody := tBody.inst henv.ordered hp tp
    simp only [Expr.instantiate1', hri, hdi, hpl, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] at tBody
    have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
    let .lam _ tBool tBody := tBody
    cases tBool with
    | const _ hu _ =>
      cases hu
      have tBody := tBody.inst henv.ordered hb tb
      have hpi (a : Expr) (k : Nat) : p.instantiate1' a k = p :=
        Expr.instantiate1'_eq_self (Nat.le_trans tp.closed.looseBVarRange_le (Nat.zero_le _))
      simp only [Expr.instantiate1', hri, hdi, hpi, hbl, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceEqDiff, if_true, if_false] at tBody
      have ⟨out, tBody⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, tBody⟩)
      let .lam hA tA tBody := tBody
      let .app _ _ _ tDec := tBody
      have hfn : (mkApp2 r.toDec p b).Closed := ⟨⟨hdc, tp.closed⟩, tb.closed⟩
      obtain ⟨proof', tproof, hproof⟩ := tr_boundApp_arg henv hA hfn tDec te
      have tApp := TrExprS.app (hr.app hp) hb (.app hr hp tr tp) tb
      exact ⟨proof', tproof, hproof.defeqU_r henv trivial
        (tA.uniq henv (.refl henv.ordered (show VLCtx.WF env Us.length [] from trivial)) tApp)⟩

def Reflection.natDITEApp (d p b H a f : VExpr) : VExpr :=
  .app (.app (.app (.app (.app d p) b) H) a) f

private theorem Reflection.natDITE_beta_core (r : Reflection) (hd : r.toDec.Closed)
    (hp : p.Closed) (hb : b.Closed) (hH : H.Closed) :
    BetaReduce (mkApp3 r.natDITE p b H)
      (mkApp2 q(@dite Nat) p (mkApp3 r.toDec p b H)) := by
  let body := mkApp2 q(@dite Nat) (.bvar 2)
    (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0))
  have hbody : LambdaBodyN 3 r.natDITE body := .succ (.succ (.succ .zero))
  have hinst (e : Expr) (he : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (he : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self he.looseBVarRange_le
  have eq : body.instantiateList [H, b, p] = mkApp2 q(@dite Nat) p (mkApp3 r.toDec p b H) := by
    simp only [body, Expr.instantiateList, Expr.instantiate1', hinst _ hd,
      hinst _ hH, hinst _ hb, hlift _ hp, hlift _ hb, hlift _ hH,
      Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
    rfl
  have hargs : ∀ x ∈ [p, b, H], x.Closed := by simp [hp, hb, hH]
  exact BetaReduce.inst_reduce hargs [] hbody eq

private theorem Reflection.natDITE_beta (r : Reflection) (hd : r.toDec.Closed)
    (hp : p.Closed) (hb : b.Closed) (hH : H.Closed) :
    BetaReduce (mkApp5 r.natDITE p b H a e)
      (mkApp4 q(@dite Nat) p (mkApp3 r.toDec p b H) a e) :=
  .app (.app (r.natDITE_beta_core hd hp hb hH))

private theorem tr_natDITEPrefix {env : VEnv} {r neg : VExpr}
    (hr : r.ClosedN) (hn : neg.ClosedN)
    (hd : env.HasType Us.length Δ.toCtx d' (Reflection.natDITEType r neg))
    (hp : env.HasType Us.length Δ.toCtx p' (.sort .zero))
    (hb : env.HasType Us.length Δ.toCtx b' .bool)
    (hH : env.HasType Us.length Δ.toCtx H' (.app (.app r p') b'))
    (td : TrExprS env Us Δ d d') (tp : TrExprS env Us Δ p p')
    (tb : TrExprS env Us Δ b b') (tH : TrExprS env Us Δ H H') :
    TrExprS env Us Δ (mkApp3 d p b H) (.app (.app (.app d' p') b') H') ∧
      env.HasType Us.length Δ.toCtx (.app (.app (.app d' p') b') H')
        (.forallE (.forallE p' .nat) (.forallE (.forallE (VExpr.app neg p').lift .nat) .nat)) := by
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
  refine ⟨td₃, ?_⟩
  simpa only [VExpr.lift, VExpr.liftN, hn.liftN_eq (Nat.zero_le _)] using hd₃

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
  have ⟨td₃, hd₃⟩ := tr_natDITEPrefix hr hn hd hp hb hH td tp tb tH
  have td₄ := TrExprS.app hd₃ ha td₃ ta
  have hd₄ := hd₃.app ha
  simp only [VExpr.inst, VExpr.inst_lift, VExpr.nat] at hd₄
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

/-- Evaluate the selector after its Boolean argument reduces, converting the
dependent witness along the same equality. -/
theorem Reflection.NatDITESpec.eval {env : VEnv} (h : NatDITESpec env U r neg d t f)
    (henv : env.Ordered)
    (hr : env.HasType U [] r (.forallE (.sort .zero) (.forallE .bool (.sort .zero))))
    (hn : neg.ClosedN) (hd : env.HasType U [] d (natDITEType r neg))
    (ht : t.ClosedN) (hf : f.ClosedN) (b : Bool)
    (hp : env.HasType U [] p (.sort .zero))
    (hb : env.IsDefEq U [] value (.boolLit b) .bool)
    (hH : env.HasType U [] H (.app (.app r p) value))
    (ha : env.HasType U [] a (.forallE p .nat))
    (he : env.HasType U [] e (.forallE (.app neg p) .nat)) :
    env.IsDefEq U [] (natDITEApp d p value H a e)
      (.app (if b then a else e) (.app (.app (if b then t else f) p) H)) .nat := by
  have hrc := hr.closedN henv trivial
  have hdc := hd.closedN henv trivial
  have hpEq := (hr.app hp).appDF hb
  have hH' : env.HasType U [] H (.app (.app r p) (.boolLit b)) := hpEq.defeqDF hH
  have hd₁ := hd.app hp
  simp only [VExpr.inst, hrc.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower, VExpr.nat, VExpr.bool] at hd₁
  have hd₂ := hd₁.appDF hb
  simp only [VExpr.inst, hrc.instN_eq (Nat.zero_le _), hn.instN_eq (Nat.zero_le _),
    VExpr.instVar_zero, ← VExpr.lift_instN_lo, VExpr.inst_lift] at hd₂
  have hd₃ := hd₂.appDF hH
  simp only [VExpr.inst, hn.instN_eq (Nat.zero_le _), ← VExpr.lift_instN_lo,
    VExpr.inst_lift] at hd₃
  have hd₄ := hd₃.appDF ha
  simp only [VExpr.inst, hn.instN_eq (Nat.zero_le _), VExpr.inst_lift] at hd₄
  exact (hd₄.appDF he).trans (h.apply henv hrc hn hdc ht hf b hp ha he hH')

/-- A reflected selector and a well-typed input to its dependent witness binder. -/
structure Reflection.NatDITEInstance (env : VEnv) (U : Nat) (p b H : VExpr) where
  r : VExpr
  neg : VExpr
  d : VExpr
  t : VExpr
  f : VExpr
  r_type : env.HasType U [] r (.forallE (.sort .zero) (.forallE .bool (.sort .zero)))
  neg_type : env.HasType U [] neg (.forallE (.sort .zero) (.sort .zero))
  d_type : env.HasType U [] d (natDITEType r neg)
  t_type : env.HasType U [] t (ofTrueType r)
  f_type : env.HasType U [] f (ofFalseType r neg)
  prop_type : env.HasType U [] p (.sort .zero)
  bool_type : env.HasType U [] b .bool
  proof_type : env.HasType U [] H (.app (.app r p) b)
  equations : NatDITESpec env U r neg d t f

theorem Reflection.NatDITEInstance.eval {env : VEnv} (v : NatDITEInstance env U p b H)
    (henv : env.Ordered) (b' : Bool) (hb : env.IsDefEq U [] b (.boolLit b') .bool)
    (ha : env.HasType U [] a (.forallE p .nat))
    (he : env.HasType U [] e (.forallE (.app v.neg p) .nat)) :
    env.IsDefEq U [] (natDITEApp v.d p b H a e)
      (.app (if b' then a else e) (.app (.app (if b' then v.t else v.f) p) H)) .nat :=
  v.equations.eval henv v.r_type (v.neg_type.closedN henv trivial) v.d_type
    (v.t_type.closedN henv trivial) (v.f_type.closedN henv trivial) b'
    v.prop_type hb v.proof_type ha he

theorem Reflection.NatDITEInstance.branchProof_type {env : VEnv}
    (v : NatDITEInstance env U p value H) (henv : env.Ordered)
    (b : Bool) (hb : env.IsDefEq U [] value (.boolLit b) .bool) :
    env.HasType U [] (.app (.app (if b then v.t else v.f) p) H)
      (if b then p else .app v.neg p) := by
  have hr := v.r_type.closedN henv trivial
  have hn := v.neg_type.closedN henv trivial
  have hp := v.r_type.app v.prop_type
  simp only [VExpr.inst, VExpr.bool] at hp
  have hH := (hp.appDF hb).defeq v.proof_type
  cases b
  · exact Reflection.ofFalseType.apply hr hn v.f_type v.prop_type hH
  · exact Reflection.ofTrueType.apply hr v.t_type v.prop_type hH

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

/-- The decision function assembled by the reflected natural-number condition check. -/
def Condition.reflectedDec (prop asBool proof : Expr) (r : Reflection) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 r.toDec
    (mkApp2 prop (.bvar 1) (.bvar 0)) (mkApp2 asBool (.bvar 1) (.bvar 0))
    (mkApp2 proof (.bvar 1) (.bvar 0))

private theorem Condition.reflectedDec_beta {prop asBool proof : Expr} (r : Reflection)
    (hp : prop.Closed) (hb : asBool.Closed) (hh : proof.Closed) (hd : r.toDec.Closed)
    (hn : n.Closed) (hm : m.Closed) :
    BetaReduce (mkApp2 (reflectedDec prop asBool proof r) n m)
      (mkApp3 r.toDec (mkApp2 prop n m) (mkApp2 asBool n m) (mkApp2 proof n m)) := by
  let body := mkApp3 r.toDec (mkApp2 prop (.bvar 1) (.bvar 0))
    (mkApp2 asBool (.bvar 1) (.bvar 0)) (mkApp2 proof (.bvar 1) (.bvar 0))
  have hbody : LambdaBodyN 2 (reflectedDec prop asBool proof r) body := .succ (.succ .zero)
  have hinst (e : Expr) (he : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  have hlift (k : Nat) : n.liftLooseBVars' 0 k = n :=
    Expr.liftLooseBVars_eq_self hn.looseBVarRange_le
  have eq : body.instantiateList [m, n] =
      mkApp3 r.toDec (mkApp2 prop n m) (mkApp2 asBool n m) (mkApp2 proof n m) := by
    simp only [body, Expr.instantiateList, Expr.instantiate1', hinst _ hp,
      hinst _ hb, hinst _ hh, hinst _ hd, hinst _ hm, hlift, Expr.liftLooseBVars_zero,
      Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
    rfl
  have hargs : ∀ x ∈ [n, m], x.Closed := by simp [hn, hm]
  exact BetaReduce.inst_reduce hargs [] hbody eq

private theorem tr_reflectedDec_equiv {env : VEnv} {prop asBool proof : Expr}
    {r : Reflection} (henv : env.WF)
    (hp : prop.Closed) (hb : asBool.Closed) (hh : proof.Closed) (hd : r.toDec.Closed)
    (te : TrExprS env Us [] (Condition.reflectedDec prop asBool proof r) e')
    (tdec : TrExprS env Us [] dec dec') (heq : env.IsDefEq Us.length [] e' dec' ty')
    (happ : TrExprS env Us [] (mkApp2 dec n m) out) :
    TrExpr env Us []
      (mkApp3 r.toDec (mkApp2 prop n m) (mkApp2 asBool n m) (mkApp2 proof n m)) out := by
  have hΔ : VLCtx.WF env Us.length [] := trivial
  let .app hfn hm tfn tm := happ
  let .app hdec hn td tn := tfn
  have eqD := (show env.IsDefEqU Us.length [] e' dec' from ⟨_, heq⟩).trans henv trivial
    (tdec.uniq henv (.refl henv.ordered hΔ) td)
  have eqD := eqD.of_r henv trivial hdec
  have t₁ := TrExprS.app (Us := Us) (Δ := []) eqD.hasType.1 hn te tn
  have eq₁ := (show env.IsDefEqU Us.length [] _ _ from ⟨_, eqD.appDF hn⟩).of_r
    henv trivial hfn
  have t₂ := TrExprS.app (Us := Us) (Δ := []) eq₁.hasType.1 hm t₁ tm
  have eq₂ := eq₁.appDF hm
  have tbeta := (t₂.trExpr henv.ordered hΔ).beta henv hΔ
    (Condition.reflectedDec_beta r hp hb hh hd tn.closed tm.closed)
  exact tbeta.defeq henv trivial ⟨_, eq₂⟩

private theorem tr_closedUnderNatNat {env : VEnv}
    (henv : env.Ordered) (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hc : e.Closed)
    (he : TrExprS env Us [(none, .vlam .nat), (none, .vlam .nat)] e e') :
    ∃ e', TrExprS env Us [] e e' := by
  -- Both binders are unused in `e`, so instantiating them with zero recovers
  -- a translation in the empty context.
  have hz₁ := TrExprS.natZero (Us := Us) (Δ := [(none, .vlam .nat)]) hp hn
  have hz₀ := TrExprS.natZero (Us := Us) (Δ := []) hp hn
  have he := he.inst henv hz₁.2 hz₁.1
  rw [Expr.instantiate1_eq_self hc.looseBVarRange_zero] at he
  have he := he.inst henv hz₀.2 hz₀.1
  rw [Expr.instantiate1_eq_self hc.looseBVarRange_zero] at he
  exact ⟨_, he⟩

private theorem tr_reflectedDec_apply {env : VEnv} {prop asBool proof : Expr}
    {r : Reflection} (henv : env.Ordered)
    (hp : prop.Closed) (hb : asBool.Closed) (hh : proof.Closed) (hd : r.toDec.Closed)
    (te : TrExprS env Us [] (Condition.reflectedDec prop asBool proof r) e')
    (tn : TrExprS env Us [] n n') (hn : env.HasType Us.length [] n' .nat)
    (tm : TrExprS env Us [] m m') (hm : env.HasType Us.length [] m' .nat) :
    ∃ e', TrExprS env Us []
      (mkApp3 r.toDec (mkApp2 prop n m) (mkApp2 asBool n m) (mkApp2 proof n m)) e' := by
  have hinst (e : Expr) (hc : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans hc.looseBVarRange_le (Nat.zero_le _))
  have hnl (k : Nat) : n.liftLooseBVars' 0 k = n :=
    Expr.liftLooseBVars_eq_self tn.closed.looseBVarRange_le
  have hml (k : Nat) : m.liftLooseBVars' 0 k = m :=
    Expr.liftLooseBVars_eq_self tm.closed.looseBVarRange_le
  simp only [Condition.reflectedDec, Expr.lam0] at te
  cases te with
  | lam _ tNat te =>
    cases tNat with
    | const _ hu _ =>
      cases hu
      have te := te.inst henv hn tn
      simp only [Expr.instantiate1', hinst _ hp, hinst _ hb, hinst _ hh, hinst _ hd,
        hnl, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false] at te
      have ⟨out, te⟩ := (show ∃ out, TrExprS env Us [] _ out from ⟨_, te⟩)
      let .lam _ tNat te := te
      cases tNat with
      | const _ hu _ =>
        cases hu
        have te := te.inst henv hm tm
        simpa only [Expr.instantiate1', hinst _ hp, hinst _ hb, hinst _ hh, hinst _ hd,
          hinst _ tn.closed, hnl, hml, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
          if_true, if_false] using (show ∃ out, TrExprS env Us [] _ out from ⟨_, te⟩)

private theorem Condition.reflectedDec_components {c : VContext}
    {prop asBool proof : Expr} {r : Reflection} (hc : c.vlctx = [])
    (hb : asBool.Closed) (hp : proof.Closed) (hn : c.venv.contains ``Nat)
    (he : c.TrExprS (reflectedDec prop asBool proof r) e') :
    (∃ b, c.TrExprS asBool b) ∧ (∃ p, c.TrExprS proof p) := by
  simp only [VContext.TrExprS, hc] at he ⊢
  cases he with
  | lam _ tNat he =>
    cases tNat with
    | const _ hu _ =>
      cases hu
      cases he with
      | lam _ tNat he =>
        cases tNat with
        | const _ hv _ =>
          cases hv
          let .app _ _ hfun hproof := he
          let .app _ _ _ hbool := hfun
          let .app _ _ hbool _ := hbool
          let .app _ _ hbool _ := hbool
          let .app _ _ hproof _ := hproof
          let .app _ _ hproof _ := hproof
          exact ⟨tr_closedUnderNatNat c.Ewf.ordered c.hasPrimitives hn hb hbool,
            tr_closedUnderNatNat c.Ewf.ordered c.hasPrimitives hn hp hproof⟩

/-- Facts extracted from the reflected condition validator with only the
Nat-valued dependent conditional enabled. This does not yet identify its
Boolean function with any particular operation on natural numbers. -/
def Condition.ReflectedNatNatChecked (c : VContext)
    (prop dec asBool proof : Expr) (r : Reflection) (p' : VExpr) : Prop :=
  c.HasType p' (.forallE .nat (.forallE .nat (.sort .zero))) ∧
    ∃ b' proof' proofTy dec' e' ty' r' neg d t f,
      c.TrExprS asBool b' ∧ c.HasType b' (.forallE .nat (.forallE .nat .bool)) ∧
      c.TrExprS proof proof' ∧ c.HasType proof' proofTy ∧
      c.HasType proofTy (.sort .zero) ∧
      c.TrExprS dec dec' ∧ c.TrExprS (reflectedDec prop asBool proof r) e' ∧
      c.venv.IsDefEq c.lparams.length c.vlctx.toCtx e' dec' ty' ∧
      c.TrExprS r.type r' ∧
      c.HasType r' (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) ∧
      c.TrExprS q(Not) neg ∧ c.HasType neg (.forallE (.sort .zero) (.sort .zero)) ∧
      c.TrExprS r.natDITE d ∧ c.HasType d (Reflection.natDITEType r' neg) ∧
      c.TrExprS r.ofTrue t ∧ c.HasType t (Reflection.ofTrueType r') ∧
      c.TrExprS r.ofFalse f ∧ c.HasType f (Reflection.ofFalseType r' neg) ∧
      Reflection.NatDITESpec c.venv c.lparams.length r' neg d t f

theorem Condition.ReflectedNatNatChecked.apply {c : VContext} {prop dec asBool proof : Expr}
    {r : Reflection} (h : ReflectedNatNatChecked c prop dec asBool proof r p')
    (hc : c.vlctx = []) (hdc : r.toDec.Closed) (tp : c.TrExprS prop p')
    (tn : c.TrExprS n n') (hn : c.HasType n' .nat)
    (tm : c.TrExprS m m') (hm : c.HasType m' .nat) :
    ∃ b H, ∃ v : Reflection.NatDITEInstance c.venv c.lparams.length
        (.app (.app p' n') m') b H,
      c.TrExprS (mkApp2 asBool n m) b ∧ c.TrExprS (mkApp2 proof n m) H ∧
      c.TrExprS r.type v.r ∧ c.TrExprS q(Not) v.neg ∧
      c.TrExprS r.natDITE v.d ∧ c.TrExprS r.ofTrue v.t ∧ c.TrExprS r.ofFalse v.f := by
  unfold ReflectedNatNatChecked at h
  simp only [VContext.TrExprS, VContext.HasType, hc, VLCtx.toCtx] at h tp tn hn tm hm ⊢
  obtain ⟨hprop, bfun, proof', proofTy, dec', e', ty', r', neg, d, t, f,
    tb, hbt, tproof, _, _, _, te, _, tr, hrt, tneg, hneg, td, hdt, tt, htt, tf, hft, hspec⟩ := h
  have hp₁ := hprop.app hn
  simp only [VExpr.inst, VExpr.nat] at hp₁
  have hP := hp₁.app hm
  simp only [VExpr.inst] at hP
  have tP := TrExprS.app hp₁ hm (.app hprop hn tp tn) tm
  have hb₁ := hbt.app hn
  simp only [VExpr.inst, VExpr.nat, VExpr.bool] at hb₁
  have hB := hb₁.app hm
  simp only [VExpr.inst] at hB
  have tB := TrExprS.app hb₁ hm (.app hbt hn tb tn) tm
  obtain ⟨out, tOut⟩ := tr_reflectedDec_apply c.Ewf.ordered tp.closed tb.closed tproof.closed hdc
    te tn hn tm hm
  obtain ⟨H, tH, hH⟩ := Reflection.natDITE_witness c.Ewf r tr.closed hdc tr hrt td
    tP hP tB hB tOut
  let v : Reflection.NatDITEInstance c.venv c.lparams.length
      (.app (.app p' n') m') (.app (.app bfun n') m') H := {
    r := r', neg, d, t, f
    r_type := hrt, neg_type := hneg, d_type := hdt, t_type := htt, f_type := hft
    prop_type := hP, bool_type := hB, proof_type := hH, equations := hspec }
  exact ⟨_, H, v, tB, tH, tr, tneg, td, tt, tf⟩

/-- Instantiate the checked polymorphic selector at typed natural-number inputs,
recovering its reflection witness from the executable decision function. -/
theorem Condition.ReflectedNatNatChecked.ite_apply {c : VContext}
    {prop dec asBool proof : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p')
    (hi : Reflection.ITEChecked c r) (hc : c.vlctx = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p')
    (tn : c.TrExprS n n') (hn : c.HasType n' .nat)
    (tm : c.TrExprS m m') (hm : c.HasType m' .nat) :
    ∃ b H, ∃ v : Reflection.ITEInstance c.venv c.lparams.length
        (.app (.app p' n') m') b H,
      c.TrExprS (mkApp2 asBool n m) b ∧ c.TrExprS (mkApp2 proof n m) H ∧
      c.TrExprS r.type v.r ∧ c.TrExprS r.ite v.i := by
  unfold ReflectedNatNatChecked at h
  unfold Reflection.ITEChecked at hi
  simp only [VContext.TrExprS, VContext.HasType, hc, VLCtx.toCtx] at h hi tp tn hn tm hm ⊢
  obtain ⟨hprop, bfun, proof', proofTy, dec', e', ty', _, neg, d, t, f,
    tb, hbt, tproof, _, _, _, te, _⟩ := h
  obtain ⟨r', i, tr, hrt, ti, hit, hspec⟩ := hi
  have hp₁ := hprop.app hn
  simp only [VExpr.inst, VExpr.nat] at hp₁
  have hP := hp₁.app hm
  simp only [VExpr.inst] at hP
  have tP := TrExprS.app hp₁ hm (.app hprop hn tp tn) tm
  have hb₁ := hbt.app hn
  simp only [VExpr.inst, VExpr.nat, VExpr.bool] at hb₁
  have hB := hb₁.app hm
  simp only [VExpr.inst] at hB
  have tB := TrExprS.app hb₁ hm (.app hbt hn tb tn) tm
  obtain ⟨out, tOut⟩ := tr_reflectedDec_apply c.Ewf.ordered tp.closed tb.closed tproof.closed hdc
    te tn hn tm hm
  obtain ⟨H, tH, hH⟩ := Reflection.ite_witness c.Ewf r tr.closed hdc tr hrt ti
    tP hP tB hB tOut
  let v : Reflection.ITEInstance c.venv c.lparams.length
      (.app (.app p' n') m') (.app (.app bfun n') m') H := {
    r := r', i
    r_type := hrt, i_type := hit, prop_type := hP, bool_type := hB, proof_type := hH
    equations := hspec }
  exact ⟨_, H, v, tB, tH, tr, ti⟩

theorem Condition.ReflectedNatNatChecked.natBle_value_inputs {c : VContext}
    {prop dec proof na nb : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (a b : Nat)
    (ta : c.TrExprS na (.natLit a)) (tb : c.TrExprS nb (.natLit b))
    (ha : c.HasType (.natLit a) .nat) (hb : c.HasType (.natLit b) .nat)
    (tB : c.TrExprS (mkApp2 q(Nat.ble) na nb) B) (hB : c.HasType B .bool) :
    c.venv.IsDefEq c.lparams.length [] B (.boolLit (Nat.ble a b)) .bool := by
  obtain ⟨_, bfun, _, _, _, _, _, _, _, _, _, _, tble, hble, _⟩ := h
  cases tble with
  | const hci hlevels hlen =>
    cases hlevels
    have tble : c.TrExprS q(Nat.ble) (.const ``Nat.ble []) := .const hci rfl hlen
    have hble₁ := hble.app ha
    simp only [VExpr.inst, VExpr.nat, VExpr.bool] at hble₁
    have tB' := TrExprS.app hble₁ hb (.app hble ha tble ta) tb
    have heq := tB.uniq c.Ewf (.refl c.Ewf.ordered c.Δwf) tB'
    have hreflect : c.IsDefEqU
        (.app (.app (.const ``Nat.ble []) (.natLit a)) (.natLit b)) (.boolLit (Nat.ble a b)) := by
      simpa only [VContext.IsDefEqU, hu, hc, VLCtx.toCtx] using
        c.hasPrimitives.natBle ⟨_, hci⟩ a b
    simpa only [hc, VLCtx.toCtx] using
      (heq.trans c.Ewf c.Δwf.toCtx hreflect).of_l c.Ewf c.Δwf.toCtx hB

theorem Condition.ReflectedNatNatChecked.natBle_value {c : VContext}
    {prop dec proof : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = [])
    (hnat : c.venv.contains ``Nat) (a b : Nat)
    (tB : c.TrExprS (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) B)
    (hB : c.HasType B .bool) :
    c.venv.IsDefEq c.lparams.length [] B (.boolLit (Nat.ble a b)) .bool := by
  have ta₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat a
  have tb₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat b
  have ta : c.TrExprS (.lit (.natVal a)) (.natLit a) := by
    simpa only [VContext.TrExprS, hc] using ta₀.1
  have tb : c.TrExprS (.lit (.natVal b)) (.natLit b) := by
    simpa only [VContext.TrExprS, hc] using tb₀.1
  have ha : c.HasType (.natLit a) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using ta₀.2
  have hb : c.HasType (.natLit b) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using tb₀.2
  exact h.natBle_value_inputs hc hu a b ta tb ha hb tB hB

theorem Condition.ReflectedNatNatChecked.natBle_apply {c : VContext}
    {prop dec proof : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (hnat : c.venv.contains ``Nat) (a b : Nat) :
    ∃ B H, ∃ v : Reflection.NatDITEInstance c.venv c.lparams.length
        (.app (.app p' (.natLit a)) (.natLit b)) B H,
      c.TrExprS (mkApp2 proof (.lit (.natVal a)) (.lit (.natVal b))) H ∧
      c.TrExprS r.type v.r ∧ c.TrExprS q(Not) v.neg ∧
      c.TrExprS r.natDITE v.d ∧ c.TrExprS r.ofTrue v.t ∧ c.TrExprS r.ofFalse v.f ∧
      c.venv.IsDefEq c.lparams.length [] B (.boolLit (Nat.ble a b)) .bool := by
  have ta₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat a
  have tb₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat b
  have ta : c.TrExprS (.lit (.natVal a)) (.natLit a) := by
    simpa only [VContext.TrExprS, hc] using ta₀.1
  have tb : c.TrExprS (.lit (.natVal b)) (.natLit b) := by
    simpa only [VContext.TrExprS, hc] using tb₀.1
  have ha : c.HasType (.natLit a) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using ta₀.2
  have hb : c.HasType (.natLit b) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using tb₀.2
  obtain ⟨B, H, v, tB, tH, tr, tneg, td, tt, tf⟩ := h.apply hc hdc tp ta ha tb hb
  have hB : c.HasType B .bool := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using v.bool_type
  exact ⟨B, H, v, tH, tr, tneg, td, tt, tf, h.natBle_value hc hu hnat a b tB hB⟩

/-- Recover the branch types from the checked conditional instead of assuming
that its structural translation already uses the canonical dependent types. -/
theorem Condition.ReflectedNatNatChecked.natDITE_branches {c : VContext}
    {prop dec asBool proof a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.NatDITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H) (td : c.TrExprS r.natDITE v.d)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop n m) (mkApp2 dec n m) a e) out) :
    ∃ a' e', c.TrExprS a a' ∧ c.TrExprS e e' ∧
      c.HasType a' (.forallE P .nat) ∧ c.HasType e' (.forallE (.app v.neg P) .nat) := by
  unfold ReflectedNatNatChecked at h
  simp only [VContext.TrExprS, VContext.HasType, hc, VLCtx.toCtx]
    at h tP tB tH td tactual ⊢
  obtain ⟨_, bfun, proof', proofTy, dec', fun', ty', r', neg, d, t, f,
    tb, _, tproof, _, _, tdec, tchecked, hchecked, _⟩ := h
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  let .app hfa hearg tfa tearg := tactual
  let .app hfd haarg tfd taarg := tfa
  let .app hfp hdecarg tfp tdecarg := tfd
  have tdecision := tr_reflectedDec_equiv c.Ewf tP.closed.1.1 tb.closed tproof.closed hdc
    tchecked tdec hchecked tdecarg
  have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfp hdecarg
    (tfp.trExpr c.Ewf.ordered hΔ) tdecision
  have hr := v.r_type.closedN c.Ewf.ordered trivial
  have hn := v.neg_type.closedN c.Ewf.ordered trivial
  have ⟨tselector, hselector⟩ := tr_natDITEPrefix hr hn v.d_type v.prop_type v.bool_type
    v.proof_type td tP tB tH
  have texpanded := (tselector.trExpr c.Ewf.ordered hΔ).beta c.Ewf hΔ
    (Reflection.natDITE_beta_core r hdc tP.closed tB.closed tH.closed)
  have eq := treplaced.uniq c.Ewf (.refl c.Ewf.ordered hΔ) texpanded
  have hcanonical := (eq.of_r c.Ewf trivial hselector).hasType.1
  have ⟨⟨_, hdom⟩, _⟩ := (hfd.uniqU c.Ewf trivial hcanonical).forallE_inv c.Ewf trivial
  have ha := haarg.defeqU_r c.Ewf trivial ⟨_, hdom⟩
  have hcanonical := hcanonical.app ha
  simp only [VExpr.inst, VExpr.inst_lift, VExpr.nat] at hcanonical
  have ⟨⟨_, hdom⟩, _⟩ := (hfa.uniqU c.Ewf trivial hcanonical).forallE_inv c.Ewf trivial
  exact ⟨_, _, taarg, tearg, ha, hearg.defeqU_r c.Ewf trivial ⟨_, hdom⟩⟩

/-- Translate the declared dependent conditional through its checked reflected
decision function to the selector carrying the computation equations. -/
theorem Condition.ReflectedNatNatChecked.natDITE_translate {c : VContext}
    {prop dec asBool proof a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.NatDITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H) (td : c.TrExprS r.natDITE v.d)
    (ta : c.TrExprS a a') (te : c.TrExprS e e')
    (ha : c.HasType a' (.forallE P .nat))
    (he : c.HasType e' (.forallE (.app v.neg P) .nat))
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop n m) (mkApp2 dec n m) a e) out) :
    c.TrExpr (mkApp4 q(@dite Nat) (mkApp2 prop n m) (mkApp2 dec n m) a e)
      (Reflection.natDITEApp v.d P B H a' e') := by
  unfold ReflectedNatNatChecked at h
  simp only [VContext.TrExprS, VContext.TrExpr, VContext.HasType, hc, VLCtx.toCtx]
    at h tP tB tH td ta te ha he tactual ⊢
  obtain ⟨_, bfun, proof', proofTy, dec', fun', ty', r', neg, d, t, f,
    tb, _, tproof, _, _, tdec, tchecked, hchecked, _⟩ := h
  have hp : prop.Closed := tP.closed.1.1
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  cases tactual with
  | app hfa hearg tfa tearg =>
    cases tfa with
    | app hfd haarg tfd taarg =>
      cases tfd with
      | app hfp hdecarg tfp tdecarg =>
        have tdecision := tr_reflectedDec_equiv c.Ewf hp tb.closed tproof.closed hdc
          tchecked tdec hchecked tdecarg
        have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfp hdecarg
          (tfp.trExpr c.Ewf.ordered hΔ) tdecision
        have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfd haarg treplaced
          (taarg.trExpr c.Ewf.ordered hΔ)
        have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfa hearg treplaced
          (tearg.trExpr c.Ewf.ordered hΔ)
        have hr := v.r_type.closedN c.Ewf.ordered trivial
        have hn := v.neg_type.closedN c.Ewf.ordered trivial
        have tselector := (tr_natDITEApp hr hn v.d_type v.prop_type v.bool_type v.proof_type
          ha he td tP tB tH ta te).1
        have texpanded := (tselector.trExpr c.Ewf.ordered hΔ).beta c.Ewf hΔ
          (Reflection.natDITE_beta r hdc tP.closed tB.closed tH.closed)
        have eq := treplaced.uniq c.Ewf (.refl c.Ewf.ordered hΔ) texpanded
        have tactual := TrExprS.app hfa hearg (.app hfd haarg
          (.app hfp hdecarg tfp tdecarg) taarg) tearg
        exact (tactual.trExpr c.Ewf.ordered hΔ).defeq c.Ewf hΔ.toCtx eq

theorem Condition.ReflectedNatNatChecked.natDITE_eval {c : VContext}
    {prop dec asBool proof a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.NatDITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H) (td : c.TrExprS r.natDITE v.d)
    (ta : c.TrExprS a a') (te : c.TrExprS e e')
    (ha : c.HasType a' (.forallE P .nat))
    (he : c.HasType e' (.forallE (.app v.neg P) .nat))
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop n m) (mkApp2 dec n m) a e) out)
    (b : Bool) (hb : c.venv.IsDefEq c.lparams.length [] B (.boolLit b) .bool) :
    c.venv.IsDefEq c.lparams.length [] out (.app (if b then a' else e')
      (.app (.app (if b then v.t else v.f) P) H)) .nat := by
  have tselector := h.natDITE_translate hc hdc v tP tB tH td ta te ha he tactual
  simp only [VContext.TrExprS, VContext.TrExpr, VContext.HasType,
    hc, VLCtx.toCtx] at tactual tselector ha he ⊢
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have eq := (tactual.trExpr c.Ewf.ordered hΔ).uniq c.Ewf (.refl c.Ewf.ordered hΔ) tselector
  have hcomp := v.eval c.Ewf.ordered b hb ha he
  exact (eq.trans c.Ewf trivial ⟨_, hcomp⟩).of_r c.Ewf trivial hcomp.hasType.2

/-- Produce a source-level proof of a true reflected comparison. This lets
dependent checker equations be instantiated without assuming a source
representation for an arbitrary abstract proof. -/
theorem Condition.ReflectedNatNatChecked.natBle_witness {c : VContext}
    {prop dec proof na nb : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (hle : n ≤ m) :
    ∃ w witness, c.TrExprS w witness ∧
      c.venv.HasType c.lparams.length [] witness (VEnv.natLeExpr p' n m) := by
  have hprop := h.1
  have hprop₁ := hprop.app hn
  simp only [VExpr.inst, VExpr.nat] at hprop₁
  have tP := TrExprS.app hprop₁ hm (.app hprop hn tp tn) tm
  obtain ⟨B, H, v, tB, tH, _, _, _, tt, _⟩ := h.apply hc hdc tp tn hn tm hm
  have hB : c.HasType B .bool := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using v.bool_type
  have hb := h.natBle_value_inputs hc hu n m tn tm hn hm tB hB
  rw [Nat.ble_eq_true_of_le hle] at hb
  have hH' := (((v.r_type.app v.prop_type).appDF hb).defeqDF v.proof_type).hasType.1
  have hr := v.r_type.closedN c.Ewf.ordered trivial
  have hneg := v.neg_type.closedN c.Ewf.ordered trivial
  simp only [VContext.TrExprS, hc] at tP tH tt
  have ⟨tW, hW⟩ := tr_reflectionProof true hr hneg v.t_type v.prop_type hH' tt tP tH
  exact ⟨_, _, (by simpa only [VContext.TrExprS, hc] using tW), hW⟩

/-- Select a branch at typed source arguments representing natural numbers.
The source witness is retained so a branch lambda can subsequently be reduced. -/
theorem Condition.ReflectedNatNatChecked.natBle_dite_eval_inputs {c : VContext}
    {prop dec proof na nb a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop na nb) (mkApp2 dec na nb) a e) out) :
    ∃ a' e' neg w witness,
      c.TrExprS a a' ∧ c.TrExprS e e' ∧ c.TrExprS q(Not) neg ∧ c.TrExprS w witness ∧
      c.venv.HasType c.lparams.length [] witness
        (if Nat.ble n m then .app (.app p' (.natLit n)) (.natLit m)
          else .app neg (.app (.app p' (.natLit n)) (.natLit m))) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (.app (if Nat.ble n m then a' else e') witness) .nat := by
  have hprop := h.1
  have hprop₁ := hprop.app hn
  simp only [VExpr.inst, VExpr.nat] at hprop₁
  have tP := TrExprS.app hprop₁ hm (.app hprop hn tp tn) tm
  obtain ⟨B, H, v, tB, tH, _, tneg, td, tt, tf⟩ := h.apply hc hdc tp tn hn tm hm
  obtain ⟨a', e', ta, te, ha, he⟩ := h.natDITE_branches hc hdc v tP tB tH td tactual
  have hB : c.HasType B .bool := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using v.bool_type
  have hb := h.natBle_value_inputs hc hu n m tn tm hn hm tB hB
  have heq := h.natDITE_eval hc hdc v tP tB tH td ta te ha he tactual _ hb
  have hH' := (((v.r_type.app v.prop_type).appDF hb).defeqDF v.proof_type).hasType.1
  have hr := v.r_type.closedN c.Ewf.ordered trivial
  have hneg := v.neg_type.closedN c.Ewf.ordered trivial
  have ht : c.venv.HasType c.lparams.length [] (if Nat.ble n m then v.t else v.f)
      (if Nat.ble n m then Reflection.ofTrueType v.r else Reflection.ofFalseType v.r v.neg) := by
    cases Nat.ble n m
    · exact v.f_type
    · exact v.t_type
  simp only [VContext.TrExprS, hc] at tP tH tt tf
  have tw : TrExprS c.venv c.lparams [] (if Nat.ble n m then r.ofTrue else r.ofFalse)
      (if Nat.ble n m then v.t else v.f) := by
    cases Nat.ble n m
    · exact tf
    · exact tt
  have ⟨tW, hW⟩ := tr_reflectionProof (Nat.ble n m) hr hneg ht v.prop_type hH' tw tP tH
  refine ⟨a', e', v.neg,
    mkApp2 (if Nat.ble n m then r.ofTrue else r.ofFalse)
      (mkApp2 prop na nb) (mkApp2 proof na nb), _, ta, te, tneg, ?_, hW, heq⟩
  simpa only [VContext.TrExprS, hc] using tW

/-- Select a branch of the actual dependent conditional at natural-number
literals, recovering the branch types and the selected proof from its checks. -/
theorem Condition.ReflectedNatNatChecked.natBle_dite_eval {c : VContext}
    {prop dec proof a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (hnat : c.venv.contains ``Nat) (n m : Nat)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop (.lit (.natVal n)) (.lit (.natVal m)))
        (mkApp2 dec (.lit (.natVal n)) (.lit (.natVal m))) a e) out) :
    ∃ a' e' neg witness,
      c.TrExprS a a' ∧ c.TrExprS e e' ∧ c.TrExprS q(Not) neg ∧
      c.venv.HasType c.lparams.length [] witness
        (if Nat.ble n m then .app (.app p' (.natLit n)) (.natLit m)
          else .app neg (.app (.app p' (.natLit n)) (.natLit m))) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (.app (if Nat.ble n m then a' else e') witness) .nat := by
  have tn₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat n
  have tm₀ := TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hnat m
  have tn : c.TrExprS (.lit (.natVal n)) (.natLit n) := by
    simpa only [VContext.TrExprS, hc] using tn₀.1
  have tm : c.TrExprS (.lit (.natVal m)) (.natLit m) := by
    simpa only [VContext.TrExprS, hc] using tm₀.1
  have hn : c.HasType (.natLit n) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using tn₀.2
  have hm : c.HasType (.natLit m) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using tm₀.2
  obtain ⟨a', e', neg, w, witness, ta, te, tneg, _, hw, heq⟩ :=
    h.natBle_dite_eval_inputs hc hu hdc tp n m tn tm hn hm tactual
  exact ⟨a', e', neg, witness, ta, te, tneg, hw, heq⟩

/-- Reduce the selected source branch lambda while preserving its proof term. -/
theorem Condition.ReflectedNatNatChecked.natBle_dite_body_inputs {c : VContext}
    {prop dec proof na nb a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop na nb) (mkApp2 dec na nb)
        (.lam0 (mkApp2 prop na nb) a) (.lam0 (mkApp q(Not) (mkApp2 prop na nb)) e)) out) :
    ∃ neg w witness,
      c.TrExprS q(Not) neg ∧ c.TrExprS w witness ∧
      c.venv.HasType c.lparams.length [] witness
        (if Nat.ble n m then .app (.app p' (.natLit n)) (.natLit m)
          else .app neg (.app (.app p' (.natLit n)) (.natLit m))) ∧
      c.TrExpr ((if Nat.ble n m then a else e).instantiate1' w) out := by
  obtain ⟨a', e', neg, w, witness, ta, te, tneg, tw, hw, heq⟩ :=
    h.natBle_dite_eval_inputs hc hu hdc tp n m tn tm hn hm tactual
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have ⟨_, _, hfn, harg⟩ := heq.hasType.2.app_inv c.Ewf.ordered trivial
  have tw₀ : TrExprS c.venv c.lparams [] w witness := by
    simpa only [VContext.TrExprS, hc] using tw
  simp only [VContext.TrExprS, hc] at ta te
  have tf : TrExprS c.venv c.lparams []
      (if Nat.ble n m then .lam0 (mkApp2 prop na nb) a
        else .lam0 (mkApp q(Not) (mkApp2 prop na nb)) e)
      (if Nat.ble n m then a' else e') := by
    cases Nat.ble n m
    · exact te
    · exact ta
  have tapp := (TrExprS.app hfn harg tf tw₀).trExpr c.Ewf.ordered hΔ
  have tapp := tapp.defeq c.Ewf hΔ.toCtx heq.symm.toU
  have hbeta : BetaReduce
      (.app (if Nat.ble n m then .lam0 (mkApp2 prop na nb) a
        else .lam0 (mkApp q(Not) (mkApp2 prop na nb)) e) w)
      ((if Nat.ble n m then a else e).instantiate1' w) := by
    cases Nat.ble n m <;> exact .beta tw₀.closed.looseBVarRange_zero
  refine ⟨neg, w, witness, tneg, tw, hw, ?_⟩
  simpa only [VContext.TrExpr, hc] using tapp.beta c.Ewf hΔ hbeta

theorem Condition.ReflectedNatNatChecked.natBle_dite_zero_inputs {c : VContext}
    {prop dec proof na nb a : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (hnat : c.venv.contains ``Nat) (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (hlt : m < n)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop na nb) (mkApp2 dec na nb)
        (.lam0 (mkApp2 prop na nb) a) (.lam0 (mkApp q(Not) (mkApp2 prop na nb)) q(Nat.zero))) out) :
    c.venv.IsDefEq c.lparams.length [] out .natZero .nat := by
  obtain ⟨_, _, _, _, _, _, tbody⟩ :=
    h.natBle_dite_body_inputs hc hu hdc tp n m tn tm hn hm tactual
  have hble : Nat.ble n m = false :=
    Bool.eq_false_iff.2 fun hle => (Nat.not_le_of_gt hlt) (Nat.le_of_ble_eq_true hle)
  simp only [hble, Bool.false_eq_true, if_false, Expr.instantiate1'] at tbody
  have hzero := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  simp only [VContext.TrExpr, hc] at tbody
  exact (tbody.uniq c.Ewf (.refl c.Ewf.ordered hΔ) (hzero.1.trExpr c.Ewf.ordered hΔ)).of_r
    c.Ewf hΔ.toCtx hzero.2

theorem Condition.ReflectedNatNatChecked.natBle_dite_zero_of_gt {c : VContext}
    {prop dec proof a : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop p') (hnat : c.venv.contains ``Nat) (n m : Nat)
    (hlt : m < n)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop (.lit (.natVal n)) (.lit (.natVal m)))
        (mkApp2 dec (.lit (.natVal n)) (.lit (.natVal m))) a
        (.lam0 (mkApp q(Not) (mkApp2 prop (.lit (.natVal n)) (.lit (.natVal m)))) q(Nat.zero))) out) :
    c.venv.IsDefEq c.lparams.length [] out .natZero .nat := by
  obtain ⟨a', e', neg, witness, _, te, _, _, heq⟩ :=
    h.natBle_dite_eval hc hu hdc tp hnat n m tactual
  have hble : Nat.ble n m = false :=
    Bool.eq_false_iff.2 fun hle => (Nat.not_le_of_gt hlt) (Nat.le_of_ble_eq_true hle)
  simp only [hble, Bool.false_eq_true, if_false] at heq
  simp only [VContext.TrExprS, hc, Expr.lam0] at te
  cases te with
  | lam hD tD tbody =>
    rename_i D body
    cases tbody with
    | const _ hlevels _ =>
      cases hlevels
      have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
      obtain ⟨u, hD⟩ := hD
      have hzero : c.venv.HasType c.lparams.length [D] .natZero .nat :=
        hz.2.weak0 c.Ewf.ordered
      have ⟨_, _, hfn, harg⟩ := heq.hasType.2.app_inv c.Ewf.ordered trivial
      have ⟨⟨_, hdom⟩, _⟩ := (hfn.uniqU c.Ewf trivial (hD.lam hzero)).forallE_inv
        c.Ewf trivial
      have hbeta := hzero.beta (harg.defeqU_r c.Ewf trivial ⟨_, hdom⟩)
      simpa only [VExpr.inst, VExpr.natZero, VExpr.nat] using heq.trans hbeta

private theorem Condition.check_reflectNatNat_core.WF {c : VContext}
    {prop dec asBool proof : Expr} (hc : c.vlctx = []) (r : Reflection)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (tp : c.TrExprS prop p') (hbclosed : asBool.Closed) (hpclosed : proof.Closed)
    (hdec : dec.FVarsIn (· ∈ c.vlctx.fvars))
    (he : (reflectedDec prop asBool proof r).FVarsIn (· ∈ c.vlctx.fvars))
    (hr : r.type.FVarsIn (· ∈ c.vlctx.fvars))
    (hd : r.natDITE.FVarsIn (· ∈ c.vlctx.fvars))
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (ite : Bool) (hi : ite = true → r.ite.FVarsIn (· ∈ c.vlctx.fvars))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (Condition.check ⟨prop, dec, .reflectNatNat asBool r proof⟩ fail
      (ite := ite) (dite := true)).WF c s fun _ _ =>
      ReflectedNatNatChecked c prop dec asBool proof r p' ∧
        (ite = true → Reflection.ITEChecked c r) := by
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨uNat, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨uNat, hNat.weak0 c.Ewf.ordered⟩
  have htBool := TrExprS.boolTrue (Us := c.lparams) (Δ := []) c.hasPrimitives hb
  obtain ⟨uBool, hBool⟩ := htBool.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciBool, _, huBool⟩ := hBool.const_inv c.Ewf.ordered trivial
  have trBool {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Bool) .bool := .const hciBool rfl huBool
  have boolType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .bool :=
    ⟨uBool, hBool.weak0 c.Ewf.ordered⟩
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have tpType : c.TrExprS q(Nat → Nat → Prop)
      (.forallE .nat (.forallE .nat (.sort .zero))) :=
    .forallE natType (natType.forallE propType) trNat
      (.forallE natType propType trNat (.sort rfl))
  have tbType : c.TrExprS q(Nat → Nat → Bool) (.forallE .nat (.forallE .nat .bool)) :=
    .forallE natType (natType.forallE boolType) trNat
      (.forallE natType boolType trNat trBool)
  have ite_bind (p : Prop) [Decidable p] (m : M Unit) (k : Unit → M Unit) :
      (if p then m >>= k else k ()) = ((if p then m else pure ()) >>= k) := by
    split <;> simp only [pure_bind]
  unfold Condition.check
  simp only [if_true, pure_bind]
  refine (checkType.WF hdec).bind fun _ _ _ ⟨dec', _, _, tdec, _, _⟩ => ?_
  refine (inferType.WF tp).bind fun _ _ _ ⟨_, _, _, tpty, hp⟩ => ?_
  refine (isDefEq.WF tpty tpType).bind fun b _ _ hpty => ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact hfail.bind fun _ _ _ h => h.elim
  simp only [if_true]
  have hp := hp.defeqU_r c.Ewf c.Δwf (hpty rfl)
  refine (Reflection.check.WF r fail hfail hr hb).bind fun _ _ _ ⟨r', tr, hrt⟩ => ?_
  have tr₀ : TrExprS c.venv c.lparams [] r.type r' := by
    simpa only [VContext.TrExprS, hc] using tr
  have hrt₀ : c.venv.HasType c.lparams.length [] r'
      (.forallE (.sort .zero) (.forallE .bool (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hrt
  have hITE {s} : (if ite then r.checkITE fail else pure ()).WF c s
      fun _ _ => ite = true → Reflection.ITEChecked c r := by
    cases ite
    · exact .pure (by intro h; cases h)
    · exact (Reflection.checkITE.WF hc r fail hfail (hi rfl) tr₀ hrt₀ hb).mono
        fun _ _ _ ⟨i, ti, hit, hspec⟩ _ => ⟨r', i, tr, hrt, ti, hit, hspec⟩
  rw [ite_bind]
  refine hITE.bind fun _ _ _ hite => ?_
  refine (Reflection.checkNatDITE.WF hc r fail hfail hd ht hf tr₀ hrt₀ hb hn).bind
    fun _ _ _ ⟨neg, d, t, f, tneg, hneg, td, hdt, tt, htt, tf, hft, hspec⟩ => ?_
  refine (checkType.WF he).bind fun _ _ _ ⟨e', ty', _, te, _, hety⟩ => ?_
  obtain ⟨⟨b', tb⟩, ⟨proof', tproof⟩⟩ := reflectedDec_components hc hbclosed hpclosed hn te
  refine (inferType.WF tb).bind fun _ _ _ ⟨_, _, _, tbty, hbt⟩ => ?_
  refine (isDefEq.WF tbty tbType).bind fun b _ _ hbty => ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact hfail.bind fun _ _ _ h => h.elim
  simp only [if_true]
  have hbt := hbt.defeqU_r c.Ewf c.Δwf (hbty rfl)
  refine (inferType.WF tproof).bind fun _ _ _ ⟨proofTy, _, _, tpty, hproof⟩ => ?_
  refine (isProp.WF tpty).bind fun b _ _ hprop => ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact hfail.bind fun _ _ _ h => h.elim
  simp only [if_true]
  refine (isDefEq.WF te tdec).bind fun b _ _ heq => ?_
  cases b
  · exact hfail.mono fun _ _ _ h => h.elim
  · exact .pure ⟨⟨hp, b', proof', proofTy, dec', e', ty', r', neg, d, t, f,
      tb, hbt, tproof, hproof, hprop rfl, tdec, te,
      (heq rfl).of_l c.Ewf c.Δwf.toCtx hety, tr, hrt,
      tneg, hneg, td, hdt, tt, htt, tf, hft, hspec⟩, hite⟩

theorem Condition.check_reflectNatNat.WF {c : VContext}
    {prop dec asBool proof : Expr} (hc : c.vlctx = []) (r : Reflection)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (tp : c.TrExprS prop p') (hbclosed : asBool.Closed) (hpclosed : proof.Closed)
    (hdec : dec.FVarsIn (· ∈ c.vlctx.fvars))
    (he : (reflectedDec prop asBool proof r).FVarsIn (· ∈ c.vlctx.fvars))
    (hr : r.type.FVarsIn (· ∈ c.vlctx.fvars))
    (hd : r.natDITE.FVarsIn (· ∈ c.vlctx.fvars))
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (Condition.check ⟨prop, dec, .reflectNatNat asBool r proof⟩ fail (dite := true)).WF c s
      fun _ _ => ReflectedNatNatChecked c prop dec asBool proof r p' :=
  (check_reflectNatNat_core.WF hc r fail hfail tp hbclosed hpclosed hdec he hr hd ht hf
    false (by intro h; cases h) hb hn).mono fun _ _ _ h => h.1

theorem Condition.check_reflectNatNat_ite.WF {c : VContext}
    {prop dec asBool proof : Expr} (hc : c.vlctx = []) (r : Reflection)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (tp : c.TrExprS prop p') (hbclosed : asBool.Closed) (hpclosed : proof.Closed)
    (hdec : dec.FVarsIn (· ∈ c.vlctx.fvars))
    (he : (reflectedDec prop asBool proof r).FVarsIn (· ∈ c.vlctx.fvars))
    (hr : r.type.FVarsIn (· ∈ c.vlctx.fvars))
    (hd : r.natDITE.FVarsIn (· ∈ c.vlctx.fvars))
    (ht : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars))
    (hf : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars))
    (hi : r.ite.FVarsIn (· ∈ c.vlctx.fvars))
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (Condition.check ⟨prop, dec, .reflectNatNat asBool r proof⟩ fail
      (ite := true) (dite := true)).WF c s fun _ _ =>
      ReflectedNatNatChecked c prop dec asBool proof r p' ∧ Reflection.ITEChecked c r :=
  (check_reflectNatNat_core.WF hc r fail hfail tp hbclosed hpclosed hdec he hr hd ht hf
    true (fun _ => hi) hb hn).mono fun _ _ _ h => ⟨h.1, h.2 rfl⟩

theorem Condition.natLE.check.WF {c : VContext} (hc : c.vlctx = [])
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (tp : c.TrExprS q(@LE.le Nat _) p')
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (Condition.natLE.check fail (dite := true)).WF c s fun _ _ =>
      ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe) q(Nat.ble)
        q(fun n m {q : Prop} (H : _ → _ → q) =>
          H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))
        Reflection.defn₁ p' := by
  apply Condition.check_reflectNatNat.WF hc _ fail hfail tp (hb := hb) (hn := hn)
  all_goals simp [reflectedDec, Reflection.natDITE, Reflection.defn₁,
    Expr.lam0, mkApp2, mkApp3, Closed, FVarsIn, Level.hasMVar']

theorem Condition.natLE.checkITE.WF {c : VContext} (hc : c.vlctx = [])
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (tp : c.TrExprS q(@LE.le Nat _) p')
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (Condition.natLE.check fail (ite := true) (dite := true)).WF c s fun _ _ =>
      ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe) q(Nat.ble)
        q(fun n m {q : Prop} (H : _ → _ → q) =>
          H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))
        Reflection.defn₁ p' ∧ Reflection.ITEChecked c Reflection.defn₁ := by
  apply Condition.check_reflectNatNat_ite.WF hc _ fail hfail tp (hb := hb) (hn := hn)
  all_goals simp [reflectedDec, Reflection.ite, Reflection.natDITE, Reflection.defn₁,
    Expr.lam0, mkApp2, mkApp3, Closed, FVarsIn, Level.hasMVar']

theorem checkNatDivCondition.WF {c : VContext} (hc : c.vlctx = [])
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (checkNatDivCondition fail).WF c s fun _ _ => ∃ p',
      c.TrExprS q(@LE.le Nat _) p' ∧
      Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe) q(Nat.ble)
        q(fun n m {q : Prop} (H : _ → _ → q) =>
          H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))
        Reflection.defn₁ p' := by
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨uNat, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨uNat, hNat.weak0 c.Ewf.ordered⟩
  have propType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ (.sort .zero) :=
    ⟨_, .sort trivial⟩
  have tpType : c.TrExprS q(Nat → Nat → Prop)
      (.forallE .nat (.forallE .nat (.sort .zero))) :=
    .forallE natType (natType.forallE propType) trNat
      (.forallE natType propType trNat (.sort rfl))
  have bindIf (p : Prop) [Decidable p] (x y : M Unit) (f : Unit → M Unit) :
      ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by
    split <;> rfl
  have eq : checkNatDivCondition fail = (do
      checkExprType q(@LE.le Nat _) q(Nat → Nat → Prop) fail
      Condition.natLE.check fail (dite := true)) := by
    simp only [checkNatDivCondition, checkExprType, bind_assoc, bindIf, pure_bind]
  rw [eq]
  refine (checkExprType.WF fail hfail (by simp [FVarsIn, Level.hasMVar']) tpType).bind
    fun _ _ _ ⟨p', tp, _⟩ => ?_
  exact (Condition.natLE.check.WF hc fail hfail tp hb hn).mono
    fun _ _ _ h => ⟨p', tp, h⟩

private theorem tr_natDivLoopType {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (tl : TrExprS env Us [] q(@LE.le Nat _) le)
    (hl : env.HasType Us.length [] le (.forallE .nat (.forallE .nat (.sort .zero)))) :
    TrExprS env Us []
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)
      (VEnv.natDivLoopType le) := by
  have hlc := hl.closedN henv trivial
  have hz := TrExprS.natZero (Us := Us) (Δ := []) hp hn
  obtain ⟨u, hNat⟩ := hz.2.isType henv trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv henv trivial
  have trNat {Δ : VLCtx} : TrExprS env Us Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : env.IsType Us.length Γ .nat :=
    ⟨u, hNat.weak0 henv⟩
  let P := VExpr.app (.app le (.natLit 1)) (.bvar 0)
  let Δ₁ : VLCtx := [(none, .vlam .nat)]
  let Δ₄ : VLCtx := [(none, .vlam .nat), (none, .vlam .nat),
    (none, .vlam P), (none, .vlam .nat)]
  have tl₁ : TrExprS env Us Δ₁ q(@LE.le Nat _) le :=
    tl.underLams_closed henv hlc [.nat]
  have tl₄ : TrExprS env Us Δ₄ q(@LE.le Nat _) le :=
    tl.underLams_closed henv hlc [.nat, .nat, P, .nat]
  have hl₁ : env.HasType Us.length Δ₁.toCtx le
      (.forallE .nat (.forallE .nat (.sort .zero))) := hl.weak0 henv
  have hl₄ : env.HasType Us.length Δ₄.toCtx le
      (.forallE .nat (.forallE .nat (.sort .zero))) := hl.weak0 henv
  have ty₁ : TrExprS env Us Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
  have hy₁ : env.HasType Us.length Δ₁.toCtx (.bvar 0) .nat := .bvar .zero
  have hz₁ := TrExprS.natZero (Us := Us) (Δ := Δ₁) hp hn
  have hs₁ := TrExprS.natSucc (Us := Us) (Δ := Δ₁) hp hn
  have hOne := hs₁.2.app hz₁.2
  have tOne := TrExprS.app hs₁.2 hz₁.2 hs₁.1 hz₁.1
  have hlOne := hl₁.app hOne
  simp only [VExpr.inst, VExpr.nat] at hlOne
  have tP := TrExprS.app hlOne hy₁ (.app hl₁ hOne tl₁ tOne) ty₁
  have hP : env.IsType Us.length Δ₁.toCtx P := ⟨_, hlOne.app hy₁⟩
  have tx₄ : TrExprS env Us Δ₄ (.bvar 0) (.bvar 0) := .bvar rfl
  have tfuel₄ : TrExprS env Us Δ₄ (.bvar 1) (.bvar 1) := .bvar rfl
  have hx₄ : env.HasType Us.length Δ₄.toCtx (.bvar 0) .nat := .bvar .zero
  have hfuel₄ : env.HasType Us.length Δ₄.toCtx (.bvar 1) .nat := .bvar (.succ .zero)
  have hs₄ := TrExprS.natSucc (Us := Us) (Δ := Δ₄) hp hn
  have hSucc := hs₄.2.app hx₄
  have tSucc := TrExprS.app hs₄.2 hx₄ hs₄.1 tx₄
  have hlSucc := hl₄.app hSucc
  simp only [VExpr.inst, VExpr.nat] at hlSucc
  have tBound := TrExprS.app hlSucc hfuel₄ (.app hl₄ hSucc tl₄ tSucc) tfuel₄
  have hBound : env.IsType Us.length Δ₄.toCtx
      (.app (.app le (.app .natSucc (.bvar 0))) (.bvar 1)) := ⟨_, hlSucc.app hfuel₄⟩
  exact .forallE natType (hP.forallE (natType.forallE (natType.forallE
    (hBound.forallE natType)))) trNat
    (.forallE hP (natType.forallE (natType.forallE (hBound.forallE natType))) tP
      (.forallE natType (natType.forallE (hBound.forallE natType)) trNat
        (.forallE natType (hBound.forallE natType) trNat
          (.forallE hBound natType tBound trNat))))

private theorem tr_natModLoopType {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (tl : TrExprS env Us [] q(@LE.le Nat _) le)
    (hl : env.HasType Us.length [] le (.forallE .nat (.forallE .nat (.sort .zero)))) :
    TrExprS env Us []
      q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)
      (VEnv.natDivLoopType le) := by
  let .forallE hdom hbody tdom tbody := tr_natDivLoopType henv hp hn tl hl
  exact .forallE hdom hbody tdom tbody

theorem checkNatDivLoop.WF {c : VContext} (hc : c.vlctx = [])
    (fail : ∀ {α}, M α)
    (hfail : ∀ {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hn : c.venv.contains ``Nat) (tl : c.TrExprS q(@LE.le Nat _) le)
    (hl : c.HasType le (.forallE .nat (.forallE .nat (.sort .zero)))) :
    (do
      unless ← isDefEq (← checkType q(Nat.div.go))
          q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail).WF c s
      fun _ _ => ∃ go, c.TrExprS q(Nat.div.go) go ∧ c.HasType go (VEnv.natDivLoopType le) := by
  have tl₀ : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le := by
    simpa only [VContext.TrExprS, hc] using tl
  have hl₀ : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hl
  have tty₀ := tr_natDivLoopType c.Ewf.ordered c.hasPrimitives hn tl₀ hl₀
  have tty : c.TrExprS
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)
      (VEnv.natDivLoopType le) := by
    simpa only [VContext.TrExprS, hc] using tty₀
  exact checkExprType.WF fail hfail (by simp [FVarsIn]) tty

theorem checkNatDivPrefix.WF {c : VContext} (hc : c.vlctx = [])
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False)
    (hb : c.venv.contains ``Bool) (hn : c.venv.contains ``Nat) :
    (do
      checkNatDivCondition fail
      unless ← isDefEq (← checkType q(Nat.div.go))
          q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail).WF c s
      fun _ _ => ∃ le go,
        c.TrExprS q(@LE.le Nat _) le ∧
        Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe) q(Nat.ble)
          q(fun n m {q : Prop} (H : _ → _ → q) =>
            H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))
          Reflection.defn₁ le ∧
        c.TrExprS q(Nat.div.go) go ∧ c.HasType go (VEnv.natDivLoopType le) := by
  refine (checkNatDivCondition.WF hc fail hfail hb hn).bind fun _ _ _ ⟨le, tl, hcond⟩ => ?_
  exact (checkNatDivLoop.WF hc fail hfail hn tl hcond.1).mono
    fun _ _ _ ⟨go, tg, hg⟩ => ⟨le, go, tl, hcond, tg, hg⟩

/-- Recover an argument at the domain of a supplied function translation.
The application's structural translation may use a definitionally equal domain. -/
private theorem tr_app_arg {env : VEnv} (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length Δ)
    (hf : env.HasType Us.length Δ.toCtx f' (.forallE A B))
    (tf : TrExpr env Us Δ f f') (tapp : TrExpr env Us Δ (.app f a) out) :
    ∃ a', TrExprS env Us Δ a a' ∧ env.HasType Us.length Δ.toCtx a' A ∧
      env.IsDefEq Us.length Δ.toCtx out (.app f' a') (B.inst a') := by
  have tactual := tapp
  obtain ⟨_, ts, _⟩ := tactual
  cases ts with
  | app hf₀ ha₀ tf₀ ta₀ =>
    have hctx := VLCtx.IsDefEq.refl henv.ordered hΔ
    have heq := (tf₀.trExpr henv.ordered hΔ).uniq henv hctx tf
    have hf₁ := (heq.of_r henv hΔ.toCtx hf).hasType.1
    obtain ⟨⟨_, hA⟩, _⟩ := (hf₀.uniqU henv hΔ.toCtx hf₁).forallE_inv henv hΔ.toCtx
    have ha₁ := ha₀.defeqU_r henv hΔ.toCtx ⟨_, hA⟩
    have tc := TrExpr.app henv hΔ.toCtx hf ha₁ tf (ta₀.trExpr henv.ordered hΔ)
    exact ⟨_, ta₀, ha₁, (tapp.uniq henv hctx tc).of_r henv hΔ.toCtx (hf.app ha₁)⟩

/-- Recover the carrier and branch types from the actual conditional translation. -/
theorem Condition.ReflectedNatNatChecked.ite_branches {c : VContext}
    {prop dec asBool proof A a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.ITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H)
    (tr : c.TrExprS r.type v.r) (ti : c.TrExprS r.ite v.i)
    (tactual : c.TrExprS
      (mkApp5 q(@_root_.ite.{1}) A (mkApp2 prop n m) (mkApp2 dec n m) a e) out) :
    ∃ A' a' e', c.TrExprS A A' ∧ c.TrExprS a a' ∧ c.TrExprS e e' ∧
      c.HasType A' (.sort (.succ .zero)) ∧ c.HasType a' A' ∧ c.HasType e' A' := by
  unfold ReflectedNatNatChecked at h
  simp only [VContext.TrExprS, VContext.HasType, hc, VLCtx.toCtx]
    at h tP tB tH tr ti tactual ⊢
  obtain ⟨_, bfun, proof', proofTy, dec', fun', ty', r', neg, d, t, f,
    tb, _, tproof, _, _, tdec, tchecked, hchecked, _⟩ := h
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  let .app hfa hearg tfa tearg := tactual
  let .app hfd haarg tfd taarg := tfa
  let .app hfp hdecarg tfp tdecarg := tfd
  have ⟨carrier, tfc⟩ : ∃ carrier, TrExprS c.venv c.lparams []
      (mkApp q(@_root_.ite.{1}) A) carrier := by
    cases tfp with
    | app _ _ tfc _ => exact ⟨_, tfc⟩
  obtain ⟨A', tA, hA⟩ := Reflection.ite_carrier c.Ewf r tr.closed hdc tr v.r_type ti
    tP v.prop_type tB v.bool_type tH v.proof_type tfc
  have hAc := hA.closedN c.Ewf.ordered trivial
  have tdecision := tr_reflectedDec_equiv c.Ewf tP.closed.1.1 tb.closed tproof.closed hdc
    tchecked tdec hchecked tdecarg
  have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfp hdecarg
    (tfp.trExpr c.Ewf.ordered hΔ) tdecision
  obtain ⟨tselector, hselector⟩ := tr_itePrefix (v.r_type.closedN c.Ewf.ordered trivial)
    v.i_type v.prop_type v.bool_type v.proof_type ti tP tB tH
  have tselector := TrExprS.app hselector hA tselector tA
  have hselector := hselector.app hA
  simp only [VExpr.inst, VExpr.instVar_zero, VExpr.instVar_succ,
    VExpr.lift, hAc.liftN_eq (Nat.zero_le _)] at hselector
  have texpanded := (tselector.trExpr c.Ewf.ordered hΔ).beta c.Ewf hΔ
    (Reflection.ite_beta_core r hdc tP.closed tB.closed tH.closed tA.closed)
  have eq := treplaced.uniq c.Ewf (.refl c.Ewf.ordered hΔ) texpanded
  have hcanonical := (eq.of_r c.Ewf trivial hselector).hasType.1
  have ⟨⟨_, hdom⟩, _⟩ := (hfd.uniqU c.Ewf trivial hcanonical).forallE_inv c.Ewf trivial
  have ha := haarg.defeqU_r c.Ewf trivial ⟨_, hdom⟩
  have hcanonical := hcanonical.app ha
  simp only [VExpr.inst, hAc.instN_eq (Nat.zero_le _)] at hcanonical
  have ⟨⟨_, hdom⟩, _⟩ := (hfa.uniqU c.Ewf trivial hcanonical).forallE_inv c.Ewf trivial
  exact ⟨A', _, _, tA, taarg, tearg, hA, ha, hearg.defeqU_r c.Ewf trivial ⟨_, hdom⟩⟩

theorem Condition.ReflectedNatNatChecked.ite_translate {c : VContext}
    {prop dec asBool proof A a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.ITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H) (ti : c.TrExprS r.ite v.i)
    (tA : c.TrExprS A A') (ta : c.TrExprS a a') (te : c.TrExprS e e')
    (hA : c.HasType A' (.sort (.succ .zero)))
    (ha : c.HasType a' A') (he : c.HasType e' A')
    (tactual : c.TrExprS
      (mkApp5 q(@_root_.ite.{1}) A (mkApp2 prop n m) (mkApp2 dec n m) a e) out) :
    c.TrExpr (mkApp5 q(@_root_.ite.{1}) A (mkApp2 prop n m) (mkApp2 dec n m) a e)
      (Reflection.iteApp v.i P B H A' a' e') := by
  unfold ReflectedNatNatChecked at h
  simp only [VContext.TrExprS, VContext.TrExpr, VContext.HasType, hc, VLCtx.toCtx]
    at h tP tB tH ti tA ta te hA ha he tactual ⊢
  obtain ⟨_, bfun, proof', proofTy, dec', fun', ty', r', neg, d, t, f,
    tb, _, tproof, _, _, tdec, tchecked, hchecked, _⟩ := h
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  let .app hfa hearg tfa tearg := tactual
  let .app hfd haarg tfd taarg := tfa
  let .app hfp hdecarg tfp tdecarg := tfd
  have tdecision := tr_reflectedDec_equiv c.Ewf tP.closed.1.1 tb.closed tproof.closed hdc
    tchecked tdec hchecked tdecarg
  have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfp hdecarg
    (tfp.trExpr c.Ewf.ordered hΔ) tdecision
  have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfd haarg treplaced
    (taarg.trExpr c.Ewf.ordered hΔ)
  have treplaced := TrExpr.app c.Ewf hΔ.toCtx hfa hearg treplaced
    (tearg.trExpr c.Ewf.ordered hΔ)
  have tselector := (tr_iteApp (v.r_type.closedN c.Ewf.ordered trivial)
    (hA.closedN c.Ewf.ordered trivial) v.i_type v.prop_type v.bool_type v.proof_type
    hA ha he ti tP tB tH tA ta te).1
  have texpanded := (tselector.trExpr c.Ewf.ordered hΔ).beta c.Ewf hΔ
    (Reflection.ite_beta r hdc tP.closed tB.closed tH.closed tA.closed)
  have eq := treplaced.uniq c.Ewf (.refl c.Ewf.ordered hΔ) texpanded
  have tactual := TrExprS.app hfa hearg (.app hfd haarg
    (.app hfp hdecarg tfp tdecarg) taarg) tearg
  exact (tactual.trExpr c.Ewf.ordered hΔ).defeq c.Ewf hΔ.toCtx eq

theorem Condition.ReflectedNatNatChecked.ite_eval {c : VContext}
    {prop dec asBool proof A a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec asBool proof r p') (hc : c.vlctx = [])
    (hdc : r.toDec.Closed)
    (v : Reflection.ITEInstance c.venv c.lparams.length P B H)
    (tP : c.TrExprS (mkApp2 prop n m) P)
    (tB : c.TrExprS (mkApp2 asBool n m) B)
    (tH : c.TrExprS (mkApp2 proof n m) H) (ti : c.TrExprS r.ite v.i)
    (tA : c.TrExprS A A') (ta : c.TrExprS a a') (te : c.TrExprS e e')
    (hA : c.HasType A' (.sort (.succ .zero)))
    (ha : c.HasType a' A') (he : c.HasType e' A')
    (tactual : c.TrExprS
      (mkApp5 q(@_root_.ite.{1}) A (mkApp2 prop n m) (mkApp2 dec n m) a e) out)
    (b : Bool) (hb : c.venv.IsDefEq c.lparams.length [] B (.boolLit b) .bool) :
    c.venv.IsDefEq c.lparams.length [] out (if b then a' else e') A' := by
  have tselector := h.ite_translate hc hdc v tP tB tH ti tA ta te hA ha he tactual
  simp only [VContext.TrExprS, VContext.TrExpr, VContext.HasType,
    hc, VLCtx.toCtx] at tactual tselector hA ha he ⊢
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have eq := (tactual.trExpr c.Ewf.ordered hΔ).uniq c.Ewf (.refl c.Ewf.ordered hΔ) tselector
  have hcomp := v.eval c.Ewf.ordered b hb hA ha he
  exact (eq.trans c.Ewf trivial ⟨_, hcomp⟩).of_r c.Ewf trivial hcomp.hasType.2

/-- Evaluate an ordering conditional at source inputs translated to literals. -/
theorem Condition.ReflectedNatNatChecked.natBle_ite_eval_inputs {c : VContext}
    {prop dec proof na nb a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r p')
    (hi : Reflection.ITEChecked c r) (hc : c.vlctx = []) (hu : c.lparams = [])
    (hdc : r.toDec.Closed) (tp : c.TrExprS prop p') (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (tactual : c.TrExprS
      (mkApp5 q(@_root_.ite.{1}) q(Nat) (mkApp2 prop na nb) (mkApp2 dec na nb) a e) out) :
    ∃ a' e', c.TrExprS a a' ∧ c.TrExprS e e' ∧
      c.HasType a' .nat ∧ c.HasType e' .nat ∧
      c.venv.IsDefEq c.lparams.length [] out (if Nat.ble n m then a' else e') .nat := by
  obtain ⟨B, H, v, tB, tH, tr, ti⟩ := h.ite_apply hi hc hdc tp tn hn tm hm
  have ht := h.1.app hn
  simp only [VExpr.inst, VExpr.nat] at ht
  have tP := TrExprS.app ht hm (.app h.1 hn tp tn) tm
  have hB : c.HasType B .bool := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using v.bool_type
  have hb := h.natBle_value_inputs hc hu n m tn tm hn hm tB hB
  obtain ⟨A', a', e', tA, ta, te, hA, ha, he⟩ := h.ite_branches hc hdc v tP tB tH tr ti tactual
  simp only [VContext.TrExprS, hc] at tA
  cases tA with
  | const hci hlevels hlen =>
    cases hlevels
    have tA : c.TrExprS q(Nat) .nat := by
      simpa only [VContext.TrExprS, hc] using (TrExprS.const hci rfl hlen)
    exact ⟨a', e', ta, te, ha, he,
      h.ite_eval hc hdc v tP tB tH ti tA ta te hA ha he tactual (Nat.ble n m) hb⟩

/-- Translate a checked loop application at concrete data arguments, recovering
the two proof arguments at the canonical positivity and fuel-bound types. -/
theorem tr_natDivLoopApp {env : VEnv} (henv : env.WF)
    (hlc : le.ClosedN)
    (hg : env.HasType Us.length [] go (VEnv.natDivLoopType le))
    (tg : TrExpr env Us [] g go)
    (ty : TrExpr env Us [] ey (.natLit y))
    (tf : TrExpr env Us [] ef (.natLit fuel))
    (ta : TrExpr env Us [] ea (.natLit a))
    (hy : env.HasType Us.length [] (.natLit y) .nat)
    (hf : env.HasType Us.length [] (.natLit fuel) .nat)
    (ha : env.HasType Us.length [] (.natLit a) .nat)
    (tactual : TrExpr env Us [] (mkApp5 g ey ehy ef ea eha) out) :
    ∃ py pa, TrExprS env Us [] ehy py ∧ TrExprS env Us [] eha pa ∧
      env.HasType Us.length [] py (VEnv.natLeExpr le 1 y) ∧
      env.HasType Us.length [] pa (VEnv.natLeExpr le (a + 1) fuel) ∧
      env.IsDefEq Us.length [] out (VEnv.natDivLoopExpr go y py fuel a pa) .nat := by
  have hΔ : VLCtx.WF env Us.length [] := trivial
  have tactual' := tactual
  obtain ⟨_, ts, _⟩ := tactual'
  let .app _ _ t₄ _ := ts
  let .app _ _ t₃ _ := t₄
  let .app _ _ t₂ _ := t₃
  have tg₁ := TrExpr.app henv hΔ.toCtx hg hy tg ty
  have hg₁ := hg.app hy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
    VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd,
    VExpr.natLit, VExpr.natSucc, VExpr.natZero, VExpr.nat] at hg₁
  obtain ⟨py, tpy, hpy, eq₂⟩ :=
    tr_app_arg henv hΔ hg₁ tg₁ (t₂.trExpr henv.ordered hΔ)
  have tg₂ := (t₂.trExpr henv.ordered hΔ).defeq henv hΔ.toCtx eq₂.toU
  have hg₂ := hg₁.app hpy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_lower, VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd] at hg₂
  have tg₃ := TrExpr.app henv hΔ.toCtx hg₂ hf tg₂ tf
  have hg₃ := hg₂.app hf
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_zero, VExpr.instVar_lower, VExpr.lift, Nat.reduceAdd] at hg₃
  have tg₄ := TrExpr.app henv hΔ.toCtx hg₃ ha tg₃ ta
  have hg₄ := hg₃.app ha
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_zero,
    VExpr.inst_lift] at hg₄
  obtain ⟨pa, tpa, hpa, eq₅⟩ := tr_app_arg henv hΔ hg₄ tg₄ tactual
  exact ⟨py, pa, tpy, tpa, hpy, hpa, eq₅⟩

/-- A closed false branch does not depend on the reflected proof binder. -/
theorem Condition.ReflectedNatNatChecked.natBle_dite_false_inputs {c : VContext}
    {prop dec proof na nb a e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (n m : Nat)
    (tn : c.TrExprS na (.natLit n)) (tm : c.TrExprS nb (.natLit m))
    (hn : c.HasType (.natLit n) .nat) (hm : c.HasType (.natLit m) .nat)
    (te : c.TrExprS e e') (he : c.HasType e' .nat) (hlt : m < n)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop na nb) (mkApp2 dec na nb)
        (.lam0 (mkApp2 prop na nb) a)
        (.lam0 (mkApp q(Not) (mkApp2 prop na nb)) e)) out) :
    c.venv.IsDefEq c.lparams.length [] out e' .nat := by
  obtain ⟨_, w, _, _, _, _, tbody⟩ :=
    h.natBle_dite_body_inputs hc hu hdc tp n m tn tm hn hm tactual
  have hble : Nat.ble n m = false :=
    Bool.eq_false_iff.2 fun hle => (Nat.not_le_of_gt hlt) (Nat.le_of_ble_eq_true hle)
  simp only [hble, Bool.false_eq_true, if_false] at tbody
  simp only [VContext.TrExprS, VContext.TrExpr, VContext.HasType, hc, VLCtx.toCtx]
    at te he tbody
  rw [Expr.instantiate1'_eq_self (Nat.le_trans te.closed.looseBVarRange_le (Nat.zero_le _))]
    at tbody
  exact (tbody.uniq c.Ewf (.refl c.Ewf.ordered
    (show VLCtx.WF c.venv c.lparams.length [] from trivial))
    (te.trExpr (Us := c.lparams) (Δ := []) c.Ewf.ordered
      (show VLCtx.WF c.venv c.lparams.length [] from trivial))).of_r c.Ewf trivial he

private theorem Condition.ReflectedNatNatChecked.natLoop_start {c : VContext}
    {prop dec proof g ey ea eha e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (ty : c.TrExprS ey (.natLit y)) (ta : c.TrExprS ea (.natLit a))
    (hbound : eha.Closed) (hpos : 0 < y)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop q(Nat.succ Nat.zero) ey)
        (mkApp2 dec q(Nat.succ Nat.zero) ey)
        (.lam0 (mkApp2 prop q(Nat.succ Nat.zero) ey)
          (mkApp5 g ey (.bvar 0) (mkApp q(Nat.succ) ea) ea eha))
        (.lam0 (mkApp q(Not) (mkApp2 prop q(Nat.succ Nat.zero) ey)) e)) out) :
    ∃ py pa, c.TrExprS eha pa ∧
      c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) ∧
      c.venv.HasType c.lparams.length [] pa (VEnv.natLeExpr le (a + 1) (a + 1)) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (VEnv.natDivLoopExpr go y py (a + 1) a pa) .nat := by
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have tOne₀ := TrExprS.app hs.2 hz.2 hs.1 hz.1
  have tOne : c.TrExprS q(Nat.succ Nat.zero) (.natLit 1) := by
    simpa only [VContext.TrExprS, hc] using tOne₀
  have hOne : c.HasType (.natLit 1) .nat := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hs.2.app hz.2
  have hy : c.HasType (.natLit y) .nat := c.hasPrimitives.natLit_type hnat y
  obtain ⟨_, w, _, _, _, _, tbody⟩ :=
    h.natBle_dite_body_inputs hc hu hdc tp 1 y tOne ty hOne hy tactual
  have hble : Nat.ble 1 y = true := Nat.ble_eq_true_of_le hpos
  simp only [hble, if_true] at tbody
  simp only [VContext.TrExprS, hc] at tg ty ta
  have hgi (k : Nat) : g.instantiate1' w k = g :=
    Expr.instantiate1'_eq_self (Nat.le_trans tg.closed.looseBVarRange_le (Nat.zero_le _))
  have hyi (k : Nat) : ey.instantiate1' w k = ey :=
    Expr.instantiate1'_eq_self (Nat.le_trans ty.closed.looseBVarRange_le (Nat.zero_le _))
  have hai (k : Nat) : ea.instantiate1' w k = ea :=
    Expr.instantiate1'_eq_self (Nat.le_trans ta.closed.looseBVarRange_le (Nat.zero_le _))
  have hbi (k : Nat) : eha.instantiate1' w k = eha :=
    Expr.instantiate1'_eq_self (Nat.le_trans hbound.looseBVarRange_le (Nat.zero_le _))
  simp only [Expr.instantiate1', hgi, hyi, hai, hbi,
    Expr.liftLooseBVars_zero, Nat.reduceSub, Nat.reduceLT, if_true, if_false] at tbody
  have tSucc := TrExprS.app hs.2 (c.hasPrimitives.natLit_type hnat a) hs.1 ta
  have hle : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using h.1
  have hg₀ : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hg
  have ⟨py', pa, _, tpa, hpy', hpa, heq⟩ :=
    tr_natDivLoopApp (ehy := w) (eha := eha) (out := out) c.Ewf
    (hle.closedN c.Ewf.ordered trivial) hg₀ (tg.trExpr c.Ewf.ordered hΔ)
    (ty.trExpr c.Ewf.ordered hΔ) (tSucc.trExpr c.Ewf.ordered hΔ)
    (ta.trExpr c.Ewf.ordered hΔ) (c.hasPrimitives.natLit_type hnat y)
    (c.hasPrimitives.natLit_type hnat (a + 1)) (c.hasPrimitives.natLit_type hnat a)
    (by simpa only [VContext.TrExpr, hc] using tbody)
  refine ⟨py', pa, ?_, hpy', hpa, heq⟩
  simpa only [VContext.TrExprS, hc] using tpa

/-- The positive entry branch of division calls the loop with successor fuel.
The bound proof is recovered from the checked application, not postulated. -/
theorem Condition.ReflectedNatNatChecked.natDiv_start {c : VContext}
    {prop dec proof g ey ea eha : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (ty : c.TrExprS ey (.natLit y)) (ta : c.TrExprS ea (.natLit a))
    (hbound : eha.Closed) (hpos : 0 < y)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop q(Nat.succ Nat.zero) ey)
        (mkApp2 dec q(Nat.succ Nat.zero) ey)
        (.lam0 (mkApp2 prop q(Nat.succ Nat.zero) ey)
          (mkApp5 g ey (.bvar 0) (mkApp q(Nat.succ) ea) ea eha))
        (.lam0 (mkApp q(Not) (mkApp2 prop q(Nat.succ Nat.zero) ey)) q(Nat.zero))) out) :
    ∃ py pa, c.TrExprS eha pa ∧
      c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) ∧
      c.venv.HasType c.lparams.length [] pa (VEnv.natLeExpr le (a + 1) (a + 1)) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (VEnv.natDivLoopExpr go y py (a + 1) a pa) .nat :=
  h.natLoop_start hc hu hdc tp hnat hg tg ty ta hbound hpos tactual

/-- The positive inner modulo branch calls the same dependent loop shape. -/
theorem Condition.ReflectedNatNatChecked.natMod_start {c : VContext}
    {prop dec proof g ey ea eha : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (ty : c.TrExprS ey (.natLit y)) (ta : c.TrExprS ea (.natLit a))
    (hbound : eha.Closed) (hpos : 0 < y)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop q(Nat.succ Nat.zero) ey)
        (mkApp2 dec q(Nat.succ Nat.zero) ey)
        (.lam0 (mkApp2 prop q(Nat.succ Nat.zero) ey)
          (mkApp5 g ey (.bvar 0) (mkApp q(Nat.succ) ea) ea eha))
        (.lam0 (mkApp q(Not) (mkApp2 prop q(Nat.succ Nat.zero) ey)) ea)) out) :
    ∃ py pa, c.TrExprS eha pa ∧
      c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) ∧
      c.venv.HasType c.lparams.length [] pa (VEnv.natLeExpr le (a + 1) (a + 1)) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (VEnv.natDivLoopExpr go y py (a + 1) a pa) .nat :=
  h.natLoop_start hc hu hdc tp hnat hg tg ty ta hbound hpos tactual

/-- The nested modulo entry conditional at closed source data arguments. -/
def natModEntryAt (prop dec g x y bound : Expr) : Expr :=
  let sx := mkApp q(Nat.succ) x
  let p := mkApp2 prop q(Nat.succ Nat.zero) y
  mkApp5 q(@_root_.ite.{1}) q(Nat) (mkApp2 prop y sx) (mkApp2 dec y sx)
    (mkApp4 q(@dite Nat) p (mkApp2 dec q(Nat.succ Nat.zero) y)
      (.lam0 p (mkApp5 g y (.bvar 0) (mkApp q(Nat.succ) sx) sx bound))
      (.lam0 (mkApp q(Not) p) sx)) sx

theorem Condition.ReflectedNatNatChecked.natMod_entry_start {c : VContext}
    {prop dec proof g ex ey bound : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hi : Reflection.ITEChecked c r) (hc : c.vlctx = []) (hu : c.lparams = [])
    (hdc : r.toDec.Closed) (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (tx : c.TrExprS ex (.natLit a)) (ty : c.TrExprS ey (.natLit y))
    (hbound : bound.Closed) (hpos : 0 < y) (hle : y ≤ a + 1)
    (tactual : c.TrExprS (natModEntryAt prop dec g ex ey bound) out) :
    ∃ py pa, c.TrExprS bound pa ∧
      c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) ∧
      c.venv.HasType c.lparams.length [] pa (VEnv.natLeExpr le (a + 2) (a + 2)) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (VEnv.natDivLoopExpr go y py (a + 2) (a + 1) pa) .nat := by
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have tsx : c.TrExprS (mkApp q(Nat.succ) ex) (.natLit (a + 1)) := by
    simp only [VContext.TrExprS, hc] at tx ⊢
    exact .app hs.2 (c.hasPrimitives.natLit_type hnat a) hs.1 tx
  have hSX : c.HasType (.natLit (a + 1)) .nat := c.hasPrimitives.natLit_type hnat _
  have hy : c.HasType (.natLit y) .nat := c.hasPrimitives.natLit_type hnat _
  unfold natModEntryAt at tactual
  obtain ⟨inner, other, tinner, _, _, _, eq⟩ :=
    h.natBle_ite_eval_inputs hi hc hu hdc tp y (a + 1) ty tsx hy hSX tactual
  have hble : Nat.ble y (a + 1) = true := Nat.ble_eq_true_of_le hle
  simp only [hble, if_true] at eq
  obtain ⟨py, pa, tpa, hpy, hpa, eqInner⟩ :=
    h.natMod_start hc hu hdc tp hnat hg tg ty tsx hbound hpos tinner
  exact ⟨py, pa, tpa, hpy, by simpa only [Nat.add_assoc] using hpa,
    by simpa only [Nat.add_assoc] using eq.trans eqInner⟩

theorem Condition.ReflectedNatNatChecked.natMod_entry_stop {c : VContext}
    {prop dec proof g ex ey bound : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hi : Reflection.ITEChecked c r) (hc : c.vlctx = []) (hu : c.lparams = [])
    (hdc : r.toDec.Closed) (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (tx : c.TrExprS ex (.natLit a)) (ty : c.TrExprS ey (.natLit y))
    (hstop : y = 0 ∨ a + 1 < y)
    (tactual : c.TrExprS (natModEntryAt prop dec g ex ey bound) out) :
    c.venv.IsDefEq c.lparams.length [] out (.natLit (a + 1)) .nat := by
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have tsx : c.TrExprS (mkApp q(Nat.succ) ex) (.natLit (a + 1)) := by
    simp only [VContext.TrExprS, hc] at tx ⊢
    exact .app hs.2 (c.hasPrimitives.natLit_type hnat a) hs.1 tx
  have hSX : c.HasType (.natLit (a + 1)) .nat := c.hasPrimitives.natLit_type hnat _
  have hy : c.HasType (.natLit y) .nat := c.hasPrimitives.natLit_type hnat _
  unfold natModEntryAt at tactual
  obtain ⟨inner, other, tinner, tother, _, _, eq⟩ :=
    h.natBle_ite_eval_inputs hi hc hu hdc tp y (a + 1) ty tsx hy hSX tactual
  rcases hstop with rfl | hlt
  · have hble : Nat.ble 0 (a + 1) = true := Nat.ble_eq_true_of_le (Nat.zero_le _)
    simp only [hble, if_true] at eq
    have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
    have tOne : c.TrExprS q(Nat.succ Nat.zero) (.natLit 1) := by
      simpa only [VContext.TrExprS, hc] using TrExprS.app hs.2 hz.2 hs.1 hz.1
    exact eq.trans (h.natBle_dite_false_inputs hc hu hdc tp 1 0 tOne ty
      (c.hasPrimitives.natLit_type hnat 1) hy tsx hSX (Nat.zero_lt_succ _) tinner)
  · have hble : Nat.ble y (a + 1) = false :=
      Bool.eq_false_iff.2 fun hle => (Nat.not_le_of_gt hlt) (Nat.le_of_ble_eq_true hle)
    simp only [hble, Bool.false_eq_true, if_false] at eq
    have heq := tother.uniq c.Ewf (.refl c.Ewf.ordered c.Δwf) tsx
    have heq := heq.of_r c.Ewf c.Δwf.toCtx hSX
    simp only [hc, VLCtx.toCtx] at heq
    exact eq.trans heq

/-- A zero divisor selects the zero-valued entry branch, including when the
comparison uses the constructor-form expression for one. -/
theorem Condition.ReflectedNatNatChecked.natDiv_zero {c : VContext}
    {prop dec proof ey a : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (ty : c.TrExprS ey (.natLit 0))
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop q(Nat.succ Nat.zero) ey)
        (mkApp2 dec q(Nat.succ Nat.zero) ey)
        (.lam0 (mkApp2 prop q(Nat.succ Nat.zero) ey) a)
        (.lam0 (mkApp q(Not) (mkApp2 prop q(Nat.succ Nat.zero) ey)) q(Nat.zero))) out) :
    c.venv.IsDefEq c.lparams.length [] out .natZero .nat := by
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have tOne : c.TrExprS q(Nat.succ Nat.zero) (.natLit 1) := by
    simpa only [VContext.TrExprS, hc] using TrExprS.app hs.2 hz.2 hs.1 hz.1
  exact h.natBle_dite_zero_inputs hc hu hdc tp hnat 1 0 tOne ty
    (c.hasPrimitives.natLit_type hnat 1) (c.hasPrimitives.natLit_type hnat 0)
    (Nat.zero_lt_succ 0) tactual

private theorem tr_natSub_inputs {env : VEnv} (henv : env.WF)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (hsub : env.contains ``Nat.sub)
    (ta : TrExprS env [] [] ea (.natLit a))
    (tb : TrExprS env [] [] eb (.natLit b)) :
    TrExpr env [] [] (mkApp2 q(Nat.sub) ea eb) (.natLit (a - b)) := by
  have hΔ : VLCtx.WF env 0 [] := trivial
  have hf := hp.natSubType hsub
  obtain ⟨_, hci, _, hlen⟩ := hf.const_inv henv.ordered trivial
  have tf : TrExprS env [] [] q(Nat.sub) (.const ``Nat.sub []) := .const hci rfl hlen
  have ha := hp.natLit_type (U := 0) (Γ := []) hn a
  have hb := hp.natLit_type (U := 0) (Γ := []) hn b
  have hf₁ := hf.app ha
  simp only [VExpr.inst, VExpr.nat] at hf₁
  have tr : TrExprS env [] [] (mkApp2 q(Nat.sub) ea eb)
      (.app (.app (.const ``Nat.sub []) (.natLit a)) (.natLit b)) :=
    .app hf₁ hb (.app hf ha tf ta) tb
  exact (tr.trExpr (Us := []) (Δ := []) henv.ordered hΔ).defeq henv trivial
    (hp.natSub hsub a b)

/-- Reduce the recursive branch, evaluate its subtraction, and retain the new
fuel-bound witness. Proof irrelevance restores the supplied positivity proof. -/
theorem Condition.ReflectedNatNatChecked.natDiv_step {c : VContext}
    {prop dec proof g ey ehy ef ea eha : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (ty : c.TrExprS ey (.natLit y)) (tf : c.TrExprS ef (.natLit fuel))
    (ta : c.TrExprS ea (.natLit a)) (thy : c.TrExprS ehy py)
    (hpy : c.HasType py (VEnv.natLeExpr le 1 y)) (hle : y ≤ a)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop ey ea) (mkApp2 dec ey ea)
        (.lam0 (mkApp2 prop ey ea)
          (mkApp q(Nat.succ) (mkApp5 g ey ehy ef (mkApp2 q(Nat.sub) ea ey) eha)))
        (.lam0 (mkApp q(Not) (mkApp2 prop ey ea)) q(Nat.zero))) out) :
    ∃ pa, c.venv.HasType c.lparams.length [] pa
        (VEnv.natLeExpr le (a - y + 1) fuel) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (.app .natSucc (VEnv.natDivLoopExpr go y py fuel (a - y) pa)) .nat := by
  have hy : c.HasType (.natLit y) .nat := c.hasPrimitives.natLit_type hnat y
  have ha : c.HasType (.natLit a) .nat := c.hasPrimitives.natLit_type hnat a
  obtain ⟨_, w, _, _, _, _, tbody⟩ :=
    h.natBle_dite_body_inputs hc hu hdc tp y a ty ta hy ha tactual
  have hble : Nat.ble y a = true := Nat.ble_eq_true_of_le hle
  simp only [hble, if_true] at tbody
  simp only [VContext.TrExprS, hc] at tg ty tf ta thy
  have hgi (k : Nat) : g.instantiate1' w k = g :=
    Expr.instantiate1'_eq_self (Nat.le_trans tg.closed.looseBVarRange_le (Nat.zero_le _))
  have hyi (k : Nat) : ey.instantiate1' w k = ey :=
    Expr.instantiate1'_eq_self (Nat.le_trans ty.closed.looseBVarRange_le (Nat.zero_le _))
  have hfyi (k : Nat) : ehy.instantiate1' w k = ehy :=
    Expr.instantiate1'_eq_self (Nat.le_trans thy.closed.looseBVarRange_le (Nat.zero_le _))
  have hfi (k : Nat) : ef.instantiate1' w k = ef :=
    Expr.instantiate1'_eq_self (Nat.le_trans tf.closed.looseBVarRange_le (Nat.zero_le _))
  have hai (k : Nat) : ea.instantiate1' w k = ea :=
    Expr.instantiate1'_eq_self (Nat.le_trans ta.closed.looseBVarRange_le (Nat.zero_le _))
  simp only [Expr.instantiate1', hgi, hyi, hfyi, hfi, hai] at tbody
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := []) c.hasPrimitives hnat
  have ⟨loop, tloop, _, eqSucc⟩ :=
    tr_app_arg (a := mkApp5 g ey ehy ef (mkApp2 q(Nat.sub) ea ey) (eha.instantiate1' w))
      (out := out) c.Ewf hΔ hs.2
    (hs.1.trExpr c.Ewf.ordered hΔ) (by simpa only [VContext.TrExpr, hc] using tbody)
  have tsub : TrExpr c.venv c.lparams [] (mkApp2 q(Nat.sub) ea ey) (.natLit (a - y)) := by
    have ta₀ : TrExprS c.venv [] [] ea (.natLit a) := by simpa only [hu] using ta
    have ty₀ : TrExprS c.venv [] [] ey (.natLit y) := by simpa only [hu] using ty
    simpa only [hu] using tr_natSub_inputs c.Ewf c.hasPrimitives hnat hsub ta₀ ty₀
  have hleTy : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using h.1
  have hg₀ : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hg
  have hpy₀ : c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hpy
  obtain ⟨py', pa, _, _, hpy', hpa, eqLoop⟩ :=
    tr_natDivLoopApp (out := loop) c.Ewf (hleTy.closedN c.Ewf.ordered trivial) hg₀
      (tg.trExpr c.Ewf.ordered hΔ) (ty.trExpr c.Ewf.ordered hΔ)
      (tf.trExpr c.Ewf.ordered hΔ) tsub
      (c.hasPrimitives.natLit_type hnat y) (c.hasPrimitives.natLit_type hnat fuel)
      (c.hasPrimitives.natLit_type hnat (a - y)) (tloop.trExpr c.Ewf.ordered hΔ)
  have eqProof := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hnat
    hleTy hg₀ hpy' hpy₀ hpa hpa
  exact ⟨pa, hpa, eqSucc.trans (hs.2.appDF (eqLoop.trans eqProof))⟩

/-- Evaluate the selected modulo recursion and recover its new fuel witness. -/
theorem Condition.ReflectedNatNatChecked.natMod_step {c : VContext}
    {prop dec proof g ey ehy ef ea eha e : Expr} {r : Reflection}
    (h : ReflectedNatNatChecked c prop dec q(Nat.ble) proof r le)
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (tp : c.TrExprS prop le) (hnat : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (hg : c.HasType go (VEnv.natDivLoopType le)) (tg : c.TrExprS g go)
    (ty : c.TrExprS ey (.natLit y)) (tf : c.TrExprS ef (.natLit fuel))
    (ta : c.TrExprS ea (.natLit a)) (thy : c.TrExprS ehy py)
    (hpy : c.HasType py (VEnv.natLeExpr le 1 y)) (hle : y ≤ a)
    (tactual : c.TrExprS
      (mkApp4 q(@dite Nat) (mkApp2 prop ey ea) (mkApp2 dec ey ea)
        (.lam0 (mkApp2 prop ey ea) (mkApp5 g ey ehy ef (mkApp2 q(Nat.sub) ea ey) eha))
        (.lam0 (mkApp q(Not) (mkApp2 prop ey ea)) e)) out) :
    ∃ pa, c.venv.HasType c.lparams.length [] pa
        (VEnv.natLeExpr le (a - y + 1) fuel) ∧
      c.venv.IsDefEq c.lparams.length [] out
        (VEnv.natDivLoopExpr go y py fuel (a - y) pa) .nat := by
  have hy : c.HasType (.natLit y) .nat := c.hasPrimitives.natLit_type hnat y
  have ha : c.HasType (.natLit a) .nat := c.hasPrimitives.natLit_type hnat a
  obtain ⟨_, w, _, _, _, _, tbody⟩ :=
    h.natBle_dite_body_inputs hc hu hdc tp y a ty ta hy ha tactual
  have hble : Nat.ble y a = true := Nat.ble_eq_true_of_le hle
  simp only [hble, if_true] at tbody
  simp only [VContext.TrExprS, hc] at tg ty tf ta thy
  have hinst (e : Expr) (he : e.Closed) (k : Nat) : e.instantiate1' w k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  simp only [Expr.instantiate1', hinst _ tg.closed, hinst _ ty.closed,
    hinst _ thy.closed, hinst _ tf.closed, hinst _ ta.closed] at tbody
  have hΔ : VLCtx.WF c.venv c.lparams.length [] := trivial
  have tsub : TrExpr c.venv c.lparams [] (mkApp2 q(Nat.sub) ea ey) (.natLit (a - y)) := by
    have ta₀ : TrExprS c.venv [] [] ea (.natLit a) := by simpa only [hu] using ta
    have ty₀ : TrExprS c.venv [] [] ey (.natLit y) := by simpa only [hu] using ty
    simpa only [hu] using tr_natSub_inputs c.Ewf c.hasPrimitives hnat hsub ta₀ ty₀
  have hleTy : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using h.1
  have hg₀ : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hg
  have hpy₀ : c.venv.HasType c.lparams.length [] py (VEnv.natLeExpr le 1 y) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hpy
  obtain ⟨py', pa, _, _, hpy', hpa, eqLoop⟩ :=
    tr_natDivLoopApp c.Ewf (hleTy.closedN c.Ewf.ordered trivial) hg₀
      (tg.trExpr c.Ewf.ordered hΔ) (ty.trExpr c.Ewf.ordered hΔ)
      (tf.trExpr c.Ewf.ordered hΔ) tsub
      (c.hasPrimitives.natLit_type hnat y) (c.hasPrimitives.natLit_type hnat fuel)
      (c.hasPrimitives.natLit_type hnat (a - y))
      (by simpa only [VContext.TrExpr, hc] using tbody)
  have eqProof := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hnat
    hleTy hg₀ hpy' hpy₀ hpa hpa
  exact ⟨pa, hpa, eqLoop.trans eqProof⟩

/-- Extract a checked equation under a fresh local as an open equation, retaining
the structural translation produced by checking the right-hand side. -/
private theorem withLocalDecl_checkEq.WF {c : VContext}
    {ty lhs rhs : Expr}
    (hty : c.TrExprS ty ty') (hty' : c.IsType ty')
    (tleft : TrExprS c.venv c.lparams ((none, .vlam ty') :: c.vlctx) lhs lhs')
    (hleft : c.venv.HasType c.lparams.length (ty' :: c.vlctx.toCtx) lhs' A)
    (hright : rhs.FVarsIn (· ∈ c.vlctx.fvars))
    (l r : Expr → Expr)
    (hl : ∀ id, l (.fvar id) = lhs.instantiate1' (.fvar id))
    (hr : ∀ id, r (.fvar id) = rhs.instantiate1' (.fvar id))
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl name bi ty fun x => do
      _ ← checkType (r x)
      unless ← isDefEq (l x) (r x) do fail).WF c s
      fun _ _ => ∃ out,
        TrExprS c.venv c.lparams ((none, .vlam ty') :: c.vlctx) rhs out ∧
        c.venv.IsDefEq c.lparams.length (ty' :: c.vlctx.toCtx) lhs' out A := by
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl hty hty' (.rfl (s := s)) fun id cwf' s' _ _ => ?_
  rw [hl id, hr id]
  let c' := c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf')
  have tleft₁ : c'.TrExprS (lhs.instantiate1' (.fvar id)) lhs' :=
    tleft.inst_fvar c.Ewf.ordered c'.Δwf
  have hleft₁ : c'.HasType lhs' A := hleft
  have hright₁ : rhs.FVarsIn (· ∈ c'.vlctx.fvars) := hright.fvars_cons
  have hx : (.fvar id : Expr).FVarsIn (· ∈ c'.vlctx.fvars) := by
    simp [FVarsIn, c', VContext.withMLC, MLCtx.vlctx, VLCtx.fvars]
  refine (checkType.WF (c := c') (hright₁.instantiate1 hx)).bind
    fun _ _ _ ⟨out, _, _, tout, _, _⟩ => ?_
  refine (isDefEq.WF (c := c') tleft₁ tout).bind fun b _ _ heq => ?_
  cases b
  · exact hfail.mono fun _ _ _ h => h.elim
  · simp only [if_true]
    apply M.WF.pure
    have hnot : id ∉ c.vlctx.fvars := (c'.Δwf.fvwf.2 id ty.fvarsList rfl).1
    have hsc : rhs.FVarsIn (· ≠ id) := hright.mono fun fv hmem he => hnot (he ▸ hmem)
    exact ⟨out, tout.uninstantiate hsc, (heq rfl).of_l c'.Ewf c'.Δwf.toCtx hleft₁⟩

/-- Division's entry conditional in the open context `[y, x]`. -/
def natDivEntryBody : Expr :=
  let p := mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.bvar 0)
  mkApp4 q(@dite Nat) p (mkApp2 q(Nat.decLe) q(Nat.succ Nat.zero) (.bvar 0))
    (.lam0 p (mkApp5 q(Nat.div.go) (.bvar 1) (.bvar 0)
      (mkApp q(Nat.succ) (.bvar 2)) (.bvar 2) (mkApp q(Nat.lt_succ_self) (.bvar 2))))
    (.lam0 (mkApp q(Not) p) q(Nat.zero))

theorem natDivEntryBody.instantiate_literals (a y : Nat) :
    (natDivEntryBody.instantiate1' (.lit (.natVal a)) 1).instantiate1' (.lit (.natVal y)) =
      Condition.natLE.dite #[q(Nat.succ Nat.zero), .lit (.natVal y)]
        (mkApp5 q(Nat.div.go) (.lit (.natVal y)) (.bvar 0)
          (mkApp q(Nat.succ) (.lit (.natVal a))) (.lit (.natVal a))
          (mkApp q(Nat.lt_succ_self) (.lit (.natVal a)))) q(Nat.zero) := by
  simp only [natDivEntryBody, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
  rfl

/-- Instantiate the entry checker output without losing its structural source
translation, which is needed to evaluate the dependent conditional. -/
theorem natDivEntryBody.at_literals {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (hfc : f.ClosedN)
    (tout : TrExprS env Us [(none, .vlam .nat), (none, .vlam .nat)] natDivEntryBody out)
    (heq : env.IsDefEq Us.length [.nat, .nat]
      (.app (.app f (.bvar 1)) (.bvar 0)) out .nat) (a y : Nat) :
    TrExprS env Us []
      (Condition.natLE.dite #[q(Nat.succ Nat.zero), .lit (.natVal y)]
        (mkApp5 q(Nat.div.go) (.lit (.natVal y)) (.bvar 0)
          (mkApp q(Nat.succ) (.lit (.natVal a))) (.lit (.natVal a))
          (mkApp q(Nat.lt_succ_self) (.lit (.natVal a)))) q(Nat.zero))
      ((out.inst (.natLit a) 1).inst (.natLit y)) ∧
    env.IsDefEq Us.length [] (.app (.app f (.natLit a)) (.natLit y))
      ((out.inst (.natLit a) 1).inst (.natLit y)) .nat := by
  have ta := TrExprS.natLit (Us := Us) (Δ := []) hp hn a
  have ty := TrExprS.natLit (Us := Us) (Δ := []) hp hn y
  have tout₁ := ta.1.instN henv ta.2 (.succ .zero) tout
  have heq₁ := heq.instN henv ta.2 (.succ .zero)
  simp only [VExpr.nat] at tout₁
  have tout₂ := tout₁.inst henv ty.2 ty.1
  have heq₂ := heq₁.instN henv ty.2 .zero
  refine ⟨?_, ?_⟩
  · simpa only [instantiate_literals] using tout₂
  · simpa only [VExpr.inst, hfc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
      VExpr.instVar_zero, VExpr.instVar_lower, VExpr.nat,
      (ta.2.closedN henv trivial).instN_eq (Nat.zero_le _),
      (ta.2.closedN henv trivial).liftN_eq (Nat.zero_le _)] using heq₂

/-- Evaluate both entry branches of the checked open equation. The loop's own
equations are separate obligations. -/
theorem natDivEntryBody.spec {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (tg : c.TrExprS q(Nat.div.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (tout : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
      natDivEntryBody out)
    (heq : c.venv.IsDefEq c.lparams.length [.nat, .nat]
      (.app (.app f (.bvar 1)) (.bvar 0)) out .nat) :
    VEnv.NatDivEntrySpec c.venv f go le := by
  have hfc := hf.closedN c.Ewf.ordered trivial
  have tlit (n : Nat) : c.TrExprS (.lit (.natVal n)) (.natLit n) := by
    simpa only [VContext.TrExprS, hc] using
      (TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hn n).1
  constructor
  · intro a
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn hfc tout heq a 0
    rw [← hc] at tr
    have hz := h.natDiv_zero hc hu hdc tp hn (tlit 0) tr
    simpa only [hu, List.length_nil, VExpr.natLit] using eq.trans hz
  · intro a y hy
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn hfc tout heq a y
    rw [← hc] at tr
    have hbound : (mkApp q(Nat.lt_succ_self) (.lit (.natVal a))).Closed := by
      simp [Closed]
    obtain ⟨py, pa, _, hpy, hpa, hs⟩ :=
      h.natDiv_start hc hu hdc tp hn hg tg (tlit y) (tlit a) hbound hy tr
    exact ⟨py, pa, (by simpa only [hu, List.length_nil] using hpy),
      (by simpa only [hu, List.length_nil] using hpa),
      (by simpa only [hu, List.length_nil] using eq.trans hs)⟩

/-- Modulo's nested entry conditional in the open context `[y, x]`. The inner
dependent branches shift both data variables under their proof binder. -/
def natModEntryBody : Expr :=
  let sx := mkApp q(Nat.succ) (.bvar 1)
  let p := mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.bvar 0)
  let sx' := mkApp q(Nat.succ) (.bvar 2)
  mkApp5 q(@_root_.ite.{1}) q(Nat)
    (mkApp2 q(@LE.le Nat _) (.bvar 0) sx) (mkApp2 q(Nat.decLe) (.bvar 0) sx)
    (mkApp4 q(@dite Nat) p (mkApp2 q(Nat.decLe) q(Nat.succ Nat.zero) (.bvar 0))
      (.lam0 p (mkApp5 q(Nat.modCore.go) (.bvar 1) (.bvar 0)
        (mkApp q(Nat.succ) sx') sx' (mkApp q(Nat.lt_succ_self) sx')))
      (.lam0 (mkApp q(Not) p) sx')) sx

theorem natModEntryBody.instantiate_literals (a y : Nat) :
    (natModEntryBody.instantiate1' (.lit (.natVal a)) 1).instantiate1' (.lit (.natVal y)) =
      natModEntryAt q(@LE.le Nat _) q(Nat.decLe) q(Nat.modCore.go)
        (.lit (.natVal a)) (.lit (.natVal y))
        (mkApp q(Nat.lt_succ_self) (mkApp q(Nat.succ) (.lit (.natVal a)))) := by
  simp only [natModEntryBody, natModEntryAt,
    Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
  rfl

theorem natModEntryBody.instantiate_fvars (x y : FVarId) :
    (natModEntryBody.instantiate1' (.fvar x) 1).instantiate1' (.fvar y) =
      Condition.natLE.ite q(Nat) #[.fvar y, mkApp q(Nat.succ) (.fvar x)]
        (Condition.natLE.dite #[q(Nat.succ Nat.zero), .fvar y]
          (mkApp5 q(Nat.modCore.go) (.fvar y) (.bvar 0)
            (mkApp q(Nat.succ) (mkApp q(Nat.succ) (.fvar x)))
            (mkApp q(Nat.succ) (.fvar x))
            (mkApp q(Nat.lt_succ_self) (mkApp q(Nat.succ) (.fvar x))))
          (mkApp q(Nat.succ) (.fvar x))) (mkApp q(Nat.succ) (.fvar x)) := by
  simp only [natModEntryBody, Condition.ite, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
  rfl

/-- Instantiate the successor entry equation and its structural translation. -/
theorem natModEntryBody.at_literals {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat) (hfc : f.ClosedN)
    (tout : TrExprS env Us [(none, .vlam .nat), (none, .vlam .nat)] natModEntryBody out)
    (heq : env.IsDefEq Us.length [.nat, .nat]
      (.app (.app f (.app .natSucc (.bvar 1))) (.bvar 0)) out .nat) (a y : Nat) :
    TrExprS env Us []
      (natModEntryAt q(@LE.le Nat _) q(Nat.decLe) q(Nat.modCore.go)
        (.lit (.natVal a)) (.lit (.natVal y))
        (mkApp q(Nat.lt_succ_self) (mkApp q(Nat.succ) (.lit (.natVal a)))))
      ((out.inst (.natLit a) 1).inst (.natLit y)) ∧
    env.IsDefEq Us.length [] (.app (.app f (.natLit (a + 1))) (.natLit y))
      ((out.inst (.natLit a) 1).inst (.natLit y)) .nat := by
  have ta := TrExprS.natLit (Us := Us) (Δ := []) hp hn a
  have ty := TrExprS.natLit (Us := Us) (Δ := []) hp hn y
  have tout₁ := ta.1.instN henv ta.2 (.succ .zero) tout
  have heq₁ := heq.instN henv ta.2 (.succ .zero)
  simp only [VExpr.nat] at tout₁
  have tout₂ := tout₁.inst henv ty.2 ty.1
  have heq₂ := heq₁.instN henv ty.2 .zero
  refine ⟨?_, ?_⟩
  · simpa only [instantiate_literals] using tout₂
  · simpa only [VExpr.inst, hfc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
      VExpr.instVar_zero, VExpr.instVar_lower, VExpr.nat, VExpr.natSucc,
      VExpr.natLit, VExpr.natZero,
      (ta.2.closedN henv trivial).instN_eq (Nat.zero_le _),
      (ta.2.closedN henv trivial).liftN_eq (Nat.zero_le _)] using heq₂

/-- The open successor equation supplies both modulo entry contracts. The zero
equation and recursive equation remain separate checking obligations. -/
theorem natModEntryBody.spec {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (hi : Reflection.ITEChecked c r)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (tg : c.TrExprS q(Nat.modCore.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (tout : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
      natModEntryBody out)
    (heq : c.venv.IsDefEq c.lparams.length [.nat, .nat]
      (.app (.app f (.app .natSucc (.bvar 1))) (.bvar 0)) out .nat) :
    VEnv.NatModEntrySpec c.venv f go le := by
  have hfc := hf.closedN c.Ewf.ordered trivial
  have tlit (n : Nat) : c.TrExprS (.lit (.natVal n)) (.natLit n) := by
    simpa only [VContext.TrExprS, hc] using
      (TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hn n).1
  constructor
  · intro a y hy
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn hfc tout heq a y
    rw [← hc] at tr
    have hz := h.natMod_entry_stop hi hc hu hdc tp hn (tlit a) (tlit y) hy tr
    simpa only [hu, List.length_nil] using eq.trans hz
  · intro a y hy hle
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn hfc tout heq a y
    rw [← hc] at tr
    have hbound : (mkApp q(Nat.lt_succ_self) (mkApp q(Nat.succ) (.lit (.natVal a)))).Closed := by
      simp [Closed]
    obtain ⟨py, pa, _, hpy, hpa, hs⟩ :=
      h.natMod_entry_start hi hc hu hdc tp hn hg tg (tlit a) (tlit y) hbound hy hle tr
    exact ⟨py, pa, (by simpa only [hu, List.length_nil] using hpy),
      (by simpa only [hu, List.length_nil] using hpa),
      (by simpa only [hu, List.length_nil] using eq.trans hs)⟩

/-- Extract the open entry equation from the two fresh-local checks. -/
theorem checkNatDivEntry.WF {c : VContext} (hc : c.vlctx = [])
    (hn : c.venv.contains ``Nat)
    (hv : TrExprS c.venv c.lparams [] value f)
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `x .default q(Nat) fun x =>
      withLocalDecl `y .default q(Nat) fun y => do
        let e := Condition.natLE.dite #[q(Nat.succ Nat.zero), y]
          (mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
            (mkApp q(Nat.lt_succ_self) x)) q(Nat.zero)
        _ ← checkType e
        unless ← isDefEq (mkApp2 value x y) e do fail).WF c s fun _ _ =>
      ∃ out,
        TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)] natDivEntryBody out ∧
        c.venv.IsDefEq c.lparams.length [.nat, .nat]
          (.app (.app f (.bvar 1)) (.bvar 0)) out .nat := by
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨u, hNat.weak0 c.Ewf.ordered⟩
  have hfc := hf.closedN c.Ewf.ordered trivial
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl (c := c) (m := c.mlctx) trNat natType (.rfl (s := s))
    fun xid xwf sx _ _ => ?_
  let cx := c.withMLC (.vlam xid `x q(Nat) .nat .default c.mlctx) (wf := xwf)
  have tvx : cx.TrExprS value f := tr_inContext hv hfc
  have tv := tvx.weakBV c.Ewf.ordered (.skip (.vlam .nat) .refl)
  have tv₂ : TrExprS c.venv c.lparams ((none, .vlam .nat) :: cx.vlctx) value f := by
    simpa only [Expr.liftLooseBVars_eq_self (s := 0) hv.closed.looseBVarRange_le,
      hfc.liftN_eq (Nat.zero_le _)] using tv
  have tx : TrExprS c.venv c.lparams ((none, .vlam .nat) :: cx.vlctx)
      (.fvar xid) (.bvar 1) := .fvar (A := .nat) (by
    simp [cx, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, hc,
      VExpr.lift, VExpr.liftN, VExpr.nat])
  have ty : TrExprS c.venv c.lparams ((none, .vlam .nat) :: cx.vlctx)
      (.bvar 0) (.bvar 0) := .bvar rfl
  have hf₂ : c.venv.HasType c.lparams.length (VLCtx.toCtx ((none, .vlam .nat) :: cx.vlctx))
      f (.forallE .nat (.forallE .nat .nat)) := hf.weak0 c.Ewf.ordered
  have hx₂ : c.venv.HasType c.lparams.length (VLCtx.toCtx ((none, .vlam .nat) :: cx.vlctx))
      (.bvar 1) .nat := .bvar (.succ .zero)
  have hy₂ : c.venv.HasType c.lparams.length (VLCtx.toCtx ((none, .vlam .nat) :: cx.vlctx))
      (.bvar 0) .nat := .bvar .zero
  have tleft := TrExprS.app (hf₂.app hx₂) hy₂ (.app hf₂ hx₂ tv₂ tx) ty
  let rhs := natDivEntryBody.instantiate1' (.fvar xid) 1
  have hright : rhs.FVarsIn (· ∈ cx.vlctx.fvars) := by
    simp [rhs, natDivEntryBody, Expr.lam0, FVarsIn,
      Expr.instantiate1', Expr.liftLooseBVars', cx, VContext.withMLC,
      MLCtx.vlctx, VLCtx.fvars, Level.hasMVar']
  have hi (a : Expr) (k : Nat) : value.instantiate1' a k = value :=
    Expr.instantiate1'_eq_self (Nat.le_trans hv.closed.looseBVarRange_le (Nat.zero_le _))
  let l := fun y => mkApp2 value (.fvar xid) y
  let r := fun y => Condition.natLE.dite #[q(Nat.succ Nat.zero), y]
    (mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) (.fvar xid)) (.fvar xid)
      (mkApp q(Nat.lt_succ_self) (.fvar xid))) q(Nat.zero)
  have hl : ∀ id, l (.fvar id) = (mkApp2 value (.fvar xid) (.bvar 0)).instantiate1' (.fvar id) := by
    intro id
    simp [l, mkApp2, mkAppB, mkApp, Expr.instantiate1', hi, Expr.liftLooseBVars']
  have hr : ∀ id, r (.fvar id) = rhs.instantiate1' (.fvar id) := by
    intro id
    simp [r, rhs, natDivEntryBody, Condition.dite, Condition.natLE, mkAppN,
      mkApp4, mkApp5, mkApp2, mkAppB, mkApp, Expr.lam0,
      Expr.instantiate1', Expr.liftLooseBVars']
  have wfy := withLocalDecl_checkEq.WF (name := `y) (bi := .default) (c := cx) (s := sx)
    (A := .nat) trNat natType tleft ((hf₂.app hx₂).app hy₂) hright l r hl hr fail hfail
  have wfy := wfy.mono (R := fun _ _ => ∃ out,
      TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)] natDivEntryBody out ∧
      c.venv.IsDefEq c.lparams.length [.nat, .nat]
        (.app (.app f (.bvar 1)) (.bvar 0)) out .nat) fun _ _ _ ⟨out, tout, heq⟩ => by
    have hsc : natDivEntryBody.FVarsIn (· ≠ xid) := by
      simp [natDivEntryBody, Expr.lam0, FVarsIn, mkApp4, mkApp5, mkApp2,
        mkAppB, mkApp, Level.hasMVar']
    have tout := tout.uninstantiateN (.succ .zero) hsc
    exact ⟨out, (by simpa only [cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc] using tout),
      (by simpa only [cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, VLCtx.toCtx, hc] using heq)⟩
  exact wfy

/-- The recursive equation's anonymous context, ordered as `[h, fuel, hy, y, x]`. -/
def natDivLoopContext (le : VExpr) : VLCtx :=
  [(none, .vlam (.app (.app le (.app .natSucc (.bvar 3))) (.app .natSucc (.bvar 0)))),
    (none, .vlam .nat),
    (none, .vlam (.app (.app le (.natLit 1)) (.bvar 0))),
    (none, .vlam .nat), (none, .vlam .nat)]

/-- The recursive conditional before substituting the five checked locals. -/
def natDivLoopBody : Expr :=
  let p := mkApp2 q(@LE.le Nat _) (.bvar 3) (.bvar 4)
  mkApp4 q(@dite Nat) p (mkApp2 q(Nat.decLe) (.bvar 3) (.bvar 4))
    (.lam0 p (mkApp q(Nat.succ)
      (mkApp5 q(Nat.div.go) (.bvar 4) (.bvar 3) (.bvar 2)
        (mkApp2 q(Nat.sub) (.bvar 5) (.bvar 4))
        (mkApp6 q(@Nat.div_rec_fuel_lemma) (.bvar 5) (.bvar 4) (.bvar 2)
          (.bvar 3) (.bvar 0) (.bvar 1)))))
    (.lam0 (mkApp q(Not) p) q(Nat.zero))

/-- Substituting the five locals recovers the executable recursive-check body. -/
theorem natDivLoopBody.instantiate_fvars (x y hy fuel h : FVarId) :
    ((((natDivLoopBody.instantiate1' (.fvar x) 4).instantiate1' (.fvar y) 3).instantiate1'
      (.fvar hy) 2).instantiate1' (.fvar fuel) 1).instantiate1' (.fvar h) =
      Condition.natLE.dite #[.fvar y, .fvar x]
        (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) (.fvar y) (.fvar hy) (.fvar fuel)
          (mkApp2 q(Nat.sub) (.fvar x) (.fvar y))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.fvar x) (.fvar y) (.fvar fuel)
            (.fvar hy) (.bvar 0) (.fvar h)))) q(Nat.zero) := by
  simp only [natDivLoopBody, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
  rfl

theorem natDivLoopBody.instantiate_literals (a y fuel : Nat)
    (hpy : epy.Closed) (hpa : epa.Closed) :
    ((((natDivLoopBody.instantiate1' (.lit (.natVal a)) 4).instantiate1'
      (.lit (.natVal y)) 3).instantiate1' epy 2).instantiate1'
      (.lit (.natVal fuel)) 1).instantiate1' epa =
      Condition.natLE.dite #[.lit (.natVal y), .lit (.natVal a)]
        (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) (.lit (.natVal y)) epy
          (.lit (.natVal fuel)) (mkApp2 q(Nat.sub) (.lit (.natVal a)) (.lit (.natVal y)))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.lit (.natVal a)) (.lit (.natVal y))
            (.lit (.natVal fuel)) epy (.bvar 0) epa))) q(Nat.zero) := by
  have hinst (e : Expr) (he : e.Closed) (v : Expr) (k : Nat) :
      e.instantiate1' v k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (he : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self he.looseBVarRange_le
  simp only [natDivLoopBody, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', hinst _ hpy, hlift _ hpy, hlift _ hpa,
    Expr.liftLooseBVars', Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, if_true, if_false]
  rfl

/-- Modulo's recursive conditional in the same five-local context as division. -/
def natModLoopBody : Expr :=
  let p := mkApp2 q(@LE.le Nat _) (.bvar 3) (.bvar 4)
  mkApp4 q(@dite Nat) p (mkApp2 q(Nat.decLe) (.bvar 3) (.bvar 4))
    (.lam0 p (mkApp5 q(Nat.modCore.go) (.bvar 4) (.bvar 3) (.bvar 2)
      (mkApp2 q(Nat.sub) (.bvar 5) (.bvar 4))
      (mkApp6 q(@Nat.div_rec_fuel_lemma) (.bvar 5) (.bvar 4) (.bvar 2)
        (.bvar 3) (.bvar 0) (.bvar 1))))
    (.lam0 (mkApp q(Not) p) (.bvar 5))

theorem natModLoopBody.instantiate_fvars (x y hy fuel h : FVarId) :
    ((((natModLoopBody.instantiate1' (.fvar x) 4).instantiate1' (.fvar y) 3).instantiate1'
      (.fvar hy) 2).instantiate1' (.fvar fuel) 1).instantiate1' (.fvar h) =
      Condition.natLE.dite #[.fvar y, .fvar x]
        (mkApp5 q(Nat.modCore.go) (.fvar y) (.fvar hy) (.fvar fuel)
          (mkApp2 q(Nat.sub) (.fvar x) (.fvar y))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.fvar x) (.fvar y) (.fvar fuel)
            (.fvar hy) (.bvar 0) (.fvar h))) (.fvar x) := by
  simp only [natModLoopBody, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
  rfl

theorem natModLoopBody.instantiate_literals (a y fuel : Nat)
    (hpy : epy.Closed) (hpa : epa.Closed) :
    ((((natModLoopBody.instantiate1' (.lit (.natVal a)) 4).instantiate1'
      (.lit (.natVal y)) 3).instantiate1' epy 2).instantiate1'
      (.lit (.natVal fuel)) 1).instantiate1' epa =
      Condition.natLE.dite #[.lit (.natVal y), .lit (.natVal a)]
        (mkApp5 q(Nat.modCore.go) (.lit (.natVal y)) epy
          (.lit (.natVal fuel)) (mkApp2 q(Nat.sub) (.lit (.natVal a)) (.lit (.natVal y)))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.lit (.natVal a)) (.lit (.natVal y))
            (.lit (.natVal fuel)) epy (.bvar 0) epa)) (.lit (.natVal a)) := by
  have hinst (e : Expr) (he : e.Closed) (v : Expr) (k : Nat) :
      e.instantiate1' v k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  have hlift (e : Expr) (he : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
    Expr.liftLooseBVars_eq_self he.looseBVarRange_le
  simp only [natModLoopBody, Condition.dite, Condition.natLE, mkAppN,
    Expr.lam0, Expr.instantiate1', hinst _ hpy, hlift _ hpy, hlift _ hpa,
    Expr.liftLooseBVars', Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, if_true, if_false]
  rfl

/-- Instantiate the recursive equation and its translation using source proofs
of positivity and the fuel bound. -/
private theorem natLoopBody_at_literals {env : VEnv} {body : Expr} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hlc : le.ClosedN) (hgc : go.ClosedN)
    (tpy : TrExprS env Us [] epy py)
    (hpy : env.HasType Us.length [] py (VEnv.natLeExpr le 1 y))
    (tpa : TrExprS env Us [] epa pa)
    (hpa : env.HasType Us.length [] pa (VEnv.natLeExpr le (a + 1) (fuel + 1)))
    (tout : TrExprS env Us (natDivLoopContext le) body out)
    (heq : env.IsDefEq Us.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat) :
    TrExprS env Us []
      (((((body.instantiate1' (.lit (.natVal a)) 4).instantiate1'
        (.lit (.natVal y)) 3).instantiate1' epy 2).instantiate1'
        (.lit (.natVal fuel)) 1).instantiate1' epa)
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) ∧
    env.IsDefEq Us.length [] (VEnv.natDivLoopExpr go y py (fuel + 1) a pa)
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) .nat := by
  have ta := TrExprS.natLit (Us := Us) (Δ := []) hp hn a
  have ty := TrExprS.natLit (Us := Us) (Δ := []) hp hn y
  have tf := TrExprS.natLit (Us := Us) (Δ := []) hp hn fuel
  have hac := ta.2.closedN henv trivial
  have hyc := ty.2.closedN henv trivial
  have hfc := tf.2.closedN henv trivial
  have hpc := hpy.closedN henv trivial
  have tq := ta.1.instN henv ta.2 (.succ (.succ (.succ (.succ .zero)))) tout
  have eq := heq.instN henv ta.2 (.succ (.succ (.succ (.succ .zero))))
  simp only [VLocalDecl.inst, VLocalDecl.depth, Nat.reduceAdd, VLCtx.toCtx, VExpr.inst,
    hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ, VExpr.instVar_zero,
    VExpr.instVar_lower, VExpr.nat, VExpr.natLit, VExpr.natSucc, VExpr.natZero] at tq eq
  have tq := ty.1.instN henv ty.2 (.succ (.succ (.succ .zero))) tq
  have eq := eq.instN henv ty.2 (.succ (.succ (.succ .zero)))
  simp only [VLocalDecl.inst, VLocalDecl.depth, Nat.reduceAdd, VExpr.inst,
    hlc.instN_eq (Nat.zero_le _),
    hac.instN_eq (Nat.zero_le _), hac.liftN_eq (Nat.zero_le _),
    VExpr.instVar_zero, VExpr.instVar_lower] at tq eq
  have tq := tpy.instN henv hpy (.succ (.succ .zero)) tq
  have eq := eq.instN henv hpy (.succ (.succ .zero))
  simp only [VLocalDecl.inst, VLocalDecl.depth, Nat.reduceAdd, VExpr.inst,
    hlc.instN_eq (Nat.zero_le _),
    hac.instN_eq (Nat.zero_le _), VExpr.instVar_lower] at tq eq
  have tq := tf.1.instN henv tf.2 (.succ .zero) tq
  have eq := eq.instN henv tf.2 (.succ .zero)
  simp only [VLocalDecl.inst, VLocalDecl.depth, Nat.reduceAdd, VExpr.inst,
    hlc.instN_eq (Nat.zero_le _),
    hac.instN_eq (Nat.zero_le _), VExpr.instVar_zero, VExpr.instVar_lower] at tq eq
  have tq := tq.inst henv hpa tpa
  have eq := eq.instN henv hpa .zero
  refine ⟨?_, ?_⟩
  · exact tq
  · simpa only [VEnv.natDivLoopExpr, VExpr.inst, hgc.instN_eq (Nat.zero_le _),
      hac.instN_eq (Nat.zero_le _), hyc.instN_eq (Nat.zero_le _),
      hyc.liftN_eq (Nat.zero_le _), hfc.liftN_eq (Nat.zero_le _),
      hfc.instN_eq (Nat.zero_le _),
      hpc.instN_eq (Nat.zero_le _), hpc.liftN_eq (Nat.zero_le _),
      VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower, VExpr.instVar_upper,
      VExpr.nat, VExpr.natLit, VExpr.natSucc, VExpr.natZero,
      VExpr.liftN, VExpr.lift, liftVar_base] using eq

theorem natDivLoopBody.at_literals {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hlc : le.ClosedN) (hgc : go.ClosedN)
    (tpy : TrExprS env Us [] epy py)
    (hpy : env.HasType Us.length [] py (VEnv.natLeExpr le 1 y))
    (tpa : TrExprS env Us [] epa pa)
    (hpa : env.HasType Us.length [] pa (VEnv.natLeExpr le (a + 1) (fuel + 1)))
    (tout : TrExprS env Us (natDivLoopContext le) natDivLoopBody out)
    (heq : env.IsDefEq Us.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat) :
    TrExprS env Us []
      (Condition.natLE.dite #[.lit (.natVal y), .lit (.natVal a)]
        (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) (.lit (.natVal y)) epy
          (.lit (.natVal fuel)) (mkApp2 q(Nat.sub) (.lit (.natVal a)) (.lit (.natVal y)))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.lit (.natVal a)) (.lit (.natVal y))
            (.lit (.natVal fuel)) epy (.bvar 0) epa))) q(Nat.zero))
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) ∧
    env.IsDefEq Us.length [] (VEnv.natDivLoopExpr go y py (fuel + 1) a pa)
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) .nat := by
  obtain ⟨tq, eq⟩ := natLoopBody_at_literals henv hp hn hlc hgc tpy hpy tpa hpa tout heq
  exact ⟨by simpa only [instantiate_literals _ _ _ tpy.closed tpa.closed] using tq, eq⟩

/-- The checked open recursive equation implies the loop contract for arbitrary
abstract proof arguments. Reflection supplies source witnesses for substitution;
proof irrelevance then removes the dependence on their particular translations. -/
theorem natDivLoopBody.spec {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (tg : c.TrExprS q(Nat.div.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (tout : TrExprS c.venv c.lparams (natDivLoopContext le) natDivLoopBody out)
    (heq : c.venv.IsDefEq c.lparams.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat) :
    VEnv.NatDivLoopSpec c.venv go le := by
  have hle₀ : c.venv.HasType 0 [] le (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using h.1
  have hg₀ : c.venv.HasType 0 [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using hg
  have tout₀ := tout
  have heq₀ := heq
  simp only [hu, List.length_nil] at tout₀ heq₀
  have tlit (n : Nat) : c.TrExprS (.lit (.natVal n)) (.natLit n) := by
    simpa only [VContext.TrExprS, hc] using
      (TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hn n).1
  have witnesses (y fuel a : Nat) (hy : 0 < y) (ha : a < fuel + 1) :
      ∃ epy py epa pa, c.TrExprS epy py ∧
        c.venv.HasType 0 [] py (VEnv.natLeExpr le 1 y) ∧ c.TrExprS epa pa ∧
        c.venv.HasType 0 [] pa (VEnv.natLeExpr le (a + 1) (fuel + 1)) := by
    obtain ⟨epy, py, tpy, hpy⟩ := h.natBle_witness hc hu hdc tp 1 y (tlit 1) (tlit y)
      (c.hasPrimitives.natLit_type hn 1) (c.hasPrimitives.natLit_type hn y) hy
    obtain ⟨epa, pa, tpa, hpa⟩ := h.natBle_witness hc hu hdc tp (a + 1) (fuel + 1)
      (tlit (a + 1)) (tlit (fuel + 1)) (c.hasPrimitives.natLit_type hn (a + 1))
      (c.hasPrimitives.natLit_type hn (fuel + 1)) (by omega)
    exact ⟨epy, py, epa, pa, tpy, (by simpa only [hu, List.length_nil] using hpy),
      tpa, (by simpa only [hu, List.length_nil] using hpa)⟩
  constructor
  · intro y fuel a py pa hy ha hya hpy hpa
    obtain ⟨epy, py', epa, pa', tpy, hpy', tpa, hpa'⟩ := witnesses y fuel a hy ha
    have tpy₀ := tpy
    have tpa₀ := tpa
    simp only [VContext.TrExprS, hc, hu] at tpy₀ tpa₀
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn
      (hle₀.closedN c.Ewf.ordered trivial) (hg₀.closedN c.Ewf.ordered trivial)
      tpy₀ hpy' tpa₀ hpa' tout₀ heq₀
    rw [← hu, ← hc] at tr
    have hpyc : c.HasType py' (VEnv.natLeExpr le 1 y) := by
      simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using hpy'
    obtain ⟨pa'', hpa'', hstep⟩ := h.natDiv_step hc hu hdc tp hn hsub hg tg
      (tlit y) (tlit fuel) (tlit a) tpy hpyc hya tr
    simp only [hu, List.length_nil] at hpa'' hstep
    have eqIn := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy hpy' hpa hpa'
    have eqOut := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy' hpy hpa'' hpa''
    exact ⟨pa'', hpa'', eqIn.trans (eq.trans hstep) |>.trans
      ((c.hasPrimitives.natSucc_type hn).appDF eqOut)⟩
  · intro y fuel a py pa hy ha hay hpy hpa
    obtain ⟨epy, py', epa, pa', tpy, hpy', tpa, hpa'⟩ := witnesses y fuel a hy ha
    have tpy₀ := tpy
    have tpa₀ := tpa
    simp only [VContext.TrExprS, hc, hu] at tpy₀ tpa₀
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn
      (hle₀.closedN c.Ewf.ordered trivial) (hg₀.closedN c.Ewf.ordered trivial)
      tpy₀ hpy' tpa₀ hpa' tout₀ heq₀
    rw [← hu, ← hc] at tr
    have hz := h.natBle_dite_zero_inputs hc hu hdc tp hn y a (tlit y) (tlit a)
      (c.hasPrimitives.natLit_type hn y) (c.hasPrimitives.natLit_type hn a) hay tr
    simp only [hu, List.length_nil] at hz
    have eqIn := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy hpy' hpa hpa'
    exact eqIn.trans (eq.trans hz)

theorem natModLoopBody.at_literals {env : VEnv} (henv : env.Ordered)
    (hp : env.HasPrimitives) (hn : env.contains ``Nat)
    (hlc : le.ClosedN) (hgc : go.ClosedN)
    (tpy : TrExprS env Us [] epy py)
    (hpy : env.HasType Us.length [] py (VEnv.natLeExpr le 1 y))
    (tpa : TrExprS env Us [] epa pa)
    (hpa : env.HasType Us.length [] pa (VEnv.natLeExpr le (a + 1) (fuel + 1)))
    (tout : TrExprS env Us (natDivLoopContext le) natModLoopBody out)
    (heq : env.IsDefEq Us.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat) :
    TrExprS env Us []
      (Condition.natLE.dite #[.lit (.natVal y), .lit (.natVal a)]
        (mkApp5 q(Nat.modCore.go) (.lit (.natVal y)) epy
          (.lit (.natVal fuel)) (mkApp2 q(Nat.sub) (.lit (.natVal a)) (.lit (.natVal y)))
          (mkApp6 q(@Nat.div_rec_fuel_lemma) (.lit (.natVal a)) (.lit (.natVal y))
            (.lit (.natVal fuel)) epy (.bvar 0) epa)) (.lit (.natVal a)))
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) ∧
    env.IsDefEq Us.length [] (VEnv.natDivLoopExpr go y py (fuel + 1) a pa)
      (((((out.inst (.natLit a) 4).inst (.natLit y) 3).inst py 2).inst
        (.natLit fuel) 1).inst pa) .nat := by
  obtain ⟨tq, eq⟩ := natLoopBody_at_literals henv hp hn hlc hgc tpy hpy tpa hpa tout heq
  exact ⟨by simpa only [instantiate_literals _ _ _ tpy.closed tpa.closed] using tq, eq⟩

/-- The checked open recursive equation implies the loop contract for arbitrary
abstract proof arguments. Reflection supplies source witnesses for substitution;
proof irrelevance then removes the dependence on their particular translations. -/
theorem natModLoopBody.spec {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (tg : c.TrExprS q(Nat.modCore.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (tout : TrExprS c.venv c.lparams (natDivLoopContext le) natModLoopBody out)
    (heq : c.venv.IsDefEq c.lparams.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat) :
    VEnv.NatModLoopSpec c.venv go le := by
  have hle₀ : c.venv.HasType 0 [] le (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using h.1
  have hg₀ : c.venv.HasType 0 [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using hg
  have tout₀ := tout
  have heq₀ := heq
  simp only [hu, List.length_nil] at tout₀ heq₀
  have tlit (n : Nat) : c.TrExprS (.lit (.natVal n)) (.natLit n) := by
    simpa only [VContext.TrExprS, hc] using
      (TrExprS.natLit (Us := c.lparams) (Δ := []) c.hasPrimitives hn n).1
  have witnesses (y fuel a : Nat) (hy : 0 < y) (ha : a < fuel + 1) :
      ∃ epy py epa pa, c.TrExprS epy py ∧
        c.venv.HasType 0 [] py (VEnv.natLeExpr le 1 y) ∧ c.TrExprS epa pa ∧
        c.venv.HasType 0 [] pa (VEnv.natLeExpr le (a + 1) (fuel + 1)) := by
    obtain ⟨epy, py, tpy, hpy⟩ := h.natBle_witness hc hu hdc tp 1 y (tlit 1) (tlit y)
      (c.hasPrimitives.natLit_type hn 1) (c.hasPrimitives.natLit_type hn y) hy
    obtain ⟨epa, pa, tpa, hpa⟩ := h.natBle_witness hc hu hdc tp (a + 1) (fuel + 1)
      (tlit (a + 1)) (tlit (fuel + 1)) (c.hasPrimitives.natLit_type hn (a + 1))
      (c.hasPrimitives.natLit_type hn (fuel + 1)) (by omega)
    exact ⟨epy, py, epa, pa, tpy, (by simpa only [hu, List.length_nil] using hpy),
      tpa, (by simpa only [hu, List.length_nil] using hpa)⟩
  constructor
  · intro y fuel a py pa hy ha hya hpy hpa
    obtain ⟨epy, py', epa, pa', tpy, hpy', tpa, hpa'⟩ := witnesses y fuel a hy ha
    have tpy₀ := tpy
    have tpa₀ := tpa
    simp only [VContext.TrExprS, hc, hu] at tpy₀ tpa₀
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn
      (hle₀.closedN c.Ewf.ordered trivial) (hg₀.closedN c.Ewf.ordered trivial)
      tpy₀ hpy' tpa₀ hpa' tout₀ heq₀
    rw [← hu, ← hc] at tr
    have hpyc : c.HasType py' (VEnv.natLeExpr le 1 y) := by
      simpa only [VContext.HasType, hc, hu, List.length_nil, VLCtx.toCtx] using hpy'
    obtain ⟨pa'', hpa'', hstep⟩ := h.natMod_step hc hu hdc tp hn hsub hg tg
      (tlit y) (tlit fuel) (tlit a) tpy hpyc hya tr
    simp only [hu, List.length_nil] at hpa'' hstep
    have eqIn := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy hpy' hpa hpa'
    have eqOut := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy' hpy hpa'' hpa''
    exact ⟨pa'', hpa'', (eqIn.trans (eq.trans hstep)).trans eqOut⟩
  · intro y fuel a py pa hy ha hay hpy hpa
    obtain ⟨epy, py', epa, pa', tpy, hpy', tpa, hpa'⟩ := witnesses y fuel a hy ha
    have tpy₀ := tpy
    have tpa₀ := tpa
    simp only [VContext.TrExprS, hc, hu] at tpy₀ tpa₀
    obtain ⟨tr, eq⟩ := at_literals c.Ewf.ordered c.hasPrimitives hn
      (hle₀.closedN c.Ewf.ordered trivial) (hg₀.closedN c.Ewf.ordered trivial)
      tpy₀ hpy' tpa₀ hpa' tout₀ heq₀
    rw [← hu, ← hc] at tr
    have hz := h.natBle_dite_false_inputs hc hu hdc tp y a (tlit y) (tlit a)
      (c.hasPrimitives.natLit_type hn y) (c.hasPrimitives.natLit_type hn a)
      (tlit a) (c.hasPrimitives.natLit_type hn a) hay tr
    simp only [hu, List.length_nil] at hz
    have eqIn := VEnv.natDivLoopExpr.proofIrrel c.Ewf.ordered c.hasPrimitives hn
      hle₀ hg₀ hpy hpy' hpa hpa'
    exact eqIn.trans (eq.trans hz)

private theorem tr_natDivLoopApply {env : VEnv} {g ey ehy ef ea eha : Expr}
    (hlc : le.ClosedN)
    (hg : env.HasType Us.length Δ.toCtx go (VEnv.natDivLoopType le))
    (hy : env.HasType Us.length Δ.toCtx y .nat)
    (hpy : env.HasType Us.length Δ.toCtx py (.app (.app le (.natLit 1)) y))
    (hf : env.HasType Us.length Δ.toCtx fuel .nat)
    (ha : env.HasType Us.length Δ.toCtx a .nat)
    (hpa : env.HasType Us.length Δ.toCtx pa (.app (.app le (.app .natSucc a)) fuel))
    (tg : TrExprS env Us Δ g go) (ty : TrExprS env Us Δ ey y)
    (tpy : TrExprS env Us Δ ehy py) (tf : TrExprS env Us Δ ef fuel)
    (ta : TrExprS env Us Δ ea a) (tpa : TrExprS env Us Δ eha pa) :
    TrExprS env Us Δ (mkApp5 g ey ehy ef ea eha)
      (.app (.app (.app (.app (.app go y) py) fuel) a) pa) ∧
    env.HasType Us.length Δ.toCtx
      (.app (.app (.app (.app (.app go y) py) fuel) a) pa) .nat := by
  have t₁ := TrExprS.app hg hy tg ty
  have h₁ := hg.app hy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _),
    VExpr.instVar_succ, VExpr.instVar_zero, VExpr.instVar_lower,
    VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd,
    VExpr.natLit, VExpr.natSucc, VExpr.natZero, VExpr.nat] at h₁
  have t₂ := TrExprS.app h₁ hpy t₁ tpy
  have h₂ := h₁.app hpy
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_lower, VExpr.lift, VExpr.liftN, liftVar_base, Nat.reduceAdd] at h₂
  have t₃ := TrExprS.app h₂ hf t₂ tf
  have h₃ := h₂.app hf
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_succ,
    VExpr.instVar_zero, VExpr.instVar_lower, VExpr.lift, Nat.reduceAdd] at h₃
  have t₄ := TrExprS.app h₃ ha t₃ ta
  have h₄ := h₃.app ha
  simp only [VExpr.inst, hlc.instN_eq (Nat.zero_le _), VExpr.instVar_zero,
    VExpr.inst_lift] at h₄
  exact ⟨.app h₄ hpa t₄ tpa, h₄.app hpa⟩

/-- Extract the recursive equation inside the existing `[y, x]` context. -/
private theorem checkNatLoopRecursion.WF {c : VContext} {x y g body : Expr}
    (rhsFn : Expr → Expr → Expr → Expr → Expr → Expr)
    (hn : c.venv.contains ``Nat)
    (tl : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le)
    (hl : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))))
    (tg : TrExprS c.venv c.lparams [] g go)
    (hg : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le))
    (tx : c.TrExprS x (.bvar 1)) (ty : c.TrExprS y (.bvar 0))
    (hx : c.HasType (.bvar 1) .nat) (hy : c.HasType (.bvar 0) .nat)
    (hbody : ∀ P : FVarId → Prop, body.FVarsIn P)
    (hbodyEq : ∀ hy fuel h : FVarId,
      ((((body.instantiate1' x 4).instantiate1' y 3).instantiate1' (.fvar hy) 2).instantiate1'
        (.fvar fuel) 1).instantiate1' (.fvar h) = rhsFn x y (.fvar hy) (.fvar fuel) (.fvar h))
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `hy .default (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y) fun hy =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
      withLocalDecl `h .default
          (mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) fuel)) fun h => do
        let e := rhsFn x y hy fuel h
        _ ← checkType e
        unless ← isDefEq (mkApp5 g y hy (mkApp q(Nat.succ) fuel) x h) e do fail
      ).WF c s fun _ _ => ∃ out,
        TrExprS c.venv c.lparams (List.append ((natDivLoopContext le).take 3) c.vlctx)
          ((body.instantiate1' x 4).instantiate1' y 3) out ∧
        c.venv.IsDefEq c.lparams.length
          (VLCtx.toCtx (List.append ((natDivLoopContext le).take 3) c.vlctx))
          (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
            (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat := by
  have hlc := hl.closedN c.Ewf.ordered trivial
  have hgc := hg.closedN c.Ewf.ordered trivial
  have hxc : x.Closed := c.mlctx.noBV ▸ tx.closed
  have hyc : y.Closed := c.mlctx.noBV ▸ ty.closed
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := c.vlctx) c.hasPrimitives hn
  have hs := TrExprS.natSucc (Us := c.lparams) (Δ := c.vlctx) c.hasPrimitives hn
  obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered c.Δwf.toCtx
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered c.Δwf.toCtx
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat := by
    have hn₀ := (c.hasPrimitives.natLit_type (U := c.lparams.length) (Γ := []) hn 0).isType
      c.Ewf.ordered trivial
    obtain ⟨u, hu⟩ := hn₀
    exact ⟨u, hu.weak0 c.Ewf.ordered⟩
  let P := VExpr.app (.app le (.natLit 1)) (.bvar 0)
  let eP := mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y
  have tOne := TrExprS.app hs.2 hz.2 hs.1 hz.1
  have hOne := hs.2.app hz.2
  have hl₁ := (hl.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)).app hOne
  simp only [VExpr.inst, VExpr.nat] at hl₁
  have tP : c.TrExprS eP P := .app hl₁ hy (.app
    (hl.weak0 c.Ewf.ordered) hOne (tr_inContext tl hlc) tOne) ty
  have hP : c.IsType P := ⟨.zero, hl₁.app hy⟩
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl tP hP (.rfl (s := s)) fun hid hwf sh _ _ => ?_
  let ch := c.withMLC (.vlam hid `hy eP P .default c.mlctx) (wf := hwf)
  have W : VLCtx.FVLift c.vlctx ch.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tx₁ : ch.TrExprS x (.bvar 2) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using tx.weakFV c.Ewf.ordered W ch.Δwf
  have ty₁ : ch.TrExprS y (.bvar 1) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using ty.weakFV c.Ewf.ordered W ch.Δwf
  have hx₁ : ch.HasType (.bvar 2) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hx.weak c.Ewf.ordered
  have hy₁ : ch.HasType (.bvar 1) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hy.weak c.Ewf.ordered
  refine M.WF.withLocalDecl (c := c) (m := ch.mlctx) (cwf := hwf)
    trNat natType (.rfl (s := sh)) fun fid fwf sf _ _ => ?_
  let cf := c.withMLC (.vlam fid `fuel q(Nat) .nat .default ch.mlctx) (wf := fwf)
  have W₁ : VLCtx.FVLift ch.vlctx cf.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tx₂ : cf.TrExprS x (.bvar 3) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using tx₁.weakFV c.Ewf.ordered W₁ cf.Δwf
  have hx₂ : cf.HasType (.bvar 3) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hx₁.weak c.Ewf.ordered
  have tf : cf.TrExprS (.fvar fid) (.bvar 0) := .fvar (A := .nat) (by
    simp [cf, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat])
  have hf : cf.HasType (.bvar 0) .nat := .bvar .zero
  let H := VExpr.app (.app le (.app .natSucc (.bvar 3))) (.app .natSucc (.bvar 0))
  let eH := mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) (.fvar fid))
  have hsF := TrExprS.natSucc (Us := c.lparams) (Δ := cf.vlctx) c.hasPrimitives hn
  have hleF := hl.weak0 c.Ewf.ordered (Γ := cf.vlctx.toCtx)
  have hleFx := hleF.app (hsF.2.app hx₂)
  simp only [VExpr.inst, VExpr.nat] at hleFx
  have tH : cf.TrExprS eH H := .app hleFx (hsF.2.app hf)
    (.app hleF (hsF.2.app hx₂) (tr_inContext tl hlc) (.app hsF.2 hx₂ hsF.1 tx₂))
    (.app hsF.2 hf hsF.1 tf)
  have hH : cf.IsType H := ⟨.zero, hleFx.app (hsF.2.app hf)⟩
  let Δ : VLCtx := (none, .vlam H) :: cf.vlctx
  have ty₂ : cf.TrExprS y (.bvar 2) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using ty₁.weakFV c.Ewf.ordered W₁ cf.Δwf
  have hy₂ : cf.HasType (.bvar 2) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hy₁.weak c.Ewf.ordered
  have tposH : ch.TrExprS (.fvar hid) (.bvar 0) := .fvar (A := P.lift) (by
    simp [ch, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type])
  have tpos : cf.TrExprS (.fvar hid) (.bvar 1) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base]
      using tposH.weakFV c.Ewf.ordered W₁ cf.Δwf
  have tx₃ : TrExprS c.venv c.lparams Δ x (.bvar 4) := by
    simpa only [Expr.liftLooseBVars_eq_self (s := 0) hxc.looseBVarRange_le,
      VExpr.liftN, liftVar_base] using tx₂.weakBV c.Ewf.ordered (.skip (.vlam H) .refl)
  have ty₃ : TrExprS c.venv c.lparams Δ y (.bvar 3) := by
    simpa only [Expr.liftLooseBVars_eq_self (s := 0) hyc.looseBVarRange_le,
      VExpr.liftN, liftVar_base] using ty₂.weakBV c.Ewf.ordered (.skip (.vlam H) .refl)
  have tf₁ : TrExprS c.venv c.lparams Δ (.fvar fid) (.bvar 1) := by
    simpa only [Expr.liftLooseBVars', VExpr.liftN, liftVar_base]
      using tf.weakBV c.Ewf.ordered (.skip (.vlam H) .refl)
  have tpos₁ : TrExprS c.venv c.lparams Δ (.fvar hid) (.bvar 2) := by
    simpa only [Expr.liftLooseBVars', VExpr.liftN, liftVar_base]
      using tpos.weakBV c.Ewf.ordered (.skip (.vlam H) .refl)
  have tg₁ : TrExprS c.venv c.lparams Δ g go := by
    have tgF : cf.TrExprS g go := tr_inContext tg hgc
    simpa only [Expr.liftLooseBVars_eq_self (s := 0) tg.closed.looseBVarRange_le,
      hgc.liftN_eq (Nat.zero_le _)]
      using tgF.weakBV c.Ewf.ordered (.skip (.vlam H) .refl)
  have hx₃ : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 4) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hx₂.weak c.Ewf.ordered
  have hy₃ : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 3) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hy₂.weak c.Ewf.ordered
  have hf₁ : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 1) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hf.weak c.Ewf.ordered
  have hpos : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 2)
      (.app (.app le (.natLit 1)) (.bvar 3)) := by
    have h : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 2) P.lift.lift.lift :=
      .bvar (.succ (.succ .zero))
    simpa only [P, Δ, VExpr.lift, VExpr.liftN, hlc.liftN_eq (Nat.zero_le _),
      liftVar_base, VExpr.natLit, VExpr.natSucc, VExpr.natZero] using h
  have hbound : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 0)
      (.app (.app le (.app .natSucc (.bvar 4))) (.app .natSucc (.bvar 1))) := by
    have h : c.venv.HasType c.lparams.length Δ.toCtx (.bvar 0) H.lift := .bvar .zero
    simpa only [H, VExpr.lift, VExpr.liftN, hlc.liftN_eq (Nat.zero_le _),
      liftVar_base, VExpr.natSucc] using h
  have tb : TrExprS c.venv c.lparams Δ (.bvar 0) (.bvar 0) := .bvar rfl
  have hs₁ := TrExprS.natSucc (Us := c.lparams) (Δ := Δ) c.hasPrimitives hn
  have ⟨tleft, hleft⟩ := tr_natDivLoopApply hlc (hg.weak0 c.Ewf.ordered)
    hy₃ hpos (hs₁.2.app hf₁) hx₃ hbound tg₁ ty₃ tpos₁
    (TrExprS.app hs₁.2 hf₁ hs₁.1 tf₁) tx₃ tb
  let rhs := (((body.instantiate1' x 4).instantiate1' y 3).instantiate1'
    (.fvar hid) 2).instantiate1' (.fvar fid) 1
  have hposFV : (.fvar hid : Expr).FVarsIn (· ∈ cf.vlctx.fvars) := tpos.fvarsIn
  have hright : rhs.FVarsIn (· ∈ cf.vlctx.fvars) :=
    ((((hbody _).instantiate1_go tx₂.fvarsIn).instantiate1_go ty₂.fvarsIn).instantiate1_go
      hposFV).instantiate1_go tf.fvarsIn
  let l := fun h => mkApp5 g y (.fvar hid) (mkApp q(Nat.succ) (.fvar fid)) x h
  let r := fun h => rhsFn x y (.fvar hid) (.fvar fid) h
  have hinst (e : Expr) (he : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
    Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
  have hl' : ∀ id, l (.fvar id) = (l (.bvar 0)).instantiate1' (.fvar id) := by
    intro id
    simp [l, mkApp5, mkApp4, mkAppB, mkApp, Expr.instantiate1',
      hinst _ hxc, hinst _ hyc, hinst _ tg.closed, Expr.liftLooseBVars']
  have hr' : ∀ id, r (.fvar id) = rhs.instantiate1' (.fvar id) := by
    intro id
    exact (hbodyEq hid fid id).symm
  have wfh := withLocalDecl_checkEq.WF (name := `h) (bi := .default) (c := cf) (s := sf)
    (A := .nat) tH hH tleft hleft hright l r hl' hr' fail hfail
  exact wfh.mono fun _ _ _ ⟨out, tout, heq⟩ => by
    -- Forget the fresh source names; their anonymous binders remain in the model context.
    have hbase : ((body.instantiate1' x 4).instantiate1' y 3).FVarsIn
        (· ∈ c.vlctx.fvars) :=
      ((hbody _).instantiate1_go tx.fvarsIn).instantiate1_go ty.fvarsIn
    have hnotF : fid ∉ ch.vlctx.fvars := (cf.Δwf.fvwf.2 fid q(Nat).fvarsList rfl).1
    have hbaseH : ((body.instantiate1' x 4).instantiate1' y 3).FVarsIn
        (· ∈ ch.vlctx.fvars) := hbase.fvars_cons
    have hscF : (((body.instantiate1' x 4).instantiate1' y 3).instantiate1'
        (.fvar hid) 2).FVarsIn (· ≠ fid) :=
      (hbaseH.instantiate1_go tposH.fvarsIn).mono fun fv hmem he => hnotF (he ▸ hmem)
    have tout := tout.uninstantiateN (.succ .zero) hscF
    have hnotH : hid ∉ c.vlctx.fvars := (ch.Δwf.fvwf.2 hid eP.fvarsList rfl).1
    have hscH : ((body.instantiate1' x 4).instantiate1' y 3).FVarsIn (· ≠ hid) :=
      hbase.mono fun fv hmem he => hnotH (he ▸ hmem)
    have tout := tout.uninstantiateN (.succ (.succ .zero)) hscH
    exact ⟨out,
      (by simpa only [VContext.withMLC_self, cf, ch, H, P, VContext.withMLC, VContext.vlctx, MLCtx.vlctx,
        natDivLoopContext, List.take_succ_cons, List.take_zero, List.append_cons,
        List.nil_append] using tout),
      (by simpa only [VContext.withMLC_self, cf, ch, H, P, VContext.withMLC, VContext.vlctx, MLCtx.vlctx,
        natDivLoopContext, List.take_succ_cons, List.take_zero, List.append_cons,
        List.nil_append, VLCtx.toCtx] using heq)⟩

theorem checkNatDivRecursion.WF {c : VContext} {x y : Expr}
    (hn : c.venv.contains ``Nat)
    (tl : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le)
    (hl : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))))
    (tg : TrExprS c.venv c.lparams [] q(Nat.div.go) go)
    (hg : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le))
    (tx : c.TrExprS x (.bvar 1)) (ty : c.TrExprS y (.bvar 0))
    (hx : c.HasType (.bvar 1) .nat) (hy : c.HasType (.bvar 0) .nat)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `hy .default (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y) fun hy =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
      withLocalDecl `h .default
          (mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) fuel)) fun h => do
        let e := Condition.natLE.dite #[y, x]
          (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) y hy fuel (mkApp2 q(Nat.sub) x y)
            (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) q(Nat.zero)
        _ ← checkType e
        unless ← isDefEq (mkApp5 q(Nat.div.go) y hy (mkApp q(Nat.succ) fuel) x h) e do fail
      ).WF c s fun _ _ => ∃ out,
        TrExprS c.venv c.lparams (List.append ((natDivLoopContext le).take 3) c.vlctx)
          ((natDivLoopBody.instantiate1' x 4).instantiate1' y 3) out ∧
        c.venv.IsDefEq c.lparams.length
          (VLCtx.toCtx (List.append ((natDivLoopContext le).take 3) c.vlctx))
          (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
            (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat := by
  refine checkNatLoopRecursion.WF
    (fun x y hy fuel h => Condition.natLE.dite #[y, x]
      (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) y hy fuel (mkApp2 q(Nat.sub) x y)
        (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) q(Nat.zero))
    hn tl hl tg hg tx ty hx hy ?_ ?_ fail hfail
  · intro P
    simp [natDivLoopBody, Expr.lam0, FVarsIn, mkApp4, mkApp5, mkApp6,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  · intro hid fid id
    have hxc : x.Closed := c.mlctx.noBV ▸ tx.closed
    have hyc : y.Closed := c.mlctx.noBV ▸ ty.closed
    have hinst (e : Expr) (he : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
      Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
    have hlift (e : Expr) (he : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
      Expr.liftLooseBVars_eq_self he.looseBVarRange_le
    simp [natDivLoopBody, Condition.dite, Condition.natLE, mkAppN,
      mkApp4, mkApp5, mkApp6, mkApp2, mkAppB, mkApp, Expr.lam0,
      Expr.instantiate1', hinst _ hxc, hinst _ hyc, hlift _ hxc, hlift _ hyc,
      Expr.liftLooseBVars']

/-- Extract modulo's recursive equation with the shared dependent-local rule. -/
theorem checkNatModRecursion.WF {c : VContext} {x y : Expr}
    (hn : c.venv.contains ``Nat)
    (tl : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le)
    (hl : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))))
    (tg : TrExprS c.venv c.lparams [] q(Nat.modCore.go) go)
    (hg : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le))
    (tx : c.TrExprS x (.bvar 1)) (ty : c.TrExprS y (.bvar 0))
    (hx : c.HasType (.bvar 1) .nat) (hy : c.HasType (.bvar 0) .nat)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `hy .default (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y) fun hy =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
      withLocalDecl `h .default
          (mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) fuel)) fun h => do
        let e := Condition.natLE.dite #[y, x]
          (mkApp5 q(Nat.modCore.go) y hy fuel (mkApp2 q(Nat.sub) x y)
            (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x
        _ ← checkType e
        unless ← isDefEq (mkApp5 q(Nat.modCore.go) y hy (mkApp q(Nat.succ) fuel) x h) e do fail
      ).WF c s fun _ _ => ∃ out,
        TrExprS c.venv c.lparams (List.append ((natDivLoopContext le).take 3) c.vlctx)
          ((natModLoopBody.instantiate1' x 4).instantiate1' y 3) out ∧
        c.venv.IsDefEq c.lparams.length
          (VLCtx.toCtx (List.append ((natDivLoopContext le).take 3) c.vlctx))
          (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
            (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) out .nat := by
  refine checkNatLoopRecursion.WF
    (fun x y hy fuel h => Condition.natLE.dite #[y, x]
      (mkApp5 q(Nat.modCore.go) y hy fuel (mkApp2 q(Nat.sub) x y)
        (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x)
    hn tl hl tg hg tx ty hx hy ?_ ?_ fail hfail
  · intro P
    simp [natModLoopBody, Expr.lam0, FVarsIn, mkApp4, mkApp5, mkApp6,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  · intro hid fid id
    have hxc : x.Closed := c.mlctx.noBV ▸ tx.closed
    have hyc : y.Closed := c.mlctx.noBV ▸ ty.closed
    have hinst (e : Expr) (he : e.Closed) (a : Expr) (k : Nat) : e.instantiate1' a k = e :=
      Expr.instantiate1'_eq_self (Nat.le_trans he.looseBVarRange_le (Nat.zero_le _))
    have hlift (e : Expr) (he : e.Closed) (k : Nat) : e.liftLooseBVars' 0 k = e :=
      Expr.liftLooseBVars_eq_self he.looseBVarRange_le
    simp [natModLoopBody, Condition.dite, Condition.natLE, mkAppN,
      mkApp4, mkApp5, mkApp6, mkApp2, mkAppB, mkApp, Expr.lam0,
      Expr.instantiate1', hinst _ hxc, hinst _ hyc, hlift _ hxc, hlift _ hyc,
      Expr.liftLooseBVars']

/-- The actual entry checks establish both closed entry equations. -/
theorem checkNatDivEntry.spec {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (tg : c.TrExprS q(Nat.div.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (hv : TrExprS c.venv c.lparams [] value f)
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `x .default q(Nat) fun x =>
      withLocalDecl `y .default q(Nat) fun y => do
        let e := Condition.natLE.dite #[q(Nat.succ Nat.zero), y]
          (mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
            (mkApp q(Nat.lt_succ_self) x)) q(Nat.zero)
        _ ← checkType e
        unless ← isDefEq (mkApp2 value x y) e do fail).WF c s
      fun _ _ => VEnv.NatDivEntrySpec c.venv f go le :=
  (checkNatDivEntry.WF hc hn hv hf fail hfail).mono fun _ _ _ ⟨_, tout, heq⟩ =>
    natDivEntryBody.spec hc hu hdc h tp hn tg hg hf tout heq

/-- The entry and recursive equation checks, in their executable order, supply
the complete division specification. -/
theorem checkNatDivEquations.WF {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (tg : c.TrExprS q(Nat.div.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (hv : TrExprS c.venv c.lparams [] value f)
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `x .default q(Nat) fun x => do
      withLocalDecl `y .default q(Nat) fun y => do
      let e := Condition.natLE.dite #[q(Nat.succ Nat.zero), y]
        (mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
          (mkApp q(Nat.lt_succ_self) x)) q(Nat.zero)
      _ ← checkType e
      unless ← isDefEq (mkApp2 value x y) e do fail
      withLocalDecl `hy .default (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y) fun hy => do
      withLocalDecl `fuel .default q(Nat) fun fuel => do
      withLocalDecl `h .default
        (mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) fuel)) fun h => do
      let e := Condition.natLE.dite #[y, x]
        (mkApp q(Nat.succ) (mkApp5 q(Nat.div.go) y hy fuel (mkApp2 q(Nat.sub) x y)
          (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) q(Nat.zero)
      _ ← checkType e
      unless ← isDefEq (mkApp5 q(Nat.div.go) y hy (mkApp q(Nat.succ) fuel) x h) e do fail
      ).WF c s fun _ _ => VEnv.NatDivSpec c.venv f go le := by
  have tl₀ : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le := by
    simpa only [VContext.TrExprS, hc] using tp
  have hl₀ : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using h.1
  have tg₀ : TrExprS c.venv c.lparams [] q(Nat.div.go) go := by
    simpa only [VContext.TrExprS, hc] using tg
  have hg₀ : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hg
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨u, hNat.weak0 c.Ewf.ordered⟩
  have hfc := hf.closedN c.Ewf.ordered trivial
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl (c := c) (m := c.mlctx) trNat natType (.rfl (s := s))
    fun xid xwf sx _ _ => ?_
  let cx := c.withMLC (.vlam xid `x q(Nat) .nat .default c.mlctx) (wf := xwf)
  have tx : cx.TrExprS (.fvar xid) (.bvar 0) := .fvar (A := .nat) (by
    simp [cx, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat])
  have hx : cx.HasType (.bvar 0) .nat := .bvar .zero
  refine M.WF.withLocalDecl (c := c) (m := cx.mlctx) (cwf := xwf)
    trNat natType (.rfl (s := sx)) fun yid ywf sy _ _ => ?_
  let cy := c.withMLC (.vlam yid `y q(Nat) .nat .default cx.mlctx) (wf := ywf)
  have W : VLCtx.FVLift cx.vlctx cy.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tx₁ : cy.TrExprS (.fvar xid) (.bvar 1) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using tx.weakFV c.Ewf.ordered W cy.Δwf
  have hx₁ : cy.HasType (.bvar 1) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hx.weak c.Ewf.ordered
  have ty : cy.TrExprS (.fvar yid) (.bvar 0) := .fvar (A := .nat) (by
    simp [cy, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat])
  have hy : cy.HasType (.bvar 0) .nat := .bvar .zero
  have hf₁ : cy.HasType f (.forallE .nat (.forallE .nat .nat)) := hf.weak0 c.Ewf.ordered
  have tv : cy.TrExprS value f := tr_inContext hv hfc
  have tleft := TrExprS.app (hf₁.app hx₁) hy (.app hf₁ hx₁ tv tx₁) ty
  let e := Condition.natLE.dite #[q(Nat.succ Nat.zero), .fvar yid]
    (mkApp5 q(Nat.div.go) (.fvar yid) (.bvar 0) (mkApp q(Nat.succ) (.fvar xid)) (.fvar xid)
      (mkApp q(Nat.lt_succ_self) (.fvar xid))) q(Nat.zero)
  have heFV : e.FVarsIn (· ∈ cy.vlctx.fvars) := by
    simp [e, Condition.dite, Condition.natLE, mkAppN, mkApp4, mkApp5,
      mkAppB, mkApp, Expr.lam0, FVarsIn,
      cy, cx, VContext.withMLC, MLCtx.vlctx, VLCtx.fvars, Level.hasMVar']
  refine (checkType.WF (c := cy) heFV).bind fun _ _ _ ⟨outE, _, _, toutE, _, _⟩ => ?_
  refine (isDefEq.WF (c := cy) tleft toutE).bind fun b _ _ heqE => ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact hfail.bind fun _ _ _ h => h.elim
  simp only [if_true, pure_bind]
  have heqE := (heqE rfl).of_l cy.Ewf cy.Δwf.toCtx ((hf₁.app hx₁).app hy)
  refine (checkNatDivRecursion.WF (c := cy) hn tl₀ hl₀ tg₀ hg₀
    tx₁ ty hx₁ hy fail hfail).mono fun _ _ _ ⟨outL, toutL, heqL⟩ => ?_
  have hnotY : yid ∉ cx.vlctx.fvars := (cy.Δwf.fvwf.2 yid q(Nat).fvarsList rfl).1
  have hbodyE {P : FVarId → Prop} : natDivEntryBody.FVarsIn P := by
    simp [natDivEntryBody, Expr.lam0, FVarsIn, mkApp4, mkApp5,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  have hscEY : (natDivEntryBody.instantiate1' (.fvar xid) 1).FVarsIn (· ≠ yid) :=
    (hbodyE.instantiate1_go tx.fvarsIn).mono fun fv hmem he => hnotY (he ▸ hmem)
  have eqE : e = (natDivEntryBody.instantiate1' (.fvar xid) 1).instantiate1' (.fvar yid) := by
    simp only [e, natDivEntryBody, Condition.dite, Condition.natLE, mkAppN,
      Expr.lam0, Expr.instantiate1', Expr.liftLooseBVars',
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false]
    rfl
  rw [eqE] at toutE
  have toutE := (toutE.uninstantiate hscEY).uninstantiateN (.succ .zero) hbodyE
  have trE : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
      natDivEntryBody outE := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc] using toutE
  have eqE : c.venv.IsDefEq c.lparams.length [.nat, .nat]
      (.app (.app f (.bvar 1)) (.bvar 0)) outE .nat := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, VLCtx.toCtx, hc] using heqE
  have hbodyL {P : FVarId → Prop} : natDivLoopBody.FVarsIn P := by
    simp [natDivLoopBody, Expr.lam0, FVarsIn, mkApp4, mkApp5, mkApp6,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  have hscLY : (natDivLoopBody.instantiate1' (.fvar xid) 4).FVarsIn (· ≠ yid) :=
    (hbodyL.instantiate1_go tx.fvarsIn).mono fun fv hmem he => hnotY (he ▸ hmem)
  simp only [natDivLoopContext, List.take_succ_cons, List.take_zero] at toutL
  have toutL := toutL.uninstantiateN (.succ (.succ (.succ .zero))) hscLY
  have toutL := toutL.uninstantiateN (.succ (.succ (.succ (.succ .zero)))) hbodyL
  have trL : TrExprS c.venv c.lparams (natDivLoopContext le) natDivLoopBody outL := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
      natDivLoopContext] using toutL
  have eqL : c.venv.IsDefEq c.lparams.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) outL .nat := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
      natDivLoopContext, List.take_succ_cons, List.take_zero, List.append_cons,
      List.nil_append, VLCtx.toCtx] using heqL
  have hentry := natDivEntryBody.spec hc hu hdc h tp hn tg hg hf trE eqE
  have hloop := natDivLoopBody.spec hc hu hdc h tp hn hsub tg hg trL eqL
  simpa only [VContext.withMLC_self] using VEnv.NatDivSpec.ofEntry hentry hloop

/-- The modulo fresh-local checks supply the entry and loop contracts. Its
preceding zero check is retained as a separate premise. -/
theorem checkNatModEquations.WF {c : VContext} {proof : Expr} {r : Reflection}
    (hc : c.vlctx = []) (hu : c.lparams = []) (hdc : r.toDec.Closed)
    (h : Condition.ReflectedNatNatChecked c q(@LE.le Nat _) q(Nat.decLe)
      q(Nat.ble) proof r le)
    (hi : Reflection.ITEChecked c r)
    (tp : c.TrExprS q(@LE.le Nat _) le) (hn : c.venv.contains ``Nat)
    (hsub : c.venv.contains ``Nat.sub)
    (tg : c.TrExprS q(Nat.modCore.go) go) (hg : c.HasType go (VEnv.natDivLoopType le))
    (hv : TrExprS c.venv c.lparams [] value f)
    (hf : c.venv.HasType c.lparams.length [] f (.forallE .nat (.forallE .nat .nat)))
    (hzero : ∀ y, c.venv.IsDefEq 0 [] (.app (.app f .natZero) (.natLit y)) .natZero .nat)
    (fail : ∀ {α}, M α)
    (hfail : ∀ {c : VContext} {s}, (fail (α := Unit)).WF c s fun _ _ => False) :
    (withLocalDecl `x .default q(Nat) fun x => do
      withLocalDecl `y .default q(Nat) fun y => do
      let sx := mkApp q(Nat.succ) x
      let e := Condition.natLE.ite q(Nat) #[y, sx]
        (Condition.natLE.dite #[q(Nat.succ Nat.zero), y]
          (mkApp5 q(Nat.modCore.go) y (.bvar 0) (mkApp q(Nat.succ) sx) sx
            (mkApp q(Nat.lt_succ_self) sx)) sx) sx
      _ ← checkType e
      unless ← isDefEq (mkApp2 value sx y) e do fail
      withLocalDecl `hy .default (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) y) fun hy => do
      withLocalDecl `fuel .default q(Nat) fun fuel => do
      withLocalDecl `h .default
        (mkApp2 q(@LE.le Nat _) (mkApp q(Nat.succ) x) (mkApp q(Nat.succ) fuel)) fun h => do
      let e := Condition.natLE.dite #[y, x]
        (mkApp5 q(Nat.modCore.go) y hy fuel (mkApp2 q(Nat.sub) x y)
          (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x
      _ ← checkType e
      unless ← isDefEq (mkApp5 q(Nat.modCore.go) y hy (mkApp q(Nat.succ) fuel) x h) e do fail
      ).WF c s fun _ _ => VEnv.NatModSpec c.venv f go le := by
  have tl₀ : TrExprS c.venv c.lparams [] q(@LE.le Nat _) le := by
    simpa only [VContext.TrExprS, hc] using tp
  have hl₀ : c.venv.HasType c.lparams.length [] le
      (.forallE .nat (.forallE .nat (.sort .zero))) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using h.1
  have tg₀ : TrExprS c.venv c.lparams [] q(Nat.modCore.go) go := by
    simpa only [VContext.TrExprS, hc] using tg
  have hg₀ : c.venv.HasType c.lparams.length [] go (VEnv.natDivLoopType le) := by
    simpa only [VContext.HasType, hc, VLCtx.toCtx] using hg
  have hz := TrExprS.natZero (Us := c.lparams) (Δ := []) c.hasPrimitives hn
  obtain ⟨u, hNat⟩ := hz.2.isType c.Ewf.ordered trivial
  obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
  have trNat {Δ : VLCtx} : TrExprS c.venv c.lparams Δ q(Nat) .nat := .const hciNat rfl huNat
  have natType {Γ : List VExpr} : c.venv.IsType c.lparams.length Γ .nat :=
    ⟨u, hNat.weak0 c.Ewf.ordered⟩
  have hfc := hf.closedN c.Ewf.ordered trivial
  rw [← c.withMLC_self]
  refine M.WF.withLocalDecl (c := c) (m := c.mlctx) trNat natType (.rfl (s := s))
    fun xid xwf sx _ _ => ?_
  let cx := c.withMLC (.vlam xid `x q(Nat) .nat .default c.mlctx) (wf := xwf)
  have tx : cx.TrExprS (.fvar xid) (.bvar 0) := .fvar (A := .nat) (by
    simp [cx, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat])
  have hx : cx.HasType (.bvar 0) .nat := .bvar .zero
  refine M.WF.withLocalDecl (c := c) (m := cx.mlctx) (cwf := xwf)
    trNat natType (.rfl (s := sx)) fun yid ywf sy _ _ => ?_
  let cy := c.withMLC (.vlam yid `y q(Nat) .nat .default cx.mlctx) (wf := ywf)
  have W : VLCtx.FVLift cx.vlctx cy.vlctx 0 1 0 := .skip_fvar _ _ .refl
  have tx₁ : cy.TrExprS (.fvar xid) (.bvar 1) := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base] using tx.weakFV c.Ewf.ordered W cy.Δwf
  have hx₁ : cy.HasType (.bvar 1) .nat := by
    simpa only [VExpr.lift, VExpr.liftN, liftVar_base, VExpr.nat] using hx.weak c.Ewf.ordered
  have ty : cy.TrExprS (.fvar yid) (.bvar 0) := .fvar (A := .nat) (by
    simp [cy, VContext.withMLC, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat])
  have hy : cy.HasType (.bvar 0) .nat := .bvar .zero
  have hf₁ : cy.HasType f (.forallE .nat (.forallE .nat .nat)) := hf.weak0 c.Ewf.ordered
  have tv : cy.TrExprS value f := tr_inContext hv hfc
  have hs₁ := TrExprS.natSucc (Us := c.lparams) (Δ := cy.vlctx) c.hasPrimitives hn
  have hsx := hs₁.2.app hx₁
  have tsx := TrExprS.app hs₁.2 hx₁ hs₁.1 tx₁
  have tleft := TrExprS.app (hf₁.app hsx) hy (.app hf₁ hsx tv tsx) ty
  let sx := mkApp q(Nat.succ) (.fvar xid)
  let e := Condition.natLE.ite q(Nat) #[.fvar yid, sx]
    (Condition.natLE.dite #[q(Nat.succ Nat.zero), .fvar yid]
      (mkApp5 q(Nat.modCore.go) (.fvar yid) (.bvar 0) (mkApp q(Nat.succ) sx) sx
        (mkApp q(Nat.lt_succ_self) sx)) sx) sx
  have heFV : e.FVarsIn (· ∈ cy.vlctx.fvars) := by
    simp [e, sx, Condition.ite, Condition.dite, Condition.natLE, mkAppN, mkApp4, mkApp5,
      mkAppB, mkApp, Expr.lam0, FVarsIn,
      cy, cx, VContext.withMLC, MLCtx.vlctx, VLCtx.fvars, Level.hasMVar']
  refine (checkType.WF (c := cy) heFV).bind fun _ _ _ ⟨outE, _, _, toutE, _, _⟩ => ?_
  refine (isDefEq.WF (c := cy) tleft toutE).bind fun b _ _ heqE => ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact hfail.bind fun _ _ _ h => h.elim
  simp only [if_true, pure_bind]
  have heqE := (heqE rfl).of_l cy.Ewf cy.Δwf.toCtx ((hf₁.app hsx).app hy)
  refine (checkNatModRecursion.WF (c := cy) hn tl₀ hl₀ tg₀ hg₀
    tx₁ ty hx₁ hy fail hfail).mono fun _ _ _ ⟨outL, toutL, heqL⟩ => ?_
  have hnotY : yid ∉ cx.vlctx.fvars := (cy.Δwf.fvwf.2 yid q(Nat).fvarsList rfl).1
  have hbodyE {P : FVarId → Prop} : natModEntryBody.FVarsIn P := by
    simp [natModEntryBody, Expr.lam0, FVarsIn, mkApp4, mkApp5,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  have hscEY : (natModEntryBody.instantiate1' (.fvar xid) 1).FVarsIn (· ≠ yid) :=
    (hbodyE.instantiate1_go tx.fvarsIn).mono fun fv hmem he => hnotY (he ▸ hmem)
  have eqE : e = (natModEntryBody.instantiate1' (.fvar xid) 1).instantiate1' (.fvar yid) :=
    (natModEntryBody.instantiate_fvars xid yid).symm
  rw [eqE] at toutE
  have toutE := (toutE.uninstantiate hscEY).uninstantiateN (.succ .zero) hbodyE
  have trE : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
      natModEntryBody outE := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc] using toutE
  have eqE : c.venv.IsDefEq c.lparams.length [.nat, .nat]
      (.app (.app f (.app .natSucc (.bvar 1))) (.bvar 0)) outE .nat := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, VLCtx.toCtx, hc] using heqE
  have hbodyL {P : FVarId → Prop} : natModLoopBody.FVarsIn P := by
    simp [natModLoopBody, Expr.lam0, FVarsIn, mkApp4, mkApp5, mkApp6,
      mkApp2, mkAppB, mkApp, Level.hasMVar']
  have hscLY : (natModLoopBody.instantiate1' (.fvar xid) 4).FVarsIn (· ≠ yid) :=
    (hbodyL.instantiate1_go tx.fvarsIn).mono fun fv hmem he => hnotY (he ▸ hmem)
  simp only [natDivLoopContext, List.take_succ_cons, List.take_zero] at toutL
  have toutL := toutL.uninstantiateN (.succ (.succ (.succ .zero))) hscLY
  have toutL := toutL.uninstantiateN (.succ (.succ (.succ (.succ .zero)))) hbodyL
  have trL : TrExprS c.venv c.lparams (natDivLoopContext le) natModLoopBody outL := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
      natDivLoopContext] using toutL
  have eqL : c.venv.IsDefEq c.lparams.length (natDivLoopContext le).toCtx
      (.app (.app (.app (.app (.app go (.bvar 3)) (.bvar 2))
        (.app .natSucc (.bvar 1))) (.bvar 4)) (.bvar 0)) outL .nat := by
    simpa only [cy, cx, VContext.withMLC, VContext.vlctx, MLCtx.vlctx, hc,
      natDivLoopContext, List.take_succ_cons, List.take_zero, List.append_cons,
      List.nil_append, VLCtx.toCtx] using heqL
  have hentry := natModEntryBody.spec hc hu hdc h hi tp hn tg hg hf trE eqE
  have hloop := natModLoopBody.spec hc hu hdc h tp hn hsub tg hg trL eqL
  simpa only [VContext.withMLC_self] using VEnv.NatModSpec.ofEntry hentry hloop hzero

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

theorem checkPrimitiveDef_natShiftRight.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧ (ves.venv .safe).contains ``Nat.div ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      VEnv.NatShiftRightSpec (ves.venv .safe) f := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hdiv := contains_primitive c hguard.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hdivTy := c.hasPrimitives.natDivType hdiv
    obtain ⟨u, hNat⟩ := (hdivTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨_, hci, _, hu⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hci⟩
    obtain ⟨_, hdivci, _, hdivUs⟩ := hdivTy.const_inv c.Ewf.ordered trivial
    have trDiv {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat.div) (.const ``Nat.div []) :=
      .const hdivci rfl hdivUs
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
        have hdiv₂ : c.venv.HasType 0 [.nat, .nat] (.const ``Nat.div [])
            (.forallE .nat (.forallE .nat .nat)) := hdivTy.weak0 c.Ewf.ordered
        have hshift := (hf₂.app hx₂).app hy₂
        have tshift := TrExprS.app (hf₂.app hx₂) hy₂ (.app hf₂ hx₂ hv₂ tx₂) ty₂
        have hright := (hdiv₂.app hshift).app htwo
        have tright := TrExprS.app (hdiv₂.app hshift) htwo
          (.app hdiv₂ hshift (trDiv (Δ := Δ₂)) tshift) ttwo
        have tleft' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tleft)
        have tright' := TrExprS.lam (name := `_) (bi := .default) natType trNat
          (TrExprS.lam (name := `_) (bi := .default) natType trNat tright)
        refine (isDefEq.WF (c := c) tleft' tright').bind fun b _ _ hsucc => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          apply M.WF.pure
          refine ⟨hn, hdiv, htype rfl, ?_⟩
          constructor
          · exact VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hx₁).app hz₁.2) hx₁
              ((hzero rfl).of_r c.Ewf c.Δwf (.lam natTy hx₁))
          · have hleft : c.venv.HasType 0 [.nat, .nat]
                (.app (.app f.lift.lift (.bvar 0)) (.app .natSucc (.bvar 1))) .nat :=
              (hf₂.app hx₂).app (hs₂.2.app hy₂)
            have he := (hsucc rfl).of_r c.Ewf c.Δwf (.lam natTy (.lam natTy hright))
            have he := VEnv.IsDefEq.lam_body c.Ewf.ordered
              (.lam natTy hleft) (.lam natTy hright) he
            exact VEnv.IsDefEq.lam_body c.Ewf.ordered hleft hright he
  · exact nofun

theorem checkPrimitiveDef_natDiv.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      ∃ go le, VEnv.NatDivSpec (ves.venv .safe) f go le := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hsub := contains_primitive c hguard.1.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hb := contains_primitive c hguard.1.2
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hsubTy := c.hasPrimitives.natSubType hsub
    obtain ⟨u, hNat⟩ := (hsubTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hciNat⟩
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hciNat rfl huNat
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat :=
      ⟨u, hNat.weak0 c.Ewf.ordered⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let fail {α} : M α := throw <| .other s!"invalid form for primitive def {``Nat.div}"
      have hfail {c : VContext} {s} : (fail (α := Unit)).WF c s fun _ _ => False := nofun
      have hdc : Reflection.defn₁.toDec.Closed := by simp [Reflection.defn₁, Closed]
      refine (checkNatDivCondition.WF (c := c) rfl fail hfail hb hn).bind
        fun _ _ _ ⟨le, tp, hcond⟩ => ?_
      have tty := tr_natDivLoopType c.Ewf.ordered c.hasPrimitives hn tp hcond.1
      refine (checkType.WF (c := c) (e := q(Nat.div.go)) (by simp [FVarsIn])).bind
        fun _ _ _ ⟨go, _, _, tg, tt, hg⟩ => ?_
      refine (isDefEq.WF (c := c) tt tty).bind fun b _ _ hloopType => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have hg := hg.defeqU_r c.Ewf c.Δwf (hloopType rfl)
        exact (checkNatDivEquations.WF (c := c) rfl rfl hdc hcond tp hn hsub
          tg hg hv hf fail hfail).bind fun _ _ _ hspec => .pure ⟨hn, htype rfl, go, le, hspec⟩
  · exact nofun

set_option backward.split false in
/-- The full modulo validator supplies all equations, including its separate
zero check and both conditional modes. -/
theorem checkPrimitiveDef_natMod.WF {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type) :
    (checkPrimitiveDef v).WF (.mk' wf .safe [] fuel) s fun _ _ =>
      (ves.venv .safe).contains ``Nat ∧
      (ves.venv .safe).IsDefEqU 0 [] type (.forallE .nat (.forallE .nat .nat)) ∧
      ∃ go le, VEnv.NatModSpec (ves.venv .safe) f go le := by
  let c := VContext.mk' wf .safe [] fuel
  unfold checkPrimitiveDef
  simp only [hname]
  refine (getEnv.WF (c := c)).bind fun _ _ _ ⟨rfl, rfl⟩ => ?_
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    have hsub := contains_primitive c hguard.1.1
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hb := contains_primitive c hguard.1.2
      (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    have hsubTy := c.hasPrimitives.natSubType hsub
    obtain ⟨u, hNat⟩ := (hsubTy.isType c.Ewf.ordered trivial).forallE_inv c.Ewf.ordered |>.1
    obtain ⟨_, hciNat, _, huNat⟩ := hNat.const_inv c.Ewf.ordered trivial
    have hn : c.venv.contains ``Nat := ⟨_, hciNat⟩
    have trNat {Δ : VLCtx} : TrExprS c.venv [] Δ q(Nat) .nat := .const hciNat rfl huNat
    have natType {Γ : List VExpr} : c.venv.IsType 0 Γ .nat :=
      ⟨u, hNat.weak0 c.Ewf.ordered⟩
    have trType : c.TrExprS q(Nat → Nat → Nat) (.forallE .nat (.forallE .nat .nat)) :=
      .forallE natType (natType.forallE natType) trNat
        (.forallE natType natType trNat trNat)
    simp only [pure_bind]
    refine (isDefEq.WF (c := c) ht trType).bind fun b _ _ htype => ?_
    cases b
    · exact nofun
    · simp only [if_true]
      have hf := hf.defeqU_r c.Ewf c.Δwf (htype rfl)
      let fail {α} : M α := throw <| .other s!"invalid form for primitive def {``Nat.mod}"
      have hfail {c : VContext} {s} : (fail (α := Unit)).WF c s fun _ _ => False := nofun
      have hdc : Reflection.defn₁.toDec.Closed := by simp [Reflection.defn₁, Closed]
      let Δ₁ : VLCtx := [(none, .vlam .nat)]
      have hf₁ : c.venv.HasType 0 [.nat] f.lift (.forallE .nat (.forallE .nat .nat)) :=
        hf.weak c.Ewf.ordered
      have hv₁ : TrExprS c.venv [] Δ₁ v.value f.lift :=
        hv.weakBV_closed c.Ewf.ordered (.skip (.vlam .nat) .refl)
      have hz₁ := TrExprS.natZero (Us := []) (Δ := Δ₁) c.hasPrimitives hn
      have tx₁ : TrExprS c.venv [] Δ₁ (.bvar 0) (.bvar 0) := .bvar rfl
      have hx₁ : c.venv.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
      have tzero : c.TrExprS (.lam0 q(Nat) (mkApp2 v.value q(Nat.zero) (.bvar 0)))
          (.lam .nat (.app (.app f.lift .natZero) (.bvar 0))) :=
        .lam natType trNat (.app (hf₁.app hz₁.2) hx₁ (.app hf₁ hz₁.2 hv₁ hz₁.1) tx₁)
      have tz : c.TrExprS (.lam0 q(Nat) q(Nat.zero)) (.lam .nat .natZero) :=
        .lam natType trNat hz₁.1
      refine (isDefEq.WF (c := c) tzero tz).bind fun b _ _ hzero => ?_
      cases b
      · exact nofun
      · simp only [if_true]
        have hzero := VEnv.IsDefEq.lam_body c.Ewf.ordered ((hf₁.app hz₁.2).app hx₁) hz₁.2
          ((hzero rfl).of_r c.Ewf c.Δwf (.lam (hNat.weak0 c.Ewf.ordered) hz₁.2))
        have hz : ∀ y, c.venv.IsDefEq 0 []
            (.app (.app f .natZero) (.natLit y)) .natZero .nat := by
          intro y
          simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
            VExpr.nat, VExpr.natZero] using
            hzero.instN c.Ewf.ordered (c.hasPrimitives.natLit_type hn y) .zero
        have propType {Γ : List VExpr} : c.venv.IsType 0 Γ (.sort .zero) :=
          ⟨_, .sort trivial⟩
        have tpType : c.TrExprS q(Nat → Nat → Prop)
            (.forallE .nat (.forallE .nat (.sort .zero))) :=
          .forallE natType (natType.forallE propType) trNat
            (.forallE natType propType trNat (.sort rfl))
        refine (checkType.WF (c := c) (e := q(@LE.le Nat _))
          (by simp [FVarsIn, Level.hasMVar'])).bind fun _ _ _ ⟨le, _, _, tp, tpt, hl⟩ => ?_
        refine (isDefEq.WF (c := c) tpt tpType).bind fun b _ _ hpropType => ?_
        cases b
        · exact nofun
        · simp only [if_true]
          have hl := hl.defeqU_r c.Ewf c.Δwf (hpropType rfl)
          have tty := tr_natModLoopType c.Ewf.ordered c.hasPrimitives hn tp hl
          refine (checkType.WF (c := c) (e := q(Nat.modCore.go)) (by simp [FVarsIn])).bind
            fun _ _ _ ⟨go, _, _, tg, tt, hg⟩ => ?_
          refine (isDefEq.WF (c := c) tt tty).bind fun b _ _ hloopType => ?_
          cases b
          · exact nofun
          · simp only [if_true]
            have hg := hg.defeqU_r c.Ewf c.Δwf (hloopType rfl)
            refine (Condition.natLE.checkITE.WF (c := c) rfl fail hfail tp hb hn).bind
              fun _ _ _ ⟨hcond, hi⟩ => ?_
            exact (checkNatModEquations.WF (c := c) rfl rfl hdc hcond hi tp hn hsub
              tg hg hv hf hz fail hfail).bind fun _ _ _ hspec =>
                .pure ⟨hn, htype rfl, go, le, hspec⟩
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

theorem checkPrimitiveDef_natDiv.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.div []) f type) :
    env'.HasType 0 [] (.const ``Nat.div []) (.forallE .nat (.forallE .nat .nat)) ∧
    env'.ReflectsNatNatNat ``Nat.div Nat.div := by
  have ⟨hn, htype, go, le, hspec⟩ :=
    M.WF.run wf (checkPrimitiveDef_natDiv.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, fun _ a b => ?_⟩
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have heval := (hspec.eval wf.hasPrimitives hn a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natMod.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.mod []) f type) :
    env'.HasType 0 [] (.const ``Nat.mod []) (.forallE .nat (.forallE .nat .nat)) ∧
    env'.ReflectsNatNatNat ``Nat.mod Nat.mod := by
  have ⟨hn, htype, go, le, hspec⟩ :=
    M.WF.run wf (checkPrimitiveDef_natMod.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  refine ⟨hdef'.hasType.1, fun _ a b => ?_⟩
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have heval := (hspec.eval a b).mono hle
  exact ((hdef'.appDF ha |>.appDF hb).trans heval).toU

theorem checkPrimitiveDef_natShiftRight.extension {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (ht : TrExprS (ves.venv .safe) [] [] v.type type)
    (hv : TrExprS (ves.venv .safe) [] [] v.value f)
    (hf : (ves.venv .safe).HasType 0 [] f type)
    (hcheck : M.run env .safe {} [] fuel (checkPrimitiveDef v) = .ok b)
    (henv' : env'.WF) (hle : ves.venv .safe ≤ env')
    (hdef : env'.IsDefEq 0 [] (.const ``Nat.shiftRight []) f type) :
    env'.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight := by
  have ⟨hn, hdiv, htype, hspec⟩ :=
    M.WF.run wf (checkPrimitiveDef_natShiftRight.WF wf v hname ht hv hf) _ hcheck
  have hdef' := (htype.mono hle).defeqDF henv' trivial hdef
  intro _ a b
  have ha := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn a).mono hle
  have hb := (wf.hasPrimitives.natLit_type (U := 0) (Γ := []) hn b).mono hle
  have henv := (wf.tr (safety := .safe)).wf
  have hp := wf.hasPrimitives (safety := .safe)
  have heval := hspec.eval henv.ordered hp hn (hp.natDivType hdiv)
    (fun a b => (hp.natDiv hdiv a b).of_r henv trivial (hp.natLit_type hn (a / b))) a b
  exact ((hdef'.appDF ha |>.appDF hb).trans (heval.mono hle)).toU

end Environment
end Lean4Lean
