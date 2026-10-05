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

end VEnv

private theorem TrExprS.weakBV_closed (henv : env.Ordered)
    (W : VLCtx.BVLift [] Δ dn 0 n 0) (h : TrExprS env Us [] e e') :
    TrExprS env Us Δ e (e'.liftN n) := by
  have h' := h.weakBV henv W
  rwa [Expr.liftLooseBVars_eq_self (s := 0) h.closed.looseBVarRange_le] at h'

namespace Environment
open TypeChecker

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

end Environment
end Lean4Lean
