import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Classes

/-! # Application and beta for anchored typed classes

Ported from the class-only portion of kim-em/lean4lean PR #53, head
`5a8c0d5f111809a95f4924c71e0e9bc8738d72e0` (`Interp`, `Obs`, and `HTS`).
These results use actual typed substitutions and definitional equalities.
They establish the class interface needed by the observation model; observation
soundness and head separation remain separate obligations.
-/

namespace Lean4Lean.VEnv.Model

/-- The element class computed from an actual anchor substitution. -/
def vcls (env : VEnv) (U : Nat) (Δ : List VExpr) (σ : VExpr.Subst)
    (t T : VExpr) : VExpr → Prop :=
  ElCls env U Δ (TyCls env U Δ (T.subst σ)) (t.subst σ)

/-- Applications of members of two classes, closed at a supplied result class. -/
def appCls (env : VEnv) (U : Nat) (Δ : List VExpr)
    (cv c C : VExpr → Prop) : VExpr → Prop :=
  fun z => ∃ w y, cv w ∧ c y ∧ ElCls env U Δ C (.app w y) z

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

theorem _root_.Lean4Lean.VExpr.inst_subst_cons {B a : VExpr} {σ : VExpr.Subst} :
    (B.inst a).subst σ = B.subst (σ.cons (a.subst σ)) := by
  rw [VExpr.inst_eq, VExpr.subst_subst]
  congr 1; funext i; cases i <;> rfl

theorem _root_.Lean4Lean.VExpr.subst_lift_inst {e a : VExpr} {σ : VExpr.Subst} :
    (e.subst σ.lift).inst a = e.subst (σ.cons a) := by
  rw [VExpr.inst_eq, VExpr.subst_subst]
  congr 1; funext i; cases i with
  | zero => rfl
  | succ i => simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons]

theorem vcls_tail {σ : VExpr.Subst} {A : VExpr} :
    vcls env U Δ σ (.bvar (i+1)) A.lift = vcls env U Δ σ.tail (.bvar i) A := by
  simp only [vcls, VExpr.lift_subst]; rfl

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The value class of an application is the class of the applications of the members of the
function's class to the members of the argument's class. -/
theorem vcls_app (W : Ctx.SubstEq env U Δ σ σ Γ) (hf : env.HasType U Γ f (.forallE A B))
    (ha : env.HasType U Γ a A) :
    vcls env U Δ σ (.app f a) (B.inst a) =
      appCls env U Δ (vcls env U Δ σ f (.forallE A B))
        (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
        (TyCls env U Δ (B.subst (σ.cons (a.subst σ)))) := by
  have hf' := hf.substDF henv W.wf hΔ W
  have ha' := ha.substDF henv W.wf hΔ W
  unfold vcls
  rw [VExpr.inst_subst_cons]
  show ElCls env U Δ _ (.app (f.subst σ) (a.subst σ)) = _
  funext z; apply propext; constructor
  · intro hz; exact ⟨_, _, ElCls.self, ElCls.self, hz⟩
  · rintro ⟨w, y, hw, hy, hz⟩
    have hfw := ElCls.collapse henv hΔ hf' TyCls.self hw
    have hay := ElCls.collapse henv hΔ ha' TyCls.self hy
    have happ : env.IsDefEq U Δ (.app (f.subst σ) (a.subst σ)) (.app w y)
        (B.subst (σ.cons (a.subst σ))) := by
      have := IsDefEq.appDF hfw hay
      rwa [← VExpr.subst_inst, VExpr.inst_subst_cons] at this
    rw [ElCls.eq_of_defeq TyCls.self happ]; exact hz

/-- Type classes along a type chain agree under a typed substitution. -/
theorem TypeChain.tyCls_subst_of_ctx (W : Ctx.SubstEq env U Δ v v Γ) (h : env.TypeChain U Γ X Y) :
    TyCls env U Δ (X.subst v) = TyCls env U Δ (Y.subst v) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W)
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W))

/-- The value class of the application of a lambda to a member of a typed class is the class
of the instantiated body (beta). -/
theorem vcls_beta (W : Ctx.SubstEq env U Δ σ σ Γ) (hA : env.HasType U Γ A (.sort u))
    (hb : env.HasType U (A :: Γ) b B)
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c) (hy : c y) :
    appCls env U Δ (vcls env U Δ σ (.lam A b) (.forallE A B)) c
        (TyCls env U Δ (B.subst (σ.cons y))) = vcls env U Δ (σ.cons y) b B := by
  have hyA := hc.hasType henv hΔ hy
  have hA' := hA.substDF henv W.wf hΔ W
  have W1 : Ctx.SubstEq env U (A.subst σ :: Δ) σ.lift σ.lift (A :: Γ) := W.lift henv hA
  have hb' := hb.substDF henv W1.wf (show OnCtx (A.subst σ :: Δ) (env.IsType U) from ⟨hΔ, _, hA'⟩) W1
  have hlam : env.HasType U Δ ((VExpr.lam A b).subst σ) ((VExpr.forallE A B).subst σ) :=
    IsDefEq.lamDF hA' hb'
  have hbeta : env.IsDefEq U Δ (.app ((VExpr.lam A b).subst σ) y) (b.subst (σ.cons y))
      (B.subst (σ.cons y)) := by
    have := IsDefEq.beta hb' hyA
    rwa [VExpr.subst_lift_inst, VExpr.subst_lift_inst] at this
  unfold vcls
  funext z; apply propext; constructor
  · rintro ⟨w, y', hw, hy', hz⟩
    have hlw := ElCls.collapse henv hΔ hlam TyCls.self hw
    have hyy := hc.defeq henv hΔ hy hy'
    have happ : env.IsDefEq U Δ (.app ((VExpr.lam A b).subst σ) y) (.app w y')
        (B.subst (σ.cons y)) := by
      have := IsDefEq.appDF hlw hyy
      rwa [VExpr.subst_lift_inst] at this
    rw [ElCls.eq_of_defeq TyCls.self (hbeta.symm.trans happ)]; exact hz
  · intro hz
    refine ⟨_, _, ElCls.self, hy, ?_⟩
    rw [ElCls.eq_of_defeq TyCls.self hbeta]; exact hz

/-- Value classes agree at related anchors. -/
theorem vcls_substEq (W : Ctx.SubstEq env U Δ σ σ' Γ) (ht : env.HasType U Γ t T) :
    vcls env U Δ σ t T = vcls env U Δ σ' t T := by
  obtain ⟨u, hT⟩ := ht.isType henv W.wf
  unfold vcls
  rw [ElCls.eq_of_defeq TyCls.self (ht.substDF henv W.wf hΔ W),
    TyCls.eq_of_defeq (hT.substDF henv W.wf hΔ W)]

/-- Value classes of definitionally equal terms agree. -/
theorem vcls_defeq (W : Ctx.SubstEq env U Δ σ σ Γ) (h : env.IsDefEq U Γ t t' T) :
    vcls env U Δ σ t T = vcls env U Δ σ t' T := by
  unfold vcls; exact ElCls.eq_of_defeq TyCls.self (h.substDF henv W.wf hΔ W)

/-- Actual typed function eta identifies the anchored classes. -/
theorem vcls_eta (W : Ctx.SubstEq env U Δ σ σ Γ)
    (hf : env.HasType U Γ f (.forallE A B)) :
    vcls env U Δ σ (.lam A (.app f.lift (.bvar 0))) (.forallE A B) =
      vcls env U Δ σ f (.forallE A B) :=
  vcls_defeq henv hΔ W (.eta hf)

omit henv hΔ in
theorem vcls_closed {e T : VExpr} (he : e.ClosedN) (hT : T.ClosedN) :
    vcls env U Δ σ e T = ElCls env U Δ (TyCls env U Δ T) e := by
  simp only [vcls, he.subst_eq .zero, hT.subst_eq .zero]

/-- Value classes at definitionally equal types agree. -/
theorem vcls_conv (W : Ctx.SubstEq env U Δ σ σ Γ) (h : env.IsDefEq U Γ T T' (.sort u)) :
    vcls env U Δ σ e T = vcls env U Δ σ e T' := by
  simp only [vcls, TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W)]

end

end Lean4Lean.VEnv.Model
