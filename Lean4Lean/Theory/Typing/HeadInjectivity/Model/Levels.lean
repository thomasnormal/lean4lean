import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Interp

/-! # Level invariance of the observation interpretation

Adapted from kim-em/lean4lean PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0 for the existing expression fragment.
Stored rules and their actual binding/typing conditions are preserved. These
structural results require neither environment validity nor typed anchors.
-/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}
local notation "Obs'" => Obs env U Δ

theorem _root_.Lean4Lean.VEnv.Model.map_eval_eq {ls ls' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) ls ls') : ls.map (·.eval) = ls'.map (·.eval) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h

theorem RuleBind.lvEq
    (h : RuleBind env U Δ doms ls lead msLen fs mC keys Km τ S')
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U)
    (hls : List.Forall₂ (· ≈ ·) ls ls') :
    RuleBind env U Δ doms ls' lead msLen fs mC keys Km τ S' := by
  refine ⟨h.1, fun x hx => ?_⟩
  have e : TyCls env U Δ ((binderTy doms ls x).subst τ) =
      TyCls env U Δ ((binderTy doms ls' x).subst τ) :=
    TyCls.eq_of_lvEq ((LvEq.instL _ w1 w2 hls).subst τ)
  have hd := h.2 x hx
  rw [e] at hd
  exact hd

/-- The value class of a constant transfers to equivalent levels. -/
theorem _root_.Lean4Lean.VEnv.Model.constCls_lvEq {T : VExpr} {ls ls' : List VLevel}
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U) (hls : List.Forall₂ (· ≈ ·) ls ls') :
    ElCls env U Δ (TyCls env U Δ (T.instL ls)) (.const n ls) =
      ElCls env U Δ (TyCls env U Δ (T.instL ls')) (.const n ls') := by
  rw [TyCls.eq_of_lvEq (LvEq.instL T w1 w2 hls), ElCls.eq_of_lvEq (LvEq.const w1 w2 hls)]

namespace Obs

/-- **Level invariance**: the observations of a term are those of its level variants
(classes are saturated by `LvEq`, levels are observed through `VLevel.eval`). -/
theorem lvEq (h : Obs' σ S t o) (ht : LvEq U t t') : Obs' σ S t' o := by
  induction h generalizing t' with
  | bvar h => cases ht; exact .bvar h
  | @sort _ _ l =>
    cases ht with
    | refl => exact .sort
    | sort _ _ h3 => have : l.eval = _ := h3; rw [this]; exact .sort
  | @piDom _ _ A B =>
    cases ht with
    | refl => exact .piDom
    | forallE h1 _ => rw [TyCls.eq_of_lvEq (h1.subst _)]; exact .piDom
  | piDomOb _ ih =>
    cases ht with
    | refl => exact .piDomOb (ih .refl)
    | forallE h1 _ => exact .piDomOb (ih h1)
  | piCod h1 h2 =>
    cases ht with
    | refl => exact .piCod h1 h2
    | forallE l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1
      rw [TyCls.eq_of_lvEq (l2.subst _)]; exact .piCod h1 h2
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    cases ht with
    | refl => exact .piCodOb h1 (fun τ hτ => ih2 τ hτ .refl) h3 hb h4 (ih5 .refl)
    | forallE l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1
      exact .piCodOb h1 (fun τ hτ => ih2 τ hτ l1) h3 hb h4 (ih5 l2)
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    cases ht with
    | refl => exact .lam h1 (fun τ hτ => ih2 τ hτ .refl) h3 hb h4 (ih5 .refl)
    | lam l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1 ⊢
      exact .lam h1 (fun τ hτ => ih2 τ hτ l1) h3 hb h4 (ih5 l2)
  | app _ h2 _ h4 ih1 ih3 =>
    cases ht with
    | refl => exact .app (ih1 .refl) h2 (fun k hk => ih3 k hk .refl) h4
    | app l1 l2 =>
      exact .app (ih1 l1) (h2.trans (ElCls.eq_of_lvEq (l2.subst _)))
        (fun k hk => ih3 k hk l2) h4
  | const h0 h1 _ h3 h4 ih2 =>
    cases ht with
    | refl => exact .const h0 h1 (fun τ hτ => ih2 τ hτ .refl) h3 h4
    | const w1 w2 w3 =>
      exact .const h0 h1 (fun τ hτ => ih2 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h3) (map_eval_eq w3 ▸ h4)
  | ctor h0 h1 _ h3 h4 hb ih2 =>
    cases ht with
    | refl => exact .ctor h0 h1 (fun τ hτ => ih2 τ hτ .refl) h3 h4 hb
    | const w1 w2 w3 =>
      exact .ctor h0 h1 (fun τ hτ => ih2 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h3) (map_eval_eq w3 ▸ h4) hb
  | rule h1 h2 h3 h4 _ h6 h7 h8 _ h10 h11 hb _ ih5 ih9 ih12 =>
    cases ht with
    | refl =>
      exact .rule h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ .refl) h6 h7 h8 (fun e => ih9 e .refl) h10
        h11 hb (ih12 .refl)
    | const w1 w2 w3 =>
      exact .rule h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h6) h7 h8
        (fun e => ih9 e (.instL _ w1 w2 w3)) h10 (h11.lvEq w1 w2 w3) hb (ih12 (.instL _ w1 w2 w3))
  | delta h1 h2 h3 _ h5 _ ih4 ih6 =>
    cases ht with
    | refl => exact .delta h1 h2 h3 (fun τ hτ => ih4 τ hτ .refl) h5 (ih6 .refl)
    | const w1 w2 w3 =>
      exact .delta h1 h2 h3 (fun τ hτ => ih4 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h5) (ih6 (.instL _ w1 w2 w3))

/-- Exact observation invariance under well-formed level variants. -/
theorem lvEq_iff (ht : LvEq U t t') : Obs' σ S t o ↔ Obs' σ S t' o :=
  ⟨(·.lvEq ht), (·.lvEq ht.symm)⟩

/-- Constant observations transfer between equivalent well-formed levels at
arbitrary valuations; no separate transfer certificate for the type is needed. -/
theorem const_levels (h : Obs' σ S (.const n ls) o)
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U)
    (hls : List.Forall₂ (· ≈ ·) ls ls') : Obs' σ' S' (.const n ls') o :=
  const_indep.1 (h.lvEq (.const w1 w2 hls))

end Obs

/-- Typing observations at a type transfers to its level variants. -/
theorem TypedAt.lvEq (h : TypedAt env U Δ cv σ S T o) (ht : LvEq U T T') :
    TypedAt env U Δ cv σ S T' o :=
  let ⟨τs, hτ, hty⟩ := h; ⟨τs, fun τ h => (hτ τ h).lvEq ht, hty⟩

end Model
end VEnv
end Lean4Lean
