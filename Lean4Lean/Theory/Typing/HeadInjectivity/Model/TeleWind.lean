import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineTele

/-! # Winding typed telescope keys into a head observation

Adapted from PR #53, exact head 5a8c0d5f111809a95f4924c71e0e9bc8738d72e0,
for the current expression language. Actual typing of the head and telescope
keys determines the class of the applied head; no projection forms are used.
-/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- Equal-length argument substitutions determine the actual arguments. -/
theorem argSubst_inj : ∀ {as bs : List VExpr}, as.length = bs.length →
    VExpr.argSubst as = VExpr.argSubst bs → as = bs := by
  intro as bs hl h
  apply List.ext_getElem hl
  intro i h1 h2
  have e := congrFun h (as.length - 1 - i)
  rw [VExpr.argSubst_lt _ (by omega), VExpr.argSubst_lt _ (by omega)] at e
  simp only [show as.length - 1 - (as.length - 1 - i) = i by omega,
    show bs.length - 1 - (as.length - 1 - i) = i by omega] at e
  exact e

theorem typed_wrap_rigid : ∀ {keys : List Key} {τs : List Ob},
    TypedOb env U Δ cv (wrap keys (.rigid n ℓs m s)) τs →
    ∃ ks : List Key, ks.length = keys.length ∧ piCodChain ks (.sort s) ∈ τs
  | [], τs, h => by
    cases h with
    | rigid h => exact ⟨[], rfl, h⟩
  | k :: keys, τs, h => by
    obtain ⟨D, c, K⟩ := k
    simp only [wrap_cons] at h
    cases h with
    | app _ _ _ _ _ _ hcod hty =>
      obtain ⟨ks, hl, hm⟩ := typed_wrap_rigid hty
      obtain ⟨K₀, hK₀, -⟩ := hcod _ hm
      exact ⟨(D, c, K₀) :: ks, by simp [hl], hK₀⟩

theorem Ob.Le.piCodChain_sort_inv : ∀ {ks : List Key} {o : Ob},
    o ≼ piCodChain ks (.sort z) → ∃ ks' : List Key, ks'.length = ks.length ∧
      o = piCodChain ks' (.sort z)
  | [], o, h => ⟨[], rfl, h.sort_inv⟩
  | k :: ks, o, h => by
    simp only [piCodChain_cons] at h
    obtain ⟨K₀, y, rfl, -, hy⟩ := h.piCodOb_inv
    obtain ⟨ks', hl, rfl⟩ := Ob.Le.piCodChain_sort_inv hy
    exact ⟨(k.1, k.2.1, K₀) :: ks', by simp [hl], rfl⟩

theorem obs_wrapForalls_sort : ∀ {ds : List VExpr} {ks : List Key} {σ : VExpr.Subst}
    {S : ObSets}, Obs' σ S (.wrapForalls ds (.sort l)) (piCodChain ks (.sort z)) → z = l.eval
  | [], [], _, _, h => by
    have := Obs.sort_mem h; simp at this; exact this
  | [], _ :: _, _, _, h => by
    have := Obs.sort_mem h; simp at this
  | _ :: _, [], _, _, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, piCodChain_nil] at h
    cases h
  | _ :: ds, _ :: ks, _, _, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, piCodChain_cons] at h
    obtain ⟨-, -, _, -, h⟩ := Obs.piCodOb_mem h
    exact obs_wrapForalls_sort (ds := ds) (ks := ks) h

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The class of applications of the members of a function's class to the members of an
argument's class. -/
theorem appCls_eq (hf : env.HasType U Δ f (.forallE A B)) (ha : env.HasType U Δ a A) :
    appCls env U Δ (ElCls env U Δ (TyCls env U Δ (.forallE A B)) f)
        (ElCls env U Δ (TyCls env U Δ A) a) (TyCls env U Δ (B.inst a)) =
      ElCls env U Δ (TyCls env U Δ (B.inst a)) (.app f a) := by
  funext z; apply propext; constructor
  · rintro ⟨w, y, hw, hy, hz⟩
    have hfw := ElCls.collapse henv hΔ hf TyCls.self hw
    have hay := ElCls.collapse henv hΔ ha TyCls.self hy
    have happ : env.IsDefEq U Δ (.app f a) (.app w y) (B.inst a) := IsDefEq.appDF hfw hay
    rw [ElCls.eq_of_defeq TyCls.self happ]; exact hz
  · intro hz; exact ⟨_, _, ElCls.self, ElCls.self, hz⟩

/-- **Winding up a chain of typed keys**: an observation typed, at the class of the function
applied to the anchors, at codomain observations of the chain, wrapped in the keys, is typed at
observations of the telescope, at the class of the function. -/
theorem tele_wind (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∀ (f : VExpr), env.HasType U Δ f ((VExpr.wrapForalls ds R).subst σ) →
    ∃ ys : List VExpr, σ' = ys.foldl VExpr.Subst.cons σ ∧ ys.length = ds.length ∧
      List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys ∧
      env.HasType U Δ (VExpr.mkApps f ys) (R.subst σ') ∧
      ∀ o τc, (∀ τ ∈ τc, Obs' σ' S' R τ) →
        TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (R.subst σ')) (VExpr.mkApps f ys)) o τc →
        ∃ τ₀, (∀ τ ∈ τ₀, Obs' σ S (VExpr.wrapForalls ds R) τ) ∧
          TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ ((VExpr.wrapForalls ds R).subst σ)) f)
            (wrap keys o) τ₀ := by
  induction h with
  | nil =>
    intro f hf
    exact ⟨[], rfl, rfl, .nil, hf, fun o τc hτc ho => ⟨τc, hτc, ho⟩⟩
  | @cons c y K σ S A ds keys σ' S' hc hy hK hb _ ih =>
    intro f hf
    have hf' : env.HasType U Δ f (.forallE (A.subst σ) ((VExpr.wrapForalls ds R).subst σ.lift)) :=
      hf
    have hyA := hc.hasType henv hΔ hy
    have happ : env.HasType U Δ (.app f y) ((VExpr.wrapForalls ds R).subst (σ.cons y)) := by
      have := IsDefEq.appDF hf' hyA
      rwa [VExpr.subst_lift_inst] at this
    obtain ⟨ys, e, hl, hk, hg, hwind⟩ := ih (.app f y) happ
    refine ⟨y :: ys, e, by simp [hl], .cons hy hk, hg, fun o τc hτc ho => ?_⟩
    obtain ⟨τ₀, h1, h2⟩ := hwind o τc hτc ho
    obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
    obtain ⟨τs, h3, h4⟩ := pi_list hc hy hτk hkk hb h1
    refine ⟨τs, h3, h4 _ _ ?_⟩
    obtain ⟨_, _, _, ec⟩ := hc.mem henv hΔ hy
    rw [ec, ← VExpr.subst_lift_inst, show (VExpr.wrapForalls (A :: ds) R).subst σ =
      .forallE (A.subst σ) ((VExpr.wrapForalls ds R).subst σ.lift) from rfl,
      appCls_eq henv hΔ hf' hyA, VExpr.subst_lift_inst]
    exact h2

end

end Model
end VEnv
end Lean4Lean
