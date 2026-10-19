import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Tele

/-! # Soundness of dependent function formation

Adapted from kim-em/lean4lean PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0. This is the actual forall formation
case of simultaneous observation soundness: its recursive premises retain
both semantic inclusion and typing at related anchors. No rule validity or
stronger environment invariant is assumed. Other expression cases and the
declaration-history proof remain separate obligations.
-/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}
local notation "Obs'" => Obs env U Δ

theorem imax_eval_zero {u v : VLevel} {ns : List Nat}
    (h : (VLevel.imax u v).eval ns = 0) : v.eval ns = 0 := by
  change (if v.eval ns = 0 then 0 else max (u.eval ns) (v.eval ns)) = 0 at h
  split at h
  · assumption
  · rename_i hv
    exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (Nat.le_max_right _ _)))

/-- A variable's strong typing derivation carries the proved base soundness. -/
theorem SD.bvar (hL : Lookup Γ i A) (wu : u.WF U) (hA : SD env U Δ Γ A A (.sort u)) :
    SD env U Δ Γ (.bvar i) (.bvar i) A :=
  ⟨.bvar hL wu hA.1, SoundAt.bvar hL⟩

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Key typing transfers from `A` under `σ` to `A` under `σ'` along `A ≡ A'`. -/
theorem keys_transfer {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ cv σ S A k) :
    (∀ k ∈ K, TypedAt env U Δ cv σ' S A' k) ∧ (∀ k ∈ K, TypedAt env U Δ cv σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => ((hK k hk).mono_le h1).mono_le h2⟩

/-- Key typing transfers back from `A'` under `σ'` to `A` under `σ` and `σ'`. -/
theorem keys_transfer_symm {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ cv σ' S A' k) :
    (∀ k ∈ K, TypedAt env U Δ cv σ S A k) ∧ (∀ k ∈ K, TypedAt env U Δ cv σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').2.1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => (hK k hk).mono_le h2⟩

theorem SoundAt.forallEDF (hAA : env.IsDefEqStrong U Γ A A' (.sort u))
    (hBB : env.IsDefEqStrong U (A::Γ) B B' (.sort v)) (ihA : SoundAt env U Δ Γ A A' (.sort u))
    (ihB : SoundAt env U Δ (A::Γ) B B' (.sort v)) :
    SoundAt env U Δ Γ (.forallE A B) (.forallE A' B') (.sort (.imax u v)) := by
  intro σ σ' S W tv tv'
  have hΓ := W.wf
  have hA := hAA.defeq.hasType.1
  have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
    TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
  have eDA : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
    TyCls.eq_of_defeq (hA.substDF henv hΓ hΔ W)
  have IHA := ihA σ σ' S W tv tv'
  have imax0 : ∀ ns, (VLevel.imax u v).eval ns = 0 → v.eval ns = 0 := by
    intro ns h; exact imax_eval_zero h
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact ⟨_, by rw [eD]; exact .piDom, .refl⟩
    · obtain ⟨p', hp', l⟩ := IHA.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
    · have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
      exact ⟨_, by rw [eC]; exact .piCod (hc.congr_D eD) hy, .refl⟩
    · have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eDA) hy hbK hK2)).1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      exact ⟨_, .piCodOb (hc.congr_D eD) h1 h2 hbK hy hp', .piCodOb_of_covers Covers.refl l⟩
  · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact ⟨_, by rw [← eD]; exact .piDom, .refl⟩
    · obtain ⟨p', hp', l⟩ := IHA.2.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
    · have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
      exact ⟨_, by rw [← eC]; exact .piCod hc' hy, .refl⟩
    · have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eDA) hy hbK hK2)).2.1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      exact ⟨_, .piCodOb hc' h1 h2 hbK hy hp', .piCodOb_of_covers Covers.refl l⟩
  · refine typedAt_sort_iff.2 ?_
    rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact .piDom (List.mem_singleton_self _)
    · exact .piDomOb (List.mem_singleton_self _)
    · exact .piCod (List.mem_singleton_self _)
    · have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      have := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eDA) hy hbK hK2)).2.2.1 p hp
      exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0
  · refine typedAt_sort_iff.2 ?_
    rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact .piDom (List.mem_singleton_self _)
    · exact .piDomOb (List.mem_singleton_self _)
    · exact .piCod (List.mem_singleton_self _)
    · have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eDA) hy hbK hK2)).2.2.2 p hp
      exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0

/-- The actual reflexive strong Pi derivation and its simultaneous soundness. -/
theorem SD.forallE (wu : u.WF U) (wv : v.WF U)
    (hA : SD env U Δ Γ A A (.sort u)) (hB : SD env U Δ (A :: Γ) B B (.sort v)) :
    SD env U Δ Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
  ⟨.forallEDF wu wv hA.1 hB.1 hB.1, SoundAt.forallEDF henv hΔ hA.1 hB.1 hA.2 hB.2⟩

end

end Model
end VEnv
end Lean4Lean
