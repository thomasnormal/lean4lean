import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Separation

/-! # Type uniqueness and dependent Pi injectivity from actual chain fields

The uniqueness induction and chain collapse adapt PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0 to the current Strong constructors.
This language needs no projection/eliminator congruence machinery. The stratified
inversion below retains the original heights, using their spare conversion step
only to align the right codomain's universe with the left one.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Structural uniqueness up to actual heterogeneous sort-typed links. -/
theorem HasTypeStrong.uniq_chain_of_chainHeadInjectivity (henv : env.WF)
    (core : env.ChainHeadInjectivity) (h1 : env.HasTypeStrong U Γ e A b) :
    OnCtx Γ (env.IsType U) →
    ∀ {B b₂}, env.HasTypeStrong U Γ e B b₂ → env.TypeChain U Γ A B := by
  induction h1 with
  | base _ ih => exact ih
  | defeq _ hAB _ _ _ _ _ ih =>
    intro hΓ B b₂ h2
    exact TypeChain.head hAB.defeq.symm (ih hΓ h2)
  | bvar a1 _ a3 _ =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | bvar b1 _ _ => cases a1.uniq b1; exact .refl a3.hasType
  | sort' a1 a2 a3 =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | sort' _ b2 b3 => exact .single (.sortDF a2 b2 (VLevel.succ_congr (a3.symm.trans b3)))
  | const a1 _ _ _ _ a6 _ _ =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | const b1 _ _ _ _ _ => cases a1.symm.trans b1; exact .refl a6.hasType
  | app _ _ _ _ _ _ a7 _ _ _ _ ih6 _ _ =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | app _ _ _ _ _ b6 _ _ =>
      have ⟨_, hB⟩ := core.forallE_chain hΓ (ih6 hΓ b6)
      exact hB.instN henv.ordered a7.hasType .zero
  | lam _ _ a3 _ _ _ _ _ ih5 _ =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | lam _ _ _ _ b5 _ =>
      exact (ih5 ⟨hΓ, _, a3.hasType⟩ b5).map
        fun h => ⟨_, .forallEDF a3.hasType h⟩
  | @forallE Γ A u body v a1 a2 a3 _ ih3 ih4 =>
    intro hΓ B b₂ h2
    refine Model.strong_chain_peel (fun h2 => ?_) h2
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have e1 := core.sort_sort hΓ (ih3 hΓ b3)
      have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, a3.hasType⟩
      have e2 := core.sort_sort hΓA (ih4 hΓA b4)
      exact .single (.sortDF ⟨a1, a2⟩ ⟨b1, b2⟩ (VLevel.imax_congr e1 e2))

/-- Every link can be retyped at the actual left endpoint's universe. -/
theorem TypeChain.collapse_of_chainHeadInjectivity (henv : env.WF)
    (core : env.ChainHeadInjectivity) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.TypeChain U Γ A B) (hA : env.HasType U Γ A (.sort u)) :
    env.IsDefEq U Γ A B (.sort u) := by
  have retype {X Y w} (hX : env.HasType U Γ X (.sort u))
      (h : env.IsDefEq U Γ X Y (.sort w)) : env.IsDefEq U Γ X Y (.sort u) := by
    have s1 := (hX.strong henv.ordered hΓ).hasType'.1
    have s2 := (h.strong henv.ordered hΓ).hasType'.1
    have e := core.sort_sort hΓ (s2.uniq_chain_of_chainHeadInjectivity henv core hΓ s1)
    exact .defeqDF (.sortDF (h.sort_r henv.ordered hΓ) (hX.sort_r henv.ordered hΓ) e) h
  induction H with
  | single h => let ⟨_, h⟩ := h; exact retype hA h
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (retype ih.hasType.2 h)

/-- Ordinary uniqueness, before the old stratified uniqueness development. -/
theorem IsDefEq.uniq_of_chainHeadInjectivity (henv : env.WF)
    (core : env.ChainHeadInjectivity) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    ∃ u, env.IsDefEq U Γ A B (.sort u) := by
  have chain := (h1.strong henv.ordered hΓ).hasType'.2.uniq_chain_of_chainHeadInjectivity
    henv core hΓ (h2.strong henv.ordered hΓ).hasType'.1
  obtain ⟨u, hA⟩ := h1.isType henv.ordered hΓ
  exact ⟨u, chain.collapse_of_chainHeadInjectivity henv core hΓ hA⟩

/-- Untyped Pi equality inverted at the actual left domain/codomain universes. -/
theorem IsDefEqU.forallE_inv_at (henv : env.WF) (core : env.ChainHeadInjectivity)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U (A :: Γ) B (.sort v)) :
    env.IsDefEq U Γ A A' (.sort u) ∧ env.IsDefEq U (A :: Γ) B B' (.sort v) := by
  obtain ⟨T, H⟩ := H
  have hPi : env.HasType U Γ (.forallE A B) (.sort (.imax u v)) := .forallE hA hB
  have chain := (H.strong henv.ordered hΓ).hasType'.1.uniq_chain_of_chainHeadInjectivity
    henv core hΓ (hPi.strong henv.ordered hΓ).hasType'.1
  have h := core.forallE_chain hΓ (.single (chain.defeqDF H))
  exact ⟨h.1.collapse_of_chainHeadInjectivity henv core hΓ hA,
    h.2.collapse_of_chainHeadInjectivity henv core ⟨hΓ, _, hA⟩ hB⟩

/-- Removing conversions from a stratified Pi typing retains the given height. -/
theorem HasTypeStratified.forallE_core
    (H : env.HasTypeStratified U Γ (.forallE A B) T true n) :
    ∃ m u v, m + 1 = n ∧ u.WF U ∧ v.WF U ∧
      env.HasTypeStratified U Γ A (.sort u) true m ∧
      env.HasTypeStratified U (A :: Γ) B (.sort v) true m := by
  obtain ⟨_, h⟩ := H.to_core
  cases h with
  | forallE hu hv hA hB => exact ⟨_, _, _, rfl, hu, hv, hA, hB⟩

/-- The original stratified Pi-injectivity contract, including both exact bounds. -/
theorem IsDefEqU.forallE_inv_stratified_of_chainHeadInjectivity (henv : env.WF)
    (core : env.ChainHeadInjectivity) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A :: Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A :: Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A' :: Γ) B' (.sort u) true n' := by
  obtain ⟨m, u, v, rfl, hu, hv, hA, hB⟩ := h2.forallE_core
  obtain ⟨m', u', v', rfl, hu', hv', hA', hB'⟩ := h3.forallE_core
  obtain ⟨hAA, hBB⟩ := H.forallE_inv_at henv core hΓ hA.hasType hB.hasType
  have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA.hasType⟩
  have hB'left := hAA.symm.defeqDF_l henv.ordered hB'.hasType
  have ⟨_, hlevels⟩ := hBB.uniq_of_chainHeadInjectivity henv core hΓA hB'left
  have e : v ≈ v' := Model.sort_injective henv hΓA ⟨_, hlevels⟩
  refine ⟨⟨u, hAA, hA.mono (Nat.le_succ _)⟩, v, hBB, hB.mono (Nat.le_succ _), ?_⟩
  exact .defeq (u := .succ v') hv' (.sortDF hv' hv e.symm)
    (.base (.sort' hv' hv' rfl)) (.base (.sort' hv hv' e)) hB'

end VEnv
end Lean4Lean
