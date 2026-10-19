import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract

/-! # Head separation from the glued model

Adapted from PR #53 at 5a8c0d5f111809a95f4924c71e0e9bc8738d72e0
for the current constant-only language and actual WF soundness.

A chain of sort-typed equalities carries the observations of its left end into those of its
right end, up to subsumption (`Model.chain_sub`). Subsumption keeps the head constructor of
`sort` and `piDom` observations. A sort has a `sort` observation and a Pi type a `piDom`
observation. Neither a Pi type has a `sort` observation, nor does a spine of a rigid constant
have a `sort` or a `piDom` observation. So no chain relates a sort to a Pi type or to a rigid
spine, or a Pi type to a rigid spine. The theorems `sort_forallE`, `sort_rigid` and
`forallE_rigid` retain actual ordinary type-chain premises. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat}

/-- A Pi type has no `sort` observation. -/
theorem forallE_not_sort {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets}
    (h : Obs env U Δ σ S (.forallE A B) (.sort z)) : False := by
  rcases Obs.forallE_iff.1 h with h | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ <;>
    cases h

/-- A spine of a rigid constant has neither a `sort` nor a `piDom` observation. -/
theorem rigid_spine_not {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob}
    (hrig : env.Rigid c) (h : Obs env U Δ σ S (.mkApps (.const c ls) args) o)
    (ho : (∃ z, o = .sort z) ∨ ∃ D, o = .piDom D) : False := by
  have hna : o.NotApp := by rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial
  obtain ⟨keys, _, hc⟩ := wrap_of_obs_mkApps h
  rcases Obs.const_iff.1 hc with ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, e, _, _, _, _, hr, _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna hr.notApp
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna hr.notApp
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact wrapLams_mkApps_head _) (hrig df hdf lsP)

theorem sort_forallE (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.sort u) (.forallE A B)) : False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact forallE_not_sort ho

theorem sort_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact rigid_spine_not hrig ho (.inl ⟨_, rfl⟩)

theorem forallE_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (.piDom (A := A) (B := B))
  rw [l.piDom_inv] at ho
  exact rigid_spine_not hrig ho (.inr ⟨_, rfl⟩)

/-- Conversions on a Strong typing append actual ordinary type-chain links. -/
theorem strong_chain_peel
    (H : ∀ {B}, env.HasTypeStrong U Γ e B false → env.TypeChain U Γ A B)
    (h2 : env.HasTypeStrong U Γ e B b) : env.TypeChain U Γ A B := by
  cases b with
  | false => exact H h2
  | true =>
    generalize hb : true = b at h2
    induction h2 with
    | base h => exact H h
    | defeq _ h1 _ _ _ _ _ ih => exact (ih H rfl).tail h1.defeq
    | _ => cases hb

/-- A Strong sort typing has its canonical successor up to actual type-chain links. -/
theorem sort_type_chain (H : env.HasTypeStrong U Γ (.sort u) T b) :
    env.TypeChain U Γ (.sort (.succ u)) T := by
  refine strong_chain_peel (fun h => ?_) H
  cases h with
  | sort' hu hv he => exact .single (.sortDF hu hv (VLevel.succ_congr he))

/-- Retype an actual ordinary equality whose left endpoint is a sort at that
sort's canonical successor, without uniqueness or separation assumptions. -/
theorem sort_equality (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ (.sort u) t T) :
    env.IsDefEq U Γ (.sort u) t (.sort (.succ u)) :=
  (sort_type_chain (H.strong henv hΓ).hasType'.1).symm.defeqDF H

/-- The original untyped sort-injectivity contract follows from actual model soundness. -/
theorem sort_injective (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨T, H⟩ := H
  exact sort_sort henv.ordered henv.soundEnv hΓ
    (.single (sort_equality henv.ordered hΓ H))

/-- The original untyped sort/Pi-separation contract follows from model soundness. -/
theorem sort_forallE_separated (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.forallE A B)) : False := by
  obtain ⟨T, H⟩ := H
  exact sort_forallE henv.ordered henv.soundEnv hΓ
    (.single (sort_equality henv.ordered hΓ H))

end Model

end VEnv
end Lean4Lean
