import Lean4Lean.Theory.Typing.HeadInjectivity.Model.HTS

/-! # Simultaneous soundness and semantic typing

Adapted from PR #53 at 5a8c0d5f111809a95f4924c71e0e9bc8738d72e0 for the
existing expression language. `sound` is the simultaneous induction principle:
it retains the actual source environment and every stored-rule obligation.
Proving `RuleValid` for the actual stored rules and along declaration histories
remains required. `sound_no_rules` discharges that obligation only when the
actual source environment contains no equations.
-/

namespace Lean4Lean.VEnv.Model

open VExpr

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

theorem inst_liftN_bvar : ∀ (e : VExpr) (k : Nat), (liftN 1 e (k+1)).inst (.bvar 0) k = e
  | .bvar i, k => by
    simp only [liftN, inst, instVar, liftVar]
    split <;> rename_i h₁
    · rcases Nat.lt_or_ge i k with h | h
      · rw [if_pos h]
      · have : i = k := by omega
        subst this; rw [if_neg (Nat.lt_irrefl _), if_pos rfl]; simp
    · rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega
  | .sort .., _ | .const .., _ => rfl
  | .app .., k => by simp only [liftN, inst, inst_liftN_bvar]
  | .lam .., k | .forallE .., k => by simp only [liftN, inst, inst_liftN_bvar]


/-- **Validity of a rule**: the `extra` case of
soundness for `df` in the model of `env`, given the soundness and semantic typing of its typing
premises. -/
def RuleValid (env : VEnv) (df : VDefEq) : Prop :=
  ∀ (U : Nat) (Δ Γ : List VExpr) (ls : List VLevel) (u : VLevel), OnCtx Δ (env.IsType U) →
    (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
    SoundAt env U Δ [] (df.type.instL ls) (df.type.instL ls) (.sort u) ∧
      HTS env U Δ [] (df.type.instL ls) (.sort u) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Simultaneous soundness for actual derivations, conditional on their stored rules. -/
theorem sound {E : VEnv} (hle : E ≤ env) (hvalid : ∀ df, E.defeqs df → RuleValid env df)
    (H : E.IsDefEqStrong U Γ t t' T) :
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T := by
  induction H with
  | bvar hL _ hA ihA =>
    replace hA := hA.mono hle
    exact ⟨SoundAt.bvar hL, .bvar hL ⟨hA, ihA.1⟩, .bvar hL ⟨hA, ihA.1⟩⟩
  | symm _ ih => exact ⟨ih.1.symm henv hΔ, ih.2.2, ih.2.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans henv hΔ ih2.1, ih1.2.1, ih2.2.2⟩
  | @sortDF l l' _ _ _ h3 => exact ⟨SoundAt.sort h3, .sort', .sort'⟩
  | @constDF c ci ls ls' u Γ hci hlw hlw' hlen hls _ h7 h8 ih0 ih8 =>
    replace hci := hle.constants hci
    replace h7 := h7.mono hle
    replace h8 := h8.mono hle
    exact ⟨SoundAt.constDF henv hΔ hci hlw hlw' hls, .const hci hlw hlen ih0.2.1 ⟨h7.hasType.1, ih0.1.refl_l henv hΔ⟩,
      .conv (.const hci hlw' ((List.Forall₂.length_eq hls).symm.trans hlen) ih0.2.2
        ⟨h7.hasType.2, ih0.1.refl_r henv hΔ⟩) ⟨h8.symm, ih8.1.symm henv hΔ⟩⟩
  | @appDF Γ A u B v f f' a a' _ _ hA hB hf ha hBB ihA ihB ihf iha ihBB =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace hf := hf.mono hle
    replace ha := ha.mono hle
    replace hBB := hBB.mono hle
    exact ⟨SoundAt.appDF henv hΔ hA hB hf hBB ha ihB.1 ihf.1 iha.1 ihBB.1,
      .app ⟨hA, ihA.1⟩ ⟨hB, ihB.1⟩ ihf.2.1 hf.defeq.hasType.1 iha.2.1
        ⟨ha.hasType.1, iha.1.refl_l henv hΔ⟩,
      .conv (.app ⟨hA, ihA.1⟩ ⟨hB, ihB.1⟩ ihf.2.2 hf.defeq.hasType.2 iha.2.2
        ⟨ha.hasType.2, iha.1.refl_r henv hΔ⟩)
        ⟨hBB.symm, ihBB.1.symm henv hΔ⟩⟩
  | @lamDF Γ A A' u B v body body' h1 h2 hAA hB hB' hb hb' ihA ihB ihB' ihb ihb' =>
    replace hAA := hAA.mono hle
    replace hB := hB.mono hle
    replace hB' := hB'.mono hle
    replace hb := hb.mono hle
    replace hb' := hb'.mono hle
    exact ⟨SoundAt.lamDF henv hΔ hAA hb ihA.1 ihb.1, .lam ihA.2.1 ⟨hAA.hasType.1, ihA.1.refl_l henv hΔ⟩ ihb.2.1
        ⟨hb.hasType.1, ihb.1.refl_l henv hΔ⟩ ⟨hB, ihB.1⟩,
      .conv (.lam ihA.2.2 ⟨hAA.hasType.2, ihA.1.refl_r henv hΔ⟩ ihb'.2.2
        ⟨hb'.hasType.2, ihb'.1.refl_r henv hΔ⟩ ⟨hB', ihB'.1⟩)
        ⟨.forallEDF h1 h2 hAA.symm hB' hB,
          SoundAt.forallEDF henv hΔ hAA.symm hB' (ihA.1.symm henv hΔ) ihB'.1⟩⟩
  | @forallEDF Γ A A' u B B' v hu hv hAA hBB hBB' ihA ihB ihB' =>
    replace hAA := hAA.mono hle
    replace hBB := hBB.mono hle
    replace hBB' := hBB'.mono hle
    exact ⟨SoundAt.forallEDF henv hΔ hAA hBB ihA.1 ihB.1,
      .forallE ihA.2.1 ⟨hAA.hasType.1, ihA.1.refl_l henv hΔ⟩ ihB.2.1
        ⟨hBB.hasType.1, ihB.1.refl_l henv hΔ⟩,
      .forallE ihA.2.2 ⟨hAA.hasType.2, ihA.1.refl_r henv hΔ⟩ ihB'.2.2
        ⟨hBB'.hasType.2, ihB'.1.refl_r henv hΔ⟩⟩
  | defeqDF _ hAB _ ihAB ihe =>
    replace hAB := hAB.mono hle
    exact ⟨SoundAt.defeqDF henv hΔ hAB ihAB.1 ihe.1, .conv ihe.2.1 ⟨hAB, ihAB.1⟩, .conv ihe.2.2 ⟨hAB, ihAB.1⟩⟩
  | @beta Γ A u B v e e' _ _ hA hB he he' _ _ ihA ihB ihe ihe' _ ihee' =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace he := he.mono hle
    replace he' := he'.mono hle
    exact ⟨SoundAt.beta henv hΔ hA hB he he' ihA.1 ihB.1 ihe.1 ihe'.1 ihee'.1, .beta_lhs, ihee'.2.1⟩
  | @eta Γ A u B v e h1 h2 hA hB hB' he he' hA' ihA ihB ihB' ihe ihe' ihA' =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace hB' := hB'.mono hle
    replace he := he.mono hle
    replace he' := he'.mono hle
    replace hA' := hA'.mono hle
    have e0 : (B.liftN 1 1).inst (.bvar 0) = B := inst_liftN_bvar B 0
    have hb0 : env.IsDefEqStrong U (A :: Γ) (.bvar 0) (.bvar 0) A.lift := .bvar .zero h1 hA'
    have hbody : HTS env U Δ (A :: Γ) (.app e.lift (.bvar 0)) B := by
      have := HTS.app ⟨hA', ihA'.1⟩ ⟨hB', ihB'.1⟩ ihe'.2.1 he'.defeq.hasType.1
        (.bvar .zero ⟨hA', ihA'.1⟩) ⟨hb0, SoundAt.bvar .zero⟩
      rwa [e0] at this
    have hBB : env.IsDefEqStrong U (A :: Γ) ((B.liftN 1 1).inst (.bvar 0))
        ((B.liftN 1 1).inst (.bvar 0)) (.sort v) := by rw [e0]; exact hB
    have sbody : SD env U Δ (A :: Γ) (.app e.lift (.bvar 0)) (.app e.lift (.bvar 0)) B := by
      have d := IsDefEqStrong.appDF h1 h2 hA' hB' he' hb0 hBB
      have sd := SoundAt.appDF henv hΔ hA' hB' he' hBB hb0 ihB'.1 ihe'.1
        (SoundAt.bvar .zero) (by rw [e0]; exact ihB.1)
      rw [e0] at d sd
      exact ⟨d, sd⟩
    exact ⟨SoundAt.eta henv hΔ he ihe.1, .lam ihA.2.1 ⟨hA, ihA.1⟩ hbody sbody ⟨hB, ihB.1⟩, ihe.2.1⟩
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact ⟨SoundAt.proofIrrel henv hΔ ihp.1 ihh.1 ihh'.1, ihh.2.1, ihh'.2.1⟩
  | @extra df ls u Γ hdf hlw hlen hu ht0 _ _ hl hr iht0 _ _ ihl ihr =>
    exact ⟨hvalid df hdf _ _ _ _ _ hΔ hlw hlen (ht0.mono hle) ⟨iht0.1, iht0.2.1⟩ (hl.mono hle)
      ⟨ihl.1, ihl.2.1⟩ (hr.mono hle) ⟨ihr.1, ihr.2.1⟩, ihl.2.1, ihr.2.1⟩

/-- The stored-rule premise is discharged by the actual absence of equations in `E`. -/
theorem sound_no_rules {E : VEnv} (hle : E ≤ env) (hE : ∀ df, ¬ E.defeqs df)
    (H : E.IsDefEqStrong U Γ t t' T) :
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T :=
  sound henv hΔ hle (fun df hd => (hE df hd).elim) H

end

end Lean4Lean.VEnv.Model
