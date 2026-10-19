import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound
import Lean4Lean.Theory.Typing.RewriteRules

/-! # Validity of actual delta equations

The delta-rule argument of PR #53, exact head
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0, specialized to the existing
expression and environment language. Actual declaration-history rewrite
metadata supplies lookup, ownership and exclusion of competing rules.
No validity assumption for quotient equations is discharged here.
-/

namespace Lean4Lean.VEnv

/-- Bare-constant equations have their declared type and own their head. -/
structure DeltaRules (env : VEnv) : Prop where
  const : ∀ df, env.defeqs df → ∀ n ls, df.lhs = .const n ls →
    ls = VLevel.params df.uvars ∧ env.constants n = some ⟨df.uvars, df.type⟩
  excl : ∀ df df', env.defeqs df → env.defeqs df' → ∀ n ls ls',
    df.lhs = .const n ls → df'.lhs.stripLams.appHead = .const n ls' → df' = df

theorem RewriteMetadata.deltaRules (M : RewriteMetadata env) : DeltaRules env := by
  constructor
  · intro df hdf n ls h
    rcases M.classify hdf with rfl | ⟨ci, rfl⟩
    · cases h
    · cases h; exact ⟨rfl, M.lookup hdf⟩
  · intro df df' hdf hdf' n ls ls' h h'
    rcases M.classify hdf with rfl | ⟨ci, rfl⟩
    · cases h
    · cases h
      rcases M.classify hdf' with rfl | ⟨ci', rfl⟩
      · have hn : ci.name = ``Quot.lift := (VExpr.const.inj h').1.symm
        exact (M.quotientNames hdf hdf' _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hn).elim
      · have hn : ci'.name = ci.name := (VExpr.const.inj h').1
        cases M.unique hdf' hdf hn
        rfl

theorem WF.deltaRules (H : env.WF) : DeltaRules env := H.rewriteMetadata.deltaRules

namespace Model

theorem quotConstructorMajor : quotDefEq.HasConstructorMajor ``Quot.mk :=
  ⟨.mkApps (.const ``Quot.lift [.param 0, .param 1])
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1], [.param 0],
    [.bvar 5, .bvar 4, .bvar 0], rfl⟩

/-- In this environment language, the only constructor major is Quot.mk. -/
theorem RewriteMetadata.installedCtor (M : VEnv.RewriteMetadata env)
    (h : IsInstalledCtor env c) : c = ``Quot.mk := by
  obtain ⟨df, hdf, hmajor⟩ := h
  rcases M.classify hdf with rfl | ⟨ci, rfl⟩
  · exact hmajor.unique quotConstructorMajor
  · obtain ⟨_, _, _, h⟩ := hmajor
    cases h

end Model

theorem WF.installed_constructor_rigid (H : env.WF)
    (h : Model.IsInstalledCtor env c) : env.Rigid c := by
  have M := H.rewriteMetadata
  have hc := Model.RewriteMetadata.installedCtor M h
  subst hc
  intro df hdf ls he
  rcases M.classify hdf with rfl | ⟨ci, rfl⟩
  · exact (by decide : (``Quot.lift : Name) ≠ ``Quot.mk) (VExpr.const.inj he).1
  · have hn : ci.name = ``Quot.mk := (VExpr.const.inj he).1
    obtain ⟨df, hctorDF, hmajor⟩ := h
    rcases M.classify hctorDF with rfl | ⟨ci', rfl⟩
    · exact M.quotientNames hdf hctorDF _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hn
    · obtain ⟨_, _, _, he⟩ := hmajor
      cases he

namespace Model

variable {env : VEnv}

theorem wrapLams_mkApps_head (ds : List VExpr) :
    (VExpr.wrapLams ds (VExpr.mkApps (.const n ls) (as ++ [a]))).stripLams.appHead =
      .const n ls := by
  rw [VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]
  exact VExpr.appHead_mkApps

theorem wrapLams_mkApps_ne_const (ds : List VExpr) :
    VExpr.wrapLams ds (VExpr.mkApps (.const n ls) (as ++ [a])) ≠ .const n' ls' := by
  cases ds <;> simp only [VExpr.wrapLams, List.foldr_nil, List.foldr_cons, VExpr.mkApps_snoc]
  all_goals intro h; cases h

/-- A stored delta equation is valid at its actual stored type. -/
theorem RuleValid.delta (henv : env.Ordered) (hdr : env.DeltaRules)
    (hctor : ∀ c, IsInstalledCtor env c → env.Rigid c)
    (hdf : env.defeqs df) (hlhs : df.lhs = .const n ls₀) : RuleValid env df := by
  intro U Δ Γ ls u hΔ hlw hlen _ _ _ ihL _ ihR
  replace ihR := ihR.1
  intro σ σ' S W tv tv'
  obtain ⟨rfl, hci⟩ := hdr.const df hdf n ls₀ hlhs
  have elhs : df.lhs.instL ls = .const n ls := by
    rw [hlhs]; simp only [VExpr.instL, VLevel.inst_map_id hlen]
  rw [elhs]
  have hrcl : (df.rhs.instL ls).ClosedN := ((henv.closed.2 hdf).2.1).instL
  have htcl : (df.type.instL ls).ClosedN := ((henv.closed.2 hdf).1.2).instL
  have IHR := ihR σ' σ' S (SubstEq.right henv hΔ W) tv' tv'
  have notRigid : ¬ env.Rigid n := fun hrig => hrig df hdf _ (by rw [hlhs]; rfl)
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, IHR.2.2.1⟩
  · cases h with
    | const hrig => exact (notRigid hrig).elim
    | delta hdf' hlhs' _ _ _ hv =>
      cases hdr.excl df _ hdf hdf' n _ _ hlhs (by rw [hlhs']; rfl)
      exact ⟨o, (Obs.closed_iff_id hrcl).2 hv, .refl⟩
    | ctor hc => exact (notRigid (hctor n hc)).elim
    | rule hdf' hl' =>
      cases hdr.excl df _ hdf hdf' n _ _ hlhs (by rw [hl']; exact wrapLams_mkApps_head _)
      rw [hlhs] at hl'
      exact (wrapLams_mkApps_ne_const _ hl'.symm).elim
  · obtain ⟨τs, hτ, hty⟩ := IHR.2.2.1 o h
    have heq : env.IsDefEq U Γ (.const n ls) (df.rhs.instL ls) (df.type.instL ls) := by
      have := IsDefEq.extra (Γ := Γ) hdf hlw hlen; rwa [elhs] at this
    rw [← vcls_defeq henv hΔ (SubstEq.right henv hΔ W) heq,
      vcls_closed (e := .const _ _) trivial htcl] at hty
    exact ⟨o, .delta hdf (by rw [hlhs]) hci (ci := ⟨df.uvars, df.type⟩)
      (fun τ hτ' => (Obs.closed_iff_id htcl).1 (hτ τ hτ')) hty
      ((Obs.closed_iff_id hrcl).1 h), .refl⟩
  · obtain ⟨τs, hτ, hty⟩ := h.const_typed hci
    rw [vcls_closed (e := .const _ _) trivial htcl]
    exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id htcl).2 (hτ τ hτ'), hty⟩

/-- Declaration-history metadata discharges delta validity without a rule certificate. -/
theorem RuleValid.delta_of_wf (H : env.WF) (hdf : env.defeqs df)
    (hlhs : df.lhs = .const n ls₀) : RuleValid env df :=
  .delta H.ordered H.deltaRules (fun _ => H.installed_constructor_rigid) hdf hlhs

/-- Soundness for actual derivations whose source has no quotient equation.
All of its stored rules are actual delta equations by declaration-history metadata. -/
theorem sound_no_quot {E : VEnv} (henv : env.WF) (hE : E.WF) (hle : E ≤ env)
    (hq : ¬ E.defeqs quotDefEq) (hΔ : OnCtx Δ (env.IsType U))
    (H : E.IsDefEqStrong U Γ t t' T) :
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T := by
  apply sound henv.ordered hΔ hle ?_ H
  intro df hdf
  rcases hE.rewriteMetadata.classify hdf with rfl | ⟨ci, rfl⟩
  · exact (hq hdf).elim
  · exact RuleValid.delta_of_wf henv (hle.defeqs hdf) rfl

end Model
end Lean4Lean.VEnv
