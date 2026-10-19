import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Structural

/-! # Structural soundness of the observation interpretation

Adapted from kim-em/lean4lean PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0 for the existing six-expression
language. Each case proves both semantic inclusions and observation typing
at related anchors from the actual recursive derivations and their simultaneous
soundness hypotheses. Stored-rule soundness and declaration-history validity
remain separate obligations.
-/

namespace Lean4Lean.VEnv.Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}
local notation "Obs'" => Obs env U Δ

theorem TypedElCls.eq_of_mem (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    c = ElCls env U Δ (TyCls env U Δ X₀) y :=
  let ⟨_, _, _, h⟩ := hc.mem henv hΔ hy; h

/-- Observations typed at a Pi type are `app` observations. -/
theorem typed_pi_app (H : TypedOb env U Δ cv o τs) (hτ : ∀ τ ∈ τs, Obs' σ S (.forallE A B) τ) :
    ∃ D c K p, o = .app D c K p := by
  cases H with
  | app => exact ⟨_, _, _, _, rfl⟩
  | sort h | piDom h | piDomOb h | piCod h | piCodOb h | rigid h | rigidArg h | rigidArgOb h => nomatch hτ _ h
  | ctorHead h | ctorArg h | ctorArgOb h =>
    obtain ⟨_, _, _, _, h, _⟩ := h; nomatch hτ _ h

/-- Enlarging the keys of a typed `app` observation by typed keys keeps it typed. -/
theorem TypedOb.app_enlarge (H : TypedOb env U Δ cv (.app D c K₁ p) τs) (hKK : Covers K K₁)
    (hd : ∀ x ∈ τd, Ob.piDomOb x ∈ τs) (hk : ∀ k ∈ K, TypedOb env U Δ c k τd)
    (hbK : Backed (· ∈ K)) :
    TypedOb env U Δ cv (.app D c K p) τs := by
  cases H with
  | app hD _ _ _ hc hC hcod hp =>
    exact .app hD hd hk hbK hc hC
      (fun x hx => let ⟨K₀, h1, h2⟩ := hcod x hx; ⟨K₀, h1, hKK.trans h2⟩) hp

/-- The `app` observations of a lambda are typed at its Pi type. -/
theorem lam_typed (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (hA : env.HasType U Γ A (.sort u))
    (ht : env.HasType U (A :: Γ) t B)
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c)
    (hK : ∀ k ∈ K, TypedAt env U Δ c σ S A k) (hbK : Backed (listSet K)) (hy : c y)
    (hp : TypedAt env U Δ (vcls env U Δ (σ.cons y) t B) (σ.cons y) (S.cons (listSet K)) B p) :
    TypedAt env U Δ (vcls env U Δ σ (.lam A t) (.forallE A B)) σ S (.forallE A B)
      (.app (TyCls env U Δ (A.subst σ)) c K p) := by
  obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
  obtain ⟨τc, hτc, hpc⟩ := hp
  obtain ⟨τs, h1, h2⟩ := pi_list hc hy hτk hkk hbK hτc
  refine ⟨τs, h1, h2 _ _ ?_⟩
  rw [vcls_beta henv hΔ W hA ht hc hy]; exact hpc

/-- The observations of an application are typed at the instantiated codomain, given the
typing invariant of the function (which identifies the domain class) and soundness for
the codomain. -/
theorem app_typed (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U (A::Γ) B (.sort v))
    (ihB : SoundAt env U Δ (A::Γ) B B (.sort v)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hfT : env.HasType U Γ f (.forallE A B))
    (ha0 : env.HasType U Γ a A)
    (hf : ∀ o, Obs' σ S f o →
      TypedAt env U Δ (vcls env U Δ σ f (.forallE A B)) σ S (.forallE A B) o)
    (ho : Obs' σ S (.app f a) o) :
    TypedAt env U Δ (vcls env U Δ σ (.app f a) (B.inst a)) σ S (B.inst a) o := by
  have ha : env.HasType U Δ (a.subst σ) (A.subst σ) := ha0.substDF henv W.wf hΔ W
  obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 ho
  obtain ⟨τs, hτs, hty⟩ := hf _ hfo
  cases hty with
  | @app _ _ _ _ _ τc _ C _ hD _ _ _ _ hC hcod hoty =>
    have eD := Obs.piDom_mem (hτs _ hD); subst eD; subst hc
    have hca := TypedElCls.of_hasType ha
    have eC : C = TyCls env U Δ (B.subst (σ.cons (a.subst σ))) := by
      obtain ⟨-, z, hz, rfl⟩ := Obs.piCod_mem (hτs _ hC)
      have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons (a.subst σ)) (A :: Γ) :=
        .cons W hA (hca.defeq henv hΔ hz ElCls.self)
      exact TyCls.eq_of_defeq (hB.substDF henv W'.wf hΔ W')
    subst eC
    rw [← vcls_app henv hΔ W hfT ha0] at hoty
    have : ∀ x ∈ τc, ∃ x', Obs' σ S (B.inst a) x' ∧ x' ≼ x := by
      intro x hx
      obtain ⟨K₀, hm, hKK₀⟩ := hcod x hx
      obtain ⟨_, ⟨τk, hτk, hkk⟩, y, hy, hxB⟩ := Obs.piCodOb_mem (hτs _ hm)
      have hay : env.IsDefEq U Δ (a.subst σ) y (A.subst σ) := ElCls.collapse henv hΔ ha .self hy
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons (a.subst σ)) (A::Γ) :=
        .cons W hA hay.symm
      have tvK : ∀ k ∈ K₀, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
          σ S A k := fun k hk => ⟨τk, hτk, hkk k hk⟩
      have hbK₀ := Obs.piCodOb_backed (hτs _ hm)
      obtain ⟨x₁, hx₁, l₁⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hca hy hbK₀ tvK)
        (tv.cons_cls henv hΔ hca ElCls.self hbK₀ tvK)).1 x hxB
      obtain ⟨x₂, hx₂, l₂⟩ := hx₁.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hKK₀ o h
          obtain ⟨k', hk', l'⟩ := hcov k hk
          exact ⟨k', hK' k' hk', l'.trans l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨x₂, Obs.inst_iff.2 hx₂, l₂.trans l₁⟩
    obtain ⟨τc', h1, h2⟩ := exists_list_cover this
    exact ⟨τc', h1, hoty.strengthen h2⟩

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

theorem SoundAt.appDF (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v)) (hf : env.IsDefEqStrong U Γ f f' (.forallE A B))
    (hBB : env.IsDefEqStrong U Γ (B.inst a) (B.inst a') (.sort v))
    (ha : env.IsDefEqStrong U Γ a a' A) (ihB : SoundAt env U Δ (A::Γ) B B (.sort v))
    (ihf : SoundAt env U Δ Γ f f' (.forallE A B)) (iha : SoundAt env U Δ Γ a a' A)
    (ihBB : SoundAt env U Δ Γ (B.inst a) (B.inst a') (.sort v)) :
    SoundAt env U Δ Γ (.app f a) (.app f' a') (B.inst a) := by
  intro σ σ' S W tv tv'
  have W'' := SubstEq.right henv hΔ W
  have hΓ := W.wf
  have haa : env.IsDefEq U Δ (a.subst σ) (a'.subst σ') (A.subst σ) :=
    ha.defeq.substDF henv hΓ hΔ W
  have hAA : env.IsDefEq U Δ (A.subst σ) (A.subst σ') (.sort u) :=
    hA.defeq.substDF henv hΓ hΔ W
  have IHf := ihf σ σ' S W tv tv'
  have IHa := iha σ σ' S W tv tv'
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
    obtain ⟨τs, hτs, hty⟩ := IHf.2.2.1 _ hfo
    cases hty with
    | app hD =>
      have eD := Obs.piDom_mem (hτs _ hD); subst eD
      obtain ⟨o₁, ho₁, l₁⟩ := IHf.1 _ hfo
      obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.1 k (hK' k hk)
      refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq .self haa)) hK1
        (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
  · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
    obtain ⟨τs, hτs, hty⟩ := IHf.2.2.2 _ hfo
    cases hty with
    | app hD =>
      have eD := Obs.piDom_mem (hτs _ hD); subst eD
      obtain ⟨o₁, ho₁, l₁⟩ := IHf.2.1 _ hfo
      obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.2.1 k (hK' k hk)
      refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq (.inr (.single (.inl ⟨_, hAA.symm⟩))) haa).symm)
        hK1 (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
  · exact app_typed henv hΔ hA.defeq hB.defeq ihB W.left tv hf.defeq.hasType.1
      ha.defeq.hasType.1 IHf.2.2.1 h
  · have := app_typed henv hΔ hA.defeq hB.defeq ihB W'' tv' hf.defeq.hasType.2
      ha.defeq.hasType.2 IHf.2.2.2 h
    rw [← vcls_conv henv hΔ W'' hBB.defeq] at this
    exact this.mono_le (ihBB σ' σ' S W'' tv' tv').2.1

/-- Lambda congruence is sound, including a change of binder domain. -/
theorem SoundAt.lamDF
    (hAA : env.IsDefEqStrong U Γ A A' (.sort u))
    (hb : env.IsDefEqStrong U (A :: Γ) body body' B)
    (ihA : SoundAt env U Δ Γ A A' (.sort u))
    (ihb : SoundAt env U Δ (A :: Γ) body body' B) :
    SoundAt env U Δ Γ (.lam A body) (.lam A' body') (.forallE A B) := by
  intro σ σ' S W tv tv'
  have W'' := SubstEq.right henv hΔ W
  have hΓ := W.wf
  have hA := hAA.defeq.hasType.1
  have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
    TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
  have eD' : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
    TyCls.eq_of_defeq (hA.substDF henv hΓ hΔ W)
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
      .cons W hA (hc.hasType henv hΔ hy)
    obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eD') hy hbK hK2)).1 p hp
    obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
    refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
    rw [eD]; exact .lam (hc.congr_D eD) h1 h2 hbK hy hp'
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
    have hc' := hc.congr_D eD.symm
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
      .cons W hA (hc'.hasType henv hΔ hy)
    obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eD') hy hbK hK2)).2.1 p hp
    obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
    refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
    rw [← eD]; exact .lam hc' h1 h2 hbK hy hp'
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
      .cons W hA (hc.hasType henv hΔ hy)
    exact lam_typed henv hΔ W.left hA hb.defeq.hasType.1 hc hKσ hbK hy ((ihb _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eD') hy hbK hK2)).2.2.1 p hp)
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
    have hc' := hc.congr_D eD.symm
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
      .cons W hA (hc'.hasType henv hΔ hy)
    have hp' := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eD') hy hbK hK2)).2.2.2 p hp
    have heqlam : env.IsDefEq U Γ (.lam A body') (.lam A' body') (.forallE A B) :=
      IsDefEq.lamDF hAA.defeq hb.defeq.hasType.2
    rw [← vcls_defeq henv hΔ W'' heqlam, ← eD, eD']
    exact lam_typed henv hΔ W'' hA hb.defeq.hasType.2 (hc'.congr_D eD') hK2 hbK hy hp'

/-- Conversion transports observation typing using the type equality's soundness. -/
theorem SoundAt.defeqDF (hAB : env.IsDefEqStrong U Γ A B (.sort u))
    (ihAB : SoundAt env U Δ Γ A B (.sort u)) (ihe : SoundAt env U Δ Γ e e' A) :
    SoundAt env U Δ Γ e e' B := by
  intro σ σ' S W tv tv'
  have IH := ihe σ σ' S W tv tv'
  refine ⟨IH.1, IH.2.1, fun o h => ?_, fun o h => ?_⟩
  · rw [← vcls_conv henv hΔ W.left hAB.defeq]
    exact (IH.2.2.1 o h).mono_le (ihAB σ σ S W.left tv tv).1
  · rw [← vcls_conv henv hΔ (SubstEq.right henv hΔ W) hAB.defeq]
    exact (IH.2.2.2 o h).mono_le (ihAB σ' σ' S (SubstEq.right henv hΔ W) tv' tv').1

/-- Actual beta equality is sound; finite backed demands support the reverse inclusion. -/
theorem SoundAt.beta (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A :: Γ) B B (.sort v))
    (he : env.IsDefEqStrong U (A :: Γ) e e B) (he' : env.IsDefEqStrong U Γ a a A)
    (ihA : SoundAt env U Δ Γ A A (.sort u))
    (ihB : SoundAt env U Δ (A :: Γ) B B (.sort v))
    (ihe : SoundAt env U Δ (A :: Γ) e e B) (ihe' : SoundAt env U Δ Γ a a A)
    (ihee' : SoundAt env U Δ Γ (e.inst a) (e.inst a) (B.inst a)) :
    SoundAt env U Δ Γ (.app (.lam A e) a) (e.inst a) (B.inst a) := by
  intro σ σ' S W tv tv'
  have W'' := SubstEq.right henv hΔ W
  have hΓ := W.wf
  have hee : env.IsDefEq U Δ (a.subst σ) (a.subst σ') (A.subst σ) :=
    he'.defeq.substDF henv hΓ hΔ W
  have IHA := ihA σ σ' S W tv tv'
  have IHe' := ihe' σ σ' S W tv tv'
  have eA : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
    TyCls.eq_of_defeq (hA.defeq.substDF henv hΓ hΔ W)
  have hce := TypedElCls.of_hasType hee.hasType.1
  have ec : ElCls env U Δ (TyCls env U Δ (A.subst σ')) (a.subst σ') =
      ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ) := by
    rw [← eA]; exact (ElCls.eq_of_defeq .self hee).symm
  have hmem' : ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ) (a.subst σ') :=
    ElCls.mem_of_defeq hee
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨D, c, K, K', hlo, hc, hK', hcov⟩ := Obs.app_iff.1 h
    obtain ⟨c₁, K₁, y, τs, p, e₁, hc₁, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 hlo
    injection e₁ with eD ec eK eo
    subst eD ec eK eo hc
    have hKσ : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
        σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have hKσ' : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
        σ' S A k := fun k hk => (hKσ k hk).mono_le IHA.1
    have hy' : env.IsDefEq U Δ y (a.subst σ') (A.subst σ) :=
      (ElCls.collapse henv hΔ hee.hasType.1 .self hy).symm.trans hee
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons (a.subst σ')) (A::Γ) :=
      .cons W hA.defeq hy'
    obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons_cls henv hΔ hce hy hbK hKσ)
      (tv'.cons_cls henv hΔ (hce.congr_D eA) hmem' hbK hKσ')).1 _ hp
    obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := S.cons (Obs' σ' S a)) fun i o h => by
      cases i with
      | zero =>
        obtain ⟨k, hk, l⟩ := hcov o h
        obtain ⟨k', hk', l'⟩ := IHe'.1 k (hK' k hk)
        exact ⟨k', hk', l'.trans l⟩
      | succ i => exact ⟨o, h, .refl⟩
    exact ⟨o₂, Obs.inst_iff.2 ho₂, l₂.trans l₁⟩
  · obtain ⟨K, hK, hbK, ho⟩ :=
      (Obs.inst_iff.1 h).compact0B fun o h => Obs.backed h tv'.1
    have hKσ' : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
        σ' S A k := fun k hk => ec ▸ IHe'.2.2.2 k (hK k hk)
    have hKσ : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
        σ S A k := fun k hk => (hKσ' k hk).mono_le IHA.2.1
    have W' : Ctx.SubstEq env U Δ (σ.cons (a.subst σ)) (σ'.cons (a.subst σ')) (A::Γ) :=
      .cons W hA.defeq hee
    obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons_cls henv hΔ hce ElCls.self hbK hKσ)
      (tv'.cons_cls henv hΔ (hce.congr_D eA) hmem' hbK hKσ')).2.1 o ho
    obtain ⟨τs, h1, h2⟩ := TypedAt.merge hKσ
    have hlam := Obs.lam (TypedElCls.of_hasType hee.hasType.1) h1 h2 hbK ElCls.self ho₁
    obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHe'.2.1 k (hK k hk)
    exact ⟨o₁, .app hlam rfl hK1 hK2, l₁⟩
  · refine app_typed henv hΔ hA.defeq hB.defeq ihB W.left tv
      (IsDefEq.lamDF hA.defeq he.defeq) he'.defeq (fun o h => ?_) h
    obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
    have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons y) (A::Γ) :=
      .cons W.left hA.defeq (hc.hasType henv hΔ hy)
    exact lam_typed henv hΔ W.left hA.defeq he.defeq hc hKσ hbK hy
      ((ihe _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv.cons_cls henv hΔ hc hy hbK hKσ)).2.2.1 p hp)
  · exact (ihee' σ' σ' S W'' tv' tv').2.2.1 o h

/-- Actual function eta is sound, retaining typed finite key demands. -/
theorem SoundAt.eta (he : env.IsDefEqStrong U Γ e e (.forallE A B))
    (ihe : SoundAt env U Δ Γ e e (.forallE A B)) :
    SoundAt env U Δ Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) := by
  intro σ σ' S W tv tv'
  have hΓ := W.wf
  have IHe := ihe σ σ' S W tv tv'
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
    have he₁' := Obs.lift_cons_iff.1 he₁
    obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
    cases hty₁ with
    | app hD =>
      have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
      have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem henv hΔ hc hy).symm
      subst ec
      obtain ⟨o₂, ho₂, l₂⟩ := IHe.1 _ he₁'
      refine ⟨o₂, ho₂, l₂.trans (Ob.Le.app' ?_ .refl)⟩
      exact Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
  · obtain ⟨o₁, ho₁, l₁⟩ := IHe.2.1 o h
    obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ ho₁
    obtain ⟨D, c, K, p, rfl⟩ := typed_pi_app hty₁ hτs₁
    cases hty₁ with
    | app hD hd hk hbK hc =>
      have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
      have hτd : ∀ x ∈ _, Obs' σ S A x := fun x hx => Obs.piDomOb_mem (hτs₁ _ (hd x hx))
      obtain ⟨y, hy⟩ := hc.nonempty
      refine ⟨_, .lam hc hτd hk hbK hy ?_, l₁⟩
      refine .app (Obs.lift_cons_iff.2 ho₁) (TypedElCls.eq_of_mem henv hΔ hc hy) (K' := K)
        (fun k hk => Obs.bvar_iff.2 hk) Covers.refl
  · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
    obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
    have he₁' := Obs.lift_cons_iff.1 he₁
    obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
    have hty₁' := hty₁
    cases hty₁ with
    | app hD =>
      have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
      have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem henv hΔ hc hy).symm
      subst ec
      have hKK : Covers K K₁ :=
        Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
      rw [vcls_defeq henv hΔ W.left (IsDefEq.eta he.defeq)]
      refine ⟨τs₁ ++ τs.map .piDomOb, fun τ hτ' => ?_,
        (hty₁'.mono fun τ hτ' => List.mem_append_left _ hτ').app_enlarge hKK
          (fun x hx => List.mem_append_right _ (List.mem_map_of_mem hx)) hK hbK⟩
      rcases List.mem_append.1 hτ' with hτ' | hτ'
      · exact hτs₁ τ hτ'
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hτ'; exact .piDomOb (hτ x hx)
  · exact IHe.2.2.2 o h

/-- Proof irrelevance is sound because typed proofs have no observations. -/
theorem SoundAt.proofIrrel
    (ihp : SoundAt env U Δ Γ p p (.sort .zero))
    (ihh : SoundAt env U Δ Γ h h p) (ihh' : SoundAt env U Δ Γ h' h' p) :
    SoundAt env U Δ Γ h h' p := by
  intro σ σ' S W tv tv'
  have IHp := ihp σ σ' S W tv tv'
  have IHh := ihh σ σ' S W tv tv'
  have IHh' := ihh' σ σ' S W tv tv'
  have e1 : ∀ o, ¬ Obs' σ S _ o := fun o h => by
    obtain ⟨τs, h1, h2⟩ := IHh.2.2.1 o h
    exact h2.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (IHp.2.2.1 τ (h1 τ hτ))⟩
  have e2 : ∀ o, ¬ Obs' σ' S _ o := fun o h => by
    obtain ⟨τs, h1, h2⟩ := IHh'.2.2.2 o h
    exact h2.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (IHp.2.2.2 τ (h1 τ hτ))⟩
  exact ⟨fun o h => (e1 o h).elim, fun o h => (e2 o h).elim,
    fun o h => (e1 o h).elim, fun o h => (e2 o h).elim⟩

/-- Constant level equality is sound with the original stored typing filter. -/
theorem SoundAt.constDF (hci : env.constants c = some ci)
    (hlw : ∀ l ∈ ls, l.WF U) (hlw' : ∀ l ∈ ls', l.WF U)
    (hls : List.Forall₂ (· ≈ ·) ls ls') :
    SoundAt env U Δ Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  intro σ σ' S W tv tv'
  have hcl : ∀ ls, (ci.type.instL ls).ClosedN := fun _ => (henv.closedC hci).instL
  refine ⟨fun o h => ⟨o, h.const_levels hlw hlw' hls, .refl⟩,
    fun o h => ⟨o, h.const_levels hlw' hlw (forall₂_equiv_symm hls), .refl⟩,
    fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨τs, h1, h2⟩ := h.const_typed hci
    rw [vcls_closed (e := .const _ _) trivial (hcl ls)]
    exact ⟨τs, fun τ hτ => (Obs.closed_iff_id (hcl ls)).2 (h1 τ hτ), h2⟩
  · obtain ⟨τs, h1, h2⟩ := (h.const_typed hci).lvEq (LvEq.instL ci.type hlw' hlw (forall₂_equiv_symm hls))
    rw [vcls_closed (e := .const _ _) trivial (hcl ls),
      TyCls.eq_of_lvEq (LvEq.instL ci.type hlw hlw' hls)]
    exact ⟨τs, fun τ hτ => (Obs.closed_iff_id (hcl ls)).2 (h1 τ hτ), h2⟩

/-- Strong derivations paired with the corresponding proved structural case. -/
theorem SD.symm (h : SD env U Δ Γ t t' T) : SD env U Δ Γ t' t T :=
  ⟨h.1.symm, h.2.symm henv hΔ⟩

theorem SD.trans (h : SD env U Δ Γ t t' T) (h' : SD env U Δ Γ t' t'' T) :
    SD env U Δ Γ t t'' T := ⟨h.1.trans h'.1, h.2.trans henv hΔ h'.2⟩

theorem SD.appDF (wu : u.WF U) (wv : v.WF U)
    (hA : SD env U Δ Γ A A (.sort u)) (hB : SD env U Δ (A :: Γ) B B (.sort v))
    (hf : SD env U Δ Γ f f' (.forallE A B)) (ha : SD env U Δ Γ a a' A)
    (hBB : SD env U Δ Γ (B.inst a) (B.inst a') (.sort v)) :
    SD env U Δ Γ (.app f a) (.app f' a') (B.inst a) :=
  ⟨.appDF wu wv hA.1 hB.1 hf.1 ha.1 hBB.1,
    SoundAt.appDF henv hΔ hA.1 hB.1 hf.1 hBB.1 ha.1 hB.2 hf.2 ha.2 hBB.2⟩

theorem SD.lamDF (wu : u.WF U) (wv : v.WF U)
    (hAA : SD env U Δ Γ A A' (.sort u))
    (hB : SD env U Δ (A :: Γ) B B (.sort v))
    (hB' : SD env U Δ (A' :: Γ) B B (.sort v))
    (hb : SD env U Δ (A :: Γ) b b' B) (hb' : SD env U Δ (A' :: Γ) b b' B) :
    SD env U Δ Γ (.lam A b) (.lam A' b') (.forallE A B) :=
  ⟨.lamDF wu wv hAA.1 hB.1 hB'.1 hb.1 hb'.1,
    SoundAt.lamDF henv hΔ hAA.1 hb.1 hAA.2 hb.2⟩

theorem SD.forallEDF (wu : u.WF U) (wv : v.WF U)
    (hAA : SD env U Δ Γ A A' (.sort u))
    (hBB : SD env U Δ (A :: Γ) B B' (.sort v))
    (hBB' : SD env U Δ (A' :: Γ) B B' (.sort v)) :
    SD env U Δ Γ (.forallE A B) (.forallE A' B') (.sort (.imax u v)) :=
  ⟨.forallEDF wu wv hAA.1 hBB.1 hBB'.1,
    SoundAt.forallEDF henv hΔ hAA.1 hBB.1 hAA.2 hBB.2⟩

theorem SD.defeqDF (wu : u.WF U) (hAB : SD env U Δ Γ A B (.sort u))
    (he : SD env U Δ Γ e e' A) : SD env U Δ Γ e e' B :=
  ⟨.defeqDF wu hAB.1 he.1, SoundAt.defeqDF henv hΔ hAB.1 hAB.2 he.2⟩

theorem SD.beta (wu : u.WF U) (wv : v.WF U)
    (hA : SD env U Δ Γ A A (.sort u)) (hB : SD env U Δ (A :: Γ) B B (.sort v))
    (he : SD env U Δ (A :: Γ) e e B) (ha : SD env U Δ Γ a a A)
    (hT : SD env U Δ Γ (B.inst a) (B.inst a) (.sort v))
    (hR : SD env U Δ Γ (e.inst a) (e.inst a) (B.inst a)) :
    SD env U Δ Γ (.app (.lam A e) a) (e.inst a) (B.inst a) :=
  ⟨.beta wu wv hA.1 hB.1 he.1 ha.1 hT.1 hR.1,
    SoundAt.beta henv hΔ hA.1 hB.1 he.1 ha.1 hA.2 hB.2 he.2 ha.2 hR.2⟩

theorem SD.eta (wu : u.WF U) (wv : v.WF U)
    (hA : SD env U Δ Γ A A (.sort u)) (hB : SD env U Δ (A :: Γ) B B (.sort v))
    (hB' : SD env U Δ (A.lift :: A :: Γ) (B.liftN 1 1) (B.liftN 1 1) (.sort v))
    (he : SD env U Δ Γ e e (.forallE A B))
    (he' : SD env U Δ (A :: Γ) e.lift e.lift (.forallE A.lift (B.liftN 1 1)))
    (hA' : SD env U Δ (A :: Γ) A.lift A.lift (.sort u)) :
    SD env U Δ Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) :=
  ⟨.eta wu wv hA.1 hB.1 hB'.1 he.1 he'.1 hA'.1,
    SoundAt.eta henv hΔ he.1 he.2⟩

theorem SD.proofIrrel (hp : SD env U Δ Γ p p (.sort .zero))
    (hh : SD env U Δ Γ h h p) (hh' : SD env U Δ Γ h' h' p) :
    SD env U Δ Γ h h' p :=
  ⟨.proofIrrel hp.1 hh.1 hh'.1, SoundAt.proofIrrel henv hΔ hp.2 hh.2 hh'.2⟩

theorem SD.constDF (hci : env.constants c = some ci)
    (hlw : ∀ l ∈ ls, l.WF U) (hlw' : ∀ l ∈ ls', l.WF U)
    (hlen : ls.length = ci.uvars) (hls : List.Forall₂ (· ≈ ·) ls ls') (wu : u.WF U)
    (hT0 : SD env U Δ [] (ci.type.instL ls) (ci.type.instL ls') (.sort u))
    (hT : SD env U Δ Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u)) :
    SD env U Δ Γ (.const c ls) (.const c ls') (ci.type.instL ls) :=
  ⟨.constDF hci hlw hlw' hlen hls wu hT0.1 hT.1,
    SoundAt.constDF henv hΔ hci hlw hlw' hls⟩

end

end Lean4Lean.VEnv.Model
