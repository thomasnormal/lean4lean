import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ExprSound

/-! # Semantically typed derivations

`HTS Γ e T` mirrors `HasTypeStrong`: every `IsDefEqStrong` premise is replaced by the premise
together with its soundness (`SD`), and every typing premise by `HTS`.
Adapted from PR #53, exact head 5a8c0d5f111809a95f4924c71e0e9bc8738d72e0,
for the existing six-expression language. The fallback constructor records
syntax only; actual typing is retained separately by the simultaneous proof.
No environment invariant or caller rule-validity assumption is added. The soundness proof
carries `HTS` for both sides of every derivation, which gives the rule cases the soundness
of the sub-derivations of their typing premises.

* `HTS.spine` (the **spine lemma**): for a constant spine `mkApps (const c ls) args` typed at
  `T` and a typed valuation, there are keys for the arguments (containing given demands),
  each with the domain type `A` of its argument in the typing derivation (`HTS Γ a A`), such
  that (P1) every observation typed at observations of `T` wrapped in the keys is typed at
  observations of the constant's type, (P2) codomain observations of the constant's type at
  the keys are covered by observations of `T`, and (P2') domain observations at each key are
  covered by observations of that key's domain type.
* `HTS.lamSpine`: the same through the lambdas of a lambda telescope, at given typed keys.
* `HTS.bvar_chain`: the type of a variable in an `HTS` derivation is chained to its context
  type.
* Inversions: `HTS.forallE_inv`, `HTS.piSD`, `HTS.lam_inv`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- Semantically typed derivations. -/
inductive HTS : List VExpr → VExpr → VExpr → Prop
  | bvar : Lookup Γ i A → SD env U Δ Γ A A (.sort u) → HTS Γ (.bvar i) A
  | other : (∀ c ls args, e ≠ .mkApps (.const c ls) args) →
    (∀ A b, e ≠ .lam A b) → (∀ A B, e ≠ .forallE A B) →
    (∀ i, e ≠ .bvar i) → HTS Γ e T
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
    HTS [] (ci.type.instL ls) (.sort u) →
    SD env U Δ [] (ci.type.instL ls) (ci.type.instL ls) (.sort u) →
    HTS Γ (.const c ls) (ci.type.instL ls)
  | app : SD env U Δ Γ A A (.sort u) → SD env U Δ (A :: Γ) B B (.sort v) →
    HTS Γ f (.forallE A B) → env.HasType U Γ f (.forallE A B) → HTS Γ a A → SD env U Δ Γ a a A →
    HTS Γ (.app f a) (B.inst a)
  | lam : HTS Γ A (.sort u) → SD env U Δ Γ A A (.sort u) → HTS (A :: Γ) b B →
    SD env U Δ (A :: Γ) b b B → SD env U Δ (A :: Γ) B B (.sort v) →
    HTS Γ (.lam A b) (.forallE A B)
  | forallE : HTS Γ A (.sort u) → SD env U Δ Γ A A (.sort u) → HTS (A :: Γ) B (.sort v) →
    SD env U Δ (A :: Γ) B B (.sort v) → HTS Γ (.forallE A B) (.sort (.imax u v))
  | conv : HTS Γ e A → SD env U Δ Γ A B (.sort u) → HTS Γ e B

/-- Soundness of the domains of a telescope. -/
inductive DomsSD : List VExpr → List VExpr → Prop
  | nil : DomsSD Γ []
  | cons : SD env U Δ Γ A A (.sort u) → DomsSD (A :: Γ) ds → DomsSD Γ (A :: ds)

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem PiSD.doms : PiSD env U Δ Γ ds R → DomsSD env U Δ Γ ds
  | .nil => .nil
  | .cons h _ h' => .cons h h'.doms

theorem mkApps_const_ne_bvar : VExpr.mkApps (.const c ls) args ≠ .bvar i := by
  intro h; rcases mkApps_const_inv h.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h

theorem mkApps_const_ne_lam : VExpr.mkApps (.const c ls) args ≠ .lam A b := by
  intro h; rcases mkApps_const_inv h.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h

theorem _root_.Lean4Lean.VExpr.mkApps_const_ne_forallE :
    VExpr.mkApps (.const c ls) args ≠ .forallE A B := by
  intro h
  rcases mkApps_const_inv h.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h

theorem HTS.sort' : HTS env U Δ Γ (.sort l) T :=
  .other (fun _ _ _ h => by rcases mkApps_inv h with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h)
    nofun nofun nofun

theorem HTS.beta_lhs : HTS env U Δ Γ (.app (.lam A e) e') T :=
  .other (fun _ _ _ h => by
      rcases mkApps_inv h with ⟨_, h⟩ | ⟨_, _, _, h⟩
      · cases h
      · injection h with h; exact mkApps_const_ne_lam h.symm)
    nofun nofun nofun

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

theorem SoundAt.refl_l (h : SoundAt env U Δ Γ t t' T) : SoundAt env U Δ Γ t t T :=
  h.trans henv hΔ (h.symm henv hΔ)

theorem SoundAt.refl_r (h : SoundAt env U Δ Γ t t' T) : SoundAt env U Δ Γ t' t' T :=
  (h.symm henv hΔ).trans henv hΔ h

/-- The extension of a typed valuation along typed keys over sound domains is typed. -/
theorem TeleKeys.typed (h : TeleKeys env U Δ σ S ds keys σ' S')
    (hds : DomsSD env U Δ Γ ds) (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ctx.SubstEq env U Δ σ' σ' (ds.reverse ++ Γ) ∧ TV env U Δ (ds.reverse ++ Γ) σ' S' := by
  induction h generalizing Γ with
  | nil => exact ⟨W, tv⟩
  | cons hc hy hK hb _ ih =>
    cases hds with
    | cons hA hds =>
      have := ih hds (.cons W hA.1.defeq.hasType.1 (hc.hasType henv hΔ hy))
        (tv.cons_cls henv hΔ hc hy hb hK)
      simpa [List.reverse_cons, List.append_assoc] using this

omit henv hΔ in
/-- Type observations transfer along a sound type equality, at one valuation. -/
theorem SD.sub (h : SD env U Δ Γ A B (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S A) (Obs' σ S B) ∧ Ob.Sub (Obs' σ S B) (Obs' σ S A) :=
  let h := h.2 σ σ S W tv tv; ⟨h.1, h.2.1⟩

end

/-- The type of a variable is chained to its context type. -/
theorem HTS.bvar_chain (H : HTS env U Δ Γ e T) (he : e = .bvar i) :
    ∃ A, Lookup Γ i A ∧ (A = T ∨ env.TypeChain U Γ A T) := by
  induction H with
  | bvar hL => cases he; exact ⟨_, hL, .inl rfl⟩
  | other _ _ _ h => exact absurd he (h _)
  | const | app | lam | forallE => cases he
  | conv _ hAB ih =>
    obtain ⟨A, hL, h⟩ := ih he
    refine ⟨A, hL, .inr ?_⟩
    rcases h with rfl | h
    · exact .single hAB.1.defeq
    · exact h.tail hAB.1.defeq

/-- Inversion of a Pi type. -/
theorem HTS.forallE_inv (H : HTS env U Δ Γ e T) (he : e = .forallE A B) :
    ∃ u v, HTS env U Δ Γ A (.sort u) ∧ SD env U Δ Γ A A (.sort u) ∧
      HTS env U Δ (A :: Γ) B (.sort v) ∧ SD env U Δ (A :: Γ) B B (.sort v) := by
  induction H with
  | forallE h1 h2 h3 h4 => cases he; exact ⟨_, _, h1, h2, h3, h4⟩
  | other _ _ h => exact absurd he (h _ _)
  | bvar | const | app | lam => cases he
  | conv _ _ ih => exact ih he

/-- A Pi telescope in a semantically typed derivation has sound domains and codomains. -/
theorem HTS.piSD : ∀ {ds Γ T}, HTS env U Δ Γ (.wrapForalls ds R) T → PiSD env U Δ Γ ds R
  | [], _, _, _ => .nil
  | _ :: _, _, _, H => by
    obtain ⟨_, _, _, hA, hB, hB'⟩ := H.forallE_inv rfl
    exact .cons hA hB' (HTS.piSD hB)

/-- Inversion of a lambda: its derivation's Pi type covers the observations of its type. -/
theorem HTS.lam_inv (H : HTS env U Δ Γ e P) (he : e = .lam A b) :
    ∃ B u v, HTS env U Δ Γ A (.sort u) ∧ SD env U Δ Γ A A (.sort u) ∧
      HTS env U Δ (A :: Γ) b B ∧ SD env U Δ (A :: Γ) b b B ∧
      SD env U Δ (A :: Γ) B B (.sort v) ∧
      (∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
        Ob.Sub (Obs' σ S P) (Obs' σ S (.forallE A B))) ∧
      (P = .forallE A B ∨ env.TypeChain U Γ (.forallE A B) P) := by
  induction H with
  | lam h1 h2 h3 h4 h5 =>
    cases he; exact ⟨_, _, _, h1, h2, h3, h4, h5, fun _ _ _ _ => Ob.Sub.refl, .inl rfl⟩
  | other _ h => exact absurd he (h _ _)
  | bvar | const | app | forallE => cases he
  | conv _ hAB ih =>
    obtain ⟨B, u, v, h1, h2, h3, h4, h5, h6, h7⟩ := ih he
    refine ⟨B, u, v, h1, h2, h3, h4, h5, fun σ S W tv =>
      ((hAB.2 σ σ S W tv tv).2.1).trans (h6 σ S W tv), .inr ?_⟩
    rcases h7 with rfl | h7
    · exact TypeChain.single hAB.1.defeq
    · exact TypeChain.tail h7 hAB.1.defeq

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The data of the spine lemma for a key with its domain type. -/
def KeyData (env : VEnv) (U : Nat) (Δ Γ : List VExpr) (σ : VExpr.Subst) (S : ObSets)
    (ka : Key × VExpr) (a : VExpr) : Prop :=
  ka.1.2.1 = ElCls env U Δ ka.1.1 (a.subst σ) ∧ (∀ x ∈ ka.1.2.2, Obs env U Δ σ S a x) ∧
  ka.1.1 = TyCls env U Δ (ka.2.subst σ) ∧ HTS env U Δ Γ a ka.2 ∧ SD env U Δ Γ a a ka.2 ∧
  Backed (fun o => o ∈ ka.1.2.2)

omit henv hΔ in
theorem forall₂_append_single {R : α → β → Prop} (H : List.Forall₂ R l₁ l₂) (h : R a b) :
    List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction H with
  | nil => exact .cons h .nil
  | cons h' _ ih => exact .cons h' ih

omit henv hΔ in
theorem forall₂_snoc_right {R : α → β → Prop} {as : List α} {bs : List β} {b : β}
    (H : List.Forall₂ R as (bs ++ [b])) :
    ∃ as₀ a, as = as₀ ++ [a] ∧ List.Forall₂ R as₀ bs ∧ R a b := by
  induction bs generalizing as with
  | nil =>
    cases H with
    | cons h H => cases H; exact ⟨[], _, rfl, .nil, h⟩
  | cons b₀ bs ih =>
    cases H with
    | cons h H =>
      obtain ⟨as₀, a, rfl, H₀, ha⟩ := ih H
      exact ⟨_ :: as₀, a, rfl, .cons h H₀, ha⟩

/-- The actual stored type of a constant head at well-formed levels. -/
def HeadTy (env : VEnv) (U : Nat) (hd Th : VExpr) : Prop :=
  ∃ c ls ci, hd = .const c ls ∧ env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧
    Th = ci.type.instL ls

/-- The spine lemma with the actual stored constant type explicit. -/
theorem HTS.spineH (H : HTS env U Δ Γ e T) {hd args} (he : e = .mkApps hd args)
    (hhd : ∃ c ls, hd = .const c ls)
    {σ S} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S)
    (Ks : List (List Ob)) (hKs : List.Forall₂ (fun K a => ∀ x ∈ K, Obs' σ S a x) Ks args)
    (τs : List Ob) (hτs : ∀ τ ∈ τs, Obs' σ S T τ) :
    ∃ Th info, HeadTy env U hd Th ∧ Th.ClosedN ∧
      (∃ u, HTS env U Δ [] Th (.sort u) ∧ SD env U Δ [] Th Th (.sort u)) ∧
      List.Forall₂ (KeyData env U Δ Γ σ S) info args ∧
      List.Forall₂ (fun K (ka : Key × VExpr) => ∀ x ∈ K, x ∈ ka.1.2.2) Ks info ∧
      (∀ o, TypedOb env U Δ (vcls env U Δ σ e T) o τs →
        ∃ τ₀, (∀ τ ∈ τ₀, Obs' .id .empty (Th) τ) ∧
        TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ Th) hd) (wrap (info.map (·.1)) o) τ₀) ∧
      (∀ x, Obs' .id .empty (Th) (piCodChain (info.map (·.1)) x) →
        ∃ x', Obs' σ S T x' ∧ x' ≼ x) ∧
      (∀ pre ka post, info = pre ++ ka :: post → ∀ x,
        Obs' .id .empty (Th) (piCodChain (pre.map (·.1)) (.piDomOb x)) →
        ∃ x', Obs' σ S ka.2 x' ∧ x' ≼ x) := by
  induction H generalizing args Ks τs with
  | bvar =>
    rcases hhd with ⟨_, _, rfl⟩
    exact absurd he.symm mkApps_const_ne_bvar
  | other h =>
    rcases hhd with ⟨_, _, rfl⟩
    exact absurd he (h _ _ _)
  | lam =>
    rcases hhd with ⟨_, _, rfl⟩
    exact absurd he.symm mkApps_const_ne_lam
  | forallE =>
    rcases hhd with ⟨_, _, rfl⟩
    exact absurd he.symm VExpr.mkApps_const_ne_forallE
  | const hci hls _ hT hsd =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨_, _, _, he'⟩
    · subst he'
      cases hKs
      refine ⟨_, [], ⟨_, _, _, rfl, hci, hls, rfl⟩, (henv.closedC hci).instL,
        ⟨_, hT, hsd⟩,
        .nil, .nil, fun o ho => ⟨τs, fun τ hτ =>
          (Obs.closed_iff_id (henv.closedC hci).instL).1 (hτs τ hτ),
          vcls_closed (e := .const _ _) trivial (henv.closedC hci).instL ▸ ho⟩,
        fun x hx => ⟨x, (Obs.closed_iff_id (henv.closedC hci).instL).2 hx, .refl⟩,
        fun pre ka post h => ?_⟩
      cases pre <;> cases h
    · cases he'
  | @app _ A u B v f a hA hB _ hfty _ hsa ihf _ =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨as, a', rfl, he'⟩
    · rcases hhd with ⟨_, _, rfl⟩; cases he'
    injection he' with hf ha; subst ha
    obtain ⟨Ks₀, Ka, rfl, hKs₀, hKa⟩ := forall₂_snoc_right hKs
    -- observation keys for the argument, large enough for the type observations
    have hτ' : ∀ τ ∈ τs, Obs' (σ.cons (a.subst σ)) (S.cons (Obs' σ S a)) B τ :=
      fun τ hτ => Obs.inst_iff.1 (hτs τ hτ)
    obtain ⟨K₀, hK₀, hK₀τ⟩ := Obs.collect (Q := Obs' σ S a)
      (P := fun K τ => Obs' (σ.cons (a.subst σ)) (ObSets.cons S (listSet K)) B τ)
      (fun _ _ _ hKK h => h.mono fun i o h => by
        cases i with
        | zero => exact hKK _ h
        | succ i => exact h)
      fun τ hτ => (hτ' τ hτ).compact0
    have hK1 : ∀ k ∈ Ka ++ K₀, Obs' σ S a k := fun k hk => by
      rcases List.mem_append.1 hk with hk | hk
      · exact hKa k hk
      · exact hK₀ k hk
    obtain ⟨K, hKK, hK, hbK⟩ := Backed.close (fun o h => Obs.backed h tv.1) hK1
    have hKτ : ∀ τ ∈ τs, Obs' (σ.cons (a.subst σ)) (S.cons (listSet K)) B τ := fun τ hτ =>
      (hK₀τ τ hτ).mono fun i o h => by
        cases i with
        | zero => exact hKK _ (List.mem_append_right _ h)
        | succ i => exact h
    have IHa := hsa.2 σ σ S W tv tv
    obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge fun k hk => IHa.2.2.1 k (hK k hk)
    have haσ : env.HasType U Δ (a.subst σ) (A.subst σ) :=
      hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
    have hc := TypedElCls.of_hasType haσ
    obtain ⟨τPi, hτPi, hwrap⟩ := pi_list hc ElCls.self hτk hkk hbK hKτ
    obtain ⟨Th, info, hTh, hcl, hT, hinfo, hKsi, P1, P2, dP2⟩ :=
      ihf hf W tv Ks₀ hKs₀ τPi hτPi
    let k : Key := (TyCls env U Δ (A.subst σ), ElCls env U Δ (TyCls env U Δ (A.subst σ))
      (a.subst σ), K)
    refine ⟨Th, info ++ [(k, A)], hTh, hcl, hT, forall₂_append_single hinfo
      ⟨rfl, hK, rfl, by assumption, hsa, hbK⟩,
      forall₂_append_single hKsi (fun x hx => hKK _ (List.mem_append_left _ hx)), fun o ho => ?_,
      fun x hx => ?_, fun pre ka post h => ?_⟩
    · rw [vcls_app henv hΔ W hfty hsa.1.defeq.hasType.1] at ho
      obtain ⟨τ₀, h1, h2⟩ := P1 _ (hwrap _ o ho)
      refine ⟨τ₀, h1, ?_⟩
      simpa [List.map_append, wrap_append] using h2
    · rw [List.map_append, piCodChain_append] at hx
      obtain ⟨y, hy, l⟩ := P2 _ hx
      obtain ⟨K₁, y₀, rfl, hKK₁, ly₀⟩ := l.piCodOb_inv
      obtain ⟨_, ⟨τk', hτk', hkk'⟩, z, hz, hyB⟩ := Obs.piCodOb_mem hy
      have hza : env.IsDefEq U Δ z (a.subst σ) (A.subst σ) :=
        (ElCls.collapse henv hΔ haσ .self hz).symm
      have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons (a.subst σ)) (A :: _) :=
        .cons W hA.1.defeq.hasType.1 hza
      have hK₁ : ∀ k ∈ K₁, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
          σ S A k := fun k hk => ⟨τk', hτk', hkk' k hk⟩
      have hcA := TypedElCls.of_hasType haσ
      have hb₁ := Obs.piCodOb_backed hy
      obtain ⟨y₁, hy₁, l₁⟩ := (hB.2 _ _ _ W' (tv.cons_cls henv hΔ hcA hz hb₁ hK₁)
        (tv.cons_cls henv hΔ hcA ElCls.self hb₁ hK₁)).1 _ hyB
      obtain ⟨y₂, hy₂, l₂⟩ := hy₁.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k', hk', l⟩ := hKK₁ o h
          exact ⟨k', hK k' hk', l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨y₂, Obs.inst_iff.2 hy₂, l₂.trans (l₁.trans ly₀)⟩
    · intro x hx
      rcases List.eq_nil_or_concat post with rfl | ⟨post', last, rfl⟩
      · have e := List.append_inj' h rfl
        obtain ⟨rfl, e2⟩ := e
        cases e2
        obtain ⟨y, hy, l⟩ := P2 _ hx
        obtain ⟨y₀, rfl, l₀⟩ := l.piDomOb_inv
        exact ⟨y₀, Obs.piDomOb_mem hy, l₀⟩
      · have : info ++ [(k, A)] = (pre ++ ka :: post') ++ [last] := by
          rw [h]; simp
        have e := List.append_inj' this rfl
        exact dP2 pre ka post' e.1 x hx
  | conv _ hAB ih =>
    have hs := SD.sub hAB W tv
    obtain ⟨τs', h1, h2⟩ := exists_list_cover fun τ hτ => hs.2 τ (hτs τ hτ)
    obtain ⟨Th, info, hTh, hcl, hT, hinfo, hKsi, P1, P2, dP2⟩ := ih he W tv Ks hKs τs' h1
    refine ⟨Th, info, hTh, hcl, hT, hinfo, hKsi, fun o ho =>
      P1 o (((vcls_conv henv hΔ W hAB.1.defeq).symm ▸ ho).strengthen h2), fun x hx => ?_, dP2⟩
    obtain ⟨x₁, hx₁, l₁⟩ := P2 x hx
    obtain ⟨x₂, hx₂, l₂⟩ := hs.1 x₁ hx₁
    exact ⟨x₂, hx₂, l₂.trans l₁⟩

/-- **The spine lemma** for constant heads. -/
theorem HTS.spine (H : HTS env U Δ Γ e T) {c ls args} (he : e = .mkApps (.const c ls) args)
    {σ S} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S)
    (Ks : List (List Ob)) (hKs : List.Forall₂ (fun K a => ∀ x ∈ K, Obs' σ S a x) Ks args)
    (τs : List Ob) (hτs : ∀ τ ∈ τs, Obs' σ S T τ) :
    ∃ ci info, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧
      (∃ u, HTS env U Δ [] (ci.type.instL ls) (.sort u) ∧
        SD env U Δ [] (ci.type.instL ls) (ci.type.instL ls) (.sort u)) ∧
      List.Forall₂ (KeyData env U Δ Γ σ S) info args ∧
      List.Forall₂ (fun K (ka : Key × VExpr) => ∀ x ∈ K, x ∈ ka.1.2.2) Ks info ∧
      (∀ o, TypedOb env U Δ (vcls env U Δ σ e T) o τs →
        ∃ τ₀, (∀ τ ∈ τ₀, Obs' .id .empty (ci.type.instL ls) τ) ∧
        TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const c ls))
          (wrap (info.map (·.1)) o) τ₀) ∧
      (∀ x, Obs' .id .empty (ci.type.instL ls) (piCodChain (info.map (·.1)) x) →
        ∃ x', Obs' σ S T x' ∧ x' ≼ x) ∧
      (∀ pre ka post, info = pre ++ ka :: post → ∀ x,
        Obs' .id .empty (ci.type.instL ls) (piCodChain (pre.map (·.1)) (.piDomOb x)) →
        ∃ x', Obs' σ S ka.2 x' ∧ x' ≼ x) := by
  obtain ⟨Th, info, hTh, -, hT, hinfo, hKsi, P1, P2, dP2⟩ :=
    H.spineH henv hΔ he ⟨c, ls, rfl⟩ W tv Ks hKs τs hτs
  obtain ⟨c', ls', ci, e, hci, hls, rfl⟩ := hTh
  cases e
  exact ⟨ci, info, hci, hls, hT, hinfo, hKsi, P1, P2, dP2⟩

/-- **The spine lemma through lambdas**: for a lambda telescope typed at `P`, typed keys along
its domains, and a chain of `app` observations at those keys typed at observations of `P`,
the body is semantically typed at some `T'` at which the innermost observation is typed (at
the extended valuation), and the domains are sound. -/
theorem HTS.lamSpine {ds : List VExpr} :
    ∀ {Γ e P X σ S σ' S' keys o τs}, HTS env U Δ Γ e P → e = .wrapLams ds X →
    Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
    TeleKeys env U Δ σ S ds keys σ' S' →
    (∀ τ ∈ τs, Obs' σ S P τ) → TypedOb env U Δ (vcls env U Δ σ e P) (wrap keys o) τs →
    ∃ T', HTS env U Δ (ds.reverse ++ Γ) X T' ∧ DomsSD env U Δ Γ ds ∧
      ∃ τc, (∀ τ ∈ τc, Obs' σ' S' T' τ) ∧ TypedOb env U Δ (vcls env U Δ σ' X T') o τc := by
  induction ds with
  | nil =>
    intro Γ e P X σ S σ' S' keys o τs H he W tv hk hτs ho
    cases hk; cases he
    exact ⟨P, H, .nil, τs, hτs, ho⟩
  | cons A ds ih =>
    intro Γ e P X σ S σ' S' keys o τs H he W tv hk hτs ho
    obtain ⟨B, u, v, _, hA, hb, hsb, hB, hsub, hch⟩ := H.lam_inv he
    subst he
    cases hk with
    | @cons c y K _ _ _ _ _ _ _ hc hy hK hbK hk =>
      obtain ⟨τs', h1, h2⟩ := exists_list_cover fun τ hτ => hsub σ S W tv τ (hτs τ hτ)
      simp only [wrap_cons] at ho
      have ecls : vcls env U Δ σ (.wrapLams (A :: ds) X) P =
          vcls env U Δ σ (.lam A (.wrapLams ds X)) (.forallE A B) := by
        rcases hch with rfl | hch
        · rfl
        · unfold vcls; rw [← TypeChain.tyCls_subst_of_ctx henv hΔ W hch]; rfl
      rw [ecls] at ho
      obtain ⟨-, -, -, -, τc, h3, h4⟩ :=
        pi_step henv hΔ hA.1.defeq.hasType.1 hB.1.defeq.hasType.1 hB.2 W tv (ho.strengthen h2)
          h1 hy
      have eb := vcls_beta henv hΔ W hA.1.defeq.hasType.1 hsb.1.defeq.hasType.1 hc hy
        (b := .wrapLams ds X)
      rw [eb] at h4
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons y) (A :: Γ) :=
        .cons W hA.1.defeq.hasType.1 (hc.hasType henv hΔ hy)
      obtain ⟨T', hT', hds, τc', h5, h6⟩ := ih hb rfl
        W' (tv.cons_cls henv hΔ hc hy hbK hK) hk h3 h4
      refine ⟨T', ?_, .cons hA hds, τc', h5, h6⟩
      simpa [List.reverse_cons, List.append_assoc] using hT'

end

end Model
end VEnv
end Lean4Lean
