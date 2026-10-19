import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ClassApplication

/-! # Constructive observation subsumption and typing

Adapted from kim-em/lean4lean PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0.
Contravariant key coverage is represented by maps between finite list indices.
The coverage-to-map proof uses finite induction, without equality on observations
or a global choice function. All pure observation forms and their finite
witness closure are retained. Observation typing covers the existing expression
fragment; no projection or case-eliminator metadata is assumed.

This layer proves subsumption, strengthening and the observation-level
proof-irrelevance obstruction. Interpretation soundness and head separation
remain separate obligations.
-/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Observations. Classes are sets of terms in the target context (`VExpr → Prop`). -/
inductive Ob where
  | sort (ℓ : List Nat → Nat)
  | piDom (D : VExpr → Prop)
  | piDomOb (o : Ob)
  | piCod (c C : VExpr → Prop)
  | piCodOb (c : VExpr → Prop) (K : List Ob) (o : Ob)
  | app (D c : VExpr → Prop) (K : List Ob) (o : Ob)
  /-- A rigid spine of the constant `n` at levels `ℓs` with `nargs` arguments, of sort `s`. -/
  | rigid (n : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat) (s : List Nat → Nat)
  | rigidArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a rigid spine has the observation `o`. -/
  | rigidArgOb (i : Nat) (o : Ob)
  /-- A constructor application of `c` at levels `ℓs` to `nargs` arguments. -/
  | ctorHead (c : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat)
  /-- The `i`-th argument of a constructor application has class `c`. -/
  | ctorArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a constructor application has `o`; `pre` records the keys of
  the earlier arguments (an annotation for typing). -/
  | ctorArgOb (i : Nat) (pre : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)
  /-- Field `j` of a value of the projection-registered family `n` has `o`; `L` lists
  observations of the earlier fields (the typing context, an annotation ignored by `≼`). -/
  | fieldOb (n : Name) (j : Nat) (L : List (List Ob)) (o : Ob)
  /-- A type observation of an application of the projection-registered family `n`: the
  domain of field `j`, at earlier fields with keys `FL`, has the observation `o`. -/
  | fieldTy (n : Name) (j : Nat) (FL : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)
  /-- ... and has type class `D`. -/
  | fieldDom (n : Name) (j : Nat) (FL : List ((VExpr → Prop) × (VExpr → Prop) × List Ob))
      (D : VExpr → Prop)

/-- Subsumption: `Ob.Le o o'` says `o'` is weaker than `o`. Key lists are compared
contravariantly, through finite index maps (keeping the definition free of
nested occurrences). -/
inductive Ob.Le : Ob → Ob → Prop
  | refl : Ob.Le o o
  | piDomOb : Ob.Le o o' → Ob.Le (.piDomOb o) (.piDomOb o')
  | piCodOb (f : Fin K.length → Fin K'.length) :
    (∀ i, Ob.Le (K'[f i]) (K[i])) → Ob.Le o o' →
    Ob.Le (.piCodOb c K o) (.piCodOb c K' o')
  | app (f : Fin K.length → Fin K'.length) :
    (∀ i, Ob.Le (K'[f i]) (K[i])) → Ob.Le o o' →
    Ob.Le (.app D c K o) (.app D c K' o')
  | rigidArgOb : Ob.Le o o' → Ob.Le (.rigidArgOb i o) (.rigidArgOb i o')
  | ctorArgOb : Ob.Le o o' → Ob.Le (.ctorArgOb i pre o) (.ctorArgOb i pre o')
  | fieldOb : Ob.Le o o' → Ob.Le (.fieldOb n j L o) (.fieldOb n j L' o')
  | fieldTy : Ob.Le o o' → Ob.Le (.fieldTy n j FL o) (.fieldTy n j FL o')

@[inherit_doc] scoped infix:50 " ≼ " => Ob.Le

/-- `Covers K' K`: every observation of `K` is subsumed by one of `K'` (an argument with the
observations `K'` satisfies the demand `K`). -/
def Covers (K' K : List Ob) : Prop := ∀ k ∈ K, ∃ k' ∈ K', k' ≼ k

/-- `Ob.Sub X Y` (`X ⊆ ↑Y`): every observation of `X` is subsumed by one of `Y`. -/
def Ob.Sub (X Y : Ob → Prop) : Prop := ∀ o, X o → ∃ o', Y o' ∧ o' ≼ o

/-! ## Subsumption -/

namespace Ob

/-- Finite dependent witness selection, proved by induction on the domain size. -/
theorem _root_.Lean4Lean.VEnv.Model.exists_fin_function {β : Type v}
    {P : Fin n → β → Prop} (h : ∀ i, ∃ y, P i y) :
    ∃ f : Fin n → β, ∀ i, P i (f i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := h 0
    obtain ⟨f, hf⟩ := ih (P := fun i y => P i.succ y) (fun i => h i.succ)
    refine ⟨Fin.cases y f, ?_⟩
    intro i
    exact Fin.cases hy hf i

/-- Coverage admits a finite index map, even when observations have no decidable equality. -/
theorem _root_.Lean4Lean.VEnv.Model.Covers.indices {K K' : List Ob} (h : Covers K' K) :
    ∃ f : Fin K.length → Fin K'.length, ∀ i, K'[f i] ≼ K[i] := by
  apply exists_fin_function (P := fun i j => K'[j] ≼ K[i])
  intro i
  obtain ⟨k', hk', hle⟩ := h K[i] (List.getElem_mem i.isLt)
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hk'
  refine ⟨⟨j, hj⟩, ?_⟩
  change K'[j] ≼ K[i]
  exact he.symm ▸ hle

/-- A finite index witness has the original membership-based coverage contract. -/
theorem _root_.Lean4Lean.VEnv.Model.Covers.of_indices
    (f : Fin K.length → Fin K'.length) (hf : ∀ i, K'[f i] ≼ K[i]) : Covers K' K := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hk
  exact ⟨_, List.getElem_mem (f ⟨i, hi⟩).isLt, hf ⟨i, hi⟩⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.iff_indices :
    Covers K' K ↔ ∃ f : Fin K.length → Fin K'.length, ∀ i, K'[f i] ≼ K[i] :=
  ⟨Covers.indices, fun ⟨f, hf⟩ => Covers.of_indices f hf⟩

theorem Le.app' (h : Covers K' K) (ho : o ≼ o') : .app D c K o ≼ .app D c K' o' :=
  let ⟨f, hf⟩ := Covers.indices h; .app f hf ho

theorem Le.piCodOb_of_covers (h : Covers K' K) (ho : o ≼ o') : .piCodOb c K o ≼ .piCodOb c K' o' :=
  let ⟨f, hf⟩ := Covers.indices h; .piCodOb f hf ho

/-- Pre- and post-composition, proved together by induction on the middle derivation
(key lists are contravariant, so each half needs the other on the keys). -/
theorem Le.trans_aux (h : x ≼ y) : (∀ w, w ≼ x → w ≼ y) ∧ (∀ z, y ≼ z → x ≼ z) := by
  induction h with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | piDomOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piDomOb (ih.1 _ .refl)
      | piDomOb h => exact .piDomOb (ih.1 _ h)
    · cases hz with
      | refl => exact .piDomOb (ih.2 _ .refl)
      | piDomOb h => exact .piDomOb (ih.2 _ h)
  | piCodOb f hf _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piCodOb f hf (iho.1 _ .refl)
      | piCodOb g hg hgo =>
        exact .piCodOb (fun i => f (g i))
          (fun i => (ihk (g i)).2 _ (hg i)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .piCodOb f hf (iho.2 _ .refl)
      | piCodOb g hg hgo =>
        exact .piCodOb (fun i => g (f i))
          (fun i => (ihk i).1 _ (hg (f i))) (iho.2 _ hgo)

  | rigidArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .rigidArgOb (ih.1 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .rigidArgOb (ih.2 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.2 _ h)
  | ctorArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .ctorArgOb (ih.1 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .ctorArgOb (ih.2 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.2 _ h)
  | fieldOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .fieldOb (ih.1 _ .refl)
      | fieldOb h => exact .fieldOb (ih.1 _ h)
    · cases hz with
      | refl => exact .fieldOb (ih.2 _ .refl)
      | fieldOb h => exact .fieldOb (ih.2 _ h)
  | fieldTy _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .fieldTy (ih.1 _ .refl)
      | fieldTy h => exact .fieldTy (ih.1 _ h)
    · cases hz with
      | refl => exact .fieldTy (ih.2 _ .refl)
      | fieldTy h => exact .fieldTy (ih.2 _ h)
  | app f hf _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .app f hf (iho.1 _ .refl)
      | app g hg hgo =>
        exact .app (fun i => f (g i))
          (fun i => (ihk (g i)).2 _ (hg i)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .app f hf (iho.2 _ .refl)
      | app g hg hgo =>
        exact .app (fun i => g (f i))
          (fun i => (ihk i).1 _ (hg (f i))) (iho.2 _ hgo)

theorem Le.trans (h1 : x ≼ y) (h2 : y ≼ z) : x ≼ z := (Le.trans_aux h1).2 _ h2

theorem _root_.Lean4Lean.VEnv.Model.Covers.refl : Covers K K := fun k hk => ⟨k, hk, .refl⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.trans (h1 : Covers K₃ K₂) (h2 : Covers K₂ K₁) : Covers K₃ K₁ := fun k hk =>
  let ⟨k₂, hk₂, l₂⟩ := h2 k hk; let ⟨k₃, hk₃, l₃⟩ := h1 k₂ hk₂; ⟨k₃, hk₃, l₃.trans l₂⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.of_subset (h : ∀ k ∈ K, k ∈ K') : Covers K' K := fun k hk => ⟨k, h k hk, .refl⟩

theorem Sub.refl : Sub X X := fun o h => ⟨o, h, .refl⟩

theorem Sub.trans (h1 : Sub X Y) (h2 : Sub Y Z) : Sub X Z := fun o h =>
  let ⟨o₁, h₁, l₁⟩ := h1 o h; let ⟨o₂, h₂, l₂⟩ := h2 o₁ h₁; ⟨o₂, h₂, l₂.trans l₁⟩

theorem Sub.of_imp (h : ∀ o, X o → Y o) : Sub X Y := fun o ho => ⟨o, h o ho, .refl⟩

/-! ### Inversion -/

theorem Le.sort_inv (h : o ≼ .sort ℓ) : o = .sort ℓ := by cases h; rfl
theorem Le.piDom_inv (h : o ≼ .piDom D) : o = .piDom D := by cases h; rfl
theorem Le.piCod_inv (h : o ≼ .piCod c C) : o = .piCod c C := by cases h; rfl
theorem Le.rigid_inv (h : o ≼ .rigid n ℓs m s) : o = .rigid n ℓs m s := by cases h; rfl
theorem Le.rigidArg_inv (h : o ≼ .rigidArg i c) : o = .rigidArg i c := by cases h; rfl
theorem Le.ctorHead_inv (h : o ≼ .ctorHead c ℓs n) : o = .ctorHead c ℓs n := by cases h; rfl
theorem Le.ctorArg_inv (h : o ≼ .ctorArg i c) : o = .ctorArg i c := by cases h; rfl

theorem Le.ctorArgOb_inv (h : o ≼ .ctorArgOb i pre x) :
    ∃ y, o = .ctorArgOb i pre y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | ctorArgOb h => exact ⟨_, rfl, h⟩

theorem Le.fieldOb_inv (h : o ≼ .fieldOb n j L x) : ∃ L' y, o = .fieldOb n j L' y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl⟩
  | fieldOb h => exact ⟨_, _, rfl, h⟩

theorem Le.fieldTy_inv (h : o ≼ .fieldTy n j FL x) : ∃ y, o = .fieldTy n j FL y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | fieldTy h => exact ⟨_, rfl, h⟩

theorem Le.fieldDom_inv (h : o ≼ .fieldDom n j FL D) : o = .fieldDom n j FL D := by cases h; rfl

theorem Le.piDomOb_inv (h : o ≼ .piDomOb x) : ∃ y, o = .piDomOb y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | piDomOb h => exact ⟨_, rfl, h⟩

theorem Le.piCodOb_inv (h : o ≼ .piCodOb c K x) :
    ∃ K₀ y, o = .piCodOb c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | piCodOb f hf ho =>
    refine ⟨_, _, rfl, ?_, ho⟩
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hk
    exact ⟨_, List.getElem_mem (f ⟨i, hi⟩).isLt, hf ⟨i, hi⟩⟩

theorem Le.app_inv (h : o ≼ .app D c K x) :
    ∃ K₀ y, o = .app D c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app f hf ho =>
    refine ⟨_, _, rfl, ?_, ho⟩
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hk
    exact ⟨_, List.getElem_mem (f ⟨i, hi⟩).isLt, hf ⟨i, hi⟩⟩

/-- The finite representation preserves exactly the intended contravariant coverage. -/
theorem Le.app_iff : .app D c K o ≼ .app D c K' o' ↔ Covers K' K ∧ o ≼ o' := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨.refl, .refl⟩
    | app f hf ho => exact ⟨Covers.of_indices f hf, ho⟩
  · rintro ⟨hK, ho⟩
    exact .app' hK ho

theorem Le.piCodOb_iff : .piCodOb c K o ≼ .piCodOb c K' o' ↔ Covers K' K ∧ o ≼ o' := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨.refl, .refl⟩
    | piCodOb f hf ho => exact ⟨Covers.of_indices f hf, ho⟩
  · rintro ⟨hK, ho⟩
    exact .piCodOb_of_covers hK ho

end Ob

/-- Choose, for each element of a list, a related witness: a list of witnesses covering it. -/
theorem exists_list_cover {α β : Type} {P : β → Prop} {R : β → α → Prop} :
    ∀ {L : List α}, (∀ x ∈ L, ∃ y, P y ∧ R y x) →
      ∃ L' : List β, (∀ y ∈ L', P y) ∧ ∀ x ∈ L, ∃ y ∈ L', R y x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨y, hy, hxy⟩ := h x (.head _)
    obtain ⟨L', h1, h2⟩ := exists_list_cover fun x hx => h x (.tail _ hx)
    refine ⟨y :: L', ?_, ?_⟩
    · intro z hz; cases hz with
      | head => exact hy
      | tail _ hz => exact h1 z hz
    · intro z hz; cases hz with
      | head => exact ⟨y, .head _, hxy⟩
      | tail _ hz => let ⟨w, hw, h⟩ := h2 z hz; exact ⟨w, .tail _ hw, h⟩

/-! ## Rigid spine observations -/

/-- A key of a spine observation: domain class, argument class, argument observations. -/
abbrev Key := (VExpr → Prop) × (VExpr → Prop) × List Ob

/-- Wrap an observation in the `app` observations of a spine of keys, outermost first. -/
def wrap (keys : List Key) (o : Ob) : Ob := keys.foldr (fun k o => .app k.1 k.2.1 k.2.2 o) o

@[simp] theorem wrap_nil : wrap [] o = o := rfl
@[simp] theorem wrap_cons : wrap (k :: ks) o = .app k.1 k.2.1 k.2.2 (wrap ks o) := rfl

theorem wrap_append : wrap (ks ++ ks') o = wrap ks (wrap ks' o) := by
  simp [wrap, List.foldr_append]

/-- The innermost observations of a rigid spine after the keys `keys`. -/
def RigidEnd (n : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) (r : Ob) : Prop :=
  (∃ s, r = .rigid n ℓs keys.length s) ∨ ∃ i, ∃ h : i < keys.length, r = .rigidArg i (keys[i]).2.1

/-- An observation that is not an `app` observation. -/
def Ob.NotApp : Ob → Prop
  | .app .. => False
  | _ => True

theorem RigidEnd.notApp (h : RigidEnd n ℓs keys r) : r.NotApp := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

/-- Spines of non-`app` endpoints are determined by the wrapped observation. -/
theorem wrap_inj {ks ks' : List Key} (h : wrap ks o = wrap ks' o') (ho : o.NotApp)
    (ho' : o'.NotApp) : ks = ks' ∧ o = o' := by
  induction ks generalizing ks' with
  | nil =>
    cases ks' with
    | nil => exact ⟨rfl, h⟩
    | cons k ks' => subst h; cases ho
  | cons k ks ih =>
    cases ks' with
    | nil => subst h; cases ho'
    | cons k' ks' =>
      simp only [wrap_cons, Ob.app.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := ih h4
      exact ⟨by rw [← this.1]; obtain ⟨_, _, _⟩ := k; obtain ⟨_, _, _⟩ := k'; simp_all, this.2⟩

/-! ## Backing

A field observation records the observations of the earlier fields (its context `L`); in an
observation set of one value these are *backed*: the set contains the canonical witnesses
`fieldOb n i (L.take i) y` for `y ∈ L[i]`, hereditarily through `app` (same key), `fieldOb`
(same context) and `ctorArgOb`. Typing is inherited by the witnesses (`TypedOb.wit`). -/

/-- The canonical witnesses of an observation. -/
def Ob.wit : Ob → List Ob
  | .fieldOb n j L o =>
    ((List.range L.length).flatMap fun i =>
        ((L[i]?).getD []).map fun y => .fieldOb n i (L.take i) y) ++
      (Ob.wit o).map (.fieldOb n j L ·)
  | .app D c K o => (Ob.wit o).map (.app D c K ·)
  | .ctorArgOb i pre o => (Ob.wit o).map (.ctorArgOb i pre ·)
  | _ => []

/-- An observation set is backed if it contains the canonical witnesses of its members. -/
def Backed (X : Ob → Prop) : Prop := ∀ o, X o → ∀ w ∈ o.wit, X w

theorem Ob.mem_wit_fieldOb {w : Ob} : w ∈ (Ob.fieldOb n j L o).wit ↔
    (∃ i Li y, L[i]? = some Li ∧ y ∈ Li ∧ w = .fieldOb n i (L.take i) y) ∨
    ∃ w', w' ∈ o.wit ∧ w = .fieldOb n j L w' := by
  simp only [Ob.wit, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro (⟨i, hi, y, hy, rfl⟩ | ⟨w', hw', rfl⟩)
    · rw [List.getElem?_eq_getElem hi] at hy
      exact .inl ⟨i, _, y, List.getElem?_eq_getElem hi, hy, rfl⟩
    · exact .inr ⟨w', hw', rfl⟩
  · rintro (⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w', hw', rfl⟩)
    · refine .inl ⟨i, (List.getElem?_eq_some_iff.1 hLi).1, y, ?_, rfl⟩
      rw [hLi]; exact hy
    · exact .inr ⟨w', hw', rfl⟩

/-! ### Finite closure under witnesses -/

mutual
/-- A size of observations along which witnesses decrease. -/
def Ob.sz : Ob → Nat
  | .fieldOb _ _ L o => 1 + Ob.szLL L + Ob.sz o
  | .app _ _ _ o => 1 + Ob.sz o
  | .ctorArgOb _ _ o => 1 + Ob.sz o
  | _ => 1
def Ob.szL : List Ob → Nat
  | [] => 0
  | o :: l => Ob.sz o + Ob.szL l
def Ob.szLL : List (List Ob) → Nat
  | [] => 0
  | K :: L => 1 + Ob.szL K + Ob.szLL L
end

theorem Ob.sz_le_szL : ∀ {K : List Ob} {y : Ob}, y ∈ K → y.sz ≤ Ob.szL K
  | _ :: _, _, .head _ => by simp only [Ob.szL]; omega
  | _ :: _, _, .tail _ h => by have := Ob.sz_le_szL h; simp only [Ob.szL]; omega

theorem Ob.szLL_take : ∀ {L : List (List Ob)} {i : Nat} {Li : List Ob} {y : Ob},
    L[i]? = some Li → y ∈ Li → Ob.szLL (L.take i) + y.sz < Ob.szLL L
  | K :: L, 0, Li, y, h, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    have := Ob.sz_le_szL hy
    simp only [List.take_zero, Ob.szLL]; omega
  | K :: L, i+1, Li, y, h, hy => by
    simp only [List.getElem?_cons_succ] at h
    have := Ob.szLL_take h hy
    simp only [List.take_succ_cons, Ob.szLL]; omega

theorem Ob.sz_wit : ∀ {o w : Ob}, w ∈ o.wit → w.sz < o.sz
  | .fieldOb n j L o, w, h => by
    rcases Ob.mem_wit_fieldOb.1 h with ⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w', hw', rfl⟩
    · have := Ob.szLL_take hLi hy; simp only [Ob.sz]; omega
    · have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .app D c K o, w, h => by
    simp only [Ob.wit, List.mem_map] at h
    obtain ⟨w', hw', rfl⟩ := h
    have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .ctorArgOb i pre o, w, h => by
    simp only [Ob.wit, List.mem_map] at h
    obtain ⟨w', hw', rfl⟩ := h
    have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .sort _, _, h | .piDom _, _, h | .piDomOb _, _, h | .piCod _ _, _, h | .piCodOb _ _ _, _, h
  | .rigid _ _ _ _, _, h | .rigidArg _ _, _, h | .rigidArgOb _ _, _, h | .ctorHead _ _ _, _, h
  | .ctorArg _ _, _, h | .fieldTy _ _ _ _, _, h | .fieldDom _ _ _ _, _, h => by
    simp [Ob.wit] at h

/-- An observation with all its witnesses, hereditarily. -/
def Ob.cl (o : Ob) : List Ob := o :: o.wit.attach.flatMap fun ⟨w, _⟩ => Ob.cl w
termination_by o.sz
decreasing_by exact Ob.sz_wit ‹_›

theorem Ob.mem_cl_self (o : Ob) : o ∈ o.cl := by unfold Ob.cl; exact List.mem_cons_self ..

theorem Ob.cl_sub (hX : Backed X) : ∀ {o : Ob}, X o → ∀ w ∈ o.cl, X w
  | o, ho, w, hw => by
    unfold Ob.cl at hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ho
    · simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hw
      obtain ⟨w', hw', hw⟩ := hw
      have := Ob.sz_wit hw'
      exact Ob.cl_sub hX (hX o ho w' hw') w hw
termination_by o => o.sz

theorem Ob.cl_closed : ∀ {o v w : Ob}, v ∈ o.cl → w ∈ v.wit → w ∈ o.cl
  | o, v, w, hv, hw => by
    unfold Ob.cl at hv ⊢
    rcases List.mem_cons.1 hv with rfl | hv
    · refine List.mem_cons_of_mem _ ?_
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
      exact ⟨w, hw, Ob.mem_cl_self w⟩
    · simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hv
      obtain ⟨w', hw', hv⟩ := hv
      have := Ob.sz_wit hw'
      refine List.mem_cons_of_mem _ ?_
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
      exact ⟨w', hw', Ob.cl_closed hv hw⟩
termination_by o => o.sz

/-- **Closure**: a finite part of a backed set extends to a finite backed part. -/
theorem Backed.close {X : Ob → Prop} {K : List Ob} (hX : Backed X) (hK : ∀ k ∈ K, X k) :
    ∃ K' : List Ob, (∀ k ∈ K, k ∈ K') ∧ (∀ k ∈ K', X k) ∧ Backed (· ∈ K') := by
  refine ⟨K.flatMap Ob.cl, fun k hk => List.mem_flatMap.2 ⟨k, hk, Ob.mem_cl_self k⟩,
    fun k hk => ?_, fun v hv w hw => ?_⟩
  · obtain ⟨o, ho, hk⟩ := List.mem_flatMap.1 hk
    exact Ob.cl_sub hX (hK o ho) k hk
  · obtain ⟨o, ho, hv⟩ := List.mem_flatMap.1 hv
    exact List.mem_flatMap.2 ⟨o, ho, Ob.cl_closed hv hw⟩

/-! ## Observation typing -/

/-- A level evaluated at evaluated level parameters. -/
def _root_.Lean4Lean.VLevel.evalAt (w : VLevel) (ℓs : List (List Nat → Nat)) : List Nat → Nat :=
  fun ns => w.eval (ℓs.map (· ns))

theorem _root_.Lean4Lean.VLevel.eval_inst_eq_evalAt (w : VLevel) (ls : List VLevel) :
    (w.inst ls).eval = w.evalAt (ls.map (·.eval)) := by
  funext ns; simp [VLevel.evalAt, VLevel.eval_inst, List.map_map, Function.comp_def]

section
variable (env : VEnv)

/-- The type of the constant `c` returns an application of the constant `I`. -/
def CtorFam (c I : Name) : Prop :=
  ∃ (ci : VConstant) (ds : List VExpr) (ls : List VLevel) (args : List VExpr),
    env.constants c = some ci ∧
    ci.type = ds.foldr VExpr.forallE (args.foldl VExpr.app (.const I ls))

/-- The constant at the head of an application spine, when present. -/
def constantHead : VExpr → Option Name
  | .const n _ => some n
  | .app f _ => constantHead f
  | _ => none

/-- The constant head after the leading forall telescope of a stored type. -/
def resultHead : VExpr → Option Name
  | .forallE _ B => resultHead B
  | e => constantHead e

theorem constantHead_foldl (f : VExpr) (args : List VExpr) :
    constantHead (args.foldl VExpr.app f) = constantHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

theorem resultHead_of_constantHead (h : constantHead e = some I) : resultHead e = some I := by
  cases e <;> simp_all [constantHead, resultHead]

/-- Family evidence computes the head of the actual stored constructor type. -/
theorem CtorFam.result_head (h : CtorFam env c I) :
    ∃ ci, env.constants c = some ci ∧ resultHead ci.type = some I := by
  obtain ⟨ci, ds, ls, args, hci, htype⟩ := h
  refine ⟨ci, hci, ?_⟩
  rw [htype]
  clear htype
  have hresult : resultHead (args.foldl VExpr.app (.const I ls)) = some I :=
    resultHead_of_constantHead ((constantHead_foldl _ _).trans rfl)
  induction ds with
  | nil => exact hresult
  | cons A ds ih => exact ih

/-- A stored constructor has at most one syntactic result family. -/
theorem CtorFam.unique (hI : CtorFam env c I) (hJ : CtorFam env c J) : I = J := by
  obtain ⟨ci, hci, hI⟩ := hI.result_head
  obtain ⟨cj, hcj, hJ⟩ := hJ.result_head
  obtain rfl := Option.some.inj (hci.symm.trans hcj)
  exact Option.some.inj (hI.symm.trans hJ)

/-- The family indicator for the constructor `c` in the type observations `τs`: a rigid
observation of `c`'s family whose sort is not zero. -/
def CtorTyped (c : Name) (τs : List Ob) : Prop :=
  ∃ I ℓs m s, .rigid I ℓs m s ∈ τs ∧ CtorFam env c I ∧ s ≠ (fun _ => 0)

end

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- `TypedOb cv o τs`: the observation `o` of a value of class `cv` is typed at the observations
`τs` of its type. Sorts are typed at their successor; type observations at some sort, a
codomain observation at a level that vanishes whenever the Pi's level does (so that
observations of propositions are typed at `sort 0` only); an `app` observation needs the Pi's
domain class, its keys typed (at their own class) at observations of the domain, its argument
class typed, and its result typed, at the class of the applications (`appCls`, the codomain
class read from `piCod`), at observations of the codomain instance at a key list it covers.
Projection observation typing is deferred until projection syntax is present. -/
inductive TypedOb : (VExpr → Prop) → Ob → List Ob → Prop
  | sort : .sort (fun ns => ℓ ns + 1) ∈ τs → TypedOb cv (.sort ℓ) τs
  | piDom : .sort ℓ ∈ τs → TypedOb cv (.piDom D) τs
  | piDomOb : .sort ℓ ∈ τs → TypedOb cv (.piDomOb o) τs
  | piCod : .sort ℓ ∈ τs → TypedOb cv (.piCod c C) τs
  | piCodOb : .sort ℓ ∈ τs → TypedOb cv' o [.sort ℓ'] → (∀ ns, ℓ ns = 0 → ℓ' ns = 0) →
    TypedOb cv (.piCodOb c K o) τs
  | app : .piDom D ∈ τs → (∀ x ∈ τd, .piDomOb x ∈ τs) → (∀ k ∈ K, TypedOb c k τd) →
    Backed (· ∈ K) → TypedElCls env U Δ D c → .piCod c C ∈ τs →
    (∀ x ∈ τc, ∃ K₀, .piCodOb c K₀ x ∈ τs ∧ Covers K K₀) →
    TypedOb (appCls env U Δ cv c C) o τc → TypedOb cv (.app D c K o) τs
  | rigid : .sort s ∈ τs → TypedOb cv (.rigid n ℓs m s) τs
  | rigidArg : .sort ℓ ∈ τs → TypedOb cv (.rigidArg i c) τs
  | rigidArgOb : .sort ℓ ∈ τs → TypedOb cv (.rigidArgOb i o) τs
  | ctorHead : CtorTyped env c τs → TypedOb cv (.ctorHead c ℓs m) τs
  | ctorArg : CtorTyped env c τs → TypedOb cv (.ctorArg i cls) τs
  | ctorArgOb : CtorTyped env c τs → TypedOb cv (.ctorArgOb i pre o) τs

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- Typing is stable under replacing the type observations by stronger ones. -/
theorem TypedOb.strengthen (H : TypedOb env U Δ cv o τs) (h : Covers τs' τs) :
    TypedOb env U Δ cv o τs' := by
  induction H generalizing τs' with
  | sort h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .sort h2
  | piDom h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDom h2
  | piDomOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDomOb h2
  | piCod h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCod h2
  | piCodOb h1 h3 h4 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCodOb h2 h3 h4
  | rigid h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigid h2
  | ctorHead h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorHead ⟨I, ℓs, m, s, h2, h3, h4⟩
  | ctorArg h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorArg ⟨I, ℓs, m, s, h2, h3, h4⟩
  | ctorArgOb h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorArgOb ⟨I, ℓs, m, s, h2, h3, h4⟩
  | rigidArg h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArg h2
  | rigidArgOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArgOb h2
  | @app _ τd K c _ τc _ C _ hD hd _ hB hc hC hcod _ ihk iho =>
    have ⟨_, h2, l⟩ := h _ hD; cases l.piDom_inv
    have ⟨_, hC', lC⟩ := h _ hC; cases lC.piCod_inv
    have ⟨τd', hd1, hd2⟩ := exists_list_cover (L := τd) (P := fun y => Ob.piDomOb y ∈ τs')
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨_, h3, l⟩ := h _ (hd x hx)
        have ⟨y, e, l'⟩ := l.piDomOb_inv; subst e; exact ⟨y, h3, l'⟩
    have ⟨τc', hc1, hc2⟩ := exists_list_cover (L := τc)
      (P := fun y => ∃ K₀, Ob.piCodOb c K₀ y ∈ τs' ∧ Covers K K₀)
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨K₀, h3, hK⟩ := hcod x hx
        have ⟨_, h4, l⟩ := h _ h3
        have ⟨K₁, y, e, hK₁, l'⟩ := l.piCodOb_inv; subst e
        exact ⟨y, ⟨K₁, h4, hK.trans hK₁⟩, l'⟩
    exact .app h2 hd1 (fun k hk => ihk k hk hd2) hB hc hC' hc1 (iho hc2)

theorem TypedOb.mono (H : TypedOb env U Δ cv o τs) (h : ∀ τ ∈ τs, τ ∈ τs') :
    TypedOb env U Δ cv o τs' := H.strengthen (.of_subset h)

/-- The observation of the zero level. -/
abbrev zeroF : List Nat → Nat := fun _ => 0

theorem TypedOb.not_sort_zero (H : TypedOb env U Δ cv (.sort ℓ) [.sort zeroF]) : False := by
  cases H with
  | sort h =>
    simp only [List.mem_singleton, Ob.sort.injEq] at h
    exact Nat.succ_ne_zero _ (congrFun h [])

theorem TypedOb.sort_congr (H : TypedOb env U Δ cv o [.sort ℓ]) (e : ∀ ns, ℓ ns = ℓ' ns) :
    TypedOb env U Δ cv o [.sort ℓ'] := by
  have : ℓ = ℓ' := funext e
  subst this; exact H

/-- **Proof irrelevance, semantically**: nothing is typed at a list of observations each of
which is typed at `[sort 0]`. -/
theorem TypedOb.not_prop (H : TypedOb env U Δ cv o τs)
    (h : ∀ τ ∈ τs, ∃ cv', TypedOb env U Δ cv' τ [.sort zeroF]) : False := by
  induction H with
  | sort h1 | piDom h1 | piDomOb h1 | piCod h1 | piCodOb h1 | rigid h1 | rigidArg h1
  | rigidArgOb h1 =>
    obtain ⟨_, h⟩ := h _ h1; exact h.not_sort_zero
  | ctorHead h1 | ctorArg h1 | ctorArgOb h1 =>
    obtain ⟨I, ℓs, m, s, h1, -, hne⟩ := h1
    obtain ⟨_, h⟩ := h _ h1
    cases h with
    | rigid h2 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h2
      exact hne h2
  | app _ _ _ _ _ _ hcod _ _ iho =>
    refine iho fun x hx => ?_
    have ⟨_, h3, _⟩ := hcod x hx
    obtain ⟨_, h⟩ := h _ h3
    cases h with
    | piCodOb h4 h5 h6 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h4; subst h4
      exact ⟨_, h5.sort_congr fun ns => h6 ns rfl⟩

/-- **Typing is inherited by the canonical witnesses.** -/
theorem TypedOb.wit (H : TypedOb env U Δ cv o τs) : ∀ w ∈ o.wit, TypedOb env U Δ cv w τs := by
  induction H with
  | app hD hd hk hB hc hC hcod _ _ iho =>
    intro w hw
    simp only [Ob.wit, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact .app hD hd hk hB hc hC hcod (iho w' hw')
  | ctorArgOb h => intro w hw; simp only [Ob.wit, List.mem_map] at hw
                   obtain ⟨w', -, rfl⟩ := hw; exact .ctorArgOb h
  | _ => intro w hw; simp [Ob.wit] at hw

/-- The typing filter contains the canonical witnesses of each of its observations. -/
theorem TypedOb.backed : Backed (fun o => TypedOb env U Δ cv o τs) :=
  fun _ ho => ho.wit

/-- Every finite typed demand extends to a finite, hereditarily backed typed demand. -/
theorem TypedOb.finite_close {K : List Ob} (hK : ∀ k ∈ K, TypedOb env U Δ cv k τs) :
    ∃ K' : List Ob, (∀ k ∈ K, k ∈ K') ∧
      (∀ k ∈ K', TypedOb env U Δ cv k τs) ∧ Backed (· ∈ K') :=
  Backed.close TypedOb.backed hK

end Model
end VEnv
end Lean4Lean
