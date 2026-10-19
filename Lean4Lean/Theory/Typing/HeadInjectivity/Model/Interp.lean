import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Obs

/-! # Interpretation of expressions by observations

Adapted from kim-em/lean4lean PR #53 at
5a8c0d5f111809a95f4924c71e0e9bc8738d72e0 for the existing six-constructor
expression language. Constants use actual lookups and stored equations, with
typing filters at their stored types. Constructor and rule observations retain
finite backed keys and the actual rule-variable binding conditions.

The structural results below require no environment validity or typing of the
anchor. Model soundness, level invariance and head separation remain separate
obligations. Projection and case-eliminator metadata are absent in this fragment.
-/

namespace Lean4Lean
namespace VExpr

/-- Apply an argument spine from left to right. -/
def mkApps (fn : VExpr) (args : List VExpr) : VExpr := args.foldl .app fn

/-- Wrap rule binders in their stored outermost-first order. -/
def wrapLams (doms : List VExpr) (body : VExpr) : VExpr := doms.foldr .lam body

/-- Remove only leading lambda binders from a stored equation. -/
def stripLams : VExpr → VExpr
  | .lam _ body => stripLams body
  | e => e

/-- The function at the head of an application spine. -/
def appHead : VExpr → VExpr
  | .app f _ => appHead f
  | e => e

theorem appHead_mkApps : (mkApps fn args).appHead = fn.appHead := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact ih

theorem stripLams_wrapLams : (wrapLams doms body).stripLams = body.stripLams := by
  induction doms with
  | nil => rfl
  | cons A doms ih => exact ih

end VExpr

/-- A constant is rigid when no stored equation has that head after removing
leading rule binders. This excludes both delta and pattern rules. -/
def VEnv.Rigid (env : VEnv) (n : Name) : Prop :=
  ∀ df, env.defeqs df → ∀ ls, df.lhs.stripLams.appHead ≠ .const n ls

/-- The final major argument of a stored equation has this constructor head. -/
def VDefEq.HasConstructorMajor (df : VDefEq) (n : Name) : Prop :=
  ∃ fn ls args, df.lhs.stripLams = .app fn (VExpr.mkApps (.const n ls) args)

theorem VDefEq.HasConstructorMajor.unique {df : VDefEq}
    (h : df.HasConstructorMajor n) (h' : df.HasConstructorMajor n') : n = n' := by
  obtain ⟨f, ls, args, he⟩ := h
  obtain ⟨f', ls', args', he'⟩ := h'
  have heads := congrArg VExpr.appHead (VExpr.app.inj (he.symm.trans he')).2
  simp only [VExpr.appHead_mkApps, VExpr.appHead] at heads
  exact (VExpr.const.inj heads).1

namespace VEnv
namespace Model

/-- Observation sets of the variables of a valuation. -/
abbrev ObSets := Nat → Ob → Prop

namespace ObSets

def cons (S : ObSets) (X : Ob → Prop) : ObSets
  | 0 => X
  | i+1 => S i

def lift_l (ρ : Lift) (S : ObSets) : ObSets := fun i => S (ρ.liftVar i)

protected def empty : ObSets := fun _ _ => False

def update (S : ObSets) (n : Nat) (X : Ob → Prop) : ObSets := fun i => if i = n then X else S i

theorem lift_l_cons {S : ObSets} : (S.cons X).lift_l ρ.cons = (S.lift_l ρ).cons X := by
  funext i; cases i <;> rfl

theorem update_cons {S : ObSets} : (S.cons X).update (n+1) Y = (S.update n Y).cons X := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change (if i+1 = n+1 then Y else S i) = (if i = n then Y else S i)
    by_cases h : i = n
    · subst i; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => h (Nat.succ.inj e)), if_neg h]

end ObSets

theorem _root_.Lean4Lean.VExpr.Subst.lift_l_cons {σ : VExpr.Subst} :
    (σ.cons x).lift_l ρ.cons = (σ.lift_l ρ).cons x := by
  funext i; cases i <;> rfl

theorem _root_.Lean4Lean.VExpr.Subst.lift_comp_cons {τ σ : VExpr.Subst} :
    τ.lift.comp (σ.cons x) = (τ.comp σ).cons x := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons]

/-- The finite set of a list of observations. -/
def listSet (K : List Ob) : Ob → Prop := fun k => k ∈ K

/-- `c` is an installed constructor: the major premise of a stored rule is headed by `c`. -/
def IsInstalledCtor (env : VEnv) (c : Name) : Prop := ∃ df, env.defeqs df ∧ df.HasConstructorMajor c

/-- The innermost observations of a constructor spine after the keys `keys`: the head, an
argument class, or an argument observation (with the keys of the earlier arguments). -/
def CtorEnd (n : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) (r : Ob) : Prop :=
  r = .ctorHead n ℓs keys.length ∨
  (∃ i, ∃ h : i < keys.length, r = .ctorArg i (keys[i]).2.1) ∨
  (∃ i, ∃ h : i < keys.length, ∃ k ∈ (keys[i]).2.2, r = .ctorArgOb i (keys.take i) k)

/-- Every key list of a spine is backed. -/
def KeysBacked (keys : List Key) : Prop := ∀ k ∈ keys, Backed (fun o => o ∈ k.2.2)

/-- The observation of a Pi telescope recording the codomain observation `x` at the keys. -/
def piCodChain (keys : List Key) (x : Ob) : Ob := keys.foldr (fun k x => .piCodOb k.2.1 k.2.2 x) x

@[simp] theorem piCodChain_nil : piCodChain [] x = x := rfl
@[simp] theorem piCodChain_cons :
    piCodChain (k :: ks) x = .piCodOb k.2.1 k.2.2 (piCodChain ks x) := rfl

theorem piCodChain_append : piCodChain (ks ++ ks') x = piCodChain ks (piCodChain ks' x) := by
  simp [piCodChain, List.foldr_append]

/-- The type of the binder `x` (de Bruijn index in the body) of a rule whose binder
domains are `doms` (outermost first), at the levels `ls`. -/
def binderTy (doms : List VExpr) (ls : List VLevel) (x : Nat) : VExpr :=
  ((doms.reverse.getD x default).liftN (x+1)).instL ls

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- Bind stored rule variables using the first bare leading occurrence, or a
constructor field absent from those leading occurrences. Fields use actual
constructor observations in mode AB, or an actually typed propositional
representative with empty observations. Every bound observation set is backed. -/
def RuleBind (doms : List VExpr) (ls : List VLevel) (lead : List VExpr) (msLen : Nat)
    (fs : List Nat) (mC : Bool) (keys : List Key)
    (Km : List Ob) (τ : VExpr.Subst) (S' : Nat → Ob → Prop) : Prop :=
  (∀ x, Backed (S' x)) ∧ ∀ x < doms.length,
    (∃ i : Nat, ∃ k : Key, lead[i]? = some (VExpr.bvar x) ∧ (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) ∧
      keys[i]? = some k ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst τ)) k.2.1 ∧ k.2.1 (τ x) ∧
      S' x = listSet k.2.2) ∨
    ((∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ ∃ j : Nat, fs[j]? = some x ∧
      ((mC = false ∧ ∃ c, .ctorArg (msLen + j) c ∈ Km ∧
          TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst τ)) c ∧ c (τ x) ∧
          S' x = fun k => ∃ pre, .ctorArgOb (msLen + j) pre k ∈ Km) ∨
       ((∃ X, TyCls env U Δ ((binderTy doms ls x).subst τ) X ∧ env.HasType U Δ (τ x) X) ∧
          (∃ P, TyCls env U Δ ((binderTy doms ls x).subst τ) P ∧
            env.HasType U Δ P (.sort .zero)) ∧
          S' x = fun _ => False)))

end

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The observation interpretation. See the module docstring for the clauses. -/
inductive Obs : VExpr.Subst → ObSets → VExpr → Ob → Prop
  | bvar : S i o → Obs σ S (.bvar i) o
  | sort : Obs σ S (.sort l) (.sort l.eval)
  | piDom : Obs σ S (.forallE A B) (.piDom (TyCls env U Δ (A.subst σ)))
  | piDomOb : Obs σ S A o → Obs σ S (.forallE A B) (.piDomOb o)
  | piCod : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c → c x →
    Obs σ S (.forallE A B) (.piCod c (TyCls env U Δ (B.subst (σ.cons x))))
  | piCodOb : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ c k τs) → Backed (listSet K) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) B o → Obs σ S (.forallE A B) (.piCodOb c K o)
  | lam : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ c k τs) → Backed (listSet K) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) t o →
    Obs σ S (.lam A t) (.app (TyCls env U Δ (A.subst σ)) c K o)
  | app : Obs σ S f (.app D c K o) → c = ElCls env U Δ D (a.subst σ) →
    (∀ k ∈ K', Obs σ S a k) → Covers K' K → Obs σ S (.app f a) o
  | const : env.Rigid n → env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs → RigidEnd n (ls.map (·.eval)) keys r →
    Obs σ S (.const n ls) (wrap keys r)
  /-- A defined constant has the observations of its value (the right side of its delta
  rule, at the same levels), filtered by typing at its type. -/
  | delta : env.defeqs df → df.lhs = .const n (VLevel.params df.uvars) →
    env.constants n = some ci → (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) o τs → Obs .id .empty (df.rhs.instL ls) o → Obs σ S (.const n ls) o
  /-- A constructor has its constructor spine observations, filtered by typing. -/
  | ctor : IsInstalledCtor env n → env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs → CtorEnd n (ls.map (·.eval)) keys r →
    KeysBacked keys → Obs σ S (.const n ls) (wrap keys r)
  /-- The rule clause: a head chain whose keys bind the rule's
  variables has the observations of the rule's right-hand side body at that binding,
  filtered by typing at the head's type. -/
  | rule : env.defeqs df →
    df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])) →
    df.rhs = .wrapLams doms body →
    env.constants n = some ci → (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap (lkeys ++ [(Dm, cm, Km)]) o) τs → lkeys.length = lead.length →
    (mC = true → ∀ df' ls', env.defeqs df' → df'.lhs.stripLams.appHead = .const n ls' →
        df' = df) →
    (mC = true → Obs .id .empty (ci.type.instL ls)
        (piCodChain lkeys (.piDomOb (.rigid I ℓsI mI fun _ => 0)))) →
    (mC = false → ∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ Km) →
    RuleBind env U Δ doms ls lead ms.length fs mC lkeys Km τ S' →
    KeysBacked (lkeys ++ [(Dm, cm, Km)]) → Obs τ S' (body.instL ls) o →
    Obs σ S (.const n ls) (wrap (lkeys ++ [(Dm, cm, Km)]) o)

/-- `o`, an observation of a value of class `cv`, is typed at a list of observations of `T`. -/
def TypedAt (cv : VExpr → Prop) (σ : VExpr.Subst) (S : ObSets) (T : VExpr) (o : Ob) : Prop :=
  ∃ τs, (∀ τ ∈ τs, Obs env U Δ σ S T τ) ∧ TypedOb env U Δ cv o τs

/-- A typed valuation for `Γ`: every observation set of a variable is backed, and every
observation of a variable is typed at observations of its type. (The anchor's typing, `Ctx.SubstEq env U Δ σ σ Γ`, is a separate hypothesis.) -/
def TV (Γ : List VExpr) (σ : VExpr.Subst) (S : ObSets) : Prop :=
  (∀ i, Backed (S i)) ∧
    ∀ i A, Lookup Γ i A → ∀ o, S i o → TypedAt env U Δ (vcls env U Δ σ (.bvar i) A) σ S A o

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

namespace Obs

theorem bvar_iff : Obs' σ S (.bvar i) o ↔ S i o :=
  ⟨fun | .bvar h => h, .bvar⟩

theorem sort_iff : Obs' σ S (.sort l) o ↔ o = .sort l.eval :=
  ⟨fun | .sort => rfl, fun h => h ▸ .sort⟩

theorem forallE_iff : Obs' σ S (.forallE A B) o ↔
    o = .piDom (TyCls env U Δ (A.subst σ)) ∨
    (∃ p, o = .piDomOb p ∧ Obs' σ S A p) ∨
    (∃ c x, o = .piCod c (TyCls env U Δ (B.subst (σ.cons x))) ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧ c x) ∨
    (∃ c K x τs p, o = .piCodOb c K p ∧ TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ c k τs) ∧ Backed (listSet K) ∧ c x ∧
      Obs' (σ.cons x) (S.cons (listSet K)) B p) := by
  constructor
  · intro h; cases h with
    | piDom => exact .inl rfl
    | piDomOb h => exact .inr (.inl ⟨_, rfl, h⟩)
    | piCod h1 h2 => exact .inr (.inr (.inl ⟨_, _, rfl, h1, h2⟩))
    | piCodOb h1 h2 h3 hb h4 h5 =>
      exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩))
  · rintro (rfl | ⟨_, rfl, h⟩ | ⟨_, _, rfl, h1, h2⟩ | ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩)
    · exact .piDom
    · exact .piDomOb h
    · exact .piCod h1 h2
    · exact .piCodOb h1 h2 h3 hb h4 h5

theorem lam_iff : Obs' σ S (.lam A t) o ↔
    ∃ c K x τs p, o = .app (TyCls env U Δ (A.subst σ)) c K p ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ c k τs) ∧ Backed (listSet K) ∧
      c x ∧ Obs' (σ.cons x) (S.cons (listSet K)) t p := by
  constructor
  · intro h; cases h with
    | lam h1 h2 h3 hb h4 h5 => exact ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩
  · rintro ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩; exact .lam h1 h2 h3 hb h4 h5

theorem app_iff : Obs' σ S (.app f a) o ↔
    ∃ D c K K', Obs' σ S f (.app D c K o) ∧ c = ElCls env U Δ D (a.subst σ) ∧
      (∀ k ∈ K', Obs' σ S a k) ∧ Covers K' K := by
  constructor
  · intro h; cases h with
    | app h1 h2 h3 h4 => exact ⟨_, _, _, _, h1, h2, h3, h4⟩
  · rintro ⟨_, _, _, _, h1, h2, h3, h4⟩; exact .app h1 h2 h3 h4

/-- Constant clauses read their recursive premises at fixed valuations. -/
theorem const_indep : Obs' σ S (.const n ls) o ↔ Obs' σ' S' (.const n ls) o := by
  constructor <;> intro h <;> cases h with
  | const h0 h1 h2 h3 h4 => exact .const h0 h1 h2 h3 h4
  | delta h1 h2 h3 h4 h5 h6 => exact .delta h1 h2 h3 h4 h5 h6
  | ctor h0 h1 h2 h3 h4 hb => exact .ctor h0 h1 h2 h3 h4 hb
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12

theorem piDom_mem (h : Obs' σ S (.forallE A B) (.piDom D)) : D = TyCls env U Δ (A.subst σ) := by
  cases h; rfl

theorem piDomOb_mem (h : Obs' σ S (.forallE A B) (.piDomOb p)) : Obs' σ S A p := by
  cases h; assumption

theorem piCod_mem (h : Obs' σ S (.forallE A B) (.piCod c C)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      ∃ x, c x ∧ C = TyCls env U Δ (B.subst (σ.cons x)) := by
  cases h with | piCod h1 h2 => exact ⟨h1, _, h2, rfl⟩

theorem piCodOb_mem (h : Obs' σ S (.forallE A B) (.piCodOb c K p)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∃ τs, (∀ τ ∈ τs, Obs' σ S A τ) ∧ ∀ k ∈ K, TypedOb env U Δ c k τs) ∧
      ∃ x, c x ∧ Obs' (σ.cons x) (S.cons (listSet K)) B p := by
  cases h with | piCodOb h1 h2 h3 _ h4 h5 => exact ⟨h1, ⟨_, h2, h3⟩, _, h4, h5⟩

theorem piCodOb_backed (h : Obs' σ S (.forallE A B) (.piCodOb c K p)) : Backed (listSet K) := by
  cases h with | piCodOb _ _ _ hb => exact hb

theorem sort_mem (h : Obs' σ S (.sort l) o) : o = .sort l.eval := sort_iff.1 h

/-! ## Weakening -/

theorem lift'_iff {t : VExpr} {ρ : Lift} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.lift' ρ) o ↔ Obs' (σ.lift_l ρ) (S.lift_l ρ) t o := by
  induction t generalizing ρ σ S o with
  | bvar i => simp only [VExpr.lift', bvar_iff]; rfl
  | sort => simp only [VExpr.lift', sort_iff]
  | const => exact const_indep
  | app f a ihf iha =>
    simp only [VExpr.lift', app_iff, ihf, iha, VExpr.subst_lift']
  | lam A t ihA iht =>
    simp only [VExpr.lift', lam_iff, ihA, iht, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]
  | forallE A B ihA ihB =>
    simp only [VExpr.lift', forallE_iff, ihA, ihB, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]

theorem lift_cons_iff {t : VExpr} :
    Obs' (σ.cons x) (S.cons X) t.lift o ↔ Obs' σ S t o := by
  rw [VExpr.lift_eq_lift', lift'_iff]; rfl

/-! ## Substitution -/

theorem lift_cons_set {σ : VExpr.Subst} {S : ObSets} (τ : VExpr.Subst) :
    (fun i => Obs' (σ.cons x) (S.cons (listSet K)) (τ.lift i)) =
      ObSets.cons (fun i => Obs' σ S (τ i)) (listSet K) := by
  funext i o; cases i with
  | zero => exact propext bvar_iff
  | succ i => exact propext lift_cons_iff

theorem subst_iff {t : VExpr} {τ σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.subst τ) o ↔ Obs' (τ.comp σ) (fun i => Obs' σ S (τ i)) t o := by
  induction t generalizing τ σ S o with
  | bvar i => simp only [VExpr.subst, bvar_iff]
  | sort => simp only [VExpr.subst, sort_iff]
  | const => exact const_indep
  | app f a ihf iha =>
    simp only [VExpr.subst, app_iff, ihf, iha, VExpr.subst_subst]
  | lam A t ihA iht =>
    simp only [VExpr.subst, lam_iff, ihA, iht, VExpr.subst_subst, VExpr.Subst.lift_comp_cons,
      lift_cons_set]
  | forallE A B ihA ihB =>
    simp only [VExpr.subst, forallE_iff, ihA, ihB, VExpr.subst_subst,
      VExpr.Subst.lift_comp_cons, lift_cons_set]

/-- Instantiation: the observations of `t.inst a` are those of `t` with the bound variable
read as `a` (anchor `a.subst σ`, observation set the observations of `a`). -/
theorem inst_iff {t a : VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.inst a) o ↔ Obs' (σ.cons (a.subst σ)) (S.cons (Obs' σ S a)) t o := by
  rw [VExpr.inst_eq, subst_iff]
  have h1 : (VExpr.Subst.one a).comp σ = σ.cons (a.subst σ) := by
    funext i; cases i <;> rfl
  have h2 : (fun i => Obs' σ S (VExpr.Subst.one a i)) = S.cons (Obs' σ S a) := by
    funext i o; cases i with
    | zero => rfl
    | succ i => exact propext bvar_iff
  rw [h1, h2]

/-! ## Monotonicity and compactness -/

/-- Monotonicity under inclusion of the observation sets. -/
theorem mono (h : Obs' σ S t o) (hS : ∀ i o, S i o → S' i o) : Obs' σ S' t o := by
  induction h generalizing S' with
  | bvar h => exact .bvar (hS _ _ h)
  | sort => exact .sort
  | piDom => exact .piDom
  | piDomOb _ ih => exact .piDomOb (ih hS)
  | piCod h1 h2 => exact .piCod h1 h2
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    refine .piCodOb h1 (fun τ hτ => ih2 τ hτ hS) h3 hb h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    refine .lam h1 (fun τ hτ => ih2 τ hτ hS) h3 hb h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | app _ h2 _ h4 ih1 ih3 => exact .app (ih1 hS) h2 (fun k hk => ih3 k hk hS) h4
  | const h0 h1 h2 h3 h4 => exact .const h0 h1 h2 h3 h4
  | delta h1 h2 h3 h4 h5 h6 => exact .delta h1 h2 h3 h4 h5 h6
  | ctor h0 h1 h2 h3 h4 hb => exact .ctor h0 h1 h2 h3 h4 hb
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12

/-- Monotonicity up to subsumption: if every observation of `S` is subsumed by one of
`S'`, every observation under `S` is subsumed by one under `S'`. -/
theorem mono_le (h : Obs' σ S t o) (hS : ∀ i o, S i o → ∃ o', S' i o' ∧ o' ≼ o) :
    ∃ o', Obs' σ S' t o' ∧ o' ≼ o := by
  induction h generalizing S' with
  | bvar h => let ⟨o', h1, h2⟩ := hS _ _ h; exact ⟨o', .bvar h1, h2⟩
  | sort => exact ⟨_, .sort, .refl⟩
  | piDom => exact ⟨_, .piDom, .refl⟩
  | piDomOb _ ih => let ⟨o', h1, h2⟩ := ih hS; exact ⟨_, .piDomOb h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨_, .piCod h1 h2, .refl⟩
  | @piCodOb _ τs _ _ _ K _ _ _ h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .piCodOb h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) hb h4 ho1,
      .piCodOb_of_covers .refl ho2⟩
  | @lam _ τs _ _ _ K _ _ _ h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .lam h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) hb h4 ho1, .app' .refl ho2⟩
  | @app _ _ _ _ _ _ _ K' _ _ h2 _ h4 ih1 ih3 =>
    have ⟨o₁, h1', l₁⟩ := ih1 hS
    have ⟨K₀, y, e, hK₀, ly⟩ := l₁.app_inv; subst e
    have ⟨K'', hK1, hK2⟩ := exists_list_cover (L := K') (R := fun y x => y ≼ x)
      fun k hk => ih3 k hk hS
    exact ⟨y, .app h1' h2 hK1 (Covers.trans hK2 (h4.trans hK₀)), ly⟩
  | const h0 h1 h2 h3 h4 => exact ⟨_, .const h0 h1 h2 h3 h4, .refl⟩
  | delta h1 h2 h3 h4 h5 h6 => exact ⟨_, .delta h1 h2 h3 h4 h5 h6, .refl⟩
  | ctor h0 h1 h2 h3 h4 hb => exact ⟨_, .ctor h0 h1 h2 h3 h4 hb, .refl⟩
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨_, .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12, .refl⟩
/-- Merge finitely many finite witnesses into one. -/
theorem collect {α : Type} {Q : Ob → Prop} {P : List Ob → α → Prop}
    (hP : ∀ K K' x, (∀ k ∈ K, k ∈ K') → P K x → P K' x) :
    ∀ {L : List α}, (∀ x ∈ L, ∃ K, (∀ k ∈ K, Q k) ∧ P K x) →
      ∃ K, (∀ k ∈ K, Q k) ∧ ∀ x ∈ L, P K x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨K₁, hQ₁, hP₁⟩ := h x (.head _)
    obtain ⟨K₂, hQ₂, hP₂⟩ := collect hP fun y hy => h y (.tail _ hy)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, fun y hy => ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hQ₁ k hk
      · exact hQ₂ k hk
    · cases hy with
      | head => exact hP _ _ _ (fun k hk => List.mem_append_left _ hk) hP₁
      | tail _ hy => exact hP _ _ _ (fun k hk => List.mem_append_right _ hk) (hP₂ y hy)

theorem update_mono {S : ObSets} (h : ∀ k ∈ K, k ∈ K') :
    ∀ i o, S.update n (listSet K) i o → S.update n (listSet K') i o := by
  intro i o h'; unfold ObSets.update at h' ⊢; split <;> simp_all [listSet]

theorem compact_bvar {S : ObSets} (h : S i o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) (.bvar i) o := by
  by_cases e : i = n
  · subst e; exact ⟨[o], by simpa using h, .bvar (by simp [ObSets.update, listSet])⟩
  · exact ⟨[], nofun, .bvar (by simpa [ObSets.update, e] using h)⟩

/-- **Compactness**: a derivation uses finitely many observations of each variable. -/
theorem compact (h : Obs' σ S t o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) t o := by
  induction h generalizing n with
  | bvar h => exact compact_bvar h n
  | sort => exact ⟨[], nofun, .sort⟩
  | piDom => exact ⟨[], nofun, .piDom⟩
  | piDomOb _ ih => let ⟨K, h1, h2⟩ := ih n; exact ⟨K, h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨[], nofun, .piCod h1 h2⟩
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .piCodOb h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 hb h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .lam h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 hb h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | app _ h2 _ h4 ih1 ih3 =>
    have ⟨K₁, hK₁, hf⟩ := ih1 n
    have ⟨K₂, hK₂, ha⟩ := collect (P := fun K k => Obs' _ (ObSets.update _ n (listSet K)) _ k)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun k hk => ih3 k hk n
    refine ⟨K₁ ++ K₂, fun k hk => ?_,
      .app (hf.mono (update_mono fun k hk => List.mem_append_left _ hk)) h2
        (fun k hk => (ha k hk).mono (update_mono fun k hk => List.mem_append_right _ hk)) h4⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact hK₁ k hk
    · exact hK₂ k hk
  | const h0 h1 h2 h3 h4 => exact ⟨[], nofun, .const h0 h1 h2 h3 h4⟩
  | delta h1 h2 h3 h4 h5 h6 => exact ⟨[], nofun, .delta h1 h2 h3 h4 h5 h6⟩
  | ctor h0 h1 h2 h3 h4 hb => exact ⟨[], nofun, .ctor h0 h1 h2 h3 h4 hb⟩
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨[], nofun, .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12⟩
/-- Compactness at the bound variable of an instantiation. -/
theorem compact0 {S : ObSets} {X : Ob → Prop} (h : Obs' σ (S.cons X) t o) :
    ∃ K : List Ob, (∀ k ∈ K, X k) ∧ Obs' σ (S.cons (listSet K)) t o := by
  have ⟨K, h1, h2⟩ := h.compact 0
  refine ⟨K, h1, h2.mono fun i o h => ?_⟩
  cases i <;> simpa [ObSets.update, ObSets.cons] using h

/-- Compactness at the bound variable `0` with a backed key list, for a backed set `X`. -/
theorem compact0B {S : ObSets} {X : Ob → Prop} (h : Obs' σ (S.cons X) t o) (hX : Backed X) :
    ∃ K : List Ob, (∀ k ∈ K, X k) ∧ Backed (listSet K) ∧ Obs' σ (S.cons (listSet K)) t o := by
  have ⟨K₀, h1, h2⟩ := h.compact0
  have ⟨K, h3, h4, h5⟩ := Backed.close hX h1
  refine ⟨K, h4, h5, h2.mono fun i o h => ?_⟩
  cases i with
  | zero => exact h3 o h
  | succ i => exact h

/-! ## Closed terms -/

theorem _root_.Lean4Lean.VExpr.ClosedN.subst_congr {e : VExpr} {σ σ' : VExpr.Subst}
    (h : e.ClosedN k) (hσ : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with
  | bvar i => exact hσ i h
  | sort | const => rfl
  | app _ _ ih1 ih2 => simp only [VExpr.subst, ih1 h.1 hσ, ih2 h.2 hσ]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp only [VExpr.subst, ih1 h.1 hσ]
    rw [ih2 h.2 fun i hi => ?_]
    cases i with
    | zero => rfl
    | succ i => simp [VExpr.Subst.lift, hσ i (by omega)]

/-- The observations of a term depend only on the valuation of its free variables. -/
theorem closed_iff {t : VExpr} (ht : t.ClosedN k) (hσ : ∀ i < k, σ i = σ' i)
    (hS : ∀ i < k, S i = S' i) : Obs' σ S t o ↔ Obs' σ' S' t o := by
  induction t generalizing k σ σ' S S' o with
  | bvar i => simp only [bvar_iff, hS i ht]
  | sort => simp only [sort_iff]
  | const => exact const_indep
  | app f a ihf iha =>
    simp only [app_iff, ihf ht.1 hσ hS, iha ht.2 hσ hS, ht.2.subst_congr hσ]
  | lam A t ihA iht =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [lam_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x X o => iht (o := o) ht.2 (hσ' x) (hS' X)]
  | forallE A B ihA ihB =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [forallE_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x => ht.2.subst_congr (hσ' x), fun x X o => ihB (o := o) ht.2 (hσ' x) (hS' X)]

theorem closed_iff_id {t : VExpr} (ht : t.ClosedN) : Obs' σ S t o ↔ Obs' .id .empty t o :=
  closed_iff ht (fun _ h => nomatch h) (fun _ h => nomatch h)

theorem _root_.Lean4Lean.VEnv.Model.wit_wrap :
    ∀ {keys : List Key} {o : Ob}, (wrap keys o).wit = o.wit.map (wrap keys)
  | [], o => by simp only [wrap_nil]; exact (List.map_id' _).symm
  | k :: keys, o => by
    simp only [wrap_cons, Ob.wit, wit_wrap, List.map_map]; rfl

theorem _root_.Lean4Lean.VEnv.Model.mem_wit_wrap {keys : List Key} :
    w ∈ (wrap keys o).wit ↔ ∃ w', w' ∈ o.wit ∧ w = wrap keys w' := by
  rw [wit_wrap, List.mem_map]; exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm⟩, fun ⟨a, b, c⟩ => ⟨a, b, c.symm⟩⟩

/-- **Backing is structural**: observation sets at backed valuations are backed. -/
theorem backed (h : Obs' σ S t o) (hS : ∀ i, Backed (S i)) : ∀ w ∈ o.wit, Obs' σ S t w := by
  induction h with
  | bvar h => exact fun w hw => .bvar (hS _ _ h w hw)
  | sort | piDom | piCod | piDomOb | piCodOb =>
    intro w hw; simp [Ob.wit] at hw
  | @lam _ _ _ c x τs K t' o h1 h2 h3 hb h4 _ _ ih5 =>
    intro w hw
    simp only [Ob.wit, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine .lam h1 h2 h3 hb h4 (ih5 (fun i => ?_) w' hw')
    cases i with
    | zero => exact hb
    | succ i => exact hS i
  | app _ h2 h3 h4 ih1 _ =>
    intro w hw
    exact .app (ih1 hS _ (by simp only [Ob.wit]; exact List.mem_map_of_mem hw)) h2 h3 h4
  | const h0 h1 h2 h3 h4 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    rcases h4 with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Ob.wit] at hw'
  | delta h1 h2 h3 h4 h5 _ _ ih6 =>
    intro w hw
    exact .delta h1 h2 h3 h4 (h5.wit w hw) (ih6 (fun _ _ h => nomatch h) w hw)
  | ctor h0 h1 h2 h3 h4 hb =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    rcases h4 with rfl | ⟨_, _, rfl⟩ | ⟨i, hi, k, hk, rfl⟩
    · simp [Ob.wit] at hw'
    · simp [Ob.wit] at hw'
    · simp only [Ob.wit, List.mem_map] at hw'
      obtain ⟨w'', hw'', rfl⟩ := hw'
      have hty := h3.wit _ (mem_wit_wrap.2 ⟨_, by simp only [Ob.wit]; exact List.mem_map_of_mem hw'', rfl⟩)
      exact .ctor h0 h1 h2 hty (.inr (.inr ⟨i, hi, w'', hb _ (List.getElem_mem hi) k hk w'' hw'', rfl⟩)) hb
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 _ _ ih12 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    have hty := h6.wit _ (mem_wit_wrap.2 ⟨_, hw', rfl⟩)
    exact .rule h1 h2 h3 h4 h5 hty h7 h8 h9 h10 h11 hb (ih12 h11.1 w' hw')

end Obs

theorem TypedAt.mono_le (h : TypedAt env U Δ cv σ S T o)
    (hT : Ob.Sub (Obs' σ S T) (Obs' σ' S' T')) : TypedAt env U Δ cv σ' S' T' o := by
  obtain ⟨τs, h1, h2⟩ := h
  have ⟨τs', h3, h4⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
    fun τ hτ => hT τ (h1 τ hτ)
  exact ⟨τs', h3, h2.strengthen h4⟩

theorem TypedAt.congr_cls (h : TypedAt env U Δ cv σ S T o) (e : cv = cv') :
    TypedAt env U Δ cv' σ S T o := e ▸ h

/-- Finitely many typed observations are typed at one common list. -/
theorem TypedAt.merge {K : List Ob} (h : ∀ k ∈ K, TypedAt env U Δ cv σ S T k) :
    ∃ τs, (∀ τ ∈ τs, Obs' σ S T τ) ∧ ∀ k ∈ K, TypedOb env U Δ cv k τs := by
  have ⟨τs, h1, h2⟩ := Obs.collect (Q := fun τ => Obs' σ S T τ)
    (P := fun τs k => TypedOb env U Δ cv k τs) (fun _ _ _ hK h => h.mono hK) fun k hk =>
      let ⟨τs, h1, h2⟩ := h k hk; ⟨τs, h1, h2⟩
  exact ⟨τs, h1, h2⟩

theorem TypedAt.lift_cons {T : VExpr} (h : TypedAt env U Δ cv σ S T o) :
    TypedAt env U Δ cv (σ.cons x) (S.cons X) T.lift o :=
  let ⟨τs, h1, h2⟩ := h; ⟨τs, fun τ hτ => Obs.lift_cons_iff.2 (h1 τ hτ), h2⟩

theorem vcls_bvar_zero {A : VExpr} :
    vcls env U Δ (σ.cons x) (.bvar 0) A.lift = ElCls env U Δ (TyCls env U Δ (A.subst σ)) x := by
  simp only [vcls, VExpr.lift_subst_cons]; rfl

theorem vcls_bvar_succ {A : VExpr} :
    vcls env U Δ (σ.cons x) (.bvar (i+1)) A.lift = vcls env U Δ σ (.bvar i) A := by
  simp only [vcls, VExpr.lift_subst_cons]; rfl

theorem TV.empty : TV env U Δ Γ σ .empty :=
  And.intro (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)

theorem TV.cons (h : TV env U Δ Γ σ S) (hb : Backed (listSet K))
    (hK : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) x) σ S A k) :
    TV env U Δ (A :: Γ) (σ.cons x) (S.cons (listSet K)) := by
  refine ⟨fun i => ?_, fun i B hL o ho => ?_⟩
  · cases i with
    | zero => exact hb
    | succ i => exact h.1 i
  · cases hL with
    | zero => rw [vcls_bvar_zero]; exact (hK o ho).lift_cons
    | succ hL => rw [vcls_bvar_succ]; exact (h.2 _ _ hL o ho).lift_cons

/-- Observations of constants require an actual stored constant. -/
theorem Obs.const_lookup (h : Obs' σ S (.const n ls) o) :
    ∃ ci, env.constants n = some ci := by
  cases h with
  | const _ hlookup _ _ _ => exact ⟨_, hlookup⟩
  | delta _ _ hlookup _ _ _ => exact ⟨_, hlookup⟩
  | ctor _ hlookup _ _ _ _ => exact ⟨_, hlookup⟩
  | rule _ _ _ hlookup _ _ _ _ _ _ _ _ _ => exact ⟨_, hlookup⟩

/-- Every constant observation passes the filter at its actual stored type. -/
theorem Obs.const_typed (h : Obs' σ S (.const n ls) o) (hci : env.constants n = some ci) :
    TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls))
      .id .empty (ci.type.instL ls) o := by
  cases h with
  | const _ hlookup hobs htyped _ => cases hci.symm.trans hlookup; exact ⟨_, hobs, htyped⟩
  | delta _ _ hlookup hobs htyped _ => cases hci.symm.trans hlookup; exact ⟨_, hobs, htyped⟩
  | ctor _ hlookup hobs htyped _ _ => cases hci.symm.trans hlookup; exact ⟨_, hobs, htyped⟩
  | rule _ _ _ hlookup hobs htyped _ _ _ _ _ _ _ =>
    cases hci.symm.trans hlookup; exact ⟨_, hobs, htyped⟩

end Model
end VEnv
end Lean4Lean
