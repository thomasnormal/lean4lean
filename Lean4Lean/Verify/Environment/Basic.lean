import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Std.SMap

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

variable (safety : DefinitionSafety) (env : VEnv) in
def TrOpaqueVal (ci : OpaqueVal) (ci' : VDefVal) : Prop :=
  TrConstVal safety env (.opaqueInfo ci) ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value ci'.value

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

/-! ### Constructive evidence for the shared inductive stages

This witness records the constructive header and constructor stages. The legacy
`AddInduct` boundary below exposes that receipt to callers of the old API, while
`TrEnvInductive` uses the richer recursor-stage receipt.
 -/

def insertConsts (C : ConstMap) (cis : List ConstantInfo) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name ci) C

inductive AddInductEvidence (safety : DefinitionSafety) (m₁ : ConstMap) (env₁ : VEnv)
    (decl : VInductDecl) (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  | intro (headers : List InductiveVal) (constructors : List ConstructorVal)
    (headerEnv : VEnv) :
    List.Forall₂
      (fun info header => info.name = header.name ∧
        TrConstant safety env₁ (.inductInfo info) header.toVConstant)
      headers decl.types →
    List.Forall₂
      (fun info ctor => info.name = ctor.name ∧
        TrConstant safety headerEnv (.ctorInfo info) ctor.toVConstant)
      constructors decl.constructorHeaders →
    env₁.addInductHeaders decl.types = some headerEnv →
    headerEnv.addConstructorHeaders decl.constructorHeaders = some env₂ →
    (headers.map (·.name)).Nodup →
    (constructors.map (·.name)).Nodup →
    (∀ info ∈ headers, m₁.find? info.name = none) →
    (∀ info ∈ constructors,
      (insertConsts m₁ (headers.map (.inductInfo ·))).find? info.name = none) →
    m₂ = insertConsts m₁
      (headers.map (.inductInfo ·) ++ constructors.map (.ctorInfo ·)) →
    AddInductEvidence safety m₁ env₁ decl m₂ env₂

namespace AddInductEvidence

variable {safety : DefinitionSafety} {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
  {decl : VInductDecl}

theorem to_addInduct
    (H : AddInductEvidence safety m₁ env₁ decl m₂ env₂) :
    env₁.addInduct decl = some env₂ := by
  cases H with
  | intro _ _ _ _ _ headerAdd constructorAdd _ _ _ _ _ =>
    unfold VEnv.addInduct
    rw [headerAdd]
    exact constructorAdd

theorem le (H : AddInductEvidence safety m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ :=
  VEnv.addInduct.le H.to_addInduct


end AddInductEvidence

/-! ### Constructive evidence for the generated recursor stage

`VDecl.WF.induct` records the header and constructor environment.  Native
registration then appends generated recursor signatures to that environment.
Keep that second stage explicit until the declaration-history relation grows a
corresponding recursor constructor. -/

structure AddInductWithRecursorsEvidence (safety : DefinitionSafety)
    (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (inductiveConstants : ConstMap) (inductiveEnv : VEnv)
    (recursors : List RecursorVal) (models : List VConstVal)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  inductiveEvidence : AddInductEvidence safety m₁ env₁ decl inductiveConstants inductiveEnv
  translations : List.Forall₂
    (fun info model => info.name = model.name ∧
      TrConstant safety inductiveEnv (.recInfo info) model.toVConstant ∧
      model.toVConstant.WF inductiveEnv)
    recursors models
  recursorAdd : inductiveEnv.addConstructorHeaders models = some env₂
  recursorNodup : (models.map (·.name)).Nodup
  recursorFresh : ∀ model ∈ models, inductiveConstants.find? model.name = none
  resultMap : m₂ = insertConsts inductiveConstants (recursors.map (fun info => .recInfo info))

namespace AddInductWithRecursorsEvidence

variable {safety : DefinitionSafety} {m₁ m₂ inductiveConstants : ConstMap}
  {env₁ env₂ inductiveEnv : VEnv} {decl : VInductDecl}
  {recursors : List RecursorVal} {models : List VConstVal}

theorem to_addInductWithRecursors
    (H : AddInductWithRecursorsEvidence safety m₁ env₁ decl inductiveConstants inductiveEnv
      recursors models m₂ env₂) :
    env₁.addInductWithRecursors decl models = some env₂ := by
  unfold VEnv.addInductWithRecursors
  rw [H.inductiveEvidence.to_addInduct]
  exact H.recursorAdd

theorem le
    (H : AddInductWithRecursorsEvidence safety m₁ env₁ decl inductiveConstants inductiveEnv
      recursors models m₂ env₂) :
    env₁ ≤ env₂ :=
  VEnv.addInductWithRecursors.le H.to_addInductWithRecursors

end AddInductWithRecursorsEvidence

theorem insertConsts_append (C : ConstMap) (first second : List ConstantInfo) :
    insertConsts C (first ++ second) = insertConsts (insertConsts C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons ci first ih =>
    simp only [insertConsts, List.foldl_cons, List.cons_append]
    exact ih (C.insert ci.name ci)

theorem insertConsts_wf : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    (insertConsts C cis).WF
  | [], _, hC, _, _ => hC
  | ci :: cis, C, hC, hfr, hnd => by
    rw [show insertConsts C (ci :: cis) = insertConsts (C.insert ci.name ci) cis by rfl]
    have hnd' := List.nodup_cons.mp hnd
    apply insertConsts_wf (hC.insert _ _ (hfr ci (.head _)))
    · intro d hd
      rw [hC.find?_insert]
      split
      · rename_i equal
        simp only [beq_iff_eq] at equal
        exact False.elim (hnd'.1 (by simpa [equal] using List.mem_map.mpr ⟨d, hd, rfl⟩))
      · exact hfr d (.tail _ hd)
    · exact hnd'.2

theorem insertConsts_find? : ∀ {cis : List ConstantInfo} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertConsts C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    have hfr' : ∀ e ∈ ds, (C.insert d.name d).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      split
      · rename_i equal
        simp only [beq_iff_eq] at equal
        exact False.elim (hnd'.1 (by simpa [equal] using List.mem_map.mpr ⟨e, he, rfl⟩))
      · exact hfr e (.tail _ he)
    rcases insertConsts_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd'.2 h with h | ⟨e, he, hn, heq⟩
    · rw [hC.find?_insert] at h
      split at h
      · rename_i equal
        simp only [beq_iff_eq] at equal
        exact .inr ⟨d, .head _, equal, by cases h; rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, hn, heq⟩

theorem insertConsts_preserves_find? {cis : List ConstantInfo} {C : ConstMap}
    (hC : C.WF) (hfr : ∀ ci ∈ cis, C.find? ci.name = none)
    (hnd : (cis.map (·.name)).Nodup) {name} {ci : ConstantInfo}
    (hold : C.find? name = some ci) :
    (insertConsts C cis).find? name = some ci := by
  induction cis generalizing C with
  | nil => exact hold
  | cons head cis ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hname : head.name ≠ name := by
      intro heq
      have hfound : C.find? head.name = some ci := by simpa [heq] using hold
      rw [hfr head (.head _)] at hfound
      cases hfound
    have hC' := hC.insert head.name head (hfr head (.head _))
    have hold' : (C.insert head.name head).find? name = some ci := by
      rw [hC.find?_insert]
      simp [hname, hold]
    have hfr' : ∀ entry ∈ cis,
        (C.insert head.name head).find? entry.name = none := by
      intro entry hentry
      rw [hC.find?_insert]
      split
      · rename_i equal
        simp only [beq_iff_eq] at equal
        exact False.elim (hnd'.1 (by
          simpa [equal] using List.mem_map.mpr ⟨entry, hentry, rfl⟩))
      · exact hfr entry (.tail _ hentry)
    rw [show insertConsts C (head :: cis) =
      insertConsts (C.insert head.name head) cis by rfl]
    exact ih hC' hfr' hnd'.2 hold'

theorem insertConsts_mem {cis : List ConstantInfo} {C : ConstMap} (hC : C.WF)
    (hfr : ∀ ci ∈ cis, C.find? ci.name = none)
    (hnd : (cis.map (·.name)).Nodup) {ci : ConstantInfo} (hci : ci ∈ cis) :
    (insertConsts C cis).find? ci.name = some ci := by
  induction cis generalizing C with
  | nil => cases hci
  | cons head cis ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hfr' : ∀ entry ∈ cis,
        (C.insert head.name head).find? entry.name = none := by
      intro entry hentry
      rw [hC.find?_insert]
      split
      · rename_i equal
        simp only [beq_iff_eq] at equal
        exact False.elim (hnd'.1 (by
          simpa [equal] using List.mem_map.mpr ⟨entry, hentry, rfl⟩))
      · exact hfr entry (.tail _ hentry)
    rw [show insertConsts C (head :: cis) =
      insertConsts (C.insert head.name head) cis by rfl]
    rcases List.mem_cons.mp hci with hhead | htail
    · subst ci
      exact insertConsts_preserves_find? (hC.insert _ _ (hfr _ (.head _)))
        hfr' hnd'.2 (by rw [hC.find?_insert]; simp)
    · exact ih (hC.insert _ _ (hfr _ (.head _))) hfr' hnd'.2 htail


/-- The legacy inductive boundary is retained for declaration-history compatibility,
   but its constructor now requires constructive staged evidence. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  | ofEvidence :
    AddInductEvidence .safe m₁ env₁ decl m₂ env₂ →
    AddInduct m₁ env₁ decl m₂ env₂

nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁.addInduct decl = some env₂ :=
  match H with
  | .ofEvidence evidence => evidence.to_addInduct

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' { stage₁ } false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A mutual block, and an unsafe definition as the one-element case. -/
  | mutualDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | mutualDef _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
