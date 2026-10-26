import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstVal.sf_mono (hsf : safety ≤ safety')
    (H : TrConstVal safety' env ci ci') : TrConstVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrDefVal.sf_mono (hsf : safety ≤ safety')
    (H : TrDefVal safety' env ci ci') : TrDefVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrOpaqueVal.sf_mono (hsf : safety ≤ safety')
    (H : TrOpaqueVal safety' env ci ci') : TrOpaqueVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

theorem TrOpaqueVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrOpaqueVal safety env ci ci') : TrOpaqueVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned { stage₁ } .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .emptyStage _
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?_emptyStage, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem AddInductEvidence.sf_mono (hsf : safety ≤ safety')
    (H : AddInductEvidence safety' m₁ env₁ decl m₂ env₂) :
    AddInductEvidence safety m₁ env₁ decl m₂ env₂ := by
  cases H with
  | intro headers constructors headerEnv hheaders hconstructors headerAdd constructorAdd
      headerNodup constructorNodup headerFresh constructorFresh mapEq =>
    refine .intro headers constructors headerEnv ?_ ?_ headerAdd constructorAdd
      headerNodup constructorNodup headerFresh constructorFresh mapEq
    · exact List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.sf_mono hsf⟩) hheaders
    · exact List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.sf_mono hsf⟩) hconstructors

theorem Aligned.addInductEvidence
    (H : AddInductEvidence safety C₁ venv₁ decl C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  cases H with
  | @intro headers constructors headerEnv hheaders hconstructors headerAdd constructorAdd
      headerNodup constructorNodup headerFresh constructorFresh mapEq =>
    have addHeaders : ∀ {infos : List InductiveVal} {types : List VInductiveType}
        {C : ConstMap} {env env' : VEnv},
        Aligned safety C env →
        List.Forall₂
          (fun info type => info.name = type.name ∧
            TrConstant safety env (.inductInfo info) type.toVConstant) infos types →
        (∀ info ∈ infos, C.find? info.name = none) →
        (infos.map (·.name)).Nodup →
        env.addInductHeaders types = some env' →
        Aligned safety (insertConsts C (infos.map (.inductInfo ·))) env' := by
      intro infos
      induction infos with
      | nil =>
        intro types C env env' aligned pairs fresh nodup added
        cases types with
        | nil =>
          cases pairs
          cases added
          simpa [insertConsts] using aligned
        | cons type types => cases pairs
      | cons info infos ih =>
        intro types C env env' aligned pairs fresh nodup added
        cases types with
        | nil => cases pairs
        | cons type types =>
          cases pairs with
          | cons pair pairs =>
            have nodup' := List.nodup_cons.mp nodup
            simp [VEnv.addInductHeaders, Option.bind_eq_some_iff] at added
            obtain ⟨next, step, rest⟩ := added
            have step' : env.addConst info.name type.toVConstant = some next := by
              rw [pair.1]
              exact step
            have freshTail : ∀ d ∈ infos,
                (C.insert info.name (.inductInfo info)).find? d.name = none := by
              intro d hd
              rw [aligned.map_wf.find?_insert]
              split
              · rename_i equal
                simp only [beq_iff_eq] at equal
                exact False.elim (nodup'.1 (by
                  simpa [equal] using List.mem_map.mpr ⟨d, hd, rfl⟩))
              · exact fresh d (.tail _ hd)
            have nextAligned := aligned.const (fresh info (.head _)) pair.2 step' rfl
            have pairs' : List.Forall₂
                (fun info type => info.name = type.name ∧
                  TrConstant safety next (.inductInfo info) type.toVConstant) infos types :=
              Lean4Lean.List.Forall₂.imp
                (fun _ _ h => ⟨h.1, h.2.mono (VEnv.addConst_le step')⟩) pairs
            have tailAligned := ih nextAligned pairs' freshTail nodup'.2 rest
            simpa [insertConsts, ConstantInfo.name, ConstantInfo.toConstantVal] using tailAligned
    have addConstructors : ∀ {infos : List ConstructorVal} {ctors : List VConstVal}
        {C : ConstMap} {env env' : VEnv},
        Aligned safety C env →
        List.Forall₂
          (fun info ctor => info.name = ctor.name ∧
            TrConstant safety env (.ctorInfo info) ctor.toVConstant) infos ctors →
        (∀ info ∈ infos, C.find? info.name = none) →
        (infos.map (·.name)).Nodup →
        env.addConstructorHeaders ctors = some env' →
        Aligned safety (insertConsts C (infos.map (.ctorInfo ·))) env' := by
      intro infos
      induction infos with
      | nil =>
        intro ctors C env env' aligned pairs fresh nodup added
        cases ctors with
        | nil =>
          cases pairs
          cases added
          simpa [insertConsts] using aligned
        | cons ctor ctors => cases pairs
      | cons info infos ih =>
        intro ctors C env env' aligned pairs fresh nodup added
        cases ctors with
        | nil => cases pairs
        | cons ctor ctors =>
          cases pairs with
          | cons pair pairs =>
            have nodup' := List.nodup_cons.mp nodup
            simp [VEnv.addConstructorHeaders, Option.bind_eq_some_iff] at added
            obtain ⟨next, step, rest⟩ := added
            have step' : env.addConst info.name ctor.toVConstant = some next := by
              rw [pair.1]
              exact step
            have freshTail : ∀ d ∈ infos,
                (C.insert info.name (.ctorInfo info)).find? d.name = none := by
              intro d hd
              rw [aligned.map_wf.find?_insert]
              split
              · rename_i equal
                simp only [beq_iff_eq] at equal
                exact False.elim (nodup'.1 (by
                  simpa [equal] using List.mem_map.mpr ⟨d, hd, rfl⟩))
              · exact fresh d (.tail _ hd)
            have nextAligned := aligned.const (fresh info (.head _)) pair.2 step' rfl
            have pairs' : List.Forall₂
                (fun info ctor => info.name = ctor.name ∧
                  TrConstant safety next (.ctorInfo info) ctor.toVConstant) infos ctors :=
              Lean4Lean.List.Forall₂.imp
                (fun _ _ h => ⟨h.1, h.2.mono (VEnv.addConst_le step')⟩) pairs
            have tailAligned := ih nextAligned pairs' freshTail nodup'.2 rest
            simpa [insertConsts, ConstantInfo.name, ConstantInfo.toConstantVal] using tailAligned
    have hheaders := addHeaders h hheaders headerFresh headerNodup headerAdd
    have hconstructors := addConstructors hheaders hconstructors constructorFresh
      constructorNodup constructorAdd
    rw [mapEq, insertConsts_append]
    exact hconstructors

theorem Aligned.addInduct (H : AddInduct C₁ venv₁ decl C₂ venv₂) :
    Aligned safety C₁ venv₁ → Aligned safety C₂ venv₂ := by
  cases H with
  | ofEvidence evidence =>
    exact Aligned.addInductEvidence (evidence.sf_mono DefinitionSafety.le_safe)

theorem Aligned.addInductWithRecursorsEvidence
    (H : AddInductWithRecursorsEvidence safety C₁ venv₁ decl inductiveConstants inductiveEnv
      recursors models C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  have hinductive := Aligned.addInductEvidence H.inductiveEvidence h
  have htranslations : List.Forall₂
      (fun info model => info.name = model.name ∧
        TrConstant safety inductiveEnv (.recInfo info) model.toVConstant)
      recursors models :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1⟩) H.translations
  have hfresh : ∀ info ∈ recursors, inductiveConstants.find? info.name = none := by
    intro info hmem
    obtain ⟨model, hmodel, htranslation⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l H.translations info hmem
    simpa [htranslation.1, ConstantInfo.name, ConstantInfo.toConstantVal] using
      H.recursorFresh model hmodel
  have hnodup : (recursors.map (·.name)).Nodup := by
    have hpair : List.Forall₂ Eq (recursors.map (·.name)) (models.map (·.name)) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp
        (fun (_ : RecursorVal) (_ : VConstVal) h => h.1) htranslations
    exact (List.forall₂_eq.mp hpair).symm ▸ H.recursorNodup
  have addRecursors : ∀ {infos : List RecursorVal} {ctors : List VConstVal}
      {C : ConstMap} {env env' : VEnv},
      Aligned safety C env →
      List.Forall₂
        (fun info ctor => info.name = ctor.name ∧
          TrConstant safety env (.recInfo info) ctor.toVConstant) infos ctors →
      (∀ info ∈ infos, C.find? info.name = none) →
      (infos.map (·.name)).Nodup →
      env.addConstructorHeaders ctors = some env' →
      Aligned safety (insertConsts C (infos.map (.recInfo ·))) env' := by
    intro infos
    induction infos with
    | nil =>
      intro ctors C env env' aligned pairs fresh nodup added
      cases ctors with
      | nil => cases pairs; cases added; simpa [insertConsts] using aligned
      | cons ctor ctors => cases pairs
    | cons info infos ih =>
      intro ctors C env env' aligned pairs fresh nodup added
      cases ctors with
      | nil => cases pairs
      | cons ctor ctors =>
        cases pairs with
        | cons pair pairs =>
          have nodup' := List.nodup_cons.mp nodup
          simp [VEnv.addConstructorHeaders, Option.bind_eq_some_iff] at added
          obtain ⟨next, step, rest⟩ := added
          have step' : env.addConst info.name ctor.toVConstant = some next := by
            rw [pair.1]
            exact step
          have freshTail : ∀ d ∈ infos,
              (C.insert info.name (.recInfo info)).find? d.name = none := by
            intro d hd
            rw [aligned.map_wf.find?_insert]
            split
            · rename_i equal
              simp only [beq_iff_eq] at equal
              exact False.elim (nodup'.1 (by
                simpa [equal] using List.mem_map.mpr ⟨d, hd, rfl⟩))
            · exact fresh d (.tail _ hd)
          have nextAligned := aligned.const (fresh info (.head _)) pair.2 step' rfl
          have pairs' : List.Forall₂
              (fun info ctor => info.name = ctor.name ∧
                TrConstant safety next (.recInfo info) ctor.toVConstant) infos ctors :=
            Lean4Lean.List.Forall₂.imp
              (fun _ _ h => ⟨h.1, h.2.mono (VEnv.addConst_le step')⟩) pairs
          have tailAligned := ih nextAligned pairs' freshTail nodup'.2 rest
          simpa [insertConsts, ConstantInfo.name, ConstantInfo.toConstantVal] using tailAligned
  rw [H.resultMap]
  exact addRecursors hinductive htranslations hfresh hnodup H.recursorAdd

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?_emptyStage] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?_emptyStage] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_le : ∀ {cis' : List VDefVal} {venv : VEnv}, venv ≤ venv.addDefEqs cis'
  | [], _ => .rfl
  | ci :: cis, venv => by
    show venv ≤ VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis
    exact VEnv.addDefEq_le.trans VEnv.addDefEqs_le

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?_emptyStage] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

private def InductiveFamilyInfo : ConstantInfo → Prop
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => True
  | _ => False

private def InductiveLookupsRejected (safety : DefinitionSafety) (constants : ConstMap) : Prop :=
  ∀ name information, constants.find? name = some information →
    InductiveFamilyInfo information → ¬safety ≤ information.safety

private theorem InductiveLookupsRejected.insert {constants : ConstMap} {information : ConstantInfo}
    (valid : constants.WF) (previous : InductiveLookupsRejected safety constants)
    (inserted : InductiveFamilyInfo information → ¬safety ≤ information.safety) :
    InductiveLookupsRejected safety (constants.insert name information) := by
  intro queried queriedInformation found family
  rw [valid.find?_insert] at found
  split at found
  · cases Option.some.inj found
    exact inserted family
  · exact previous queried queriedInformation found family

private theorem InductiveLookupsRejected.addQuot1 {result : Prop}
    (continuation : ∀ constants environment, constants.WF →
      InductiveLookupsRejected safety constants → property constants environment → result)
    (constants environment) (valid : constants.WF)
    (previous : InductiveLookupsRejected safety constants)
    (added : AddQuot1 name kind semantic property constants environment) : result := by
  obtain ⟨levels, type, nextEnvironment, translated, fresh, installed, remaining⟩ := added
  exact continuation _ _ (valid.insert _ _ fresh)
    (previous.insert valid (by intro impossible; cases impossible)) remaining

private theorem InductiveLookupsRejected.addQuot
    (added : AddQuot initial final initialEnvironment finalEnvironment)
    (valid : initial.WF) (previous : InductiveLookupsRejected safety initial) :
    InductiveLookupsRejected safety final := by
  dsimp [AddQuot] at added
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ valid previous added
  rintro _ _ _ rejected ⟨rfl, rfl⟩
  exact rejected

private theorem TrEnv'.inductiveFamilyLookupsRejected
    (valid : TrEnv' safety constants quotient environment) :
    InductiveLookupsRejected safety constants := by
  induction valid with
  | empty => intro _ _ impossible; simp [SMap.find?_emptyStage] at impossible
  | ignore _ ignored previous inductionHypothesis =>
    exact inductionHypothesis.insert previous.map_wf (fun _ => ignored)
  | «axiom» _ _ _ _ previous inductionHypothesis
  | defn _ _ _ _ previous inductionHypothesis
  | thm _ _ _ _ _ previous inductionHypothesis
  | «opaque» _ _ _ _ previous inductionHypothesis =>
    exact inductionHypothesis.insert previous.map_wf (by intro impossible; cases impossible)
  | mutualDef _ distinct fresh _ _ _ previous inductionHypothesis =>
    intro queried queriedInformation found family
    rcases insertDefs_find? previous.map_wf fresh distinct found with found | ⟨_, _, _, impossible⟩
    · exact inductionHypothesis queried queriedInformation found family
    · subst queriedInformation
      have impossible : False := by simpa [InductiveFamilyInfo] using family
      exact impossible.elim
  | quot _ added previous inductionHypothesis =>
    exact inductionHypothesis.addQuot added previous.map_wf

theorem TrEnv'.inductiveLookupRejected (valid : TrEnv' safety constants quotient environment)
    (found : constants.find? name = some (.inductInfo header)) :
    ¬safety ≤ (ConstantInfo.inductInfo header).safety :=
  valid.inductiveFamilyLookupsRejected name _ found trivial

theorem TrEnv'.recursorLookupRejected (valid : TrEnv' safety constants quotient environment)
    (found : constants.find? name = some (.recInfo header)) :
    ¬safety ≤ (ConstantInfo.recInfo header).safety :=
  valid.inductiveFamilyLookupsRejected name _ found trivial

theorem TrEnv'.constructorLookupRejected (valid : TrEnv' safety constants quotient environment)
    (found : constants.find? name = some (.ctorInfo header)) :
    ¬safety ≤ (ConstantInfo.ctorInfo header).safety :=
  valid.inductiveFamilyLookupsRejected name _ found trivial

theorem TrEnv.inductiveLookupRejected (valid : TrEnv safety native environment)
    (found : native.find? name = some (.inductInfo header)) :
    ¬safety ≤ (ConstantInfo.inductInfo header).safety :=
  TrEnv'.inductiveLookupRejected valid (name := name)
    (by rwa [← valid.map_wf.find?'_eq_find?])

theorem TrEnv.inductiveNotInModel (valid : TrEnv safety native environment)
    (found : native.find? name = some (.inductInfo header)) :
    ¬environment.contains name := by
  rintro ⟨semantic, translated⟩
  exact valid.inductiveLookupRejected found (valid.find?_uniq found translated).2.1

theorem TrEnv.recursorLookupRejected (valid : TrEnv safety native environment)
    (found : native.find? name = some (.recInfo header)) :
    ¬safety ≤ (ConstantInfo.recInfo header).safety :=
  TrEnv'.recursorLookupRejected valid (name := name)
    (by rwa [← valid.map_wf.find?'_eq_find?])

theorem TrEnv.recursorNotInModel (valid : TrEnv safety native environment)
    (found : native.find? name = some (.recInfo header)) :
    ¬environment.contains name := by
  rintro ⟨semantic, translated⟩
  exact valid.recursorLookupRejected found (valid.find?_uniq found translated).2.1

theorem TrEnv.constructorLookupRejected (valid : TrEnv safety native environment)
    (found : native.find? name = some (.ctorInfo header)) :
    ¬safety ≤ (ConstantInfo.ctorInfo header).safety :=
  TrEnv'.constructorLookupRejected valid (name := name)
    (by rwa [← valid.map_wf.find?'_eq_find?])

theorem TrEnv.constructorNotInModel (valid : TrEnv safety native environment)
    (found : native.find? name = some (.ctorInfo header)) :
    ¬environment.contains name := by
  rintro ⟨semantic, translated⟩
  exact valid.constructorLookupRejected found (valid.find?_uniq found translated).2.1

/-! A typechecker context may use a non-inductive optimization only when this
    rejection contract is available. Keeping it as a separate witness lets
    `TrEnv'` allow constructive inductive families without silently invalidating
    the optimizer proofs that still target the non-inductive fragment. -/
structure TrEnv.RejectsInductiveFamilies (valid : TrEnv safety native environment) : Prop where
  inductiveNotInModel : ∀ {name header},
    native.find? name = some (.inductInfo header) → ¬environment.contains name
  recursorNotInModel : ∀ {name header},
    native.find? name = some (.recInfo header) → ¬environment.contains name
  constructorNotInModel : ∀ {name header},
    native.find? name = some (.ctorInfo header) → ¬environment.contains name

theorem TrEnv.rejectsInductiveFamilies (valid : TrEnv safety native environment) :
    TrEnv.RejectsInductiveFamilies valid where
  inductiveNotInModel := valid.inductiveNotInModel
  recursorNotInModel := valid.recursorNotInModel
  constructorNotInModel := valid.constructorNotInModel

theorem AddInductWithRecursorsEvidence.sf_mono (hsf : safety ≤ safety')
    (H : AddInductWithRecursorsEvidence safety' m₁ env₁ decl inductiveConstants inductiveEnv
      recursors models m₂ env₂) :
    AddInductWithRecursorsEvidence safety m₁ env₁ decl inductiveConstants inductiveEnv
      recursors models m₂ env₂ := by
  cases H with
  | mk inductiveEvidence translations recursorAdd recursorNodup recursorFresh resultMap =>
    refine .mk (inductiveEvidence.sf_mono hsf) ?_ recursorAdd recursorNodup recursorFresh resultMap
    exact List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1.sf_mono hsf, h.2.2⟩) translations

/- The complete constructive receipt also proves well-formedness of the
   semantic environment after the generated recursor signatures are added.
   The staged declaration WF premise is kept explicit because the receipt
   records translations and insertion equations, while the recursor stage
   supplies the final `VEnv.WF` extension. -/
theorem AddInductWithRecursorsEvidence.result_wf
    (H : AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models C' env') (henv : env.WF)
    (hdecl : VDecl.WF env (.induct decl) inductiveEnv) : env'.WF := by
  have hinductive : inductiveEnv.WF :=
    VEnv.WF.decl henv hdecl
  exact VEnv.addConstructorHeaders.wf hinductive (by
    intro model hmem
    obtain ⟨info, hinfo, htranslation⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r H.translations model hmem
    exact htranslation.2.2) H.recursorAdd

/-! A staging relation for environments after a constructive inductive registration.

`TrEnv'` retains the non-inductive lookup-rejection contract used by the current
typechecker. This companion relation embeds that history and adds a complete
header/constructor/recursor registration in one explicit branch. -/
inductive TrEnvInductive (safety : DefinitionSafety) : ConstMap → Bool → VEnv → Prop where
  | legacy : TrEnv' safety C Q env → TrEnvInductive safety C Q env
  | induct :
    TrEnvInductive safety C Q env →
    VDecl.WF env (.induct decl) inductiveEnv →
    AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models resultConstants result →
    TrEnvInductive safety resultConstants Q result

theorem TrEnvInductive.wf (H : TrEnvInductive safety C Q venv) : venv.WF := by
  induction H with
  | legacy H => exact H.wf
  | induct previous hdecl evidence ih =>
    exact evidence.result_wf ih hdecl

theorem TrEnvInductive.aligned (H : TrEnvInductive safety C Q venv) :
    Aligned safety C venv := by
  induction H with
  | legacy H => exact H.aligned
  | induct _ _ evidence ih => exact Aligned.addInductWithRecursorsEvidence evidence ih

theorem TrEnvInductive.map_wf (H : TrEnvInductive safety C Q venv) : C.WF :=
  H.aligned.map_wf

theorem TrEnvInductive.find?_iff (H : TrEnvInductive safety C Q venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci :=
  H.aligned.find?_iff

theorem TrEnvInductive.find? (H : TrEnvInductive safety C Q venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? h hs

theorem TrEnvInductive.find?_uniq (H : TrEnvInductive safety C Q venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq h hs

/-! The constructive inductive receipt carries enough freshness information to
    establish the constant-map invariant directly.  This is useful at the
    migration boundary because it does not rely on the legacy `TrEnv'` branch
    or on the typechecker's family-rejection contract. -/
theorem AddInductEvidence.map_wf
    (H : AddInductEvidence safety C env decl C' env') (hC : C.WF) : C'.WF := by
  cases H with
  | @intro headers constructors headerEnv hheaders hconstructors headerAdd constructorAdd
      headerNodup constructorNodup headerFresh constructorFresh mapEq =>
    have headerFresh' : ∀ info ∈ headers.map (ConstantInfo.inductInfo ·),
        C.find? info.name = none := by
      intro info hinfo
      obtain ⟨header, hheader, rfl⟩ := List.mem_map.mp hinfo
      exact headerFresh header hheader
    have headerWF : (insertConsts C (headers.map (ConstantInfo.inductInfo ·))).WF := by
      apply insertConsts_wf hC headerFresh'
      have headerNames :
          (headers.map (ConstantInfo.inductInfo ·)).map (·.name) = headers.map (·.name) := by
        induction headers with
        | nil => rfl
        | cons header headers ih =>
          simp [ConstantInfo.name, ConstantInfo.toConstantVal]
      rw [headerNames]
      exact headerNodup
    have constructorFresh' : ∀ info ∈ constructors.map (ConstantInfo.ctorInfo ·),
        (insertConsts C (headers.map (ConstantInfo.inductInfo ·))).find? info.name = none := by
      intro info hinfo
      obtain ⟨constructor, hconstructor, rfl⟩ := List.mem_map.mp hinfo
      exact constructorFresh constructor hconstructor
    rw [mapEq, insertConsts_append]
    apply insertConsts_wf headerWF constructorFresh'
    have constructorNames :
        (constructors.map (ConstantInfo.ctorInfo ·)).map (·.name) = constructors.map (·.name) := by
      induction constructors with
      | nil => rfl
      | cons constructor constructors ih =>
        simp [ConstantInfo.name, ConstantInfo.toConstantVal]
    rw [constructorNames]
    exact constructorNodup

/- Exact map lookups for the constructive header and constructor receipt.  These
   are the positive counterparts of the legacy family-rejection lemmas and keep
   the inserted model value paired with the source metadata. -/
theorem AddInductEvidence.lookupReceipt
    (H : AddInductEvidence safety C env decl C' env') (hC : C.WF) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      List.Forall₂
        (fun info header => info.name = header.name ∧
          TrConstant safety env (.inductInfo info) header.toVConstant)
        headers decl.types ∧
      List.Forall₂
        (fun info ctor => info.name = ctor.name ∧
          TrConstant safety headerEnv (.ctorInfo info) ctor.toVConstant)
        constructors decl.constructorHeaders ∧
      (∀ info ∈ headers, C'.find? info.name = some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, C'.find? ctor.name = some (.ctorInfo ctor)) := by
  cases H with
  | @intro headers constructors headerEnv hheaders hconstructors headerAdd constructorAdd
      headerNodup constructorNodup headerFresh constructorFresh mapEq =>
    have headerMap : C'.find? =
        (insertConsts (insertConsts C (headers.map (ConstantInfo.inductInfo ·)))
          (constructors.map (ConstantInfo.ctorInfo ·))).find? := by
      rw [mapEq, insertConsts_append]
    have headerBase : (insertConsts C (headers.map (ConstantInfo.inductInfo ·))).WF := by
      apply insertConsts_wf
      · exact hC
      · intro ci hci
        obtain ⟨header, hheader, rfl⟩ := List.mem_map.mp hci
        exact headerFresh header hheader
      · simpa only [List.map_map, Function.comp_def, ConstantInfo.name,
          ConstantInfo.toConstantVal] using headerNodup
    have constructorFresh' : ∀ ci ∈ constructors.map (ConstantInfo.ctorInfo ·),
        (insertConsts C (headers.map (ConstantInfo.inductInfo ·))).find? ci.name = none := by
      intro ci hci
      obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hci
      exact constructorFresh ctor hctor
    refine ⟨headers, constructors, headerEnv, hheaders, hconstructors, ?_, ?_⟩
    · intro info hinfo
      rw [headerMap]
      have hheader :
          (insertConsts C (headers.map (ConstantInfo.inductInfo ·))).find?
            info.name = some (.inductInfo info) := by
        exact insertConsts_mem hC
          (fun ci hci => by
            obtain ⟨header, hheader, rfl⟩ := List.mem_map.mp hci
            exact headerFresh header hheader)
          (by simpa only [List.map_map, Function.comp_def, ConstantInfo.name,
            ConstantInfo.toConstantVal] using headerNodup)
          (List.mem_map.mpr ⟨info, hinfo, rfl⟩)
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using
        insertConsts_preserves_find? headerBase constructorFresh'
          (by simpa only [List.map_map, Function.comp_def, ConstantInfo.name,
            ConstantInfo.toConstantVal] using constructorNodup) hheader
    · intro ctor hctor
      rw [headerMap]
      exact insertConsts_mem headerBase constructorFresh'
        (by simpa only [List.map_map, Function.comp_def, ConstantInfo.name,
          ConstantInfo.toConstantVal] using constructorNodup)
        (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)

/- Legacy consumers can now use the constructive `AddInduct` boundary without
   unpacking its evidence constructor themselves. Generated recursor lookups
   remain on `AddInductWithRecursorsEvidence`. -/
theorem AddInduct.map_wf
    (H : AddInduct C env decl C' env') (hC : C.WF) : C'.WF := by
  cases H with
  | ofEvidence evidence => exact evidence.map_wf hC

theorem AddInduct.lookupReceipt
    (H : AddInduct C env decl C' env') (hC : C.WF) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      List.Forall₂
        (fun info header => info.name = header.name ∧
          TrConstant .safe env (.inductInfo info) header.toVConstant)
        headers decl.types ∧
      List.Forall₂
        (fun info ctor => info.name = ctor.name ∧
          TrConstant .safe headerEnv (.ctorInfo info) ctor.toVConstant)
        constructors decl.constructorHeaders ∧
      (∀ info ∈ headers, C'.find? info.name = some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, C'.find? ctor.name = some (.ctorInfo ctor)) := by
  cases H with
  | ofEvidence evidence => exact evidence.lookupReceipt hC

theorem AddInductWithRecursorsEvidence.map_wf
    (H : AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models C' env') (hC : C.WF) : C'.WF := by
  rw [H.resultMap]
  apply insertConsts_wf (H.inductiveEvidence.map_wf hC)
  · intro info hinfo
    obtain ⟨recursor, hrecursor, rfl⟩ := List.mem_map.mp hinfo
    obtain ⟨model, hmodel, htranslation⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l H.translations recursor hrecursor
    have hname : (ConstantInfo.recInfo recursor).name = model.name := by
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using htranslation.1
    rw [hname]
    exact H.recursorFresh model hmodel
  · have htranslations : List.Forall₂
        (fun info model => info.name = model.name) recursors models := by
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) H.translations
    have hpair : List.Forall₂ Eq (recursors.map (·.name)) (models.map (·.name)) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact htranslations
    have recursorNames :
        (recursors.map (fun info => ConstantInfo.recInfo info)).map (·.name) =
          recursors.map (·.name) := by
      induction recursors with
      | nil => rfl
      | cons info recursors ih =>
        simp [ConstantInfo.name, ConstantInfo.toConstantVal]
    rw [recursorNames]
    exact (List.forall₂_eq.mp hpair).symm ▸ H.recursorNodup

/- Exact lookups for generated recursor signatures after the constructive
   registration stage.  The `Forall₂` translation receipt supplies the name
   alignment between native recursor metadata and the stored model value. -/
theorem AddInductWithRecursorsEvidence.recursorLookup
    (H : AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models C' env') (hC : C.WF) :
    ∀ info ∈ recursors, C'.find? info.name = some (.recInfo info) := by
  intro info hinfo
  rw [H.resultMap]
  have hbase : inductiveConstants.WF := H.inductiveEvidence.map_wf hC
  have hfresh : ∀ ci ∈ recursors.map (ConstantInfo.recInfo ·),
      inductiveConstants.find? ci.name = none := by
    intro ci hci
    obtain ⟨recursor, hrecursor, rfl⟩ := List.mem_map.mp hci
    obtain ⟨model, hmodel, htranslation⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l H.translations recursor hrecursor
    have hname : (ConstantInfo.recInfo recursor).name = model.name := by
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using htranslation.1
    rw [hname]
    exact H.recursorFresh model hmodel
  have hnodup :
      (recursors.map (ConstantInfo.recInfo ·)).map (·.name) |>.Nodup := by
    have htranslations : List.Forall₂
        (fun recursor model => recursor.name = model.name) recursors models :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) H.translations
    have hpair : List.Forall₂ Eq (recursors.map (·.name)) (models.map (·.name)) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact htranslations
    have hnames :
        (recursors.map (ConstantInfo.recInfo ·)).map (·.name) = recursors.map (·.name) := by
      induction recursors with
      | nil => rfl
      | cons info recursors ih =>
        simp [ConstantInfo.name, ConstantInfo.toConstantVal]
    rw [hnames]
    exact (List.forall₂_eq.mp hpair).symm ▸ H.recursorNodup
  simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using
    insertConsts_mem hbase hfresh hnodup
      (List.mem_map.mpr ⟨info, hinfo, rfl⟩)

/- The complete staged receipt keeps the earlier header and constructor
   lookups available after generated recursors are inserted. -/
theorem AddInductWithRecursorsEvidence.lookupReceipt
    (H : AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models C' env') (hC : C.WF) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      List.Forall₂
        (fun info header => info.name = header.name ∧
          TrConstant safety env (.inductInfo info) header.toVConstant)
        headers decl.types ∧
      List.Forall₂
        (fun info ctor => info.name = ctor.name ∧
          TrConstant safety headerEnv (.ctorInfo info) ctor.toVConstant)
        constructors decl.constructorHeaders ∧
      (∀ info ∈ headers, C'.find? info.name = some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, C'.find? ctor.name = some (.ctorInfo ctor)) ∧
      (∀ info ∈ recursors, C'.find? info.name = some (.recInfo info)) := by
  obtain ⟨headers, constructors, headerEnv, hheaders, hconstructors,
      hheader, hconstructor⟩ := H.inductiveEvidence.lookupReceipt hC
  have hbase : inductiveConstants.WF := H.inductiveEvidence.map_wf hC
  have hfresh : ∀ ci ∈ recursors.map (ConstantInfo.recInfo ·),
      inductiveConstants.find? ci.name = none := by
    intro ci hci
    obtain ⟨recursor, hrecursor, rfl⟩ := List.mem_map.mp hci
    obtain ⟨model, hmodel, htranslation⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l H.translations recursor hrecursor
    have hname : (ConstantInfo.recInfo recursor).name = model.name := by
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using htranslation.1
    rw [hname]
    exact H.recursorFresh model hmodel
  have hnodup :
      (recursors.map (ConstantInfo.recInfo ·)).map (·.name) |>.Nodup := by
    have htranslations : List.Forall₂
        (fun recursor model => recursor.name = model.name) recursors models :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) H.translations
    have hpair : List.Forall₂ Eq (recursors.map (·.name)) (models.map (·.name)) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact htranslations
    have hnames :
        (recursors.map (ConstantInfo.recInfo ·)).map (·.name) = recursors.map (·.name) := by
      induction recursors with
      | nil => rfl
      | cons info recursors ih =>
        simp [ConstantInfo.name, ConstantInfo.toConstantVal]
    rw [hnames]
    exact (List.forall₂_eq.mp hpair).symm ▸ H.recursorNodup
  have hmap : C'.find? =
      (insertConsts inductiveConstants (recursors.map (ConstantInfo.recInfo ·))).find? := by
    rw [H.resultMap]
  refine ⟨headers, constructors, headerEnv, hheaders, hconstructors, ?_, ?_, ?_⟩
  · intro info hinfo
    rw [hmap]
    simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using
      insertConsts_preserves_find? hbase hfresh hnodup (hheader info hinfo)
  · intro ctor hctor
    rw [hmap]
    simpa only [ConstantInfo.name, ConstantInfo.toConstantVal] using
      insertConsts_preserves_find? hbase hfresh hnodup (hconstructor ctor hctor)
  · exact H.recursorLookup hC

theorem TrEnvInductive.env_find? {env : Environment}
    (H : TrEnvInductive safety env.constants Q venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have h' : env.constants.find? name = some ci := by
    rwa [← H.map_wf.find?'_eq_find?]
  exact H.find? h' hs

theorem TrEnvInductive.env_find?_uniq {env : Environment}
    (H : TrEnvInductive safety env.constants Q venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  have h' : env.constants.find? name = some ci := by
    rwa [← H.map_wf.find?'_eq_find?]
  exact H.find?_uniq h' hs

theorem TrEnv'.quotientObjects (valid : TrEnv' safety constants true environment) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] := by
  generalize quotientEq : true = quotient at valid
  induction valid with
  | empty => cases quotientEq
  | ignore _ _ _ inductionHypothesis => exact inductionHypothesis quotientEq
  | «axiom» _ _ _ added _ inductionHypothesis =>
    exact (inductionHypothesis quotientEq).mono (VEnv.addConst_le added)
  | defn _ _ _ added _ inductionHypothesis =>
    exact (inductionHypothesis quotientEq).mono
      ((VEnv.addConst_le added).trans VEnv.addDefEq_le)
  | mutualDef _ _ _ _ added _ _ inductionHypothesis =>
    exact (inductionHypothesis quotientEq).mono
      ((VEnv.addConsts_le added).trans VEnv.addDefEqs_le)
  | thm _ _ _ _ added _ inductionHypothesis =>
    exact (inductionHypothesis quotientEq).mono (VEnv.addConst_le added)
  | «opaque» _ _ _ added _ inductionHypothesis =>
    exact (inductionHypothesis quotientEq).mono (VEnv.addConst_le added)
  | quot _ added _ inductionHypothesis => exact VEnv.addQuot_objs added.to_addQuot

theorem TrEnv.quotientObjects (valid : TrEnv safety native environment)
    (initialized : native.quotInit = true) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] := by
  apply TrEnv'.quotientObjects
  simpa [TrEnv, initialized] using valid
