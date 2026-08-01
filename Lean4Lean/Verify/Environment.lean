import Lean4Lean.Environment
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

private theorem primitive_contains (n : Name) (h : n ∈ [
    ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
    ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
    ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble, ``Nat.bitwise, ``Nat.land,
    ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList,
    ``Char.ofNat]) : Environment.primitives.contains n := by
  apply Std.TreeSet.mem_iff_contains.mp
  simpa [Environment.primitives, NameSet.ofList] using h

theorem checkNoMVarNoFVar.WF (env : Environment) (n : Name) (e : Expr) :
    (Kernel.Environment.checkNoMVarNoFVar env n e).WF fun _ =>
      e.FVarsIn (fun _ => False) := by
  intro _ h
  cases hm : e.hasMVar <;> cases hf : e.hasFVar <;>
    simp only [Kernel.Environment.checkNoMVarNoFVar, Kernel.Environment.checkNoMVar,
      Kernel.Environment.checkNoFVar, hm, hf, Bool.false_eq_true,
      if_false, if_true, pure_bind, throw, throwThe, MonadExceptOf.throw] at h
  all_goals try
    change (Except.error _ : Except Exception Unit) = .ok _ at h
    cases h
  change FVarsIn (fun _ => False) e
  rw [fvarsIn_iff]
  exact ⟨by simp [fvarsList_eq_nil.2 hf], fvarsIn_iff_hasMVar.2 hm⟩

theorem checkName.WF (env : Environment) (n : Name) (allowPrimitive : Bool) :
    (Kernel.Environment.checkName env n allowPrimitive).WF fun _ =>
      env.constants.find? n = none ∧
        (allowPrimitive = false → Environment.primitives.contains n = false) := by
  intro _ h
  cases hc : env.constants.contains n <;>
    simp only [Kernel.Environment.checkName, Kernel.Environment.contains, hc,
      Bool.false_eq_true, if_false, if_true, pure_bind, throw, throwThe,
      MonadExceptOf.throw] at h
  all_goals try
    change (Except.error _ : Except Exception Unit) = .ok _ at h
    cases h
  constructor
  · apply Option.not_isSome_iff_eq_none.1
    rw [← SMap.find?_isSome, hc]
    decide
  · intro ha
    subst allowPrimitive
    cases hp : Environment.primitives.contains n
    · rfl
    · simp [hp] at h

theorem checkConstantVal.WF {ves : VEnvs} (wf : ves.WF env)
    (v : ConstantVal) (allowPrimitive : Bool) :
    (checkConstantVal env v allowPrimitive).WF
      (.mk' wf safety v.levelParams fuel) {} fun _ _ =>
        ∃ type', TrExprS (ves.venv safety) v.levelParams [] v.type type' ∧
          (VConstant.mk v.levelParams.length type').WF (ves.venv safety) ∧
          env.constants.find? v.name = none ∧
          (allowPrimitive = false → Environment.primitives.contains v.name = false) := by
  unfold checkConstantVal
  refine (M.WF.liftExcept (checkName.WF env v.name allowPrimitive)).bind
    fun _ _ _ hname => ?_
  refine (M.WF.liftExcept (show
    (Kernel.Environment.checkDuplicatedUnivParams v.levelParams).WF (fun _ => True) from
      fun _ _ => trivial)).bind
    fun _ _ _ _ => ?_
  refine (M.WF.liftExcept (checkNoMVarNoFVar.WF env v.name v.type)).bind
    fun _ _ _ hclosed => ?_
  refine (checkType.WF (hclosed.mono fun _ h => h.elim)).bind fun sort _ _ hsort => ?_
  let ⟨type', sort', _, htype, hsort', hty⟩ := hsort
  refine (ensureSort.WF hsort').bind fun _ _ _ ⟨⟨_, hsort, hdef⟩, hs⟩ => .pure ?_
  obtain ⟨_, rfl⟩ := hs
  let .sort hsort := hsort
  exact ⟨type', htype, ⟨_, hty.defeqU_r (VContext.mk' wf safety v.levelParams fuel).Ewf
    (VContext.mk' wf safety v.levelParams fuel).Δwf hdef.symm⟩, hname⟩

theorem checkDefinitionBody.WF {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hv : v.safety ≠ .unsafe) (allowPrimitive : Bool) :
    (do
      checkConstantVal env v.toConstantVal allowPrimitive
      Kernel.Environment.checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| Exception.declTypeMismatch env (.defnDecl v) valType).WF
      (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
        ∃ ci' : VDefVal, TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' ∧
          ci'.WF (ves.venv v.safety) ∧ env.constants.find? v.name = none ∧
          (allowPrimitive = false → Environment.primitives.contains v.name = false) := by
  refine (checkConstantVal.WF (ves := ves) wf v.toConstantVal allowPrimitive).bind
    fun _ _ _ ⟨type', htype, _, hfresh, hnprim⟩ => ?_
  refine (M.WF.liftExcept (checkNoMVarNoFVar.WF env v.name v.value)).bind
    fun _ _ _ hclosed => ?_
  refine (checkType.WF (hclosed.mono fun _ h => h.elim)).bind
    fun valType _ _ ⟨value', valType', _, hvalue, hvalType, hvalueTy⟩ => ?_
  refine (isDefEq.WF hvalType htype).bind fun b _ _ hdef => ?_
  cases b
  · exact .throw
  · apply M.WF.pure
    let ci' : VDefVal :=
      { name := v.name, uvars := v.levelParams.length, type := type', value := value' }
    have hle := wf.mono (safety := v.safety) (safety' := .safe) DefinitionSafety.le_safe
    refine ⟨ci', ?_, ?_, hfresh, hnprim⟩
    · refine ⟨⟨⟨?_, rfl, htype.mono hle⟩, rfl⟩, hvalue.mono hle⟩
      cases hs : v.safety <;> simp_all [ConstantInfo.safety,
        ConstantInfo.isUnsafe, ConstantInfo.isPartial]
    · exact (hvalueTy.defeqU_r (VContext.mk' wf .safe v.levelParams fuel).Ewf
        (VContext.mk' wf .safe v.levelParams fuel).Δwf (hdef rfl)).mono hle

theorem checkOpaqueBody.WF {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (do
      checkConstantVal env v.toConstantVal
      Kernel.Environment.checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| Exception.declTypeMismatch env (.opaqueDecl v) valType).WF
      (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
        ∃ ci' : VDefVal,
          let vsafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
          TrOpaqueVal vsafety (ves.venv vsafety) v ci' ∧
          ci'.WF (ves.venv vsafety) ∧ env.constants.find? v.name = none ∧
          Environment.primitives.contains v.name = false := by
  refine (checkConstantVal.WF (ves := ves) wf v.toConstantVal false).bind
    fun _ _ _ ⟨type', htype, _, hfresh, hnprim⟩ => ?_
  refine (M.WF.liftExcept (checkNoMVarNoFVar.WF env v.name v.value)).bind
    fun _ _ _ hclosed => ?_
  refine (checkType.WF (hclosed.mono fun _ h => h.elim)).bind
    fun valType _ _ ⟨value', valType', _, hvalue, hvalType, hvalueTy⟩ => ?_
  refine (isDefEq.WF hvalType htype).bind fun b _ _ hdef => ?_
  cases b
  · exact .throw
  · apply M.WF.pure
    let vsafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
    let ci' : VDefVal :=
      { name := v.name, uvars := v.levelParams.length, type := type', value := value' }
    have hle := wf.mono (safety := vsafety) (safety' := .safe) DefinitionSafety.le_safe
    refine ⟨ci', ?_, ?_, hfresh, hnprim rfl⟩
    · exact ⟨⟨⟨DefinitionSafety.le_rfl, rfl, htype.mono hle⟩, rfl⟩,
        hvalue.mono hle⟩
    · exact (hvalueTy.defeqU_r (VContext.mk' wf .safe v.levelParams fuel).Ewf
        (VContext.mk' wf .safe v.levelParams fuel).Δwf (hdef rfl)).mono hle

theorem checkTheoremBody.WF {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (do
      checkConstantVal env v.toConstantVal
      if !(← isProp v.type) then
        throw <| Exception.thmTypeIsNotProp env v.name v.type
      Kernel.Environment.checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| Exception.declTypeMismatch env (.thmDecl v) valType).WF
      (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
        ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.thmInfo v) ci' ∧
          ci'.WF (ves.venv .safe) ∧ env.constants.find? v.name = none ∧
          Environment.primitives.contains v.name = false := by
  refine (checkConstantVal.WF (ves := ves) wf v.toConstantVal false).bind
    fun _ _ _ ⟨type', htype, _, hfresh, hnprim⟩ => ?_
  refine (isProp.WF htype).bind fun b _ _ _ => ?_
  cases b
  · exact .throw
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
    refine (M.WF.liftExcept (checkNoMVarNoFVar.WF env v.name v.value)).bind
      fun _ _ _ hclosed => ?_
    refine (checkType.WF (hclosed.mono fun _ h => h.elim)).bind
      fun valType _ _ ⟨value', valType', _, hvalue, hvalType, hvalueTy⟩ => ?_
    refine (isDefEq.WF hvalType htype).bind fun b _ _ hdef => ?_
    cases b
    · exact .throw
    · apply M.WF.pure
      let ci' : VDefVal :=
        { name := v.name, uvars := v.levelParams.length, type := type', value := value' }
      refine ⟨ci', ?_, ?_, hfresh, hnprim rfl⟩
      · exact ⟨⟨⟨DefinitionSafety.le_rfl, rfl, htype⟩, rfl⟩, hvalue⟩
      · exact hvalueTy.defeqU_r (VContext.mk' wf .safe v.levelParams fuel).Ewf
          (VContext.mk' wf .safe v.levelParams fuel).Δwf (hdef rfl)

theorem VEnv.addConst_constants {env env' : VEnv} {n m : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') (hne : n ≠ m) :
    env'.constants m = env.constants m := by
  simp [VEnv.addConst] at h
  split at h <;> cases h
  simp [hne]

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv} (hle : env₁ ≤ env₂)
    (h₁ : env₁.addConst n ci = some env₁') (h₂ : env₂.addConst n ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  constructor
  · intro m a hm
    by_cases hnm : n = m
    · simp [hnm] at hm ⊢
      exact hm
    · simp [hnm] at hm ⊢
      exact hle.constants hm
  · exact hle.defeqs

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} {df : VDefEq} (hle : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df := by
  constructor
  · exact hle.constants
  · intro df' h
    rcases h with rfl | h
    · exact VEnv.addDefEq_self
    · exact VEnv.addDefEq_le.defeqs (hle.defeqs h)

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} {n : Name} {ci : VConstant}
    (hp : env.HasPrimitives)
    (hadd : env.addConst n ci = some env')
    (hn : Environment.primitives.contains n = false) : env'.HasPrimitives := by
  have hle := VEnv.addConst_le hadd
  have hconst (m : Name) (hm : Environment.primitives.contains m) :
      env'.constants m = env.constants m := by
    apply VEnv.addConst_constants hadd
    rintro rfl
    simp [hn] at hm
  have hcontains (m : Name) (hm : Environment.primitives.contains m) :
      env'.contains m ↔ env.contains m := by
    simp only [VEnv.contains]
    rw [hconst m hm]
  refine {
    bool := fun h => by
      have ⟨hf, ht⟩ := hp.bool ((hcontains ``Bool (primitive_contains _ (by simp))).1 h)
      exact ⟨(hcontains ``Bool.false (primitive_contains _ (by simp))).2 hf,
        (hcontains ``Bool.true (primitive_contains _ (by simp))).2 ht⟩
    boolFalse := fun h => hp.boolFalse
      (hconst ``Bool.false (primitive_contains _ (by simp)) ▸ h)
    boolTrue := fun h => hp.boolTrue
      (hconst ``Bool.true (primitive_contains _ (by simp)) ▸ h)
    nat := fun h => by
      have ⟨hz, hs⟩ := hp.nat ((hcontains ``Nat (primitive_contains _ (by simp))).1 h)
      exact ⟨(hcontains ``Nat.zero (primitive_contains _ (by simp))).2 hz,
        (hcontains ``Nat.succ (primitive_contains _ (by simp))).2 hs⟩
    natZero := fun h => hp.natZero
      (hconst ``Nat.zero (primitive_contains _ (by simp)) ▸ h)
    natSucc := fun h => hp.natSucc
      (hconst ``Nat.succ (primitive_contains _ (by simp)) ▸ h)
    natAdd := fun h a b =>
      (hp.natAdd ((hcontains ``Nat.add (primitive_contains _ (by simp))).1 h) a b).mono hle
    natSub := fun h a b =>
      (hp.natSub ((hcontains ``Nat.sub (primitive_contains _ (by simp))).1 h) a b).mono hle
    natMul := fun h a b =>
      (hp.natMul ((hcontains ``Nat.mul (primitive_contains _ (by simp))).1 h) a b).mono hle
    natPow := fun h a b =>
      (hp.natPow ((hcontains ``Nat.pow (primitive_contains _ (by simp))).1 h) a b).mono hle
    natGcd := fun h a b =>
      (hp.natGcd ((hcontains ``Nat.gcd (primitive_contains _ (by simp))).1 h) a b).mono hle
    natMod := fun h a b =>
      (hp.natMod ((hcontains ``Nat.mod (primitive_contains _ (by simp))).1 h) a b).mono hle
    natDiv := fun h a b =>
      (hp.natDiv ((hcontains ``Nat.div (primitive_contains _ (by simp))).1 h) a b).mono hle
    natBEq := fun h a b =>
      (hp.natBEq ((hcontains ``Nat.beq (primitive_contains _ (by simp))).1 h) a b).mono hle
    natBLE := fun h a b =>
      (hp.natBLE ((hcontains ``Nat.ble (primitive_contains _ (by simp))).1 h) a b).mono hle
    natLAnd := fun h a b =>
      (hp.natLAnd ((hcontains ``Nat.land (primitive_contains _ (by simp))).1 h) a b).mono hle
    natLOr := fun h a b =>
      (hp.natLOr ((hcontains ``Nat.lor (primitive_contains _ (by simp))).1 h) a b).mono hle
    natXor := fun h a b =>
      (hp.natXor ((hcontains ``Nat.xor (primitive_contains _ (by simp))).1 h) a b).mono hle
    natShiftLeft := fun h a b => (hp.natShiftLeft
      ((hcontains ``Nat.shiftLeft (primitive_contains _ (by simp))).1 h) a b).mono hle
    natShiftRight := fun h a b => (hp.natShiftRight
      ((hcontains ``Nat.shiftRight (primitive_contains _ (by simp))).1 h) a b).mono hle
    charOfNat := fun h => hp.charOfNat
      (hconst ``Char.ofNat (primitive_contains _ (by simp)) ▸ h)
    stringOfList := fun h =>
      let ⟨h₁, h₂, h₃⟩ := hp.stringOfList
        (hconst ``String.ofList (primitive_contains _ (by simp)) ▸ h)
      ⟨h₁, h₂.mono hle, h₃.mono hle⟩ }

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} {df : VDefEq} (hp : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives := by
  refine {
    bool := hp.bool
    boolFalse := hp.boolFalse
    boolTrue := hp.boolTrue
    nat := hp.nat
    natZero := hp.natZero
    natSucc := hp.natSucc
    natAdd := fun h a b => (hp.natAdd h a b).mono VEnv.addDefEq_le
    natSub := fun h a b => (hp.natSub h a b).mono VEnv.addDefEq_le
    natMul := fun h a b => (hp.natMul h a b).mono VEnv.addDefEq_le
    natPow := fun h a b => (hp.natPow h a b).mono VEnv.addDefEq_le
    natGcd := fun h a b => (hp.natGcd h a b).mono VEnv.addDefEq_le
    natMod := fun h a b => (hp.natMod h a b).mono VEnv.addDefEq_le
    natDiv := fun h a b => (hp.natDiv h a b).mono VEnv.addDefEq_le
    natBEq := fun h a b => (hp.natBEq h a b).mono VEnv.addDefEq_le
    natBLE := fun h a b => (hp.natBLE h a b).mono VEnv.addDefEq_le
    natLAnd := fun h a b => (hp.natLAnd h a b).mono VEnv.addDefEq_le
    natLOr := fun h a b => (hp.natLOr h a b).mono VEnv.addDefEq_le
    natXor := fun h a b => (hp.natXor h a b).mono VEnv.addDefEq_le
    natShiftLeft := fun h a b => (hp.natShiftLeft h a b).mono VEnv.addDefEq_le
    natShiftRight := fun h a b => (hp.natShiftRight h a b).mono VEnv.addDefEq_le
    charOfNat := hp.charOfNat
    stringOfList := fun h =>
      let ⟨h₁, h₂, h₃⟩ := hp.stringOfList h
      ⟨h₁, h₂.mono VEnv.addDefEq_le, h₃.mono VEnv.addDefEq_le⟩ }

open private Lean.Kernel.Environment.add from Lean.Environment

private def VEnv.insertConst (env : VEnv) (n : Name) (ci : VConstant) : VEnv :=
  { env with constants := fun m => if n = m then some ci else env.constants m }

private theorem VEnv.addConst_insert {env : VEnv} {n : Name} {ci : VConstant}
    (h : env.constants n = none) :
    env.addConst n ci = some (env.insertConst n ci) := by
  simp [VEnv.addConst, h, VEnv.insertConst]

private def VEnv.insertDefConst (env : VEnv) (ci : VDefVal) : VEnv :=
  { env with constants := fun m =>
    if ci.name = m then some ci.toVConstant else env.constants m }

private theorem VEnv.addConst_insertDef {env : VEnv} {ci : VDefVal}
    (h : env.constants ci.name = none) :
    env.addConst ci.name ci.toVConstant = some (env.insertDefConst ci) := by
  simp [VEnv.addConst, h, VEnv.insertDefConst]

theorem TrEnv.constants_eq_none (H : TrEnv safety env venv)
    (h : env.constants.find? n = none) : venv.constants n = none := by
  apply Option.not_isSome_iff_eq_none.1
  rw [Option.isSome_iff_exists]
  rintro ⟨ci, hci⟩
  obtain ⟨ci', hci', _⟩ := H.aligned.find?_iff.2 ⟨ci, hci⟩
  rw [h] at hci'
  contradiction

theorem addAxiom.WF {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal)
    (fuel : FuelConfig := {}) :
    (addAxiom env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addAxiom
  simp only [if_true, pure_bind]
  let vsafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  refine (M.WF.run wf (checkConstantVal.WF (ves := ves) wf v.toConstantVal false
    (safety := vsafety) (fuel := fuel))).bind fun _ ⟨vty, htr, hvwf, hfresh, hnprim⟩ => ?_
  apply Except.WF.pure
  let vci : VConstant := ⟨v.levelParams.length, vty⟩
  have hvwf' : vci.WF (ves.venv vsafety) := hvwf
  have htr' : TrConstant vsafety (ves.venv vsafety) (.axiomInfo v) vci :=
    ⟨DefinitionSafety.le_rfl, rfl, htr⟩
  have hvnone (safety) : (ves.venv safety).constants v.name = none :=
    (wf.tr).constants_eq_none hfresh
  let ves' : VEnvs := ⟨fun safety =>
    if safety ≤ vsafety then (ves.venv safety).insertConst v.name vci else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := by
        intro safety
        simp only [ves']
        split
        · rename_i hs
          apply TrEnv'.axiom
          · exact (htr'.sf_mono hs).mono (wf.mono hs)
          · exact hfresh
          · exact hvwf'.mono (wf.mono hs)
          · exact (ves.venv _).addConst_insert (hvnone _)
          · exact wf.tr
        · rename_i hs
          exact TrEnv'.ignoreConst hfresh hs wf.tr
      hasPrimitives := by
        intro safety
        simp only [ves']
        split
        · exact wf.hasPrimitives.addConst
            ((ves.venv safety).addConst_insert (hvnone safety)) (hnprim rfl)
        · exact wf.hasPrimitives
      safePrimitives := by
        intro n ci hfind hp
        have hmap := (wf.tr (safety := .safe)).map_wf
        change (env.constants.insert v.name (.axiomInfo v)).find?' n = some ci at hfind
        rw [(hmap.insert _ _ hfresh).find?'_eq_find?, hmap.find?_insert] at hfind
        split at hfind
        · rename_i hn
          cases hfind
          have : v.name = n := LawfulBEq.eq_of_beq hn
          subst n
          simp [hnprim rfl] at hp
        · apply wf.safePrimitives _ hp
          change env.constants.find?' n = some ci
          rwa [hmap.find?'_eq_find?]
      mono := by
        intro safety safety' hle
        by_cases hs' : safety' ≤ vsafety
        · have hs : safety ≤ vsafety := DefinitionSafety.le_trans hle hs'
          simp only [ves', if_pos hs', if_pos hs]
          exact VEnv.addConst_mono (wf.mono hle)
            ((ves.venv safety').addConst_insert (hvnone safety'))
            ((ves.venv safety).addConst_insert (hvnone safety))
        · by_cases hs : safety ≤ vsafety
          · simp only [ves', if_neg hs', if_pos hs]
            exact (wf.mono hle).trans <|
              VEnv.addConst_le ((ves.venv safety).addConst_insert (hvnone safety))
          · simp only [ves', if_neg hs', if_neg hs]
            exact wf.mono hle }
  · intro safety
    simp only [ves']
    split
    · exact VEnv.addConst_le ((ves.venv safety).addConst_insert (hvnone safety))
    · exact .rfl

theorem addDefinition.WF_nonprimitive {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hv : v.safety ≠ .unsafe)
    (hn : Environment.primitives.contains v.name = false) (fuel : FuelConfig := {}) :
    (addDefinition env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hs : v.safety
  · exact (hv hs).elim
  all_goals
    unfold addDefinition
    simp only [hs, pure_bind, if_false, if_true, hn, Bool.false_eq_true]
    refine (M.WF.run wf (checkDefinitionBody.WF (ves := ves) wf v hv false
      (fuel := fuel))).bind fun _ ⟨ci', htr, hciwf, hfresh, _⟩ => ?_
    apply Except.WF.pure
    have hvnone (safety) : (ves.venv safety).constants v.name = none :=
      (wf.tr).constants_eq_none hfresh
    have hname := htr.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    have hvnone' (safety) : (ves.venv safety).constants ci'.name = none :=
      hname ▸ hvnone safety
    have hn' : Environment.primitives.contains ci'.name = false := hname ▸ hn
    have hcisafety : (ConstantInfo.defnInfo v).safety = v.safety := by
      cases hsafety : v.safety <;> simp [ConstantInfo.safety,
        ConstantInfo.isUnsafe, ConstantInfo.isPartial, hsafety]
    let ves' : VEnvs := ⟨fun safety => if safety ≤ v.safety then
      ((ves.venv safety).insertDefConst ci').addDefEq ci'.toDefEq else ves.venv safety⟩
    refine ⟨ves', ?_, ?_⟩
    · refine {
        tr := by
          intro safety
          simp only [ves']
          split
          · rename_i hsafety
            apply TrEnv'.defn
            · exact (htr.sf_mono hsafety).mono (wf.mono hsafety)
            · exact hfresh
            · exact hciwf.mono (wf.mono hsafety)
            · simpa [hname] using (ves.venv _).addConst_insertDef (hvnone' _)
            · exact wf.tr
          · rename_i hsafety
            exact TrEnv'.ignoreConst hfresh (hcisafety ▸ hsafety) wf.tr
        hasPrimitives := by
          intro safety
          simp only [ves']
          split
          · exact (wf.hasPrimitives.addConst
              ((ves.venv safety).addConst_insertDef (hvnone' safety)) hn').addDefEq
          · exact wf.hasPrimitives
        safePrimitives := by
          intro n ci hfind hp
          have hmap := (wf.tr (safety := .safe)).map_wf
          change (env.constants.insert v.name (.defnInfo v)).find?' n = some ci at hfind
          rw [(hmap.insert _ _ hfresh).find?'_eq_find?, hmap.find?_insert] at hfind
          split at hfind
          · rename_i hname'
            cases hfind
            have : v.name = n := LawfulBEq.eq_of_beq hname'
            subst n
            simp [hn] at hp
          · apply wf.safePrimitives _ hp
            change env.constants.find?' n = some ci
            rwa [hmap.find?'_eq_find?]
        mono := by
          intro safety safety' hle
          by_cases hs' : safety' ≤ v.safety
          · have hsafety : safety ≤ v.safety := DefinitionSafety.le_trans hle hs'
            simp only [ves', if_pos hs', if_pos hsafety]
            exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hle)
              ((ves.venv safety').addConst_insertDef (hvnone' safety'))
              ((ves.venv safety).addConst_insertDef (hvnone' safety))
          · by_cases hsafety : safety ≤ v.safety
            · simp only [ves', if_neg hs', if_pos hsafety]
              exact ((wf.mono hle).trans <| VEnv.addConst_le
                ((ves.venv safety).addConst_insertDef (hvnone' safety))).trans
                VEnv.addDefEq_le
            · simp only [ves', if_neg hs', if_neg hsafety]
              exact wf.mono hle }
    · intro safety
      simp only [ves']
      split
      · exact (VEnv.addConst_le
          ((ves.venv safety).addConst_insertDef (hvnone' safety))).trans VEnv.addDefEq_le
      · exact .rfl

theorem addOpaque.WF {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal)
    (fuel : FuelConfig := {}) :
    (addOpaque env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addOpaque
  simp only [if_true, pure_bind]
  let vsafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  refine (M.WF.run wf (checkOpaqueBody.WF (ves := ves) wf v
    (fuel := fuel))).bind fun _ ⟨ci', htr, hciwf, hfresh, hnprim⟩ => ?_
  apply Except.WF.pure
  have hvnone (safety) : (ves.venv safety).constants v.name = none :=
    (wf.tr).constants_eq_none hfresh
  let ves' : VEnvs := ⟨fun safety => if safety ≤ vsafety then
    (ves.venv safety).insertConst v.name ci'.toVConstant else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := by
        intro safety
        simp only [ves']
        split
        · rename_i hsafety
          apply TrEnv'.opaque
          · exact (htr.sf_mono hsafety).mono (wf.mono hsafety)
          · exact hfresh
          · exact hciwf.mono (wf.mono hsafety)
          · exact (ves.venv _).addConst_insert (hvnone _)
          · exact wf.tr
        · rename_i hsafety
          exact TrEnv'.ignoreConst hfresh hsafety wf.tr
      hasPrimitives := by
        intro safety
        simp only [ves']
        split
        · exact wf.hasPrimitives.addConst
            ((ves.venv safety).addConst_insert (hvnone safety)) hnprim
        · exact wf.hasPrimitives
      safePrimitives := by
        intro n ci hfind hp
        have hmap := (wf.tr (safety := .safe)).map_wf
        change (env.constants.insert v.name (.opaqueInfo v)).find?' n = some ci at hfind
        rw [(hmap.insert _ _ hfresh).find?'_eq_find?, hmap.find?_insert] at hfind
        split at hfind
        · rename_i hname
          cases hfind
          have : v.name = n := LawfulBEq.eq_of_beq hname
          subst n
          simp [hnprim] at hp
        · apply wf.safePrimitives _ hp
          change env.constants.find?' n = some ci
          rwa [hmap.find?'_eq_find?]
      mono := by
        intro safety safety' hle
        by_cases hs' : safety' ≤ vsafety
        · have hsafety : safety ≤ vsafety := DefinitionSafety.le_trans hle hs'
          simp only [ves', if_pos hs', if_pos hsafety]
          exact VEnv.addConst_mono (wf.mono hle)
            ((ves.venv safety').addConst_insert (hvnone safety'))
            ((ves.venv safety).addConst_insert (hvnone safety))
        · by_cases hsafety : safety ≤ vsafety
          · simp only [ves', if_neg hs', if_pos hsafety]
            exact (wf.mono hle).trans <| VEnv.addConst_le
              ((ves.venv safety).addConst_insert (hvnone safety))
          · simp only [ves', if_neg hs', if_neg hsafety]
            exact wf.mono hle }
  · intro safety
    simp only [ves']
    split
    · exact VEnv.addConst_le ((ves.venv safety).addConst_insert (hvnone safety))
    · exact .rfl

theorem addTheorem.WF {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal)
    (fuel : FuelConfig := {}) :
    (addTheorem env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addTheorem
  simp only [if_true, pure_bind]
  refine (M.WF.run wf (checkTheoremBody.WF (ves := ves) wf v
    (fuel := fuel))).bind fun _ ⟨ci', htr, hciwf, hfresh, hnprim⟩ => ?_
  apply Except.WF.pure
  have hvnone (safety) : (ves.venv safety).constants v.name = none :=
    (wf.tr).constants_eq_none hfresh
  have hname := htr.1.2
  dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
  have hvnone' (safety) : (ves.venv safety).constants ci'.name = none :=
    hname ▸ hvnone safety
  have hn' : Environment.primitives.contains ci'.name = false := hname ▸ hnprim
  let ves' : VEnvs := ⟨fun safety =>
    ((ves.venv safety).insertDefConst ci').addDefEq ci'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := by
        intro safety
        simp only [ves']
        apply TrEnv'.thm
        · exact (htr.sf_mono (DefinitionSafety.le_safe (a := safety))).mono
            (wf.mono (safety := safety) (safety' := .safe) DefinitionSafety.le_safe)
        · exact hfresh
        · exact hciwf.mono
            (wf.mono (safety := safety) (safety' := .safe) DefinitionSafety.le_safe)
        · simpa [hname] using (ves.venv _).addConst_insertDef (hvnone' _)
        · exact wf.tr
      hasPrimitives := by
        intro safety
        exact (wf.hasPrimitives.addConst
          ((ves.venv safety).addConst_insertDef (hvnone' safety)) hn').addDefEq
      safePrimitives := by
        intro n ci hfind hp
        have hmap := (wf.tr (safety := .safe)).map_wf
        change (env.constants.insert v.name (.thmInfo v)).find?' n = some ci at hfind
        rw [(hmap.insert _ _ hfresh).find?'_eq_find?, hmap.find?_insert] at hfind
        split at hfind
        · rename_i hname'
          cases hfind
          have : v.name = n := LawfulBEq.eq_of_beq hname'
          subst n
          simp [hnprim] at hp
        · apply wf.safePrimitives _ hp
          change env.constants.find?' n = some ci
          rwa [hmap.find?'_eq_find?]
      mono := by
        intro safety safety' hle
        exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hle)
          ((ves.venv safety').addConst_insertDef (hvnone' safety'))
          ((ves.venv safety).addConst_insertDef (hvnone' safety)) }
  · intro safety
    exact (VEnv.addConst_le
      ((ves.venv safety).addConst_insertDef (hvnone' safety))).trans VEnv.addDefEq_le

/-- The intended main theorem of the `Verify` development, currently unproved:
if `env` is well-formed and `addDecl env decl` (in checking mode) succeeds,
then the resulting environment is also well-formed, and it extends `env`.

None of the pieces of this theorem exist yet: nothing relates
`Lean.Kernel.Environment.add` to the `TrEnv` relation, and nothing repackages
the `checkType.WF`/`isDefEq.WF` postconditions at the empty local context into
the abstract `VDecl.WF` premises needed to extend `TrEnv`. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration) :
    (addDecl env decl).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  sorry

end Lean4Lean
