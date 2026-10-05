import Lean4Lean.Environment
import Lean4Lean.Verify.Primitive

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker
open private eqReady? eqTypeExpr quotTypeExpr quotMkTypeExpr quotLiftTypeExpr
  quotIndTypeExpr from Lean4Lean.Quot

def VEnvs.empty : VEnvs := ⟨fun _ => ∅⟩

theorem VEnvs.WF.empty (mainModule : Name) (trustLevel : UInt32 := 0) :
    VEnvs.empty.WF (Environment.empty mainModule trustLevel) := by
  refine {
    tr := .empty
    hasPrimitives := ?_
    safePrimitives := ?_
    mono := fun _ => .rfl }
  · intro safety
    change VEnv.HasPrimitives VEnv.empty
    constructor <;> simp [VEnv.empty, VEnv.contains, VEnv.ReflectsNatNatNat]
  · intro n ci h _
    change ({} : ConstMap).find?' n = some ci at h
    rw [SMap.WF.empty.find?'_eq_find?] at h
    simp [SMap.find?] at h

private def trExprResult (Us : List Name) (Δ : VLCtx) : Expr → Option VExpr
  | .bvar i => (Δ.find? (.inl i)).map fun x => x.1
  | .sort u => (VLevel.ofLevel Us u).map VExpr.sort
  | .const c us => (us.mapM (VLevel.ofLevel Us)).map (VExpr.const c)
  | .app f a => return .app (← trExprResult Us Δ f) (← trExprResult Us Δ a)
  | .forallE _ ty body _ => do
    let ty' ← trExprResult Us Δ ty
    return .forallE ty' (← trExprResult Us ((none, .vlam ty') :: Δ) body)
  | .mdata _ e => trExprResult Us Δ e
  | _ => none

private theorem TrExprS.eq_trExprResult (H : TrExprS env Us Δ e e')
    (hr : trExprResult Us Δ e = some r) : e' = r := by
  induction H generalizing r with
  | bvar h => simp [trExprResult, h] at hr; exact hr
  | fvar => simp [trExprResult] at hr
  | sort h => simp [trExprResult, h] at hr; exact hr
  | const _ hm _ => simp [trExprResult, hm] at hr; exact hr
  | app _ _ _ _ ihf iha =>
    simp [trExprResult] at hr
    rcases hr with ⟨rf, hf, ra, ha, rfl⟩
    rw [ihf hf, iha ha]
  | forallE _ _ _ _ iht ihb =>
    simp [trExprResult] at hr
    rcases hr with ⟨rt, ht, rb, hb, rfl⟩
    have := iht ht
    subst rt
    rw [ihb hb]
  | mdata _ ih => exact ih hr
  | lam | letE | lit | proj => simp [trExprResult] at hr

private theorem trEqType_eq
    (h : TrExprS env [u] [] (eqTypeExpr u) e) : e = eqConst.type :=
  h.eq_trExprResult (by
    simp [trExprResult, eqTypeExpr, eqConst, Lean.Expr.prop, VLevel.ofLevel, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, VExpr.liftN, liftVar])

private theorem trQuotType_eq
    (h : TrExprS env [`u] [] quotTypeExpr e) : e = quotConst.type :=
  h.eq_trExprResult rfl

private theorem trQuotMkType_eq
    (h : TrExprS env [`u] [] quotMkTypeExpr e) : e = quotMkConst.type :=
  h.eq_trExprResult rfl

private theorem trQuotLiftType_eq
    (h : TrExprS env [`u, `v] [] quotLiftTypeExpr e) : e = quotLiftConst.type :=
  h.eq_trExprResult rfl

private theorem trQuotIndType_eq
    (h : TrExprS env [`u] [] quotIndTypeExpr e) : e = quotIndConst.type :=
  h.eq_trExprResult rfl

private theorem primitive_contains (n : Name) (h : n ∈ [
    ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
    ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
    ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble, ``Nat.bitwise, ``Nat.land,
    ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList,
    ``Char.ofNat]) : Environment.primitives.contains n := by
  apply Std.TreeSet.mem_iff_contains.mp
  simpa [Environment.primitives, NameSet.ofList] using h

private theorem not_reduction_primitive
    (hn : Environment.primitives.contains n = false) : n ∉ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
      ``Char.ofNat, ``String.ofList, ``Nat.add] := by
  intro h
  have : Environment.primitives.contains n := primitive_contains n <| by
    simp only [List.mem_cons] at h ⊢
    grind
  simp [hn] at this

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

theorem checkEqType.WF {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady := by
  intro _ h
  have hready : eqReady? env := by
    cases hr : eqReady? env
    · simp [checkEqType, hr] at h
    · rfl
  have hex : ∃ u info,
      env.find? ``Eq = some (.inductInfo info) ∧
      info.levelParams = [u] ∧ info.isUnsafe = false ∧ info.type == eqTypeExpr u := by
    unfold eqReady? at hready
    repeat first | split at hready | simp_all
  obtain ⟨u, info, hfind, hparams, hsafe, htype⟩ := hex
  intro safety
  have hcisafe : (ConstantInfo.inductInfo info).safety = .safe := by
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hsafe]
  obtain ⟨ci, hci, htr⟩ := (wf.tr (safety := safety)).find? hfind
    (hcisafe ▸ DefinitionSafety.le_safe)
  have htreq := htr.2.2.eqv htype
  change TrExprS (ves.venv safety) info.levelParams [] (eqTypeExpr u) ci.type at htreq
  rw [hparams] at htreq
  have htype' : ci.type = eqConst.type := trEqType_eq htreq
  have huvars : ci.uvars = 1 := by
    have huv := htr.2.1
    change info.levelParams.length = ci.uvars at huv
    simpa [hparams] using huv.symm
  show (ves.venv safety).constants ``Eq = some eqConst
  rw [hci]
  cases ci
  simp_all [eqConst]

theorem checkPrimitiveHeader.WF (v : DefinitionVal) :
    (checkPrimitiveHeader v).WF fun _ =>
      v.safety = .safe ∧ v.levelParams = [] ∧
      v.name ∈ [``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
        ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
        ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
        ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat] ∧
      (v.name = ``Char.ofNat → v.type == q(Nat → Char)) ∧
      (v.name = ``String.ofList → v.type == q(List Char → String)) := by
  have guardWF (b : Bool) (e : Exception) :
      (checkPrimitiveGuard b e).WF fun _ => b := by
    unfold checkPrimitiveGuard
    cases b
    · exact nofun
    · exact fun _ _ => rfl
  unfold checkPrimitiveHeader
  refine Except.WF.bind (guardWF _ _) fun _ hd => ?_
  refine Except.WF.bind (guardWF _ _) fun _ hs => ?_
  refine Except.WF.bind (guardWF _ _) fun _ hchar => ?_
  refine Except.WF.mono (guardWF _ _) fun _ hstring => ?_
  simp at hs
  let ⟨hsafe, hparams⟩ := hs
  refine ⟨hsafe, hparams, ?_, ?_, ?_⟩
  · have hd' := Std.TreeSet.mem_iff_contains.mpr hd
    simpa [Environment.definitionPrimitives, NameSet.ofList] using hd'
  · intro hname
    simpa [hname] using hchar
  · intro hname
    simpa [hname] using hstring

private theorem trListChar_eq
    (h : TrExprS env Us Δ q(List Char) e) : e = .listChar := by
  cases h with
  | app _ _ hlist hchar =>
    cases hlist with
    | const _ hlistMap _ =>
      cases hchar with
      | const _ hcharMap _ =>
        have hlistMap' : _ := hlistMap
        have hcharMap' : _ := hcharMap
        simp only [List.mapM_cons, VLevel.ofLevel, List.mapM_nil, pure] at hlistMap'
        simp only [List.mapM_nil, pure] at hcharMap'
        cases hlistMap'
        cases hcharMap'
        rfl

private theorem trListCharNil_eq
    (h : TrExprS env Us Δ q(List.nil (α := Char)) e) : e = .listCharNil := by
  cases h with
  | app _ _ hnil hchar =>
    cases hnil with
    | const _ hnilMap _ =>
      cases hchar with
      | const _ hcharMap _ =>
        have hnilMap' : _ := hnilMap
        have hcharMap' : _ := hcharMap
        simp only [List.mapM_cons, VLevel.ofLevel, List.mapM_nil, pure] at hnilMap'
        simp only [List.mapM_nil, pure] at hcharMap'
        cases hnilMap'
        cases hcharMap'
        rfl

private theorem trListCharCons_eq
    (h : TrExprS env Us Δ q(List.cons (α := Char)) e) : e = .listCharCons := by
  cases h with
  | app _ _ hcons hchar =>
    cases hcons with
    | const _ hconsMap _ =>
      cases hchar with
      | const _ hcharMap _ =>
        have hconsMap' : _ := hconsMap
        have hcharMap' : _ := hcharMap
        simp only [List.mapM_cons, VLevel.ofLevel, List.mapM_nil, pure] at hconsMap'
        simp only [List.mapM_nil, pure] at hcharMap'
        cases hconsMap'
        cases hcharMap'
        rfl

private theorem trListCharConsType_eq
    (h : TrExprS env Us Δ q(Char → List Char → List Char) e) :
    e = .forallE .char (.forallE .listChar .listChar) := by
  cases h with
  | forallE _ _ hchar hrest =>
    cases hchar with
    | const _ hcharMap _ =>
      have hcharMap' : _ := hcharMap
      simp only [List.mapM_nil, pure] at hcharMap'
      cases hcharMap'
      cases hrest with
      | forallE _ _ hlist₁ hlist₂ =>
        rw [trListChar_eq hlist₁, trListChar_eq hlist₂]
        rfl

theorem checkStringPrimitiveDeps.WF {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (checkStringPrimitiveDeps v).WF
      (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
        v.name = ``String.ofList →
          (ves.venv .safe).HasType v.levelParams.length [] .listCharNil .listChar ∧
          (ves.venv .safe).HasType v.levelParams.length [] .listCharCons
            (.forallE .char <| .forallE .listChar .listChar) := by
  unfold checkStringPrimitiveDeps
  let c := VContext.mk' wf .safe v.levelParams fuel
  split
  · rename_i hname
    have hname' : v.name = ``String.ofList := LawfulBEq.eq_of_beq hname
    refine (checkType.WF (c := c) (e := q(List Char)) (by simp [FVarsIn]; rfl)).bind
      fun _ _ _ ⟨listChar, _, _, hlistChar, _, _⟩ => ?_
    have hlistCharEq := trListChar_eq hlistChar
    refine (checkType.WF (c := c) (e := q(List.nil (α := Char)))
      (by simp [FVarsIn]; rfl)).bind
      fun nilType _ _ ⟨nil, nilType', _, hnil, hnilType, hnilTy⟩ => ?_
    have hnilEq := trListCharNil_eq hnil
    refine (isDefEq.WF (c := c) hnilType hlistChar).bind fun b _ _ hnilDef => ?_
    cases b
    · exact .throw
    · refine (M.WF.pure (c := c) (Q := fun _ _ => True) trivial).bind
        fun _ _ _ _ => ?_
      refine (checkType.WF (c := c) (e := q(Char → List Char → List Char))
          (by simp [FVarsIn]; rfl)).bind
        fun _ _ _ ⟨consExpected, _, _, hconsExpected, _, _⟩ => ?_
      have hconsExpectedEq := trListCharConsType_eq hconsExpected
      refine (checkType.WF (c := c) (e := q(List.cons (α := Char)))
        (by simp [FVarsIn]; rfl)).bind
        fun consType _ _ ⟨cons, consType', _, hcons, hconsType, hconsTy⟩ => ?_
      have hconsEq := trListCharCons_eq hcons
      refine (isDefEq.WF (c := c) hconsType hconsExpected).bind fun b _ _ hconsDef => ?_
      cases b
      · exact .throw
      · apply M.WF.pure
        intro _
        subst listChar
        subst nil
        subst consExpected
        subst cons
        constructor
        · exact hnilTy.defeqU_r (VContext.mk' wf .safe v.levelParams fuel).Ewf
            (VContext.mk' wf .safe v.levelParams fuel).Δwf (hnilDef rfl)
        · exact hconsTy.defeqU_r (VContext.mk' wf .safe v.levelParams fuel).Ewf
            (VContext.mk' wf .safe v.levelParams fuel).Δwf (hconsDef rfl)
  · apply M.WF.pure
    rename_i hname
    intro h
    rw [h] at hname
    simp at hname

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

theorem checkPrimitiveDefinition.WF {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (checkPrimitiveDefinition env v fuel).WF fun _ =>
        ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.defnInfo v) ci' ∧
          ci'.WF (ves.venv .safe) ∧ env.constants.find? v.name = none ∧
          v.safety = DefinitionSafety.safe ∧ v.levelParams = [] ∧
          v.name ∈ [``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
            ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
            ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
            ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat] ∧
          (v.name = ``Char.ofNat → v.type == q(Nat → Char)) ∧
          (v.name = ``String.ofList → v.type == q(List Char → String)) ∧
          (v.name = ``String.ofList →
            (ves.venv .safe).HasType 0 [] .listCharNil .listChar ∧
            (ves.venv .safe).HasType 0 [] .listCharCons
              (.forallE .char <| .forallE .listChar .listChar)) := by
  unfold Lean4Lean.checkPrimitiveDefinition
  refine (checkPrimitiveHeader.WF v).bind
    fun _ ⟨hsafe, hparams, hname, hchar, hstring⟩ => ?_
  refine (show (M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
    (fuel := fuel) (Environment.checkPrimitiveDef v)).WF (fun _ => True) from
      fun _ _ => trivial).bind fun allow _ => ?_
  have hv : v.safety ≠ .unsafe := by simp [hsafe]
  have finish (allow : Bool) (hdeps : allow = true →
      v.name = ``String.ofList →
        (ves.venv .safe).HasType v.levelParams.length [] .listCharNil .listChar ∧
        (ves.venv .safe).HasType v.levelParams.length [] .listCharCons
          (.forallE .char <| .forallE .listChar .listChar)) :
      (M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
        (fuel := fuel) do
          checkConstantVal env v.toConstantVal allow
          Kernel.Environment.checkNoMVarNoFVar env v.name v.value
          let valType ← TypeChecker.checkType v.value
          if !(← isDefEq valType v.type) then
            throw <| Exception.declTypeMismatch env (.defnDecl v) valType).WF fun _ =>
        ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.defnInfo v) ci' ∧
          ci'.WF (ves.venv .safe) ∧ env.constants.find? v.name = none ∧
          v.safety = DefinitionSafety.safe ∧ v.levelParams = [] ∧
          v.name ∈ [``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
            ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
            ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
            ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat] ∧
          (v.name = ``Char.ofNat → v.type == q(Nat → Char)) ∧
          (v.name = ``String.ofList → v.type == q(List Char → String)) ∧
          (v.name = ``String.ofList →
            (ves.venv .safe).HasType 0 [] .listCharNil .listChar ∧
            (ves.venv .safe).HasType 0 [] .listCharCons
              (.forallE .char <| .forallE .listChar .listChar)) := by
    refine (M.WF.run wf (checkDefinitionBody.WF (ves := ves) wf v hv allow)).mono
      fun _ ⟨ci', htr, hciwf, hfresh, hn⟩ => ?_
    have hp : Environment.primitives.contains v.name := primitive_contains v.name <| by
      simp only [List.mem_cons] at hname ⊢
      grind
    have ha : allow = true := by
      cases allow
      · simp [hn rfl] at hp
      · rfl
    rw [hsafe] at htr hciwf
    rw [hparams] at hdeps
    exact ⟨ci', htr, hciwf, hfresh, hsafe, hparams, hname, hchar, hstring, hdeps ha⟩
  cases allow
  · simpa only [Bool.false_eq_true, if_false, pure_bind] using finish false nofun
  · simp only [if_true]
    refine (M.WF.run wf (checkStringPrimitiveDeps.WF (ves := ves) wf v)).bind
      fun _ hdeps => finish true fun _ => hdeps

theorem checkPrimitiveDefinition.primitiveCheck (env : Environment) (v : DefinitionVal)
    (fuel : FuelConfig) :
    (checkPrimitiveDefinition env v fuel).WF fun _ =>
      ∃ b, M.run env .safe {} v.levelParams fuel (Environment.checkPrimitiveDef v) = .ok b := by
  unfold checkPrimitiveDefinition
  refine (show (checkPrimitiveHeader v).WF (fun _ => True) from fun _ _ => trivial).bind
    fun _ _ => ?_
  refine (show (M.run env .safe {} v.levelParams fuel (Environment.checkPrimitiveDef v)).WF
    (fun b => M.run env .safe {} v.levelParams fuel (Environment.checkPrimitiveDef v) = .ok b)
    from fun _ h => h).bind fun b hb => ?_
  exact fun _ _ => ⟨b, hb⟩

private theorem TrDefVal.charOfNat_type
    (htr : TrDefVal .safe env (.defnInfo v) ci')
    (hp : v.levelParams = []) (ht : v.type == q(Nat → Char)) :
    ci'.toVConstant = { uvars := 0, type := .forallE .nat .char } := by
  rcases htr with ⟨⟨⟨hs, hu, htype⟩, hn⟩, hvalue⟩
  dsimp [ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.name,
    ConstantInfo.toConstantVal] at hu htype hn
  rw [hp] at hu htype
  have h := htype.eqv ht
  generalize he : ci'.type = e at h
  cases h with
  | forallE hnty hnbody hnat hchar =>
    cases hnat with
    | const hnatConst hnatMap hnatLen =>
      cases hchar with
      | const hcharConst hcharMap hcharLen =>
        have hnatMap' : _ := hnatMap
        have hcharMap' : _ := hcharMap
        simp only [List.mapM_nil, pure] at hnatMap' hcharMap'
        cases hnatMap'
        cases hcharMap'
        subst_vars
        simp only [List.length_nil] at hu hnatLen hcharLen
        cases ci' with
        | mk vc value =>
          cases vc with
          | mk c name =>
            cases c with
            | mk uvars type =>
              simp only at hu he ⊢
              congr
              omega

private theorem TrDefVal.stringOfList_type
    (htr : TrDefVal .safe env (.defnInfo v) ci')
    (hp : v.levelParams = []) (ht : v.type == q(List Char → String)) :
    ci'.toVConstant = { uvars := 0, type := .forallE .listChar .string } := by
  rcases htr with ⟨⟨⟨hs, hu, htype⟩, hn⟩, hvalue⟩
  dsimp [ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.name,
    ConstantInfo.toConstantVal] at hu htype hn
  rw [hp] at hu htype
  have h := htype.eqv ht
  generalize he : ci'.type = e at h
  cases h with
  | forallE hnty hnbody hdom hbody =>
    cases hdom with
    | app hfunTy hargTy hfun harg =>
      cases hfun with
      | const hlistConst hlistMap hlistLen =>
        cases harg with
        | const hcharConst hcharMap hcharLen =>
          cases hbody with
          | const hstringConst hstringMap hstringLen =>
            have hlistMap' : _ := hlistMap
            have hcharMap' : _ := hcharMap
            have hstringMap' : _ := hstringMap
            simp only [List.mapM_cons, VLevel.ofLevel, List.mapM_nil, pure] at hlistMap'
            simp only [List.mapM_nil, pure] at hcharMap' hstringMap'
            cases hlistMap'
            cases hcharMap'
            cases hstringMap'
            subst_vars
            simp only [List.length_nil] at hu hcharLen hstringLen
            cases ci' with
            | mk vc value =>
              cases vc with
              | mk c name =>
                cases c with
                | mk uvars type =>
                  simp only at hu he ⊢
                  congr
                  omega

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

theorem VEnv.HasPrimitives.mono_of_constants {env env' : VEnv}
    (hp : env.HasPrimitives) (hle : env ≤ env')
    (hconst : ∀ m ∈ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
      ``Char.ofNat, ``String.ofList], env'.constants m = env.constants m)
    (hadd : env'.ReflectsNatNatNat ``Nat.add Nat.add) : env'.HasPrimitives := by
  have hcontains (m : Name) (hm : m ∈ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
      ``Char.ofNat, ``String.ofList]) :
      env'.contains m ↔ env.contains m := by
    simp only [VEnv.contains]
    rw [hconst m hm]
  refine {
    bool := fun h => by
      have ⟨hf, ht⟩ := hp.bool ((hcontains ``Bool (by simp)).1 h)
      exact ⟨(hcontains ``Bool.false (by simp)).2 hf,
        (hcontains ``Bool.true (by simp)).2 ht⟩
    boolFalse := fun h => hp.boolFalse
      (hconst ``Bool.false (by simp) ▸ h)
    boolTrue := fun h => hp.boolTrue
      (hconst ``Bool.true (by simp) ▸ h)
    nat := fun h => by
      have ⟨hz, hs⟩ := hp.nat ((hcontains ``Nat (by simp)).1 h)
      exact ⟨(hcontains ``Nat.zero (by simp)).2 hz,
        (hcontains ``Nat.succ (by simp)).2 hs⟩
    natZero := fun h => hp.natZero
      (hconst ``Nat.zero (by simp) ▸ h)
    natSucc := fun h => hp.natSucc
      (hconst ``Nat.succ (by simp) ▸ h)
    natAdd := hadd
    charOfNat := fun h => hp.charOfNat
      (hconst ``Char.ofNat (by simp) ▸ h)
    stringOfList := fun h =>
      let ⟨h₁, h₂, h₃⟩ := hp.stringOfList
        (hconst ``String.ofList (by simp) ▸ h)
      ⟨h₁, h₂.mono hle, h₃.mono hle⟩ }

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} {n : Name} {ci : VConstant}
    (hp : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hn : n ∉ [``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ,
      ``Char.ofNat, ``String.ofList, ``Nat.add]) : env'.HasPrimitives := by
  have hle := VEnv.addConst_le hadd
  apply hp.mono_of_constants hle
  · intro m hm
    apply VEnv.addConst_constants hadd
    rintro rfl
    exact hn (by simp_all)
  · intro h a b
    have heq := VEnv.addConst_constants hadd (m := ``Nat.add) (by
      rintro rfl
      exact hn (by simp))
    have h' : env.contains ``Nat.add := by simpa only [VEnv.contains, heq] using h
    exact (hp.natAdd h' a b).mono hle

theorem VEnv.HasPrimitives.addLiteralDef {env env' : VEnv} {n : Name} {ci : VConstant}
    (hp : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hn : n = ``Char.ofNat ∨ n = ``String.ofList)
    (hchar : n = ``Char.ofNat → ci = { uvars := 0, type := .forallE .nat .char })
    (hstring : n = ``String.ofList →
      ci = { uvars := 0, type := .forallE .listChar .string } ∧
      env.HasType 0 [] .listCharNil .listChar ∧
      env.HasType 0 [] .listCharCons
        (.forallE .char <| .forallE .listChar .listChar)) : env'.HasPrimitives := by
  have hle := VEnv.addConst_le hadd
  have hother (m : Name) (hm : m ∈ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ]) : n ≠ m := by
    simp only [List.mem_cons] at hm
    simp at hm
    rcases hn with rfl | rfl <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hconst (m : Name) (hm : m ∈ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ]) :
      env'.constants m = env.constants m := VEnv.addConst_constants hadd (hother m hm)
  have hcontains (m : Name) (hm : m ∈ [
      ``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ]) :
      env'.contains m ↔ env.contains m := by
    simp only [VEnv.contains]
    rw [hconst m hm]
  refine {
    bool := fun h => by
      have ⟨hf, ht⟩ := hp.bool ((hcontains ``Bool (by simp)).1 h)
      exact ⟨(hcontains ``Bool.false (by simp)).2 hf,
        (hcontains ``Bool.true (by simp)).2 ht⟩
    boolFalse := fun h => hp.boolFalse (hconst ``Bool.false (by simp) ▸ h)
    boolTrue := fun h => hp.boolTrue (hconst ``Bool.true (by simp) ▸ h)
    nat := fun h => by
      have ⟨hz, hs⟩ := hp.nat ((hcontains ``Nat (by simp)).1 h)
      exact ⟨(hcontains ``Nat.zero (by simp)).2 hz,
        (hcontains ``Nat.succ (by simp)).2 hs⟩
    natZero := fun h => hp.natZero (hconst ``Nat.zero (by simp) ▸ h)
    natSucc := fun h => hp.natSucc (hconst ``Nat.succ (by simp) ▸ h)
    natAdd := fun h a b => by
      have heq := VEnv.addConst_constants hadd (m := ``Nat.add) (by
        rcases hn with rfl | rfl <;> decide)
      have h' : env.contains ``Nat.add := by simpa only [VEnv.contains, heq] using h
      exact (hp.natAdd h' a b).mono hle
    charOfNat := fun h => by
      by_cases heq : n = ``Char.ofNat
      · subst n
        have : ci = _ := Option.some.inj ((VEnv.addConst_self hadd).symm.trans h)
        simpa [this] using hchar rfl
      · exact hp.charOfNat (VEnv.addConst_constants hadd heq ▸ h)
    stringOfList := fun h => by
      by_cases heq : n = ``String.ofList
      · subst n
        have hci : ci = _ := Option.some.inj ((VEnv.addConst_self hadd).symm.trans h)
        have ⟨hty, hnil, hcons⟩ := hstring rfl
        exact ⟨hci.symm.trans hty, hnil.mono hle, hcons.mono hle⟩
      · let ⟨hty, hnil, hcons⟩ := hp.stringOfList
          (VEnv.addConst_constants hadd heq ▸ h)
        exact ⟨hty, hnil.mono hle, hcons.mono hle⟩ }

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
            ((ves.venv safety).addConst_insert (hvnone safety))
            (not_reduction_primitive (hnprim rfl))
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

private theorem addQuotInfo.WF {ves : VEnvs} (wf : ves.WF env)
    (hq : env.quotInit = false) (v : QuotVal) (ci' : VConstant)
    (htype : ∀ {type'}, TrExprS (ves.venv .safe) v.levelParams [] v.type type' →
      type' = ci'.type)
    (huvars : v.levelParams.length = ci'.uvars) (fuel : FuelConfig := {}) :
    (addQuotInfo env v fuel).WF fun env' =>
      ∃ ves' : VEnvs, env' = env.add (.quotInfo v) ∧ VEnvs.WF env' ves' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        ∀ safety, TrConstant safety (ves.venv safety) (.quotInfo v) ci' ∧
          (ves.venv safety).addConst v.name ci' = some (ves'.venv safety) ∧
          env.constants.find? v.name = none := by
  unfold addQuotInfo
  refine (M.WF.run wf (checkConstantVal.WF (ves := ves) wf v.toConstantVal false
    (safety := .safe) (fuel := fuel))).bind
    fun _ ⟨vty, htr, hvwf, hfresh, hnprim⟩ => ?_
  apply Except.WF.pure
  have hvty : vty = ci'.type := htype htr
  have hvwf' : ci'.WF (ves.venv .safe) := by
    simpa [huvars, hvty] using hvwf
  have htr' : TrConstant .safe (ves.venv .safe) (.quotInfo v) ci' := by
    refine ⟨?_, huvars, hvty ▸ htr⟩
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  have hvnone (safety) : (ves.venv safety).constants v.name = none :=
    (wf.tr).constants_eq_none hfresh
  let ves' : VEnvs := ⟨fun safety => (ves.venv safety).insertConst v.name ci'⟩
  refine ⟨ves', rfl, ?_, ?_, ?_⟩
  · refine {
      tr := by
        intro safety
        simp only [ves']
        have hbase := wf.tr (safety := safety)
        change TrEnv' safety env.constants env.quotInit (ves.venv safety) at hbase
        rw [hq] at hbase
        simpa [TrEnv, hq] using TrEnv'.quotInfo
          ((htr'.sf_mono DefinitionSafety.le_safe).mono
            (wf.mono DefinitionSafety.le_safe))
          hfresh (hvwf'.mono (wf.mono DefinitionSafety.le_safe))
          ((ves.venv _).addConst_insert (hvnone _)) hbase
      hasPrimitives := by
        intro safety
        exact wf.hasPrimitives.addConst
          ((ves.venv safety).addConst_insert (hvnone safety))
          (not_reduction_primitive (hnprim rfl))
      safePrimitives := by
        intro n ci hfind hp
        have hmap := (wf.tr (safety := .safe)).map_wf
        change (env.constants.insert v.name (.quotInfo v)).find?' n = some ci at hfind
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
        exact VEnv.addConst_mono (wf.mono hle)
          ((ves.venv safety').addConst_insert (hvnone safety'))
          ((ves.venv safety).addConst_insert (hvnone safety)) }
  · intro safety
    exact VEnv.addConst_le ((ves.venv safety).addConst_insert (hvnone safety))
  · intro safety
    exact ⟨(htr'.sf_mono DefinitionSafety.le_safe).mono
      (wf.mono DefinitionSafety.le_safe),
      (ves.venv safety).addConst_insert (hvnone safety), hfresh⟩

theorem addQuotVerified.WF {ves : VEnvs} (wf : ves.WF env)
    (fuel : FuelConfig := {}) :
    (addQuotVerified env fuel).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addQuotVerified
  split
  · exact .pure ⟨ves, wf, fun _ => .rfl⟩
  · rename_i hq
    have hq' : env.quotInit = false := by
      cases he : env.quotInit
      · rfl
      · exact (hq he).elim
    refine (checkEqType.WF wf).bind fun _ hready => ?_
    extract_lets quot quotMk quotLift quotInd
    refine (addQuotInfo.WF wf hq' quot quotConst trQuotType_eq rfl fuel).bind
      fun env1 hres1 => ?_
    obtain ⟨ves1, heq1, wf1, hmono1, hstep1⟩ := hres1
    subst env1
    refine (addQuotInfo.WF wf1 (by simpa using hq') quotMk quotMkConst
      trQuotMkType_eq rfl fuel).bind
      fun env2 hres2 => ?_
    obtain ⟨ves2, heq2, wf2, hmono2, hstep2⟩ := hres2
    subst env2
    refine (addQuotInfo.WF wf2 (by simpa using hq') quotLift quotLiftConst
      trQuotLiftType_eq rfl fuel).bind
      fun env3 hres3 => ?_
    obtain ⟨ves3, heq3, wf3, hmono3, hstep3⟩ := hres3
    subst env3
    refine (addQuotInfo.WF wf3 (by simpa using hq') quotInd quotIndConst
      trQuotIndType_eq rfl fuel).bind
      fun env4 hres4 => ?_
    obtain ⟨ves4, heq4, wf4, hmono4, hstep4⟩ := hres4
    subst env4
    apply Except.WF.pure
    let ves' : VEnvs := ⟨fun safety => (ves4.venv safety).addDefEq quotDefEq⟩
    have hadd (safety) : AddQuot env.constants
        ((((env.add (.quotInfo quot)).add (.quotInfo quotMk)).add
          (.quotInfo quotLift)).add (.quotInfo quotInd)).constants
        (ves.venv safety) (ves'.venv safety) := by
      unfold AddQuot AddQuot1
      refine ⟨quot.levelParams, quot.type, ves1.venv safety, ?_, ?_, ?_, ?_⟩
      · simpa [quot] using
          (hstep1 .safe).1.mono (wf.mono DefinitionSafety.le_safe)
      · exact (hstep1 safety).2.2
      · exact (hstep1 safety).2.1
      refine ⟨quotMk.levelParams, quotMk.type, ves2.venv safety, ?_, ?_, ?_, ?_⟩
      · simpa [quotMk] using
          (hstep2 .safe).1.mono (wf1.mono DefinitionSafety.le_safe)
      · exact (hstep2 safety).2.2
      · exact (hstep2 safety).2.1
      refine ⟨quotLift.levelParams, quotLift.type, ves3.venv safety, ?_, ?_, ?_, ?_⟩
      · simpa [quotLift] using
          (hstep3 .safe).1.mono (wf2.mono DefinitionSafety.le_safe)
      · exact (hstep3 safety).2.2
      · exact (hstep3 safety).2.1
      refine ⟨quotInd.levelParams, quotInd.type, ves4.venv safety, ?_, ?_, ?_, ?_⟩
      · simpa [quotInd] using
          (hstep4 .safe).1.mono (wf3.mono DefinitionSafety.le_safe)
      · exact (hstep4 safety).2.2
      · exact (hstep4 safety).2.1
      exact ⟨rfl, rfl⟩
    refine ⟨ves', ?_, ?_⟩
    · refine {
        tr := by
          intro safety
          have hbase := wf.tr (safety := safety)
          change TrEnv' safety env.constants env.quotInit (ves.venv safety) at hbase
          rw [hq'] at hbase
          simpa [TrEnv, ves'] using
            TrEnv'.quot (hready safety) (hadd safety) hbase
        hasPrimitives := by
          intro safety
          exact (wf4.hasPrimitives (safety := safety)).addDefEq
        safePrimitives := by
          intro n ci hfind hp
          apply wf4.safePrimitives (n := n) (ci := ci) (by simpa using hfind) hp
        mono := by
          intro safety safety' hle
          exact VEnv.addDefEq_mono (wf4.mono hle) }
    · intro safety
      exact (hmono1 safety).trans <| (hmono2 safety).trans <|
        (hmono3 safety).trans <| (hmono4 safety).trans VEnv.addDefEq_le

theorem addDefinitionHeader.WF {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hv : v.safety ≠ .safe) (fuel : FuelConfig := {}) :
    (addDefinitionHeader env v fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinitionHeader
  refine (M.WF.run wf (checkConstantVal.WF (ves := ves) wf v.toConstantVal false
    (safety := v.safety) (fuel := fuel))).bind
    fun _ ⟨vty, htr, hvwf, hfresh, hnprim⟩ => ?_
  apply Except.WF.pure
  let vci : VConstant := ⟨v.levelParams.length, vty⟩
  have hvwf' : vci.WF (ves.venv v.safety) := hvwf
  have hcisafety : (ConstantInfo.defnInfo v).safety = v.safety := by
    cases hs : v.safety <;>
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hs]
  have htr' : TrConstant v.safety (ves.venv v.safety) (.defnInfo v) vci := by
    exact ⟨hcisafety ▸ DefinitionSafety.le_rfl, rfl, htr⟩
  have hvnone (safety) : (ves.venv safety).constants v.name = none :=
    (wf.tr).constants_eq_none hfresh
  let ves' : VEnvs := ⟨fun safety =>
    if safety ≤ v.safety then (ves.venv safety).insertConst v.name vci else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := by
        intro safety
        simp only [ves']
        split
        · rename_i hs
          apply TrEnv'.opaqueDefn
          · exact (htr'.sf_mono hs).mono (wf.mono hs)
          · exact hcisafety ▸ hv
          · exact hfresh
          · exact hvwf'.mono (wf.mono hs)
          · exact (ves.venv _).addConst_insert (hvnone _)
          · exact wf.tr
        · rename_i hs
          exact TrEnv'.ignoreConst hfresh (hcisafety ▸ hs) wf.tr
      hasPrimitives := by
        intro safety
        simp only [ves']
        split
        · exact wf.hasPrimitives.addConst
            ((ves.venv safety).addConst_insert (hvnone safety))
            (not_reduction_primitive (hnprim rfl))
        · exact wf.hasPrimitives
      safePrimitives := by
        intro n ci hfind hp
        have hmap := (wf.tr (safety := .safe)).map_wf
        change (env.constants.insert v.name (.defnInfo v)).find?' n = some ci at hfind
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
        by_cases hs' : safety' ≤ v.safety
        · have hs : safety ≤ v.safety := DefinitionSafety.le_trans hle hs'
          simp only [ves', if_pos hs', if_pos hs]
          exact VEnv.addConst_mono (wf.mono hle)
            ((ves.venv safety').addConst_insert (hvnone safety'))
            ((ves.venv safety).addConst_insert (hvnone safety))
        · by_cases hs : safety ≤ v.safety
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

theorem addDefinition.WF_unsafe {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hv : v.safety = .unsafe) (fuel : FuelConfig := {}) :
    (addDefinition env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp only [hv, pure_bind, if_true]
  refine (addDefinitionHeader.WF wf v (by simp [hv]) fuel).bind
    fun env' ⟨ves', wf', hmono⟩ => ?_
  refine (show (Kernel.Environment.checkNoMVarNoFVar env' v.name v.value).WF
    (fun _ => True) from fun _ _ => trivial).bind fun _ _ => ?_
  refine (show (M.run env' (safety := .unsafe) (lctx := {})
    (lparams := v.levelParams) (fuel := fuel) do
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env' (.defnDecl v) valType).WF
    (fun _ => True) from fun _ _ => trivial).bind fun _ _ => ?_
  exact .pure ⟨ves', wf', hmono⟩

theorem addMutualHeaders.WF {ves : VEnvs} (wf : ves.WF env)
    (hs : safety ≠ .safe) (levelParams : List Name) (vs : List DefinitionVal)
    (fuel : FuelConfig := {}) :
    (addMutualHeaders env safety levelParams fuel vs).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  induction vs generalizing env ves with
  | nil => exact .pure ⟨ves, wf, fun _ => .rfl⟩
  | cons v vs ih =>
    simp only [addMutualHeaders]
    cases hvs : v.safety != safety
    · have hvs' : v.safety = safety := by simpa using hvs
      cases hvp : v.levelParams != levelParams
      · refine (addDefinitionHeader.WF wf v (hvs' ▸ hs) fuel).bind
          fun env' ⟨ves', wf', hmono⟩ => ?_
        refine (ih (ves := ves') wf').mono fun _ ⟨ves'', wf'', hmono'⟩ =>
          ⟨ves'', wf'', fun safety => (hmono safety).trans (hmono' safety)⟩
      · exact nofun
    · exact nofun

theorem checkMutualBodies.WF (env : Environment) (safety : DefinitionSafety)
    (levelParams : List Name) (vs : List DefinitionVal) (fuel : FuelConfig := {}) :
    (checkMutualBodies env safety levelParams vs fuel).WF fun _ => True :=
  fun _ _ => trivial

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
              ((ves.venv safety).addConst_insertDef (hvnone' safety))
              (not_reduction_primitive hn')).addDefEq
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

theorem addDefinition.WF_primitive {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hv : v.safety ≠ .unsafe)
    (hp : Environment.primitives.contains v.name = true) (fuel : FuelConfig := {}) :
    (addDefinition env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hs : v.safety
  · exact (hv hs).elim
  ·
    unfold addDefinition
    simp only [hs, pure_bind, if_true, hp]
    refine Except.WF.bind (x := checkPrimitiveDefinition env v fuel)
      (fun r h => And.intro (checkPrimitiveDefinition.WF wf v (fuel := fuel) r h)
        (checkPrimitiveDefinition.primitiveCheck env v fuel r h)) ?_
    rintro _ ⟨⟨ci', htr, hciwf, hfresh, hsafe, hparams, hprim, hchar, hstring, hdeps⟩,
      b, hcheck⟩
    apply Except.WF.pure
    have hvnone (safety) : (ves.venv safety).constants v.name = none :=
      (wf.tr).constants_eq_none hfresh
    have hname := htr.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    have hvnone' (safety) : (ves.venv safety).constants ci'.name = none :=
      hname ▸ hvnone safety
    let ves' : VEnvs := ⟨fun safety =>
      ((ves.venv safety).insertDefConst ci').addDefEq ci'.toDefEq⟩
    have htr' (safety) : TrEnv safety (env.add (.defnInfo v)) (ves'.venv safety) := by
      apply TrEnv'.defn
      · exact (htr.sf_mono (DefinitionSafety.le_safe (a := safety))).mono
          (wf.mono (safety := safety) (safety' := .safe) DefinitionSafety.le_safe)
      · exact hfresh
      · exact hciwf.mono
          (wf.mono (safety := safety) (safety' := .safe) DefinitionSafety.le_safe)
      · simpa [hname] using (ves.venv safety).addConst_insertDef (hvnone' safety)
      · exact wf.tr
    refine ⟨ves', ?_, ?_⟩
    · refine {
        tr := htr' _
        hasPrimitives := by
          intro safety
          have hadd := (ves.venv safety).addConst_insertDef (hvnone' safety)
          by_cases hnat : v.name = ``Nat.add
          · have hnat' : ci'.name = ``Nat.add := hname.symm.trans hnat
            have hle : ves.venv safety ≤ ves'.venv safety :=
              (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
            apply (wf.hasPrimitives (safety := safety)).mono_of_constants hle
            · intro m hm
              change ((ves.venv safety).insertDefConst ci').constants m =
                (ves.venv safety).constants m
              exact VEnv.addConst_constants hadd (by
                rw [hnat']
                rintro rfl
                simp at hm)
            · have hu : ci'.uvars = 0 := by
                have h := htr.1.1.2.1
                change v.levelParams.length = ci'.uvars at h
                simpa [hparams] using h.symm
              have ht := htr.1.1.2.2
              have hv := htr.2
              change TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type at ht
              change TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value at hv
              rw [hparams] at ht hv hcheck
              have hf : (ves.venv .safe).HasType 0 [] ci'.value ci'.type := by
                simpa [VDefVal.WF, hu] using hciwf
              have hdef := VEnv.IsDefEq.extra0 VEnv.addDefEq_self
                ((htr' safety).wf.ordered.defEqWF VEnv.addDefEq_self)
              have hdef' : (ves'.venv safety).IsDefEq 0 []
                  (.const ``Nat.add []) ci'.value ci'.type := by
                simpa [ves', VDefVal.toDefEq, hu, hnat', VLevel.params] using hdef
              exact Environment.checkPrimitiveDef_natAdd.reflects wf v hnat ht hv hf hcheck
                (htr' safety).wf ((wf.mono DefinitionSafety.le_safe).trans hle) hdef'
          by_cases hlit : v.name = ``Char.ofNat ∨ v.name = ``String.ofList
          · apply (wf.hasPrimitives.addLiteralDef hadd (hlit.imp hname.symm.trans hname.symm.trans)
                (fun hn => ?_) (fun hn => ?_)).addDefEq
            · apply TrDefVal.charOfNat_type htr hparams
              apply hchar
              exact hname.trans hn
            · refine ⟨TrDefVal.stringOfList_type htr hparams (hstring (hname.trans hn)), ?_⟩
              exact (hdeps (hname.trans hn)).imp
                (fun h => h.mono (wf.mono DefinitionSafety.le_safe))
                (fun h => h.mono (wf.mono DefinitionSafety.le_safe))
          · apply (wf.hasPrimitives.addConst hadd ?_).addDefEq
            intro hm
            rw [← hname] at hm
            simp only [List.mem_cons] at hm
            simp at hm
            rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm
            · rw [hm] at hprim; simp at hprim
            · rw [hm] at hprim; simp at hprim
            · rw [hm] at hprim; simp at hprim
            · rw [hm] at hprim; simp at hprim
            · rw [hm] at hprim; simp at hprim
            · rw [hm] at hprim; simp at hprim
            · exact hlit (.inl hm)
            · exact hlit (.inr hm)
            · exact hnat hm
        safePrimitives := by
          intro n ci hfind hnprim
          have hmap := (wf.tr (safety := .safe)).map_wf
          change (env.constants.insert v.name (.defnInfo v)).find?' n = some ci at hfind
          rw [(hmap.insert _ _ hfresh).find?'_eq_find?, hmap.find?_insert] at hfind
          split at hfind
          · rename_i hname'
            cases hfind
            have : v.name = n := LawfulBEq.eq_of_beq hname'
            subst n
            constructor
            · simp [hsafe, ConstantInfo.safety, ConstantInfo.isUnsafe,
                ConstantInfo.isPartial]
            · exact hparams
          · apply wf.safePrimitives _ hnprim
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
  · unfold addDefinition
    simp only [hs, pure_bind, if_true, hp]
    refine (checkPrimitiveDefinition.WF (ves := ves) wf v (fuel := fuel)).bind
      fun _ ⟨_, _, _, _, hsafe, _⟩ => ?_
    cases hs.symm.trans hsafe

theorem addDefinition.WF {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig := {}) :
    (addDefinition env v true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hs : v.safety
  · exact addDefinition.WF_unsafe wf v hs fuel
  all_goals
    have hv : v.safety ≠ .unsafe := by simp [hs]
    cases hp : Environment.primitives.contains v.name
    · exact addDefinition.WF_nonprimitive wf v hv hp fuel
    · exact addDefinition.WF_primitive wf v hv hp fuel

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
            ((ves.venv safety).addConst_insert (hvnone safety))
            (not_reduction_primitive hnprim)
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
          ((ves.venv safety).addConst_insertDef (hvnone' safety))
          (not_reduction_primitive hn')).addDefEq
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

theorem addMutual.WF {ves : VEnvs} (wf : ves.WF env) (vs : List DefinitionVal)
    (fuel : FuelConfig := {}) :
    (addMutual env vs true fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases vs with
  | nil => exact nofun
  | cons v vs =>
    cases hs : v.safety
    ·
      simp only [addMutual, hs, pure_bind, if_true]
      refine (addMutualHeaders.WF wf (by decide) v.levelParams (v :: vs) fuel).bind
        fun env' ⟨ves', wf', hmono⟩ => ?_
      refine (checkMutualBodies.WF env' .unsafe v.levelParams (v :: vs) fuel).bind
        fun _ _ => ?_
      exact .pure ⟨ves', wf', hmono⟩
    · intro _ h
      simp only [addMutual, hs, pure_bind, if_true] at h
      change (Except.error _ : Except Exception Environment) = .ok _ at h
      cases h
    ·
      simp only [addMutual, hs, pure_bind, if_true]
      refine (addMutualHeaders.WF wf (by decide) v.levelParams (v :: vs) fuel).bind
        fun env' ⟨ves', wf', hmono⟩ => ?_
      refine (checkMutualBodies.WF env' .partial v.levelParams (v :: vs) fuel).bind
        fun _ _ => ?_
      exact .pure ⟨ves', wf', hmono⟩

/-- The intended main theorem of the `Verify` development, currently unproved:
if `env` is well-formed and `addDecl env decl` (in checking mode) succeeds,
then the resulting environment is also well-formed, and it extends `env`.

The non-inductive frontend is covered by `addDeclVerified.WF` below. The
unrestricted theorem still requires the missing inductive specification and
its connection to the executable checker. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration) :
    (addDecl env decl).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  sorry

theorem addDeclVerified.WF {ves : VEnvs} (wf : ves.WF env) (decl : Declaration)
    (fuel : FuelConfig := {}) :
    (addDeclVerified env decl fuel).WF fun env' =>
      ∃ ves' : VEnvs, VEnvs.WF env' ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => simpa [addDeclVerified] using addAxiom.WF wf v fuel
  | defnDecl v => simpa [addDeclVerified] using addDefinition.WF wf v fuel
  | thmDecl v => simpa [addDeclVerified] using addTheorem.WF wf v fuel
  | opaqueDecl v => simpa [addDeclVerified] using addOpaque.WF wf v fuel
  | mutualDefnDecl vs => simpa [addDeclVerified] using addMutual.WF wf vs fuel
  | quotDecl => simpa [addDeclVerified] using addQuotVerified.WF wf fuel
  | inductDecl lparams nparams types isUnsafe => simp [addDeclVerified, Except.WF]

theorem addDeclVerified.foldlM_WF {ves : VEnvs} (wf : ves.WF env)
    (decls : List Declaration) (fuel : FuelConfig := {}) :
    (decls.foldlM (fun env decl => addDeclVerified env decl fuel) env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  induction decls generalizing env ves with
  | nil => exact .pure ⟨ves, wf, fun _ => .rfl⟩
  | cons decl decls ih =>
    simp only [List.foldlM_cons]
    refine (addDeclVerified.WF wf decl fuel).bind fun env' ⟨ves', wf', hle⟩ => ?_
    exact (ih wf').mono fun _ ⟨ves'', wf'', hle'⟩ =>
      ⟨ves'', wf'', fun safety => (hle safety).trans (hle' safety)⟩

theorem addDeclVerified.fromEmpty (mainModule : Name) (decls : List Declaration)
    (fuel : FuelConfig := {}) :
    (decls.foldlM (fun env decl => addDeclVerified env decl fuel)
      (Environment.empty mainModule)).WF fun env => ∃ ves : VEnvs, ves.WF env :=
  (addDeclVerified.foldlM_WF (.empty mainModule) decls fuel).mono
    fun _ ⟨ves, wf, _⟩ => ⟨ves, wf⟩

end Lean4Lean
