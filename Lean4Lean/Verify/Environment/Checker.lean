import Lean4Lean.Verify.Environment.Primitive

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

theorem ConstantInfo.defnInfo_safety (v : DefinitionVal) :
    (ConstantInfo.defnInfo v).safety = v.safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  cases v.safety <;> rfl

structure NativeValueFrame (before after : Environment) : Prop where
  map_wf : after.constants.WF
  lookups : ∀ {name ci}, before.constants.find? name = some ci →
    after.constants.find? name = some ci
  values : ∀ {name ci value}, after.constants.find? name = some ci →
    ci.value? = some value → before.constants.find? name = some ci

theorem NativeValueFrame.refl (hmap : env.constants.WF) : NativeValueFrame env env :=
  ⟨hmap, id, fun hfind _ => hfind⟩

theorem NativeValueFrame.trans (first : NativeValueFrame before middle)
    (second : NativeValueFrame middle after) : NativeValueFrame before after :=
  ⟨second.map_wf, fun hfind => second.lookups (first.lookups hfind),
    fun hfind hvalue => first.values (second.values hfind hvalue) hvalue⟩

theorem NativeValueFrame.addConst {ci : ConstantInfo} (hmap : env.constants.WF)
    (hfresh : env.constants.find? ci.name = none) (hvalue : ci.value? = none) :
    NativeValueFrame env (env.add ci) := by
  refine ⟨hmap.insert _ _ hfresh, ?_, ?_⟩
  · intro name info hfind
    change (env.constants.insert ci.name ci).find? name = some info
    rw [hmap.find?_insert]
    split
    · rename_i hname
      have hname : ci.name = name := beq_iff_eq.mp hname
      subst name
      rw [hfresh] at hfind
      contradiction
    · exact hfind
  · intro name info value hfind hv
    change (env.constants.insert ci.name ci).find? name = some info at hfind
    rw [hmap.find?_insert] at hfind
    split at hfind
    · cases hfind
      rw [hvalue] at hv
      contradiction
    · exact hfind

theorem NativeValueFrame.foldlM {Item State Error : Type} (getEnv : State → Environment)
    (step : State → Item → Except Error State) (items : List Item) (initial : State)
    (hmap : (getEnv initial).constants.WF)
    (hstep : ∀ item current, (getEnv current).constants.WF →
      ∀ next, step current item = .ok next → NativeValueFrame (getEnv current) (getEnv next)) :
    ∀ final, items.foldlM step initial = .ok final →
      NativeValueFrame (getEnv initial) (getEnv final) := by
  induction items generalizing initial with
  | nil => intro final hresult; cases hresult; exact .refl hmap
  | cons item items ih =>
    intro final hresult
    rw [List.foldlM_cons] at hresult
    cases hnext : step initial item with
    | error exception =>
      rw [hnext] at hresult
      cases hresult
    | ok next =>
      rw [hnext] at hresult
      change items.foldlM step next = .ok final at hresult
      have hframe := hstep item initial hmap next hnext
      exact hframe.trans (ih next hframe.map_wf final hresult)

structure CheckerEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop where
  aligned : Aligned safety env.constants venv
  wf : venv.WF
  safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
    safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
    TrExpr venv ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length))

/-! A checker-facing view that retains constructive inductive history. `CheckerEnv` remains the
value-checking contract used by the existing frontend, while this companion carries positive
family lookups for consumers that must see registered inductive declarations. -/
structure CheckerEnvInductive (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (Q : Bool) : Prop where
  history : TrEnvInductive safety env.constants Q venv
  safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
    safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
    TrExpr venv ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length))

/- Consume a constructive generated-recursors receipt at the checker boundary.
   The prior history, map equalities, declaration WF, and safe-value callback
   remain explicit; this theorem only packages them into the checker-facing
   history structure. -/
theorem AddInductWithRecursorsEvidence.toCheckerEnvInductive
    {safety : DefinitionSafety}
    (H : AddInductWithRecursorsEvidence safety C env decl inductiveConstants inductiveEnv
      recursors models C' env')
    (native resultNative : Kernel.Environment)
    (history : TrEnvInductive safety native.constants Q env)
    (hmap : native.constants = C) (hresultMap : resultNative.constants = C')
    (hdecl : VDecl.WF env (.induct decl) inductiveEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      resultNative.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr env' ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety resultNative env' Q := by
  subst C
  subst C'
  refine ⟨H.to_trEnvInductive history hdecl, ?_⟩
  intro name ci value h hs hsafe hv
  exact hvalues name ci h hs hsafe hv

/- A safety-indexed environment model whose histories may contain registered
   inductive families. This is deliberately separate from `VEnvs.WF`: the
   latter stores the legacy `TrEnv` relation, whose lookup-rejection contract
   cannot represent an inductive declaration. -/
structure VEnvs.InductiveWF (env : Environment) (ves : VEnvs) (Q : Bool) : Prop where
  history : ∀ {safety}, TrEnvInductive safety env.constants Q (ves.venv safety)
  hasPrimitives : ∀ {safety}, (ves.venv safety).HasPrimitives
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  mono : ∀ {safety safety'}, safety ≤ safety' → ves.venv safety' ≤ ves.venv safety

theorem VEnvs.InductiveWF.map_wf (H : VEnvs.InductiveWF env ves Q) : env.constants.WF :=
  (H.history (safety := .safe)).map_wf

theorem VEnvs.InductiveWF.venv_wf (H : VEnvs.InductiveWF env ves Q)
    (safety : DefinitionSafety) : (ves.venv safety).WF :=
  (H.history (safety := safety)).wf

theorem VEnvs.InductiveWF.toCheckerEnvInductive
    (H : VEnvs.InductiveWF env ves Q) (safety : DefinitionSafety)
    (safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr (ves.venv safety) ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety env (ves.venv safety) Q :=
  ⟨H.history, safeValues⟩

theorem VEnvs.InductiveWF.toCheckerEnvInductive_and_wf
    (H : VEnvs.InductiveWF env ves Q) (safety : DefinitionSafety)
    (safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr (ves.venv safety) ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety env (ves.venv safety) Q ∧
      env.constants.WF ∧ (ves.venv safety).WF :=
  ⟨H.toCheckerEnvInductive safety safeValues, H.map_wf, H.venv_wf safety⟩

theorem CheckerEnvInductive.map_wf
    (H : CheckerEnvInductive safety env venv Q) : env.constants.WF :=
  H.history.map_wf

theorem CheckerEnvInductive.venv_wf
    (H : CheckerEnvInductive safety env venv Q) : venv.WF :=
  H.history.wf

theorem CheckerEnvInductive.toCheckerEnv
    (H : CheckerEnvInductive safety env venv Q) : CheckerEnv safety env venv :=
  ⟨H.history.aligned, H.history.wf, H.safeValues⟩

theorem CheckerEnvInductive.find?
    (H : CheckerEnvInductive safety env venv Q)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.history.env_find? h hs

theorem CheckerEnvInductive.find?_uniq
    (H : CheckerEnvInductive safety env venv Q)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.history.env_find?_uniq h hs

theorem CheckerEnvInductive.of_valueFrame
    (H : CheckerEnvInductive safety env venv Q)
    (history : TrEnvInductive safety env'.constants Q venv')
    (hframe : NativeValueFrame env env') (hle : venv ≤ venv') :
    CheckerEnvInductive safety env' venv' Q :=
  ⟨history, fun hfind hs hsafe hv =>
    (H.safeValues (hframe.values hfind hv) hs hsafe hv).mono hle⟩

theorem TrEnv.checkerEnv (H : TrEnv safety env venv) : CheckerEnv safety env venv :=
  ⟨H.aligned, H.wf, by
    intro name ci value hfind hs hsafe hv
    have hdelta : ci.deltaValue? = some value := by
      cases ci <;> simp [ConstantInfo.value?, ConstantInfo.deltaValue?] at hv ⊢ <;> assumption
    have hfind' : env.find? name = some ci := by
      simpa only [Kernel.Environment.find?, H.map_wf.find?'_eq_find?] using hfind
    exact H.of_value hfind' hs hdelta⟩

theorem CheckerEnv.map_wf (H : CheckerEnv safety env venv) : env.constants.WF := H.aligned.map_wf

theorem CheckerEnv.find?_iff (H : CheckerEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := by
  conv => enter [1, 1, _, 1, 1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem CheckerEnv.find? (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem CheckerEnv.find?_uniq (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem checkName.WF (mapWF : env.constants.WF) (name : Name) (allowPrimitive : Bool) :
    (Environment.checkName env name allowPrimitive).WF fun _ =>
      env.find? name = none ∧ (Environment.primitives.contains name → allowPrimitive) := by
  intro _ h
  have hn : env.contains name = false := by
    cases hfind : env.contains name <;> [rfl; skip]
    simp [Environment.checkName, hfind, (· >>= ·), Except.bind] at h
  change env.constants.contains name = false at hn
  rw [SMap.find?_isSome] at hn
  refine ⟨?_, fun ha => ?_⟩
  · rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
    cases hfind : env.constants.find? name <;> simp_all
  · have hc : env.constants.contains name = false := by rwa [SMap.find?_isSome]
    simpa only [Environment.checkName, Kernel.Environment.contains, hc, ↓reduceIte, ha,
      ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false,
      show (pure PUnit.unit : Except Exception PUnit) = .ok PUnit.unit from rfl] using h

private theorem checkNoMVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVar env name e).WF fun _ => e.hasMVar = false := by
  intro _ h; cases hmv : e.hasMVar <;> [rfl; simp [Environment.checkNoMVar, hmv] at h]

private theorem checkNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoFVar env name e).WF fun _ => e.hasFVar = false := by
  intro _ h; cases hfv : e.hasFVar <;> [rfl; simp [Environment.checkNoFVar, hfv] at h]

theorem checkNoMVarNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVarNoFVar env name e).WF fun _ => e.FVarsIn fun _ => False := by
  refine (checkNoMVar.WF env name e).bind fun _ hm =>
    (checkNoFVar.WF env name e).mono fun _ hf => ?_
  refine fvarsIn_iff.2 ⟨fun fv hmem => ?_, fvarsIn_iff_hasMVar.2 hm⟩
  rw [fvarsList_eq_nil.2 hf] at hmem
  simp at hmem

private theorem Except.WF.trivial (x : Except ε α) : x.WF fun _ => True :=
  fun _ _ => True.intro

private theorem TypeChecker.M.WF.pureBind {c : VContext}
    {s : VState} {f : β → M α} {Q} {x : β}
    (H : (f x).WF c s Q) : ((Pure.pure x : M β) >>= f).WF c s Q := H

/-- The part of `checkConstantVal` that does not check the name. `addDefinition` runs it before
`Primitive.checkDef`, so that the latter's `isDefEq` calls act on terms already known to be well
typed, and defers the name check until the primitive verdict is available. -/
theorem checkConstantValBody.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (state : VState := {}) (fuel : FuelConfig := {}) :
    (checkConstantValBody env ci.toConstantVal).WF (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
      ∃ ci' : VConstVal,
        ci.levelParams.length = ci'.uvars ∧
        TrExprS (ves.venv safety) ci.levelParams [] ci.type ci'.type ∧
        ci.name = ci'.name ∧
        ci'.toVConstant.WF (ves.venv safety) := by
  -- Duplicate level parameters are rejected operationally; no later proof needs that fact.
  refine (M.WF.liftExcept (Except.WF.trivial _)).bind fun _ _ _ _ => ?_
  refine (M.WF.liftExcept
    (checkNoMVarNoFVar.WF env ci.name ci.type)).bind fun _ _ _ hclosed => ?_
  have hclosed' : ci.type.FVarsIn
      (· ∈ (VContext.mk' wf safety ci.levelParams fuel).vlctx.fvars) := by
    simpa [VContext.mk', VContext.mk1] using hclosed
  refine (checkType.WF hclosed').bind fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
  refine (ensureSort.WF hsort).bind fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => .pure ?_
  obtain ⟨u, rfl⟩ := hsortEq
  cases hsort' with | sort hu
  refine ⟨{ name := ci.name, uvars := ci.levelParams.length, type := type' }, rfl, htype, rfl, ?_⟩
  exact ⟨_, hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) hdefeq.symm⟩

theorem checkConstantValCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (state : VState := {})
    (fuel : FuelConfig := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
        ∃ ci' : VConstVal,
          ci.levelParams.length = ci'.uvars ∧
          TrExprS (ves.venv safety) ci.levelParams [] ci.type ci'.type ∧
          ci.name = ci'.name ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (Environment.primitives.contains ci.name → allowPrimitive) := by
  refine (M.WF.liftExcept
    (checkName.WF (wf.tr (safety := safety)).map_wf ci.name allowPrimitive)).bind
    fun _ _ _ hname => ?_
  exact (checkConstantValBody.WF wf ci _ fuel).mono fun _ _ _ ⟨ci', hu, ht, hn', hci⟩ =>
    ⟨ci', hu, ht, hn', hci, hname⟩

theorem CheckerEnv.of_valueFrame (hchecker : CheckerEnv safety env venv)
    (hframe : NativeValueFrame env env') (hle : venv ≤ venv')
    (hvenv : venv'.WF) (haligned : Aligned safety env'.constants venv') :
    CheckerEnv safety env' venv' :=
  ⟨haligned, hvenv,
    fun hfind hs hsafe hv => (hchecker.safeValues (hframe.values hfind hv) hs hsafe hv).mono hle⟩

theorem CheckerEnv.addConst (H : CheckerEnv safety env venv)
    (hfresh : env.constants.find? ci.name = none)
    (htr : TrConstant safety venv ci ci') (hvalue : ci.value? = none)
    (hconst : ci'.WF venv) (hadd : venv.addConst ci.name ci' = some venv') :
    CheckerEnv safety (env.add ci) venv' := by
  refine H.of_valueFrame (NativeValueFrame.addConst (ci := ci) H.aligned.map_wf hfresh hvalue)
    (VEnv.addConst_le hadd) ?_ (H.aligned.const hfresh htr hadd rfl)
  obtain ⟨decls, hdecls⟩ := H.wf
  exact ⟨_, hdecls.decl (.axiom
    (ci := { name := ci.name, uvars := ci'.uvars, type := ci'.type }) hconst hadd)⟩

theorem checkConstantVal.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (hs : safety ≤ ci.safety)
    (state : VState := {}) (fuel : FuelConfig := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
        ∃ ci' : VConstVal, TrConstVal safety (ves.venv safety) ci ci' ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (Environment.primitives.contains ci.name → allowPrimitive) :=
  (checkConstantValCore.WF wf ci allowPrimitive state fuel).mono
    fun _ _ _ ⟨ci', hu, ht, hn', hci, hn, hp⟩ => ⟨ci', ⟨⟨hs, hu, ht⟩, hn'⟩, hci, hn, hp⟩

def checkBodyCore (env : Environment) (decl : Declaration) (type value : Expr) : M Unit := do
  let valueType ← checkType value
  if !(← isDefEq valueType type) then
    throw <| Exception.declTypeMismatch env decl valueType

/-- The body check proper, with the mvar/fvar check already discharged. `addDefinition` runs
the two in the same `do` block for a safe definition but splits them for an unsafe one (the
mvar/fvar check happens before the constant is added as an axiom), so they are verified
separately.

Stated against a single-level model (`VEnvAt`): a mutual block's bodies are checked in the
temporary environment holding the whole block as axioms, which has no model at every level. -/
theorem checkBodyCore.WF {env : Environment} {venv : VEnv} (wf : VEnvAt env safety venv)
    (decl : Declaration) (levelParams : List Name) (type value : Expr)
    (type' : VExpr) (hdeclType : TrExprS venv levelParams [] type type')
    (hclosed : value.FVarsIn fun _ => False) (state : VState := {})
    (fuel : FuelConfig := {}) :
    (checkBodyCore env decl type value).WF (.mk1 wf levelParams fuel) state fun _ _ =>
      ∃ value', TrExprS venv levelParams [] value value' ∧
        venv.HasType levelParams.length [] value' type' := by
  have hclosed' : value.FVarsIn (· ∈ (VContext.mk1 wf levelParams fuel).vlctx.fvars) := by
    simpa [VContext.mk1] using hclosed
  refine (checkType.WF hclosed').bind
    fun valueType _ _ ⟨value', _, _, hvalue, hvalueType, hhasType⟩ => ?_
  refine (isDefEq.WF hvalueType hdeclType).bind fun equal _ _ hequal => ?_
  split <;> [exact .throw; rename_i hnot]
  exact .pure ⟨value', hvalue, hhasType.defeqU_r wf.tr.wf trivial (hequal (by simpa using hnot))⟩

def checkBody (env : Environment) (name : Name)
    (type value : Expr) (decl : Declaration) : M Unit := do
  Environment.checkNoMVarNoFVar env name value
  checkBodyCore env decl type value

theorem checkBody.WF {env : Environment} (wf : VEnvAt env safety venv)
    (decl : Declaration) (name : Name) (value : Expr)
    (hdeclType : TrExprS venv levelParams [] type type')
    (state : VState := {}) (fuel : FuelConfig := {}) :
    (checkBody env name type value decl).WF (.mk1 wf levelParams fuel) state fun _ _ =>
      ∃ value', TrExprS venv levelParams [] value value' ∧
        venv.HasType levelParams.length [] value' type' :=
  (M.WF.liftExcept (checkNoMVarNoFVar.WF env name value)).bind fun _ _ _ hclosed =>
  checkBodyCore.WF wf decl levelParams type value type' hdeclType hclosed _ fuel

def checkTheorem (env : Environment) (v : TheoremVal) : M Unit := do
  checkConstantVal env v.toConstantVal
  if !(← isProp v.type) then
    throw <| Exception.thmTypeIsNotProp env v.name v.type
  Environment.checkNoMVarNoFVar env v.name v.value
  let valueType ← checkType v.value
  if !(← isDefEq valueType v.type) then
    throw <| Exception.declTypeMismatch env (.thmDecl v) valueType

theorem checkTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal)
    (fuel : FuelConfig := {}) :
    (checkTheorem env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
      ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.thmInfo v) ci' ∧
        ci'.WF (ves.venv .safe) ∧
        (ves.venv .safe).HasType ci'.uvars [] ci'.type (.sort .zero) ∧
        env.find? v.name = none ∧ Environment.primitives.contains v.name = false := by
  refine (checkConstantVal.WF wf (.thmInfo v) false DefinitionSafety.le_rfl {} fuel).bind
    fun _ state _ ⟨ci', htr, hci, hn, hnonprim⟩ => ?_
  refine (isProp.WF htr.1.2.2).bind fun isProp state' _ hprop => ?_
  split <;> [exact .throw; rename_i hnot]
  have hisProp : isProp = true := by cases isProp <;> simp_all
  refine .pureBind <| checkBody.WF _ _ _ _ htr.1.2.2 _ fuel
    |>.mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
  let ci'' : VDefVal := { ci' with value := value' }
  refine ⟨ci'', ⟨htr, hvalue⟩, ?_, htr.1.2.1 ▸ hprop hisProp, hn, ?_⟩
  · rwa [VDefVal.WF, ← htr.1.2.1]
  · simp at hnonprim; exact hnonprim

/-- The type and the body, with neither the name check nor the primitive check. -/
theorem checkDefinitionBody.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (state : VState := {}) (fuel : FuelConfig := {}) :
    (checkDefinitionBody env v).WF (.mk' wf safety v.levelParams fuel) state fun _ _ => ∃ ci' : VDefVal,
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv safety) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv safety) v.levelParams [] v.value ci'.value ∧
      ci'.WF (ves.venv safety) := by
  refine (checkConstantValBody.WF wf (.defnInfo v) state fuel).bind
    fun _ state' _ ⟨ci', hu, ht, hname, hci⟩ => ?_
  exact (checkBody.WF _ _ _ _ ht _ fuel).mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ =>
    ⟨{ ci' with value := value' }, hu, ht, hname, hvalue, (hu ▸ hvalueType :)⟩

def checkDefinition (env : Environment) (v : DefinitionVal) : M Unit := do
  checkDefinitionBody env v
  Environment.checkName env v.name (← Primitive.checkDef v)

theorem checkDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig := {}) :
    (checkDefinition env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ => ∃ ci' : VDefVal,
      (Environment.primitives.contains v.name → Primitive.PrimitiveResult (ves.venv .safe) v ci') ∧
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
      ci'.WF (ves.venv .safe) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v {} fuel).bind fun _ state _ ⟨ci', hu, ht, hname, hvalue, hci⟩ => ?_
  refine (Primitive.checkDef.WF wf v ci' hu ht hvalue hci state fuel).bind fun allow state' _ hp => ?_
  exact (M.WF.liftExcept (checkName.WF (wf.tr (safety := .safe)).map_wf v.name allow)).mono
    fun _ _ _ hn => ⟨ci', hp ∘ hn.2, hu, ht, hname, hvalue, hci, hn.1⟩

def checkOpaque (env : Environment) (v : OpaqueVal) : M Unit := do
  checkConstantVal env v.toConstantVal
  Environment.checkNoMVarNoFVar env v.name v.value
  let valueType ← checkType v.value
  if !(← isDefEq valueType v.type) then
    throw <| Exception.declTypeMismatch env (.opaqueDecl v) valueType

theorem checkDefinition.WF_primitive {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (value : DefinitionVal) (primitiveName : Environment.primitives.contains value.name = true)
    (fuel : FuelConfig := {}) :
    (checkDefinition env value).WF (.mk' wf .safe value.levelParams fuel) {} fun _ _ =>
      ∃ translated : VDefVal, Primitive.PrimitiveResult (ves.venv .safe) value translated ∧
        value.levelParams.length = translated.uvars ∧
        TrExprS (ves.venv .safe) value.levelParams [] value.type translated.type ∧
        value.name = translated.name ∧
        TrExprS (ves.venv .safe) value.levelParams [] value.value translated.value ∧
        translated.WF (ves.venv .safe) ∧ env.find? value.name = none :=
  (checkDefinition.WF wf value fuel).mono
    fun _ _ _ ⟨translated, primitive, universes, header, name, body, wellFormed, fresh⟩ =>
      ⟨translated, primitive primitiveName, universes, header, name, body, wellFormed, fresh⟩

/-- Verify the complete opaque-declaration check. The body is checked, so it is packaged into
the resulting `VDefVal`; `TrEnv'.opaque` consumes it. An opaque body still contributes no
definitional equality -- that is `TrEnv'.opaque` adding no `addDefEq`, not the body going
unrecorded. -/
theorem checkOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal)
    (fuel : FuelConfig := {}) :
    (checkOpaque env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ => ∃ ci' : VDefVal,
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
      ci'.toVConstant.WF (ves.venv .safe) ∧
      ci'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
      Environment.primitives.contains v.name = false := by
  refine (checkConstantValCore.WF wf (.opaqueInfo v) false {} fuel).bind
    fun _ state _ ⟨ci', hu, ht, hname, hci, hfresh, hnonprim⟩ => ?_
  refine checkBody.WF _ _ _ _ ht _ fuel |>.mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
  refine ⟨{ ci' with value := value' }, hu, ht, hname, hvalue, hci, ?_, hfresh, ?_⟩
  · rwa [VDefVal.WF, ← hu]
  · simp at hnonprim; exact hnonprim
