import Lean4Lean.Verify.Environment.Lemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

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

theorem NativeValueFrame.addConst (hmap : env.constants.WF)
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

theorem TrEnv.checkerEnv (H : TrEnv safety env venv) : CheckerEnv safety env venv :=
  ⟨H.aligned, H.wf, TrEnv'.of_value H⟩

theorem CheckerEnv.empty (mainModule : Name) (trustLevel : UInt32 := 0) :
    CheckerEnv safety (Environment.empty mainModule trustLevel) VEnv.empty := by
  refine ⟨.empty, ⟨[], .empty⟩, ?_⟩
  intro name ci value hfind _ _ _
  change ({} : ConstMap).find? name = some ci at hfind
  simp [SMap.find?] at hfind

theorem CheckerEnv.map_wf (H : CheckerEnv safety env venv) : env.constants.WF :=
  H.aligned.map_wf

theorem CheckerEnv.find?_iff (H : CheckerEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem CheckerEnv.find? (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem CheckerEnv.find?_uniq (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem CheckerEnv.of_value (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety)
    (hci : ci.safety = .safe) (hv : ci.value? = some value) :
    TrExpr venv ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.safeValues (by simpa only [Kernel.Environment.find?, H.map_wf.find?'_eq_find?] using h)
    hs hci hv

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
  refine H.of_valueFrame (NativeValueFrame.addConst (ci := ci) H.map_wf hfresh hvalue)
    (VEnv.addConst_le hadd) ?_ (H.aligned.const hfresh htr hadd rfl)
  obtain ⟨decls, hdecls⟩ := H.wf
  exact ⟨_, hdecls.decl (.axiom
    (ci := { name := ci.name, uvars := ci'.uvars, type := ci'.type }) hconst hadd)⟩

end Lean4Lean
