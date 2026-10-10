import Lean4Lean.Verify.Environment.Lemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

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

theorem CheckerEnv.addConst (H : CheckerEnv safety env venv)
    (hfresh : env.constants.find? ci.name = none)
    (htr : TrConstant safety venv ci ci') (hvalue : ci.value? = none)
    (hconst : ci'.WF venv) (hadd : venv.addConst ci.name ci' = some venv') :
    CheckerEnv safety (env.add ci) venv' := by
  refine ⟨H.aligned.const hfresh htr hadd rfl, ?_, ?_⟩
  · obtain ⟨decls, hdecls⟩ := H.wf
    exact ⟨_, hdecls.decl (.axiom
      (ci := { name := ci.name, uvars := ci'.uvars, type := ci'.type }) hconst hadd)⟩
  · intro name info value hfind hs hsafe hv
    change (env.constants.insert ci.name ci).find? name = some info at hfind
    rw [H.map_wf.find?_insert] at hfind
    split at hfind
    · cases hfind
      rw [hvalue] at hv
      contradiction
    · exact (H.safeValues hfind hs hsafe hv).mono (VEnv.addConst_le hadd)

end Lean4Lean
