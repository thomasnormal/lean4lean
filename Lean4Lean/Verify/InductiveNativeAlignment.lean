import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.Environment.Lemmas

namespace Lean4Lean
open Lean hiding Environment Exception

namespace NativeInductive

private theorem alignedHeaders
    {safety : DefinitionSafety} {constants : ConstMap} {env : VEnv}
    {headerConstants : ConstMap} {result : VEnv}
    (entries : List HeaderEntry) (headers : List VInductiveType)
    (haligned : Aligned safety constants env)
    (hmodels : entries.map (·.model) = headers.map (·.toVConstVal))
    (hsemantic : ∀ entry ∈ entries,
      TrConstVal .safe env (.inductInfo entry.info) entry.model)
    (hfresh : FreshHeaders constants entries)
    (hadd : env.addInductHeaders headers = some result)
    (hmap : headerConstants = insertHeaders constants entries) :
    Aligned safety headerConstants result := by
  induction entries generalizing constants env headerConstants result headers with
  | nil =>
    cases headers with
    | nil =>
      cases hmodels
      simp only [insertHeaders] at hmap
      subst headerConstants
      cases hadd
      exact haligned
    | cons header headers => exact False.elim (by simpa using hmodels)
  | cons entry entries ih =>
    cases headers with
    | nil => exact False.elim (by simpa using hmodels)
    | cons header headers =>
      simp only [List.map_cons, List.cons.injEq] at hmodels
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
      have hname : entry.info.name = header.name := by
        calc
          entry.info.name = entry.model.name := (hsemantic entry (by simp)).2
          _ = header.toVConstVal.name := congrArg VConstVal.name hmodels.1
          _ = header.name := rfl
      have hmodelName : entry.info.name = entry.model.name :=
        (hsemantic entry (by simp)).2
      have htr : TrConstant safety env (.inductInfo entry.info) entry.model.toVConstant :=
        (hsemantic entry (by simp)).1.sf_mono DefinitionSafety.le_safe
      have hstep' : env.addConst entry.model.name entry.model.toVConstant = some next := by
        simpa [hmodels.1] using hstep
      have hfresh' : constants.find? entry.model.name = none := by
        simpa [hmodelName] using hfresh.1
      have hnextAligned : Aligned safety (constants.insert entry.model.name
          (.inductInfo entry.info)) next :=
        haligned.const hfresh' htr hstep' hmodelName
      have hsemantic' : ∀ e ∈ entries,
          TrConstVal .safe next (.inductInfo e.info) e.model := by
        intro e he
        exact (hsemantic e (by simp [he])).mono (VEnv.addConst_le hstep)
      have hnextFresh : FreshHeaders (constants.insert entry.info.name
          (.inductInfo entry.info)) entries := by
        simpa [hmodelName] using hfresh.2
      have hnextMap : headerConstants = insertHeaders
          (constants.insert entry.info.name (.inductInfo entry.info)) entries := by
        simpa [insertHeaders] using hmap
      have hnextAligned' : Aligned safety (constants.insert entry.info.name
          (.inductInfo entry.info)) next := by
        simpa [hmodelName] using hnextAligned
      have hnext := ih headers hnextAligned' hmodels.2 hsemantic' hnextFresh hrest hnextMap
      simpa [insertHeaders, hname] using hnext

private theorem trConstValModelShape
    {safety : DefinitionSafety} {env : VEnv} {entry : RegistrationEntry}
    (h : TrConstVal safety env entry.toConstantInfo entry.model) : entry.ModelShape := by
  cases entry with
  | header entry => exact ⟨h.2.symm, h.1.2.1.symm⟩
  | constructor entry => exact ⟨h.2.symm, h.1.2.1.symm⟩
  | recursor entry => exact ⟨h.2.symm, h.1.2.1.symm⟩

private theorem alignedEntries
    {safety : DefinitionSafety} {constants : ConstMap} {env : VEnv}
    {resultConstants : ConstMap} {result : VEnv}
    (entries : List RegistrationEntry) (models : List VConstVal)
    (haligned : Aligned safety constants env)
    (hmodels : entries.map (·.model) = models)
    (hsemantic : ∀ entry ∈ entries,
      TrConstVal .safe env entry.toConstantInfo entry.model)
    (hfresh : FreshOrdered constants entries)
    (hadd : env.addConstructorHeaders models = some result)
    (hmap : resultConstants = insertOrdered constants entries) :
    Aligned safety resultConstants result := by
  induction entries generalizing constants env resultConstants result models with
  | nil =>
    cases models with
    | nil =>
      cases hmodels
      simp only [insertOrdered] at hmap
      subst resultConstants
      cases hadd
      exact haligned
    | cons head tail => exact False.elim (by simpa using hmodels)
  | cons entry entries ih =>
    cases models with
    | nil => exact False.elim (by simpa using hmodels)
    | cons model models =>
      simp only [List.map_cons, List.cons.injEq] at hmodels
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
      have hshape : entry.ModelShape := trConstValModelShape (hsemantic entry (by simp))
      have hname : entry.toConstantInfo.name = model.name := by
        calc
          entry.toConstantInfo.name = entry.model.name := hshape.toConstantInfo.1.symm
          _ = model.name := congrArg VConstVal.name hmodels.1
      have htr : TrConstant safety env entry.toConstantInfo model.toVConstant := by
        simpa [hmodels.1] using (hsemantic entry (by simp)).1.sf_mono DefinitionSafety.le_safe
      have hstep' : env.addConst model.name model.toVConstant = some next := hstep
      have hnextAligned : Aligned safety (constants.insert model.name
          entry.toConstantInfo) next :=
        haligned.const (by simpa [hname] using hfresh.1) htr hstep' hname
      have hsemantic' : ∀ e ∈ entries,
          TrConstVal .safe next e.toConstantInfo e.model := by
        intro e he
        exact (hsemantic e (by simp [he])).mono (VEnv.addConst_le hstep)
      have hnextFresh : FreshOrdered
          (entry.insert constants) entries := hfresh.2
      have hnextMap : resultConstants = insertOrdered
          (entry.insert constants) entries := by
        simpa [insertOrdered] using hmap
      have hnextAligned' : Aligned safety (entry.insert constants) next := by
        rw [entry.insert_modelShape hshape]
        simpa [hmodels.1] using hnextAligned
      have hnext := ih models hnextAligned' hmodels.2 hsemantic' hnextFresh hrest hnextMap
      simpa [insertOrdered, entry.insert_modelShape hshape] using hnext

theorem RegistrationEvidence.aligned
    {safety : DefinitionSafety}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned safety constants env) :
    Aligned safety resultConstants result := by
  have hheaders : Aligned safety evidence.headerConstants evidence.headerEnv := by
    apply alignedHeaders evidence.headers decl.types haligned evidence.headerModels
      (fun entry hmem => evidence.headerTranslation entry hmem)
      evidence.headerFresh evidence.headerAdd evidence.headerMap
  have hconstructors : Aligned safety evidence.constructorConstants evidence.constructorEnv := by
    apply alignedEntries
      (evidence.constructors.map (fun entry => .constructor entry))
      decl.constructorHeaders hheaders
    · simpa only [List.map_map, Function.comp_def, RegistrationEntry.model] using
        evidence.constructorModels
    · intro entry hmem
      simp only [List.mem_map] at hmem
      obtain ⟨entry, hmem, rfl⟩ := hmem
      exact evidence.constructorTranslation entry hmem
    · have h := (FreshConstructors.ordered evidence.headerConstants evidence.constructors).2
        evidence.constructorFresh
      simpa only [List.map_map, Function.comp_def] using h
    · exact evidence.constructorAdd
    · rw [evidence.constructorMap, ← insertOrdered_constructors]
  apply alignedEntries
    (evidence.recursors.map (fun entry => .recursor entry))
    (evidence.recursors.map (·.model)) hconstructors
  · simp only [List.map_map, Function.comp_def, RegistrationEntry.model]
  · intro entry hmem
    simp only [List.mem_map] at hmem
    obtain ⟨entry, hmem, rfl⟩ := hmem
    exact evidence.recursorTranslation entry hmem
  · have h := (FreshRecursors.ordered evidence.constructorConstants evidence.recursors).2
      evidence.recursorFresh
    simpa only [List.map_map, Function.comp_def] using h
  · exact evidence.recursorAdd
  · calc
      resultConstants = insertRecursors evidence.constructorConstants evidence.recursors :=
        evidence.resultMap
      _ = insertOrdered evidence.constructorConstants
          (evidence.recursors.map (fun entry => .recursor entry)) := by
        rw [insertOrdered_recursors]

theorem RegistrationEvidence.headerEnvWF
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.headerEnv.WF := by
  exact VEnv.addInductHeaders.wf henv
    (fun header hmem => (evidence.declWF.1 header hmem).2) evidence.headerAdd

theorem RegistrationEvidence.constructorEnvWF
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.constructorEnv.WF := by
  exact VEnv.addConstructorHeaders.wf (evidence.headerEnvWF henv)
    (fun ctor hmem => (evidence.declWF.2 evidence.headerEnv evidence.headerAdd ctor hmem).2)
    evidence.constructorAdd

theorem RegistrationEvidence.resultWF
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) : result.WF := by
  exact VEnv.addConstructorHeaders.wf (evidence.constructorEnvWF henv)
    (by
      intro model hmem
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
      exact hrecursors entry hentry)
    evidence.recursorAdd

end NativeInductive
end Lean4Lean
