import Lean4Lean.Theory.InductiveHeaders

namespace Lean4Lean

variable {env env' : VEnv} {ctors : List VConstVal} {ctor : VConstVal}

theorem VEnv.addConstructorHeaders.exists
    (fresh : ∀ constructor ∈ ctors, env.constants constructor.name = none)
    (distinct : (ctors.map VConstVal.name).Nodup) :
    ∃ extended, env.addConstructorHeaders ctors = some extended := by
  induction ctors generalizing env with
  | nil => exact ⟨env, rfl⟩
  | cons first remaining induction =>
    have firstFresh := fresh first (by simp)
    have names := List.nodup_cons.mp distinct
    let next : VEnv := { env with constants := fun name =>
      if first.name = name then some first.toVConstant else env.constants name }
    have registered : env.addConst first.name first.toVConstant = some next := by
      simp only [VEnv.addConst, firstFresh, next]
    have remainingFresh : ∀ constructor ∈ remaining, next.constants constructor.name = none := by
      intro constructor member
      have different : first.name ≠ constructor.name := by
        intro equal
        exact names.1 (equal ▸ List.mem_map.mpr ⟨constructor, member, rfl⟩)
      exact (if_neg different).trans (fresh constructor (by simp [member]))
    obtain ⟨extended, final⟩ := induction remainingFresh names.2
    exact ⟨extended, by simp only [addConstructorHeaders, registered]; exact final⟩

theorem VEnv.addConstructorHeaders.append (env : VEnv) (first second : List VConstVal) :
    env.addConstructorHeaders (first ++ second) =
      (env.addConstructorHeaders first >>= fun next => next.addConstructorHeaders second) := by
  induction first generalizing env with
  | nil => rfl
  | cons ctor first ih =>
    simp only [List.cons_append, addConstructorHeaders, ih, bind_assoc]

theorem VEnv.addConstructorHeaders.le
    (hadd : env.addConstructorHeaders ctors = some env') : env ≤ env' := by
  induction ctors generalizing env with
  | nil => cases hadd; exact .rfl
  | cons ctor ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (addConst_le hstep).trans (ih hrest)

theorem VEnv.addConstructorHeaders.constants
    (hadd : env.addConstructorHeaders ctors = some env') (hmem : ctor ∈ ctors) :
    env'.constants ctor.name = some ctor.toVConstant := by
  induction ctors generalizing env with
  | nil => cases hmem
  | cons first ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact (addConstructorHeaders.le hrest).constants (addConst_self hstep)
    · exact ih hrest hmem

theorem VEnv.addConstructorHeaders.fresh
    (hadd : env.addConstructorHeaders ctors = some env') (hmem : ctor ∈ ctors) :
    env.constants ctor.name = none := by
  induction ctors generalizing env with
  | nil => cases hmem
  | cons first ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    rcases List.mem_cons.mp hmem with rfl | hmem
    · unfold VEnv.addConst at hstep
      split at hstep <;> simp_all
    · cases found : env.constants ctor.name with
      | none => rfl
      | some value =>
        have found' := (addConst_le hstep).constants found
        rw [@ih next hrest hmem] at found'
        cases found'

theorem VEnv.addConstructorHeaders.defeqs_eq
    (hadd : env.addConstructorHeaders ctors = some env') : env'.defeqs = env.defeqs := by
  induction ctors generalizing env with
  | nil => cases hadd; rfl
  | cons ctor ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (ih hrest).trans (addConst.defeqs_eq hstep)

theorem VEnv.addConstructorHeaders.ordered (hordered : env.Ordered)
    (htypes : ∀ ctor ∈ ctors, ctor.toVConstant.WF env)
    (hadd : env.addConstructorHeaders ctors = some env') : env'.Ordered := by
  induction ctors generalizing env with
  | nil => cases hadd; exact hordered
  | cons ctor ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    refine ih (.const hordered (htypes ctor (by simp)) hstep) ?_ hrest
    intro remaining hmem
    exact (htypes remaining (by simp [hmem])).mono (addConst_le hstep)

theorem VEnv.addConstructorHeaders.wf
    (henv : env.WF) (htypes : ∀ ctor ∈ ctors, ctor.toVConstant.WF env)
    (hadd : env.addConstructorHeaders ctors = some env') : env'.WF := by
  induction ctors generalizing env env' with
  | nil => cases hadd; exact henv
  | cons ctor ctors ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    have hctor : ctor.toVConstant.WF env := htypes ctor (by simp)
    obtain ⟨decls, hdecls⟩ := henv
    have hnext : nextEnv.WF := by
      exact ⟨_, .decl (.axiom hctor hstep) hdecls⟩
    apply ih hnext
    · intro remaining hmem
      exact (htypes remaining (by simp [hmem])).mono (addConst_le hstep)
    · exact hrest

end Lean4Lean
