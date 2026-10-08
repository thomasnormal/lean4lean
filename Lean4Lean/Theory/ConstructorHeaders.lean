import Lean4Lean.Theory.InductiveHeaders

namespace Lean4Lean

def VEnv.addConstructorHeaders (env : VEnv) : List VConstVal → Option VEnv
  | [] => some env
  | ctor :: ctors => do
    let env ← env.addConst ctor.name ctor.toVConstant
    env.addConstructorHeaders ctors

variable {env env' : VEnv} {ctors : List VConstVal} {ctor : VConstVal}

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

end Lean4Lean
