import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

def VEnv.addInductHeaders (env : VEnv) : List VInductiveType → Option VEnv
  | [] => some env
  | header :: headers => do
    let env ← env.addConst header.name header.toVConstant
    env.addInductHeaders headers

def VInductDecl.HeadersWF (env : VEnv) (decl : VInductDecl) : Prop :=
  ∀ header ∈ decl.types, header.uvars = decl.uvars ∧ header.toVConstant.WF env

variable {env env' : VEnv} {decl : VInductDecl} {headers : List VInductiveType}
  {header : VInductiveType} {name : Name} {constant : VConstant}

theorem VInductDecl.HeadersWF.mono (hheaders : decl.HeadersWF env) (hle : env ≤ env') :
    decl.HeadersWF env' :=
  fun header hmem => ⟨(hheaders header hmem).1, (hheaders header hmem).2.mono hle⟩

theorem VEnv.addInductHeaders.le
    (hadd : env.addInductHeaders headers = some env') : env ≤ env' := by
  induction headers generalizing env with
  | nil => cases hadd; exact .rfl
  | cons header headers ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (addConst_le hstep).trans (ih hrest)

theorem VEnv.addInductHeaders.constants
    (hadd : env.addInductHeaders headers = some env') (hmem : header ∈ headers) :
    env'.constants header.name = some header.toVConstant := by
  induction headers generalizing env with
  | nil => cases hmem
  | cons firstHeader headers ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact (addInductHeaders.le hrest).constants (addConst_self hstep)
    · exact ih hrest hmem

private theorem VEnv.addConst.defeqs_eq
    (hadd : env.addConst name constant = some env') : env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  rfl

theorem VEnv.addInductHeaders.defeqs_eq
    (hadd : env.addInductHeaders headers = some env') : env'.defeqs = env.defeqs := by
  induction headers generalizing env with
  | nil => cases hadd; rfl
  | cons header headers ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (ih hrest).trans (addConst.defeqs_eq hstep)

theorem VEnv.addInductHeaders.ordered (hordered : env.Ordered)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF env)
    (hadd : env.addInductHeaders headers = some env') : env'.Ordered := by
  induction headers generalizing env with
  | nil => cases hadd; exact hordered
  | cons header headers ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    refine ih (.const hordered (htypes header (by simp)) hstep) ?_ hrest
    intro remaining hmem
    exact (htypes remaining (by simp [hmem])).mono (addConst_le hstep)

def boolInductDecl : VInductDecl := {
  uvars := 0
  nparams := 0
  types := [{
    name := ``Bool
    uvars := 0
    type := .sort (.succ .zero)
    ctors := [
      { name := ``Bool.false, uvars := 0, type := .const ``Bool [] },
      { name := ``Bool.true, uvars := 0, type := .const ``Bool [] }]
  }]
}

def natInductDecl : VInductDecl := {
  uvars := 0
  nparams := 0
  types := [{
    name := ``Nat
    uvars := 0
    type := .sort (.succ .zero)
    ctors := [
      { name := ``Nat.zero, uvars := 0, type := .const ``Nat [] },
      { name := ``Nat.succ, uvars := 0,
        type := .forallE (.const ``Nat []) (.const ``Nat []) }]
  }]
}

theorem boolInductDecl.headersWF : boolInductDecl.HeadersWF env := by
  intro header hmem
  simp only [boolInductDecl, List.mem_singleton] at hmem
  subst header
  exact ⟨rfl, ⟨_, .sort trivial⟩⟩

theorem natInductDecl.headersWF : natInductDecl.HeadersWF env := by
  intro header hmem
  simp only [natInductDecl, List.mem_singleton] at hmem
  subst header
  exact ⟨rfl, ⟨_, .sort trivial⟩⟩

end Lean4Lean
