import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

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

theorem VEnv.addConst.defeqs_eq
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

theorem VEnv.addInductHeaders.wf
    (henv : env.WF) (htypes : ∀ header ∈ headers, header.toVConstant.WF env)
    (hadd : env.addInductHeaders headers = some env') : env'.WF := by
  induction headers generalizing env env' with
  | nil => cases hadd; exact henv
  | cons header headers ih =>
    obtain ⟨nextEnv, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    have hheader : header.toVConstant.WF env := htypes header (by simp)
    obtain ⟨decls, hdecls⟩ := henv
    have hnext : nextEnv.WF := by
      exact ⟨_, .decl (.axiom hheader hstep) hdecls⟩
    apply ih hnext
    · intro remaining hmem
      exact (htypes remaining (by simp [hmem])).mono (addConst_le hstep)
    · exact hrest

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

theorem boolInductDecl.constructorWF {env : VEnv}
    (hadd : VEnv.empty.addInductHeaders boolInductDecl.types = some env) :
    ∀ ctor ∈ boolInductDecl.types.flatMap (fun type => type.ctors),
      ctor.toVConstant.WF env := by
  have hbool := VEnv.addInductHeaders.constants hadd
    (header := boolInductDecl.types[0]) (by simp [boolInductDecl])
  intro ctor hmem
  simp [boolInductDecl] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨_, .const hbool (by simp) rfl⟩
  · exact ⟨_, .const hbool (by simp) rfl⟩

theorem natInductDecl.constructorWF {env : VEnv}
    (hadd : VEnv.empty.addInductHeaders natInductDecl.types = some env) :
    ∀ ctor ∈ natInductDecl.types.flatMap (fun type => type.ctors),
      ctor.toVConstant.WF env := by
  have hnat := VEnv.addInductHeaders.constants hadd
    (header := natInductDecl.types[0]) (by simp [natInductDecl])
  have hnatType (ctx : List VExpr) : env.IsType 0 ctx (.const ``Nat []) :=
    ⟨_, .const hnat (by simp) rfl⟩
  intro ctor hmem
  simp [natInductDecl] at hmem
  rcases hmem with rfl | rfl
  · exact hnatType []
  · exact .forallE (hnatType []) (hnatType [_])

end Lean4Lean
