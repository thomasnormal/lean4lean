import Lean4Lean.Theory.InductiveHeaders
import Lean4Lean.Verify.PrimitiveInductive

namespace Lean4Lean
open Lean hiding Environment Exception

def TrConstructor (env : VEnv) (lparams : List Name)
    (ctor : Constructor) (vctor : VConstVal) : Prop :=
  ctor.name = vctor.name ∧ lparams.length = vctor.uvars ∧
    TrExprS env lparams [] ctor.type vctor.type

theorem TrConstructor.mono (htr : TrConstructor env lparams ctor vctor) (hle : env ≤ env') :
    TrConstructor env' lparams ctor vctor :=
  ⟨htr.1, htr.2.1, htr.2.2.mono hle⟩

def TrInductiveType (headerEnv ctorEnv : VEnv) (lparams : List Name)
    (type : InductiveType) (vtype : VInductiveType) : Prop :=
  type.name = vtype.name ∧ lparams.length = vtype.uvars ∧
    TrExprS headerEnv lparams [] type.type vtype.type ∧
    List.Forall₂ (TrConstructor ctorEnv lparams) type.ctors vtype.ctors

def TrInductDecl (headerEnv ctorEnv : VEnv) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (decl : VInductDecl) : Prop :=
  lparams.length = decl.uvars ∧ nparams = decl.nparams ∧
    List.Forall₂ (TrInductiveType headerEnv ctorEnv lparams) types decl.types

private theorem boolInductDecl.tr (env : VEnv) {env' : VEnv}
    (hadd : env.addInductHeaders boolInductDecl.types = some env') :
    TrInductDecl env env' [] 0 [{
      name := ``Bool
      type := .sort (.succ .zero)
      ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩]
    }] boolInductDecl := by
  have hbool := VEnv.addInductHeaders.constants hadd
    (header := boolInductDecl.types[0]) (by simp [boolInductDecl])
  refine ⟨rfl, rfl, .cons ?_ .nil⟩
  refine ⟨rfl, rfl, .sort rfl, .cons ?_ (.cons ?_ .nil)⟩
  · exact ⟨rfl, rfl, .const hbool rfl rfl⟩
  · exact ⟨rfl, rfl, .const hbool rfl rfl⟩

private theorem natInductDecl.tr (env : VEnv) {env' : VEnv}
    (binderName : Name) (binderInfo : BinderInfo)
    (hadd : env.addInductHeaders natInductDecl.types = some env') :
    TrInductDecl env env' [] 0 [{
      name := ``Nat
      type := .sort (.succ .zero)
      ctors := [⟨``Nat.zero, .const ``Nat []⟩,
        ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]
    }] natInductDecl := by
  have hnat := VEnv.addInductHeaders.constants hadd
    (header := natInductDecl.types[0]) (by simp [natInductDecl])
  have hnatType (ctx : List VExpr) : env'.IsType 0 ctx (.const ``Nat []) :=
    ⟨.succ .zero, .const hnat nofun rfl⟩
  refine ⟨rfl, rfl, .cons ?_ .nil⟩
  refine ⟨rfl, rfl, .sort rfl, .cons ?_ (.cons ?_ .nil)⟩
  · exact ⟨rfl, rfl, .const hnat rfl rfl⟩
  · exact ⟨rfl, rfl, .forallE (hnatType []) (hnatType [_])
      (.const hnat rfl rfl) (.const hnat rfl rfl)⟩

theorem Environment.PrimitiveInductiveDecl.toVDecl
    (hdecl : PrimitiveInductiveDecl lparams nparams types isUnsafe) (env : VEnv) :
    ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧ decl.HeadersWF env ∧
      ∀ env', env.addInductHeaders decl.types = some env' →
        TrInductDecl env env' lparams nparams types decl := by
  cases hdecl with
  | bool =>
    exact ⟨boolInductDecl, .inl rfl, boolInductDecl.headersWF, fun env' => boolInductDecl.tr env⟩
  | nat binderName binderInfo =>
    exact ⟨natInductDecl, .inr rfl, natInductDecl.headersWF,
      fun env' => natInductDecl.tr env binderName binderInfo⟩

private theorem boolConstructorUvars (ctor : VConstVal)
    (hmem : ctor ∈ boolInductDecl.constructorHeaders) :
    ctor.uvars = boolInductDecl.uvars := by
  change ctor ∈ ([
    { name := ``Bool.false, uvars := 0, type := .const ``Bool [] },
    { name := ``Bool.true, uvars := 0, type := .const ``Bool [] }
  ] : List VConstVal) at hmem
  simp at hmem
  rcases hmem with rfl | rfl <;> rfl

private theorem natConstructorUvars (ctor : VConstVal)
    (hmem : ctor ∈ natInductDecl.constructorHeaders) :
    ctor.uvars = natInductDecl.uvars := by
  change ctor ∈ ([
    { name := ``Nat.zero, uvars := 0, type := .const ``Nat [] },
    { name := ``Nat.succ, uvars := 0, type := .forallE (.const ``Nat []) (.const ``Nat []) }
  ] : List VConstVal) at hmem
  simp at hmem
  rcases hmem with rfl | rfl <;> rfl

private theorem boolInductDecl.wf (env : VEnv) : boolInductDecl.WF env := by
  refine ⟨boolInductDecl.headersWF, ?_⟩
  intro env' hadd ctor hmem
  exact ⟨boolConstructorUvars ctor hmem, boolInductDecl.constructorWF hadd ctor hmem⟩

private theorem natInductDecl.wf (env : VEnv) : natInductDecl.WF env := by
  refine ⟨natInductDecl.headersWF, ?_⟩
  intro env' hadd ctor hmem
  exact ⟨natConstructorUvars ctor hmem,
    natInductDecl.constructorWF hadd ctor hmem⟩

theorem Environment.PrimitiveInductiveDecl.toVDecl_WF
    (hdecl : PrimitiveInductiveDecl lparams nparams types isUnsafe) (env : VEnv) :
    ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧ decl.HeadersWF env ∧
      decl.WF env ∧
      ∀ env', env.addInductHeaders decl.types = some env' →
        TrInductDecl env env' lparams nparams types decl := by
  obtain ⟨decl, hkind, hheaders, htr⟩ := hdecl.toVDecl env
  refine ⟨decl, hkind, hheaders, ?_, htr⟩
  rcases hkind with rfl | rfl
  · exact boolInductDecl.wf env
  · exact natInductDecl.wf env

theorem Environment.checkPrimitiveInductive.toVDecl
    (env : Kernel.Environment) (venv : VEnv)
    (hcheck : checkPrimitiveInductive env lparams nparams types isUnsafe = .ok true) :
    ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧ decl.HeadersWF venv ∧
      ∀ venv', venv.addInductHeaders decl.types = some venv' →
        TrInductDecl venv venv' lparams nparams types decl :=
  ((checkPrimitiveInductive.eq_true_iff env lparams nparams types isUnsafe).mp hcheck).toVDecl venv

theorem Environment.checkPrimitiveInductive.toVDecl_WF
    (env : Kernel.Environment) (venv : VEnv)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    (checkPrimitiveInductive env lparams nparams types isUnsafe).WF fun isPrimitive =>
      isPrimitive = true → ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧
        ∀ venv', venv.addInductHeaders decl.types = some venv' →
          TrInductDecl venv venv' lparams nparams types decl := by
  intro isPrimitive result
  intro hprimitive
  have checked : checkPrimitiveInductive env lparams nparams types isUnsafe = .ok true := by
    simpa [hprimitive] using result
  exact checkPrimitiveInductive.toVDecl env venv checked

theorem Environment.checkPrimitiveInductive.toVDecl_WF_model
    (env : Kernel.Environment) (venv : VEnv)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    (checkPrimitiveInductive env lparams nparams types isUnsafe).WF fun isPrimitive =>
      isPrimitive = true → ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧ decl.WF venv ∧
        ∀ venv', venv.addInductHeaders decl.types = some venv' →
          TrInductDecl venv venv' lparams nparams types decl := by
  intro isPrimitive result hprimitive
  have checked : checkPrimitiveInductive env lparams nparams types isUnsafe = .ok true := by
    simpa [hprimitive] using result
  exact (checkPrimitiveInductive.eq_true_iff env lparams nparams types isUnsafe).mp checked |>.toVDecl_WF venv

end Lean4Lean
