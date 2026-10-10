import Lean4Lean.Verify.InductiveParamScope

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem run.paramsValid (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result =>
      result.1.nparams = numParams ∧ ParamValidity numParams result.1.lctx result.1.params := by
  cases types with
  | nil => exact Except.WF.throw
  | cons type types =>
    unfold run
    apply withParams.validContext
    intro lctx remainder params state' hvalid _
    refine (run.loop.frameWithParams numParams lctx params 0 fuel env state').mono ?_
    intro result hframe
    exact ⟨hframe.1.trans hvalid.context.size,
      hframe.2.1.symm ▸ hframe.2.2.symm ▸ hvalid⟩

theorem run.paramsValid_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      result.nparams = numParams ∧ ParamValidity numParams result.lctx result.params :=
  (run.paramsValid fuel numParams types env state).map fun _ hvalid => hvalid

theorem ParamContext.params_noLooseBVars {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params) :
    ∀ param ∈ params, param.looseBVarRange' = 0 := by
  intro param hparam
  rcases hcontext.declaration hparam with ⟨decl, _, hexpr, _⟩
  rw [← hexpr]
  rfl

theorem openParams_noLooseBVars (type : Expr) (params : Array Expr)
    (htype : type.looseBVarRange' ≤ params.size)
    (hparams : ∀ param ∈ params, param.looseBVarRange' = 0) :
    (type.instantiateRev params).looseBVarRange' = 0 := by
  rw [Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply Nat.eq_zero_of_le_zero
  apply Expr.instantiateMany_looseBVarRange (bound := 0) (depth := 0)
  · simpa using htype
  · intro param hparam
    have hmem : param ∈ params := by simpa using hparam
    simpa only [hparams param hmem] using Nat.le_refl 0

theorem Result.openAux_noLooseBVars (result : Result) (numParams : Nat) (type : Expr)
    (hvalid : ElimNestedInductive.ParamValidity numParams result.lctx result.params)
    (htype : type.looseBVarRange' ≤ numParams) :
    (result.openAux type).looseBVarRange' = 0 :=
  openParams_noLooseBVars type result.params (hvalid.context.size.symm ▸ htype)
    hvalid.context.params_noLooseBVars

theorem Result.openAux_scopeFlag (result : Result) (numParams : Nat) (type : Expr)
    (hvalid : ElimNestedInductive.ParamValidity numParams result.lctx result.params)
    (htype : type.looseBVarRange' ≤ numParams) :
    (result.openAux type).hasLooseBVars = false :=
  noLooseBVars_flag _ (result.openAux_noLooseBVars numParams type hvalid htype)

theorem run.openAux_scope (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      ∀ type, type.looseBVarRange' ≤ numParams → (result.openAux type).looseBVarRange' = 0 :=
  (run.paramsValid_run' fuel numParams types env state).mono fun result hvalid type htype =>
    result.openAux_noLooseBVars numParams type hvalid.2 htype

end Lean4Lean.ElimNestedInductive
