import Lean4Lean.Verify.InductiveNestedScope

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem ParamContext.params_eq_fvars {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params) :
    params = (lctx.toList.reverse.map (fun decl => Expr.fvar decl.fvarId)).toArray := by
  apply Array.toList_inj.mp
  change params.toList = lctx.toList.reverse.map LocalDecl.toExpr
  rw [List.map_reverse, hcontext.decls, List.reverse_reverse]

theorem ParamContext.abstract_range {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params) (type : Expr) :
    (type.abstract params).looseBVarRange' ≤ max type.looseBVarRange' numParams := by
  have hparams : params = ((lctx.toList.reverse.map LocalDecl.fvarId).map Expr.fvar).toArray := by
    rw [List.map_map]
    exact hcontext.params_eq_fvars
  rw [hparams, Expr.abstract_eq]
  simpa only [Nat.zero_add, List.length_map, List.length_reverse, hcontext.length] using
    Expr.abstractFVars_looseBVarRange type (lctx.toList.reverse.map LocalDecl.fvarId) 0

theorem ParamContext.abstract_scopedRange {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params) (type : Expr)
    (htype : type.looseBVarRange' = 0) :
    (type.abstract params).looseBVarRange' ≤ numParams := by
  simpa only [htype, Nat.zero_max] using hcontext.abstract_range type

theorem replaceParams.eq_ok (params : Array Expr) (type : Expr) (sourceParams : Array Expr)
    (env : Environment) (state : State) (hsize : sourceParams.size = params.size) :
    replaceParams params type sourceParams env state =
      .ok ((type.abstract sourceParams).instantiateRev params, state) := by
  simp only [replaceParams, hsize, beq_self_eq_true]
  rfl

theorem replaceParams.noLooseBVars (numParams : Nat) (source target : LocalContext)
    (sourceParams params : Array Expr) (type : Expr) (env : Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamContext numParams target params) (htype : type.looseBVarRange' = 0) :
    (replaceParams params type sourceParams env state).WF fun result =>
      result.1.looseBVarRange' = 0 ∧ result.2 = state := by
  rw [replaceParams.eq_ok params type sourceParams env state
    (hsource.size.trans htarget.size.symm)]
  apply Except.WF.pure
  exact ⟨openParams_noLooseBVars _ params
    (htarget.size.symm ▸ hsource.abstract_scopedRange type htype)
    htarget.params_noLooseBVars, rfl⟩

theorem replaceParams.auxRange (numParams : Nat) (source target : LocalContext)
    (sourceParams params : Array Expr) (type : Expr) (env : Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamContext numParams target params) (htype : type.looseBVarRange' = 0) :
    (replaceParams params type sourceParams env state).WF fun result =>
      (result.1.abstract params).looseBVarRange' ≤ numParams :=
  (replaceParams.noLooseBVars numParams source target sourceParams params type env state
    hsource htarget htype).mono fun result hscope =>
      htarget.abstract_scopedRange result.1 hscope.1

theorem replaceParams.finalAux_scope (result : Result) (numParams : Nat)
    (source : LocalContext) (sourceParams : Array Expr) (type : Expr)
    (env : Environment) (state : State) (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamValidity numParams result.lctx result.params)
    (htype : type.looseBVarRange' = 0) :
    (replaceParams result.params type sourceParams env state).WF fun returned =>
      (result.openAux (returned.1.abstract result.params)).hasLooseBVars = false :=
  (replaceParams.auxRange numParams source result.lctx sourceParams result.params type env state
    hsource htarget.context htype).mono fun _ hrange =>
      result.openAux_scopeFlag numParams _ htarget hrange

end Lean4Lean.ElimNestedInductive
