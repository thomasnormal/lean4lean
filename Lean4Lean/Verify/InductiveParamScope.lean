import Lean4Lean.Verify.InductiveParamValidity

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

def ContextNoLooseBVars (lctx : LocalContext) : Prop :=
  ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' = 0

theorem ContextNoLooseBVars.empty : ContextNoLooseBVars {} := by
  intro decl hdecl
  have hmem : decl.toExpr ∈ ({} : LocalContext).toList.map LocalDecl.toExpr :=
    List.mem_map.mpr ⟨decl, hdecl, rfl⟩
  rw [ParamContext.empty.decls] at hmem
  simp at hmem

theorem ContextNoLooseBVars.mkLocalDecl {lctx : LocalContext}
    (hscope : ContextNoLooseBVars lctx) (fvar : FVarId) (name : Name) (domain : Expr)
    (bi : BinderInfo) (hdomain : domain.looseBVarRange' = 0) :
    ContextNoLooseBVars (lctx.mkLocalDecl fvar name domain bi) := by
  intro decl hdecl
  simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
  rcases hdecl with rfl | hdecl
  · exact hdomain
  · exact hscope decl hdecl

theorem instantiate1_fvar_noLooseBVars (body : Expr) (fvar : FVarId)
    (hbody : body.looseBVarRange' ≤ 1) :
    (body.instantiate1 (.fvar fvar)).looseBVarRange' = 0 := by
  rw [Expr.instantiate1_eq]
  apply Nat.eq_zero_of_le_zero
  exact Expr.instantiate1'_looseBVarRange (n := 0) (k := 0) hbody (Nat.le_refl 0)

theorem noLooseBVars_flag (type : Expr) (hscope : type.looseBVarRange' = 0) :
    type.hasLooseBVars = false := by
  simp only [Expr.hasLooseBVars, Expr.looseBVarRange_eq, hscope]
  rfl

theorem ParamValidity.parameterScopeAt {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    (hscope : ContextNoLooseBVars lctx) (index : Nat) (hindex : index < params.size) :
    (lctx.getFVar! params[index]).type.looseBVarRange' = 0 := by
  rcases hvalid.declarationAt index hindex with ⟨decl, hposition, _, hexpr, _⟩
  have hmem : decl ∈ lctx.toList := List.mem_reverse.mp (List.mem_of_getElem? hposition)
  have hlookup : lctx.findFVar? params[index] = some decl := by
    rw [← hexpr]
    exact hvalid.find?_eq hmem
  simp only [LocalContext.findFVar?] at hlookup
  simpa only [LocalContext.getFVar!, LocalContext.get!, hlookup] using hscope decl hmem

private theorem withParams_loop_noLooseBVars (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (htype : type.looseBVarRange' = 0) (hscope : ContextNoLooseBVars lctx)
    (hnext : ∀ lctx' remainder params' state', ContextNoLooseBVars lctx' →
      remainder.looseBVarRange' = 0 → (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero => exact hnext lctx type params state hscope htype
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      have hparts : domain.looseBVarRange' = 0 ∧ body.looseBVarRange' ≤ 1 := by
        change max domain.looseBVarRange' (body.looseBVarRange' - 1) = 0 at htype
        omega
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      exact ih _ _ _ _ (instantiate1_fvar_noLooseBVars body _ hparts.2)
        (hscope.mkLocalDecl _ name domain bi hparts.1)
    | _ => exact Except.WF.throw

theorem withParams.noLooseBVars (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (htype : type.looseBVarRange' = 0)
    (hnext : ∀ lctx remainder params state', ContextNoLooseBVars lctx →
      remainder.looseBVarRange' = 0 → (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams_loop_noLooseBVars numParams type {} #[] next env state post htype
    ContextNoLooseBVars.empty hnext

theorem withParams.getScope (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ContextNoLooseBVars result.1.1 ∧
        result.1.2.1.looseBVarRange' = 0 :=
  withParams.noLooseBVars type numParams _ env state _ htype fun _ _ _ _ hscope hbody =>
    .pure ⟨hscope, hbody⟩

theorem withParams.getScopedContext (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamValidity numParams result.1.1 result.1.2.2 ∧
        ContextNoLooseBVars result.1.1 ∧ result.1.2.1.looseBVarRange' = 0 := by
  intro result hresult
  exact ⟨(withParams.getValidContext type numParams env state result hresult).1,
    withParams.getScope type numParams env state htype result hresult⟩

theorem withParams.getScopeFlags (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result =>
        (∀ decl ∈ result.1.1.toList, decl.type.hasLooseBVars = false) ∧
          result.1.2.1.hasLooseBVars = false :=
  (withParams.getScope type numParams env state htype).mono fun _ hscope =>
    ⟨fun decl hdecl => noLooseBVars_flag decl.type (hscope.1 decl hdecl),
      noLooseBVars_flag _ hscope.2⟩

theorem run.loop.contextScope (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Environment) (state : State) (hscope : ContextNoLooseBVars lctx) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      ContextNoLooseBVars result.1.lctx :=
  (run.loop.frame numParams lctx params index fuel env state).mono fun _ hframe =>
    hframe.2.symm ▸ hscope

theorem run.contextScope (fuel numParams : Nat) (first : InductiveType)
    (rest : List InductiveType) (env : Environment) (state : State)
    (hfirst : first.type.looseBVarRange' = 0) :
    (run fuel numParams (first :: rest) env state).WF fun result =>
      ContextNoLooseBVars result.1.lctx := by
  unfold run
  apply withParams.noLooseBVars
  · exact hfirst
  · intro lctx remainder params state' hscope _
    exact run.loop.contextScope numParams lctx params 0 fuel env state' hscope

theorem run.contextScope_run' (fuel numParams : Nat) (first : InductiveType)
    (rest : List InductiveType) (env : Environment) (state : State)
    (hfirst : first.type.looseBVarRange' = 0) :
    (StateT.run' (run fuel numParams (first :: rest) env) state).WF fun result =>
      ContextNoLooseBVars result.lctx :=
  (run.contextScope fuel numParams first rest env state hfirst).map fun _ hscope => hscope

theorem run.contextScopeFlags (fuel numParams : Nat) (first : InductiveType)
    (rest : List InductiveType) (env : Environment) (state : State)
    (hfirst : first.type.looseBVarRange' = 0) :
    (run fuel numParams (first :: rest) env state).WF fun result =>
      ∀ decl ∈ result.1.lctx.toList, decl.type.hasLooseBVars = false :=
  (run.contextScope fuel numParams first rest env state hfirst).mono fun _ hscope decl hdecl =>
    noLooseBVars_flag decl.type (hscope decl hdecl)

end Lean4Lean.ElimNestedInductive
