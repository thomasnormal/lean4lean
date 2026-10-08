import Lean4Lean.Verify.InductiveParamBinding
import Lean4Lean.Verify.InductiveParamScope

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

def SourceReserved (type : Expr) (ngen : NameGenerator) : Prop :=
  ∀ fvar ∈ type.fvarsList, ngen.Reserves fvar

theorem SourceReserved.noFVars (type : Expr) (ngen : NameGenerator)
    (hfvars : type.hasFVar = false) : SourceReserved type ngen := by
  intro fvar hmem
  rw [fvarsList_eq_nil.mpr hfvars] at hmem
  cases hmem

theorem SourceReserved.current_fresh {type : Expr} {ngen : NameGenerator}
    (hreserved : SourceReserved type ngen) : ⟨ngen.curr⟩ ∉ type.fvarsList :=
  fun hmem => NameGenerator.not_reserves_self (hreserved _ hmem)

theorem instantiate1_fvar_mem (type : Expr) (id : FVarId) (depth : Nat) :
    ∀ fvar ∈ (type.instantiate1' (.fvar id) depth).fvarsList,
      fvar = id ∨ fvar ∈ type.fvarsList := by
  induction type generalizing depth with
  | bvar index =>
    simp only [Expr.instantiate1']
    split <;> [skip; split] <;> simp [Expr.fvarsList, Expr.liftLooseBVars', *]
  | _ => simp_all [Expr.instantiate1', Expr.fvarsList] <;> grind

theorem SourceReserved.instantiate1_current {body : Expr} {ngen : NameGenerator}
    (hreserved : SourceReserved body ngen) :
    SourceReserved (body.instantiate1 (.fvar ⟨ngen.curr⟩)) ngen.next := by
  intro fvar hmem
  rw [Expr.instantiate1_eq] at hmem
  rcases instantiate1_fvar_mem body ⟨ngen.curr⟩ 0 fvar hmem with rfl | hmem
  · exact NameGenerator.next_reserves_self
  · exact NameGenerator.Reserves.mono .next (hreserved fvar hmem)

theorem abstract_instantiate1_fresh (type : Expr) (id : FVarId) (depth : Nat)
    (hfresh : id ∉ type.fvarsList) :
    (type.instantiate1' (.fvar id) depth).abstract1 id depth = type := by
  induction type generalizing depth with
    simp_all [Expr.instantiate1', Expr.abstract1, Expr.fvarsList]
  | bvar index =>
    split <;> [skip; split]
    · simp [Expr.abstract1, *]
    · simp [Expr.abstract1, Expr.liftLooseBVars', *]
    · obtain _ | index := index <;> simp [Expr.abstract1] <;> omega

def reconstructParams (decls : List LocalDecl) (body : Expr) : Expr :=
  decls.foldl (fun result decl =>
    .forallE decl.userName decl.type (result.abstract1 decl.fvarId) decl.binderInfo) body

theorem ParamValidity.bindingScope {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    (hscope : ContextNoLooseBVars lctx) : lctx.BindingScope := by
  intro fvar decl hlookup
  rw [hvalid.wf.find?_eq_find?_toList] at hlookup
  have hmem := List.mem_of_find?_eq_some hlookup
  refine ⟨hscope decl hmem, ?_⟩
  intro value hvalue
  rw [(hvalid.context.binders decl hmem).1] at hvalue
  cases hvalue

theorem ParamValidity.mkForall_reconstruct {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    (hscope : ContextNoLooseBVars lctx) (body : Expr) (hbody : body.looseBVarRange' = 0) :
    lctx.mkForall params body = reconstructParams lctx.toList body := by
  let ids := lctx.toList.reverse.map LocalDecl.fvarId
  have hnodup : ids.Nodup := by
    simpa only [ids, List.map_reverse] using List.nodup_reverse.mpr hvalid.wf.nodup
  have hparams : params = (ids.map Expr.fvar).toArray := by
    have hvars : lctx.toList.reverse.map LocalDecl.toExpr = params.toList := by
      rw [List.map_reverse, hvalid.context.decls, List.reverse_reverse]
    simp only [ids, List.map_map]
    change params = (lctx.toList.reverse.map LocalDecl.toExpr).toArray
    rw [hvars, Array.toArray_toList]
  have hlookup : ∀ id ∈ ids, ∃ decl, lctx.find? id = some decl := by
    intro id hmem
    rcases List.mem_map.mp hmem with ⟨decl, hdecl, rfl⟩
    exact ⟨decl, hvalid.find?_eq (List.mem_reverse.mp hdecl)⟩
  rw [hparams]
  change lctx.mkBinding false (ids.map Expr.fvar).toArray body = _
  rw [LocalContext.mkBinding_eq hbody (hvalid.bindingScope hscope) hnodup,
    LocalContext.mkBindingList_eq_fold hlookup hnodup]
  simp only [ids, List.foldr_map, List.foldr_reverse, reconstructParams]
  apply List.foldl_congr
  intro result decl hdecl
  rw [LocalContext.mkBindingList1, hvalid.find?_eq hdecl]
  have hshape := (hvalid.context.binders decl hdecl).1
  cases decl with
  | cdecl => rfl
  | ldecl index id name domain value nondep kind => cases nondep <;> cases hshape

private theorem withParams_loop_reconstruct (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Environment) (state : State) (post : ResultType × State → Prop)
    (hreserved : SourceReserved type state.ngen)
    (hnext : ∀ lctx' remainder params' state',
      reconstructParams lctx'.toList remainder = reconstructParams lctx.toList type →
      (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero => exact hnext lctx type params state rfl
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      have hbody : SourceReserved body state.ngen := by
        intro fvar hmem
        exact hreserved fvar (List.mem_append_right _ hmem)
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      apply ih _ _ _ _ hbody.instantiate1_current
      intro lctx' remainder params' state' hreconstruct
      apply hnext lctx' remainder params' state'
      rw [hreconstruct, LocalContext.mkLocalDecl_toList]
      simp only [reconstructParams, List.foldl_cons, LocalDecl.userName, LocalDecl.type,
        LocalDecl.fvarId, LocalDecl.binderInfo, Expr.instantiate1_eq,
        abstract_instantiate1_fresh body _ 0 hbody.current_fresh]
    | _ => exact Except.WF.throw

theorem withParams.reconstruct (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Environment) (state : State) (post : ResultType × State → Prop)
    (hreserved : SourceReserved type state.ngen)
    (hnext : ∀ lctx remainder params state', reconstructParams lctx.toList remainder = type →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  apply withParams_loop_reconstruct numParams type {} #[] next env state post hreserved
  intro lctx remainder params state' hreconstruct
  have hnil : ({} : LocalContext).toList = [] :=
    List.eq_nil_of_length_eq_zero ParamContext.empty.length
  exact hnext lctx remainder params state' (by
    simpa only [hnil, reconstructParams, List.foldl_nil] using hreconstruct)

theorem withParams.getReconstruction (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (hscope : type.looseBVarRange' = 0)
    (hreserved : SourceReserved type state.ngen) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.mkForall result.1.2.2 result.1.2.1 = type := by
  have hreconstruct := withParams.reconstruct type numParams
    (fun lctx remainder params => pure (lctx, remainder, params)) env state
    (fun result => reconstructParams result.1.1.toList result.1.2.1 = type)
    hreserved (fun _ _ _ _ heq => .pure heq)
  intro result hresult
  have hcontext := withParams.getScopedContext type numParams env state hscope result hresult
  exact (hcontext.1.mkForall_reconstruct hcontext.2.1 _ hcontext.2.2).trans
    (hreconstruct result hresult)

theorem withParams.getReconstruction_noFVars (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (hscope : type.looseBVarRange' = 0)
    (hfvars : type.hasFVar = false) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.mkForall result.1.2.2 result.1.2.1 = type :=
  withParams.getReconstruction type numParams env state hscope
    (SourceReserved.noFVars type state.ngen hfvars)

private theorem withParams_loop_extract (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Environment) (state : State) :
    withParams.loop next lctx type params remaining env state =
      ((withParams.loop (fun lctx remainder params => pure (lctx, remainder, params))
        lctx type params remaining >>= fun result => next result.1 result.2.1 result.2.2)
        env state) := by
  induction remaining generalizing type lctx params state with
  | zero => rfl
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      exact ih (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (params.push (.fvar ⟨state.ngen.curr⟩)) { state with ngen := state.ngen.next }
    | _ => rfl

theorem withParams.sourceReconstruction (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Environment) (state : State) (post : ResultType × State → Prop)
    (hscope : type.looseBVarRange' = 0) (hreserved : SourceReserved type state.ngen)
    (hnext : ∀ lctx remainder params state', lctx.mkForall params remainder = type →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  rw [show withParams type numParams next env state = _ from
    withParams_loop_extract numParams type {} #[] next env state]
  exact (withParams.getReconstruction type numParams env state hscope hreserved).bind
    fun result heq => hnext result.1.1 result.1.2.1 result.1.2.2 result.2 heq

theorem withParams.mkForall_source (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) (hscope : type.looseBVarRange' = 0)
    (hreserved : SourceReserved type state.ngen) :
    (withParams type numParams (fun lctx remainder params => pure (lctx.mkForall params remainder))
      env state).WF fun result => result.1 = type :=
  withParams.sourceReconstruction type numParams _ env state _ hscope hreserved
    fun _ _ _ _ heq => .pure heq

end Lean4Lean.ElimNestedInductive
