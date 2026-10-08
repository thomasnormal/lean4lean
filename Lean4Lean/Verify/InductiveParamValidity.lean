import Lean4Lean.Verify.InductiveParams
import Lean4Lean.Verify.NameGenerator

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

def ContextReserved (lctx : LocalContext) (ngen : NameGenerator) : Prop :=
  ∀ decl ∈ lctx.toList, ngen.Reserves decl.fvarId

theorem ContextReserved.empty (ngen : NameGenerator) : ContextReserved {} ngen := by
  intro decl hdecl
  have hmem : decl.toExpr ∈ ({} : LocalContext).toList.map LocalDecl.toExpr :=
    List.mem_map.mpr ⟨decl, hdecl, rfl⟩
  rw [ParamContext.empty.decls] at hmem
  simp at hmem

theorem ContextReserved.fresh {lctx : LocalContext} {ngen : NameGenerator}
    (hreserved : ContextReserved lctx ngen) (hwf : lctx.WF) :
    lctx.find? ⟨ngen.curr⟩ = none := by
  rw [hwf.find?_eq_find?_toList, List.find?_eq_none]
  intro decl hdecl
  simp only [beq_iff_eq]
  intro heq
  exact NameGenerator.not_reserves_self (heq.symm ▸ hreserved decl hdecl)

theorem ContextReserved.push_current {lctx : LocalContext} {ngen : NameGenerator}
    (hreserved : ContextReserved lctx ngen) (name : Name) (domain : Expr) (bi : BinderInfo) :
    ContextReserved (lctx.mkLocalDecl ⟨ngen.curr⟩ name domain bi) ngen.next := by
  intro decl hdecl
  simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
  rcases hdecl with rfl | hdecl
  · exact NameGenerator.next_reserves_self
  · exact NameGenerator.Reserves.mono .next (hreserved decl hdecl)

structure ParamValidity (numParams : Nat) (lctx : LocalContext) (params : Array Expr) : Prop where
  context : ParamContext numParams lctx params
  wf : lctx.WF

theorem ParamValidity.empty : ParamValidity 0 {} #[] :=
  ⟨ParamContext.empty, .nil⟩

theorem ParamValidity.push_current {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    {ngen : NameGenerator} (hvalid : ParamValidity numParams lctx params)
    (hreserved : ContextReserved lctx ngen) (name : Name) (domain : Expr) (bi : BinderInfo) :
    ParamValidity (numParams + 1) (lctx.mkLocalDecl ⟨ngen.curr⟩ name domain bi)
      (params.push (.fvar ⟨ngen.curr⟩)) :=
  ⟨hvalid.context.push ⟨ngen.curr⟩ name domain bi,
    hvalid.wf.mkLocalDecl (hreserved.fresh hvalid.wf)⟩

theorem ParamValidity.nodup {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) : params.toList.Nodup := by
  have hnodup : (lctx.toList.map LocalDecl.toExpr).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.pairwise_map.mp hvalid.wf.nodup).imp fun hne heq =>
      hne (Expr.fvar.inj heq)
  rw [hvalid.context.decls] at hnodup
  exact List.nodup_reverse.mp hnodup

theorem ParamValidity.find?_eq {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) {decl : LocalDecl} (hdecl : decl ∈ lctx.toList) :
    lctx.find? decl.fvarId = some decl := by
  have hkeys : (lctx.toList.map fun entry => (entry.fvarId, entry)).NodupKeys := by
    simpa [List.NodupKeys, List.map_map] using hvalid.wf.nodup
  rw [hvalid.wf.find?_eq_find?_toList, ← List.map_fst_lookup]
  exact hkeys.lookup_eq_some.mpr (List.mem_map.mpr ⟨decl, hdecl, rfl⟩)

theorem ParamValidity.parameterLookup {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    {fvar : FVarId} (hparam : Expr.fvar fvar ∈ params) :
    ∃ decl, lctx.find? fvar = some decl ∧ decl.toExpr = .fvar fvar ∧
      decl.value? (allowNondep := true) = none ∧ decl.kind = .default := by
  rcases hvalid.context.declaration hparam with ⟨decl, hdecl, hexpr, hshape⟩
  have hid : decl.fvarId = fvar := Expr.fvar.inj hexpr
  exact ⟨decl, hid ▸ hvalid.find?_eq hdecl, hexpr, hshape⟩

private theorem context_indices {lctx : LocalContext} (hwf : lctx.WF) :
    lctx.toList.reverse.map LocalDecl.index = List.range lctx.numIndices := by
  induction hwf with
  | nil => rfl
  | cons hid hlookup hindex hwf ih =>
    simp [LocalContext.toList, LocalContext.numIndices, hindex, List.range_succ] at ih ⊢
    exact ih

theorem ParamValidity.indices {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) :
    lctx.toList.reverse.map LocalDecl.index = List.range numParams := by
  simpa only [hvalid.context.count] using context_indices hvalid.wf

theorem ParamValidity.declarationAt {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) (index : Nat) (hindex : index < params.size) :
    ∃ decl, lctx.toList.reverse[index]? = some decl ∧ decl.index = index ∧
      decl.toExpr = params[index] ∧ decl.value? (allowNondep := true) = none ∧
      decl.kind = .default := by
  have hnum : index < numParams := by simpa only [hvalid.context.size] using hindex
  have hlist : index < lctx.toList.reverse.length := by
    simpa only [List.length_reverse, hvalid.context.length] using hnum
  let decl := lctx.toList.reverse[index]'hlist
  have hposition : lctx.toList.reverse[index]? = some decl := List.getElem?_eq_getElem hlist
  have hdeclindex := congrArg (fun entries => entries[index]?) hvalid.indices
  simp only [List.getElem?_map, hposition, Option.map_some, List.getElem?_range hnum,
    Option.some.injEq] at hdeclindex
  have hvars : lctx.toList.reverse.map LocalDecl.toExpr = params.toList := by
    rw [List.map_reverse, hvalid.context.decls, List.reverse_reverse]
  have hexpr := congrArg (fun entries => entries[index]?) hvars
  simp only [List.getElem?_map, hposition, Option.map_some, Array.getElem?_toList,
    Array.getElem?_eq_getElem hindex, Option.some.injEq] at hexpr
  have hmem : decl ∈ lctx.toList := List.mem_reverse.mp (List.getElem_mem hlist)
  exact ⟨decl, hposition, hdeclindex, hexpr, hvalid.context.binders decl hmem⟩

theorem ParamValidity.parameterLookupAt {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    (index : Nat) (hindex : index < params.size) :
    ∃ decl, lctx.findFVar? params[index] = some decl ∧ decl.index = index ∧
      decl.toExpr = params[index] ∧ decl.value? (allowNondep := true) = none ∧
      decl.kind = .default := by
  rcases hvalid.declarationAt index hindex with ⟨decl, hposition, hdeclindex, hexpr, hshape⟩
  have hmem : decl ∈ lctx.toList := List.mem_reverse.mp (List.mem_of_getElem? hposition)
  refine ⟨decl, ?_, hdeclindex, hexpr, hshape⟩
  rw [← hexpr]
  exact hvalid.find?_eq hmem

theorem ParamValidity.getFVar!_index {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) (index : Nat) (hindex : index < params.size) :
    (lctx.getFVar! params[index]).index = index := by
  rcases hvalid.parameterLookupAt index hindex with ⟨decl, hlookup, hdeclindex, _⟩
  simp only [LocalContext.findFVar?] at hlookup
  simp only [LocalContext.getFVar!, LocalContext.get!, hlookup, hdeclindex]

def IndexedParamLookup (numParams : Nat) (lctx : LocalContext) (params : Array Expr) : Prop :=
  params.size = numParams ∧ ∀ (index : Nat) (hindex : index < params.size),
    ∃ decl, lctx.findFVar? params[index] = some decl ∧ decl.index = index ∧
      decl.toExpr = params[index] ∧ decl.value? (allowNondep := true) = none ∧ decl.kind = .default

theorem ParamValidity.indexedLookup {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) : IndexedParamLookup numParams lctx params :=
  ⟨hvalid.context.size, hvalid.parameterLookupAt⟩

private theorem withParams_loop_validContext (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hvalid : ParamValidity params.size lctx params)
    (hreserved : ContextReserved lctx state.ngen)
    (hnext : ∀ lctx' remainder params' state',
      ParamValidity (params.size + remaining) lctx' params' →
      ContextReserved lctx' state'.ngen → (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero => exact hnext lctx type params state (by simpa using hvalid) hreserved
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      apply ih
      · simpa using hvalid.push_current hreserved name domain bi
      · exact hreserved.push_current name domain bi
      · intro lctx' remainder params' state' hvalid' hreserved'
        apply hnext lctx' remainder params' state'
        · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid'
        · exact hreserved'
    | _ => exact Except.WF.throw

theorem withParams.validContext (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamValidity numParams lctx params →
      ContextReserved lctx state'.ngen → (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  apply withParams_loop_validContext
  · exact ParamValidity.empty
  · exact ContextReserved.empty state.ngen
  · intro lctx remainder params state' hvalid hreserved
    exact hnext lctx remainder params state' (by simpa using hvalid) hreserved

theorem withParams.getValidContext (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamValidity numParams result.1.1 result.1.2.2 ∧
        ContextReserved result.1.1 result.2.ngen :=
  withParams.validContext type numParams _ env state _ fun _ _ _ _ hvalid hreserved =>
    .pure ⟨hvalid, hreserved⟩

theorem withParams.getIndexedLookup (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => IndexedParamLookup numParams result.1.1 result.1.2.2 :=
  (withParams.getValidContext type numParams env state).mono fun _ hvalid => hvalid.1.indexedLookup

def Result.ParamValidity (numParams : Nat) (result : Result) : Prop :=
  result.nparams = numParams ∧ ∃ params, ElimNestedInductive.ParamValidity numParams result.lctx params

theorem run.paramValidity (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result => result.1.ParamValidity numParams := by
  cases types with
  | nil => exact Except.WF.throw
  | cons type types =>
    unfold run
    apply withParams.validContext
    intro lctx remainder params state' hvalid _
    refine (run.loop.frame numParams lctx params 0 fuel env state').mono ?_
    intro result hframe
    exact ⟨hframe.1.trans hvalid.context.size, params, hframe.2.symm ▸ hvalid⟩

theorem run.contextWF (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result => result.1.lctx.WF :=
  (run.paramValidity fuel numParams types env state).mono fun _ hvalid => by
    rcases hvalid.2 with ⟨params, hparams⟩
    exact hparams.wf

theorem run.contextLookup (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result =>
      ∀ decl ∈ result.1.lctx.toList, result.1.lctx.find? decl.fvarId = some decl :=
  (run.paramValidity fuel numParams types env state).mono fun _ hvalid => by
    rcases hvalid.2 with ⟨params, hparams⟩
    exact fun _ hdecl => hparams.find?_eq hdecl

theorem run.paramValidity_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      result.ParamValidity numParams :=
  (run.paramValidity fuel numParams types env state).map fun _ hvalid => hvalid

def Result.IndexedParamLookup (numParams : Nat) (result : Result) : Prop :=
  result.nparams = numParams ∧ ∃ params, ElimNestedInductive.IndexedParamLookup numParams result.lctx params

theorem run.indexedLookup (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result => result.1.IndexedParamLookup numParams :=
  (run.paramValidity fuel numParams types env state).mono fun _ hvalid => by
    rcases hvalid.2 with ⟨params, hparams⟩
    exact ⟨hvalid.1, params, hparams.indexedLookup⟩

theorem run.indexedLookup_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      result.IndexedParamLookup numParams :=
  (run.indexedLookup fuel numParams types env state).map fun _ hlookup => hlookup

end Lean4Lean.ElimNestedInductive
