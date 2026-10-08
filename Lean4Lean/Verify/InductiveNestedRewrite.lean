import Lean4Lean.Verify.InductiveNestedGuard

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

def State.NestedAuxScoped (state : State) : Prop :=
  ∀ entry ∈ state.nestedAux, entry.1.looseBVarRange' = 0

theorem State.NestedAuxScoped.empty (state : State) :
    ({ state with nestedAux := #[] } : State).NestedAuxScoped := by
  simp [State.NestedAuxScoped]

theorem State.NestedAuxScoped.push {state : State} (hstate : state.NestedAuxScoped)
    (type : Expr) (name : Name) (htype : type.looseBVarRange' = 0) :
    ({ state with nestedAux := state.nestedAux.push (type, name) } : State).NestedAuxScoped := by
  intro entry hentry
  rcases Array.mem_push.mp hentry with hentry | rfl
  · exact hstate entry hentry
  · exact htype

theorem mkUniqueName.frame (name : Name) (env : Environment) (state : State) :
    (mkUniqueName name env state).WF fun returned =>
      returned.2.nestedAux = state.nestedAux ∧ returned.2.newTypes = state.newTypes ∧
        returned.2.lvls = state.lvls ∧ returned.2.ngen = state.ngen := by
  unfold mkUniqueName
  exact .pure ⟨rfl, rfl, rfl, rfl⟩

private theorem modify_bind (update : State → State) (next : PUnit → M α)
    (env : Environment) (state : State) :
    ((modify update >>= next) env state) = next ⟨⟩ env (update state) := rfl

private theorem get_bind (next : State → M α) (env : Environment) (state : State) :
    ((get >>= next) env state) = next state env state := rfl

private theorem read_bind (next : Environment → M α) (env : Environment) (state : State) :
    ((read >>= next) env state) = next env env state := rfl

private theorem lift_scope (action : Except Exception α) (env : Environment) (state : State)
    (hstate : state.NestedAuxScoped) :
    ((liftM action : M α) env state).WF fun returned => returned.2.NestedAuxScoped := by
  cases action with
  | error exception => exact .throw
  | ok value => exact .pure hstate

private theorem lift_bind_scope (action : Except Exception α) (next : α → M β)
    (env : Environment) (state : State)
    (hnext : ∀ value, (next value env state).WF fun returned => returned.2.NestedAuxScoped) :
    ((liftM action >>= next) env state).WF fun returned => returned.2.NestedAuxScoped := by
  cases action with
  | error exception => exact .throw
  | ok value => exact hnext value

private theorem liftM_ok_eq (value : α) :
    (liftM (m := Except Exception) (Except.ok value) : M α) = pure value := by
  rfl

private theorem bind_eq (action : M α) (next : α → M β) (env : Environment) (state : State) :
    ((action >>= next) env state) =
      match action env state with
      | .error exception => .error exception
      | .ok (value, state') => next value env state' := by
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split <;> rename_i h
  · simp [h]
  · simp [h]

private theorem forIn_scope (items : List α) (initial : β)
    (step : α → β → M (ForInStep β)) (env : Environment) (state : State)
    (hstate : state.NestedAuxScoped)
    (hstep : ∀ item acc state', state'.NestedAuxScoped →
      (step item acc env state').WF fun returned => returned.2.NestedAuxScoped) :
    (forIn items initial step env state).WF fun returned => returned.2.NestedAuxScoped := by
  induction items generalizing initial state with
  | nil => exact .pure hstate
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item initial state hstate).bind ?_
    rintro ⟨next, state'⟩ hnext
    cases next with
    | done acc => exact .pure hnext
    | yield acc => exact ih acc state' hnext

private theorem mapM_scope (items : List α) (step : α → M β)
    (env : Environment) (state : State) (hstate : state.NestedAuxScoped)
    (hstep : ∀ item state', state'.NestedAuxScoped →
      (step item env state').WF fun returned => returned.2.NestedAuxScoped) :
    (items.mapM step env state).WF fun returned => returned.2.NestedAuxScoped := by
  induction items generalizing state with
  | nil => exact .pure hstate
  | cons item items ih =>
    rw [List.mapM_cons]
    refine (hstep item state hstate).bind ?_
    rintro ⟨value, state'⟩ hnext
    exact (ih state' hnext).bind fun returned hreturned => .pure hreturned

private theorem mkAppList_scope (fn : Expr) (args : List Expr)
    (hfn : fn.looseBVarRange' = 0) (hargs : ∀ arg ∈ args, arg.looseBVarRange' = 0) :
    (fn.mkAppList args).looseBVarRange' = 0 := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih =>
    apply ih
    · simp [Expr.looseBVarRange', hfn, hargs arg (by simp)]
    · intro other hmem
      exact hargs other (List.mem_cons_of_mem arg hmem)

theorem NestedAppScope.constPrefixRange {type : Expr} {info : InductiveVal}
    (hscope : NestedAppScope type info) (name : Name) (levels : List Level) :
    (mkAppRange (.const name levels) 0 info.numParams type.getAppArgs).looseBVarRange' = 0 := by
  have hlength : (type.getAppArgs.toList.take info.numParams).length = info.numParams := by
    simp [List.length_take, Nat.min_eq_left hscope.2.1]
  rw [Expr.mkAppRange_eq (e := .const name levels) (args := type.getAppArgs)
    (i := 0) (j := info.numParams)
    (l₁ := []) (l₂ := type.getAppArgs.toList.take info.numParams)
    (l₃ := type.getAppArgs.toList.drop info.numParams) (by simp) rfl (by simpa using hlength)]
  apply mkAppList_scope _ _ rfl
  intro arg hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨index, hindex, heq⟩
  have hparam : index < info.numParams := hlength ▸ hindex
  have harg : index < type.getAppArgs.size := Nat.lt_of_lt_of_le hparam hscope.2.1
  rw [List.getElem_take, Array.getElem_toList harg] at heq
  rw [← heq, ← getElem!_pos type.getAppArgs index harg]
  exact hscope.argRange index hparam

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem replaceParams.pushNestedAuxScoped (numParams : Nat) (source target : LocalContext)
    (sourceParams params : Array Expr) (type : Expr) (name : Name)
    (env : Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamContext numParams target params)
    (hstate : state.NestedAuxScoped) (htype : type.looseBVarRange' = 0) :
    (do
      let entry ← replaceParams params type sourceParams
      modify fun (state : State) => { state with nestedAux := state.nestedAux.push (entry, name) }
      return entry : M Expr) env state |>.WF fun returned => returned.2.NestedAuxScoped := by
  refine (replaceParams.noLooseBVars numParams source target sourceParams params type env state
    hsource htarget htype).bind ?_
  rintro ⟨entry, state'⟩ ⟨hentry, hframe⟩
  dsimp only at hentry hframe
  subst state'
  have hscope : ({ state with nestedAux := state.nestedAux.push (entry, name) } : State).NestedAuxScoped :=
    State.NestedAuxScoped.push hstate entry name hentry
  change (((do
    modify (fun (state : State) => { state with nestedAux := state.nestedAux.push (entry, name) })
    pure entry) : M Expr) env state).WF _
  rw [modify_bind]
  exact .pure hscope

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem replaceIfNested.scope (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceIfNested lctx sourceParams As e env state).WF
      fun returned => returned.2.NestedAuxScoped := by
  unfold replaceIfNested
  refine (isNestedInductiveApp?.scope e env state).bind ?_
  rintro ⟨selected, state'⟩ ⟨hframe, hselected⟩
  dsimp only at hframe hselected
  subst state'
  cases selected with
  | none => exact .pure hstate
  | some info =>
    dsimp only
    rw [Expr.withApp_eq]
    have hscope := hselected info rfl
    rcases hscope.1 with ⟨headName, headLevels, hhead⟩
    rw [hhead]
    have harity : info.numParams ≤ e.getAppArgs.size := hscope.2.1
    simp only [if_pos harity]
    have hprefix :
        (mkAppRange (.const headName headLevels) 0 info.numParams e.getAppArgs).looseBVarRange' = 0 := by
      simpa [hhead] using hscope.prefixRange
    refine (replaceParams.noLooseBVars numParams lctx source As sourceParams _ env state
      hsource htarget hprefix).bind ?_
    rintro ⟨Iparams, state'⟩ ⟨hIparams, hframe⟩
    dsimp only at hIparams hframe
    subst state'
    simp only
    rw [get_bind]
    generalize hfound : Array.findSome? _ state.nestedAux = found
    cases found with
    | some auxI_name => exact .pure hstate
    | none =>
      simp only
      simp only [pure_bind]
      rw [read_bind]
      refine (forIn_scope info.all none _ env state hstate ?_).bind ?_
      · intro J_name result state' hloop
        generalize hget : env.get J_name = found
        cases found with
        | error exception => exact .throw
        | ok constant =>
          cases constant with
          | inductInfo J_info =>
            rw [liftM_ok_eq]
            simp only [pure_bind]
            rw [bind_eq]
            generalize hname : mkUniqueName (`_nested ++ J_name) env state' = named
            cases named with
            | error exception => exact .throw
            | ok named =>
              rcases named with ⟨auxJ_name, state''⟩
              have hnamed := mkUniqueName.frame (`_nested ++ J_name) env state'
              rw [hname] at hnamed
              have hnamed' := hnamed _ rfl
              have hpre : state''.NestedAuxScoped := by
                intro entry hentry
                apply hloop entry
                rw [← hnamed'.1]
                exact hentry
              simp only
              refine (lift_bind_scope
                (instantiateForallParams (J_info.type.instantiateLevelParams J_info.levelParams headLevels)
                  info.numParams e.getAppArgs)
                (fun auxJ_type => _) env state'' ?_)
              intro auxJ_type
              have hJprefix :
                  (mkAppRange (.const J_name headLevels) 0 info.numParams e.getAppArgs).looseBVarRange' = 0 :=
                hscope.constPrefixRange J_name headLevels
              refine (replaceParams.noLooseBVars numParams lctx source As sourceParams _ env state''
                hsource htarget hJprefix).bind ?_
              rintro ⟨JAs', state'''⟩ ⟨hJscope, hframe⟩
              dsimp only at hJscope hframe
              subst state'''
              have hpush :
                  ({ state'' with nestedAux := state''.nestedAux.push (JAs', auxJ_name) } : State).NestedAuxScoped :=
                State.NestedAuxScoped.push hpre JAs' auxJ_name hJscope
              dsimp
              rw [modify_bind]
              split
              · rw [get_bind]
                refine (mapM_scope J_info.ctors _ env _ hpush ?_).bind ?_
                · intro J_ctor_name state''' hctors
                  generalize hctor : env.get J_ctor_name = found
                  cases found with
                  | error exception => exact .throw
                  | ok J_ctor_info =>
                    rw [liftM_ok_eq]
                    simp only [pure_bind]
                    refine (lift_scope
                      (instantiateForallParams
                        (J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams headLevels)
                        info.numParams e.getAppArgs) env state''' hctors).bind ?_
                    rintro ⟨auxJ_ctor_type, state''''⟩ hctor
                    exact .pure hctor
                · rintro ⟨auxJ_ctors, state''''⟩ hctors
                  dsimp
                  rw [modify_bind]
                  exact .pure hctors
              · refine (mapM_scope J_info.ctors _ env _ hpush ?_).bind ?_
                · intro J_ctor_name state''' hctors
                  generalize hctor : env.get J_ctor_name = found
                  cases found with
                  | error exception => exact .throw
                  | ok J_ctor_info =>
                    rw [liftM_ok_eq]
                    simp only [pure_bind]
                    refine (lift_scope
                      (instantiateForallParams
                        (J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams headLevels)
                        info.numParams e.getAppArgs) env state''' hctors).bind ?_
                    rintro ⟨auxJ_ctor_type, state''''⟩ hctor
                    exact .pure hctor
                · rintro ⟨auxJ_ctors, state''''⟩ hctors
                  dsimp
                  rw [modify_bind]
                  exact .pure hctors
          | _ => exact .pure hloop
      · rintro ⟨result, state'⟩ hresult
        dsimp
        split
        · exact .pure hresult
        · exact .pure hresult

end Lean4Lean.ElimNestedInductive
