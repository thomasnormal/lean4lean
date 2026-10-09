import Lean4Lean.Verify.InductiveNestedGuard
import Lean4Lean.Verify.InductiveParamBinding

namespace Lean

theorem Expr.instantiateLevelParams_looseBVarRange (e : Expr) (params : List Name)
    (levels : List Level) :
    (e.instantiateLevelParams params levels).looseBVarRange' = e.looseBVarRange' := by
  rw [Expr.instantiateLevelParams_eq]
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', Expr.looseBVarRange']

end Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

def Environment.InductiveDeclRange (env : Kernel.Environment) : Prop :=
  ∀ name info, env.get name = .ok (.inductInfo info) →
    info.type.looseBVarRange' = 0 ∧
      ∀ ctorName, ctorName ∈ info.ctors →
        (∃ ctorInfo, env.get ctorName = .ok (.ctorInfo ctorInfo)) ∧
          ∀ ctorInfo, env.get ctorName = .ok (.ctorInfo ctorInfo) →
            ctorInfo.type.looseBVarRange' = 0

theorem Environment.InductiveDeclRange.inductiveType
    (h : Environment.InductiveDeclRange env)
    (hget : env.get name = .ok (.inductInfo info)) :
    (info.type.instantiateLevelParams info.levelParams levels).looseBVarRange' = 0 := by
  rw [Expr.instantiateLevelParams_looseBVarRange]
  exact (h name info hget).1

theorem Environment.InductiveDeclRange.constructorType
    (h : Environment.InductiveDeclRange env)
    (hget : env.get name = .ok (.inductInfo info))
    (ctorName : Name) (hctor : ctorName ∈ info.ctors)
    (ctorInfo : ConstructorVal)
    (hctorGet : env.get ctorName = .ok (.ctorInfo ctorInfo)) :
    (ctorInfo.type.instantiateLevelParams ctorInfo.levelParams levels).looseBVarRange' = 0 := by
  rw [Expr.instantiateLevelParams_looseBVarRange]
  exact (h name info hget).2 ctorName hctor |>.2 ctorInfo hctorGet

theorem Environment.InductiveDeclRange.constructorInfo
    (h : Environment.InductiveDeclRange env)
    (hget : env.get name = .ok (.inductInfo info))
    (ctorName : Name) (hctor : ctorName ∈ info.ctors) :
    ∃ ctorInfo, env.get ctorName = .ok (.ctorInfo ctorInfo) :=
  (h name info hget).2 ctorName hctor |>.1

end Lean4Lean

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

private theorem lift_wf (action : Except Exception α) (env : Environment) (state : State)
    (Q : α → Prop) (haction : action.WF Q) :
    ((liftM action : M α) env state).WF fun returned => Q returned.1 ∧ returned.2 = state := by
  cases action with
  | error exception => exact .throw
  | ok value => exact .pure ⟨haction _ rfl, rfl⟩

private theorem lift_bind_scope (action : Except Exception α) (next : α → M β)
    (env : Environment) (state : State)
    (hnext : ∀ value, (next value env state).WF fun returned => returned.2.NestedAuxScoped) :
    ((liftM action >>= next) env state).WF fun returned => returned.2.NestedAuxScoped := by
  cases action with
  | error exception => exact .throw
  | ok value => exact hnext value

private theorem lift_bind_any (action : Except Exception α) (next : α → M β)
    (env : Environment) (state : State) (post : β × State → Prop)
    (hnext : ∀ value, (next value env state).WF post) :
    ((liftM action >>= next) env state).WF post := by
  cases action with
  | error exception => exact .throw
  | ok value => exact hnext value

private theorem lift_bind_wf (action : Except Exception α) (next : α → M β)
    (env : Environment) (state : State) (post : β × State → Prop)
    (Q : α → Prop) (haction : action.WF Q)
    (hnext : ∀ value, Q value → (next value env state).WF post) :
    ((liftM action >>= next) env state).WF post := by
  cases action with
  | error exception => exact .throw
  | ok value => exact hnext value (haction _ rfl)

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

private theorem replace_step_scope (action : M (Option Expr)) (next : Option Expr → M Expr)
    (env : Environment) (state : State)
    (haction : (action env state).WF fun returned => returned.2.NestedAuxScoped)
    (hnext : ∀ result state', state'.NestedAuxScoped →
      (next result env state').WF fun returned => returned.2.NestedAuxScoped) :
    ((action >>= next) env state).WF fun returned => returned.2.NestedAuxScoped := by
  exact haction.bind fun result hscope => hnext result.1 result.2 hscope

private theorem replaceM_scope (f? : Expr → M (Option Expr))
    (hstep : ∀ e env state, state.NestedAuxScoped →
      (f? e env state).WF fun returned => returned.2.NestedAuxScoped)
    (e : Expr) (env : Environment) (state : State) (hstate : state.NestedAuxScoped) :
    (e.replaceM f? env state).WF fun returned => returned.2.NestedAuxScoped := by
  unfold Expr.replaceM
  induction e generalizing state with
  | bvar =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | const =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | sort =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | fvar =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | mvar =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | lit =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result <;> exact .pure hresult
  | mdata data e ih =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none => exact (ih state' hresult).bind fun _ hscope => .pure hscope
  | proj typeName idx e ih =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none => exact (ih state' hresult).bind fun _ hscope => .pure hscope
  | app f a ihf iha =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none =>
        exact (ihf state' hresult).bind fun _ hscope =>
          (iha _ hscope).bind fun _ hscope => .pure hscope
  | lam name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none =>
        exact (iht state' hresult).bind fun _ hscope =>
          (ihb _ hscope).bind fun _ hscope => .pure hscope
  | forallE name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none =>
        exact (iht state' hresult).bind fun _ hscope =>
          (ihb _ hscope).bind fun _ hscope => .pure hscope
  | letE name type value body nondep iht ihv ihb =>
    unfold Expr.replaceNoCacheT
    apply replace_step_scope
    · exact hstep _ _ _ hstate
    · intro result state' hresult
      cases result with
      | some eNew => exact .pure hresult
      | none =>
        exact (iht state' hresult).bind fun _ hscope =>
          (ihv _ hscope).bind fun _ hscope =>
            (ihb _ hscope).bind fun _ hscope => .pure hscope

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

private def OptionExprRange (bound : Nat) : Option Expr → Prop
  | none => True
  | some value => value.looseBVarRange' ≤ bound

private def ForInStepOptionRange (bound : Nat) : ForInStep (Option Expr) → Prop
  | .done value => OptionExprRange bound value
  | .yield value => OptionExprRange bound value

private theorem forIn_scope_range (items : List α) (initial : Option Expr)
    (step : α → Option Expr → M (ForInStep (Option Expr))) (bound : Nat)
    (env : Environment) (state : State) (hstate : state.NestedAuxScoped)
    (hinitial : OptionExprRange bound initial)
    (hstep : ∀ item acc state', state'.NestedAuxScoped → OptionExprRange bound acc →
      (step item acc env state').WF fun returned =>
        returned.2.NestedAuxScoped ∧ ForInStepOptionRange bound returned.1) :
    (forIn items initial step env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ OptionExprRange bound returned.1 := by
  induction items generalizing initial state with
  | nil => exact .pure ⟨hstate, hinitial⟩
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item initial state hstate hinitial).bind ?_
    rintro ⟨next, state'⟩ hnext
    cases next with
    | done acc => exact .pure ⟨hnext.1, hnext.2⟩
    | yield acc => exact ih acc state' hnext.1 hnext.2

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

def ConstructorRange (numParams : Nat) (ctor : Constructor) : Prop :=
  ctor.type.looseBVarRange' ≤ numParams

def InductiveTypeRange (numParams : Nat) (indType : InductiveType) : Prop :=
  indType.type.looseBVarRange' ≤ numParams ∧
    ∀ ctor ∈ indType.ctors, ConstructorRange numParams ctor

def State.NewTypesRange (numParams : Nat) (state : State) : Prop :=
  ∀ indType ∈ state.newTypes, InductiveTypeRange numParams indType

def Result.TypesRange (numParams : Nat) (result : Result) : Prop :=
  ∀ indType ∈ result.types, InductiveTypeRange numParams indType

theorem State.NewTypesRange.push {numParams : Nat} {state : State}
    (hstate : State.NewTypesRange numParams state)
    (newType : InductiveType) (hnewType : InductiveTypeRange numParams newType) :
    State.NewTypesRange numParams { state with newTypes := state.newTypes.push newType } := by
  intro indType hmem
  rcases Array.mem_push.mp hmem with hmem | rfl
  · exact hstate indType hmem
  · exact hnewType

private theorem NestedAppScope.prefixArgsRange {type : Expr} {info : InductiveVal}
    (hscope : NestedAppScope type info) :
    ∀ param ∈ type.getAppArgs.extract 0 info.numParams, param.looseBVarRange' = 0 := by
  intro param hparam
  rcases Array.mem_iff_getElem.mp hparam with ⟨index, hindex, hvalue⟩
  have hindex' : index < info.numParams := by
    simp [Array.size_extract] at hindex
    omega
  have hargs := hscope.2.1
  have hvalue' : type.getAppArgs[index]! = param := by
    rw [getElem!_pos _ _ (by omega)]
    have hget := Array.getElem_extract (xs := type.getAppArgs) (start := 0)
      (stop := info.numParams) (i := index) hindex
    simpa using hget.symm.trans hvalue
  rw [← hvalue']
  exact hscope.argRange index hindex'

private theorem forIn_scope_newTypesRange (items : List α) (initial : Option Expr)
    (step : α → Option Expr → M (ForInStep (Option Expr))) (rangeBound optionBound index : Nat)
    (env : Environment) (state : State) (hstate : state.NestedAuxScoped)
    (hrange : State.NewTypesRange rangeBound state) (hindex : index < state.newTypes.size)
    (hinitial : OptionExprRange optionBound initial)
    (hstep : ∀ item acc state', state'.NestedAuxScoped →
      State.NewTypesRange rangeBound state' → index < state'.newTypes.size →
      OptionExprRange optionBound acc →
      item ∈ items →
      (step item acc env state').WF fun returned =>
        returned.2.NestedAuxScoped ∧ State.NewTypesRange rangeBound returned.2 ∧
          index < returned.2.newTypes.size ∧ ForInStepOptionRange optionBound returned.1) :
    (forIn items initial step env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange rangeBound returned.2 ∧
        index < returned.2.newTypes.size ∧ OptionExprRange optionBound returned.1 := by
  induction items generalizing initial state with
  | nil => exact .pure ⟨hstate, hrange, hindex, hinitial⟩
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item initial state hstate hrange hindex hinitial (by simp)).bind ?_
    rintro ⟨next, state'⟩ hnext
    cases next with
    | done acc => exact .pure ⟨hnext.1, hnext.2.1, hnext.2.2.1, hnext.2.2.2⟩
    | yield acc =>
      exact ih acc state' hnext.1 hnext.2.1 hnext.2.2.1 hnext.2.2.2 (by
        intro other otherAcc otherState otherScope otherRange otherIndex otherOption otherMem
        exact hstep other otherAcc otherState otherScope otherRange otherIndex otherOption
          (by simp [otherMem]))

private theorem mapM_scope_newTypesRange (items : List α) (step : α → M β)
    (pred : β → Prop) (bound index : Nat) (env : Environment) (state : State)
    (hstate : state.NestedAuxScoped) (hrange : State.NewTypesRange bound state)
    (hindex : index < state.newTypes.size)
    (hstep : ∀ item state', state'.NestedAuxScoped → State.NewTypesRange bound state' →
      index < state'.newTypes.size →
      item ∈ items →
      (step item env state').WF fun returned =>
        returned.2.NestedAuxScoped ∧ State.NewTypesRange bound returned.2 ∧
          index < returned.2.newTypes.size ∧ pred returned.1) :
    (items.mapM step env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange bound returned.2 ∧
        index < returned.2.newTypes.size ∧ ∀ value ∈ returned.1, pred value := by
  induction items generalizing state with
  | nil => exact .pure ⟨hstate, hrange, hindex, by simp⟩
  | cons item items ih =>
    rw [List.mapM_cons]
    refine (hstep item state hstate hrange hindex (by simp)).bind ?_
    rintro ⟨value, state'⟩ hnext
    refine (ih state' hnext.1 hnext.2.1 hnext.2.2.1 (by
      intro other otherState otherScope otherRange otherIndex otherMem
      exact hstep other otherState otherScope otherRange otherIndex (by simp [otherMem]))).bind ?_
    intro returned hrest
    exact .pure ⟨hrest.1, hrest.2.1, hrest.2.2.1, by
      intro other hother
      rcases List.mem_cons.mp hother with rfl | hother
      · exact hnext.2.2.2
      · exact hrest.2.2.2 other hother⟩

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

private theorem mkAppList_range (fn : Expr) (args : List Expr) (bound : Nat)
    (hfn : fn.looseBVarRange' ≤ bound)
    (hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ bound) :
    (fn.mkAppList args).looseBVarRange' ≤ bound := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih =>
    apply ih
    · have hmax : max fn.looseBVarRange' arg.looseBVarRange' ≤ bound :=
        (Nat.max_le).2 ⟨hfn, hargs arg (by simp)⟩
      simpa [Expr.looseBVarRange'] using hmax
    · intro other hmem
      exact hargs other (by simp [hmem])

theorem mkAppN_range (fn : Expr) (args : Array Expr) (bound : Nat)
    (hfn : fn.looseBVarRange' ≤ bound)
    (hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ bound) :
    (mkAppN fn args).looseBVarRange' ≤ bound := by
  change (args.foldl Expr.app fn).looseBVarRange' ≤ bound
  rw [← Array.foldl_toList, ← Expr.mkAppList_eq_foldl]
  apply mkAppList_range
  · exact hfn
  · intro arg hmem
    apply hargs arg
    simpa using hmem

theorem mkAppRange_tail_range (fn : Expr) (args : Array Expr) (start bound : Nat)
    (hstart : start ≤ args.size) (hfn : fn.looseBVarRange' ≤ bound)
    (hargs : ∀ arg ∈ args.toList.drop start, arg.looseBVarRange' ≤ bound) :
    (mkAppRange fn start args.size args).looseBVarRange' ≤ bound := by
  rw [Expr.mkAppRange_eq (e := fn) (args := args) (i := start) (j := args.size)
    (l₁ := args.toList.take start) (l₂ := args.toList.drop start) (l₃ := [])
    (by simp [List.take_append_drop])]
  · apply mkAppList_range
    · exact hfn
    · exact hargs
  · simp [List.length_take, Nat.min_eq_left hstart]
  · simp

private theorem argsList_range (e : Expr) (args : List Expr) (bound : Nat)
    (hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ bound) :
    ∀ arg ∈ e.getAppArgsList args, arg.looseBVarRange' ≤ max e.looseBVarRange' bound := by
  induction e generalizing args bound with
  | bvar => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | const => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | sort => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | fvar => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | mvar => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | lit => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | mdata data e ih => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | proj typeName idx e ih => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | app f a ihf iha =>
    intro arg hmem
    have hargs' : ∀ arg ∈ a :: args, arg.looseBVarRange' ≤ max a.looseBVarRange' bound := by
      intro other hother
      rcases List.mem_cons.mp hother with rfl | hother
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (hargs other hother) (Nat.le_max_right _ _)
    have h := ihf (a :: args) (max a.looseBVarRange' bound) hargs' arg hmem
    simpa [Expr.getAppArgsList, Expr.looseBVarRange', Nat.max_assoc, Nat.max_left_comm,
      Nat.max_comm] using h
  | lam name type body bi iht ihb => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | forallE name type body bi iht ihb => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)
  | letE name type value body nondep iht ihv ihb => intro arg hmem; exact Nat.le_trans (hargs arg (by simpa [Expr.getAppArgsList] using hmem)) (Nat.le_max_right _ _)

private theorem appFn_range (e : Expr) :
    e.getAppFn.looseBVarRange' ≤ e.looseBVarRange' := by
  induction e with
  | bvar => simp [Expr.getAppFn, Expr.looseBVarRange']
  | const => simp [Expr.getAppFn, Expr.looseBVarRange']
  | sort => simp [Expr.getAppFn, Expr.looseBVarRange']
  | fvar => simp [Expr.getAppFn, Expr.looseBVarRange']
  | mvar => simp [Expr.getAppFn, Expr.looseBVarRange']
  | lit => simp [Expr.getAppFn, Expr.looseBVarRange']
  | mdata data e ih => simp [Expr.getAppFn, Expr.looseBVarRange']
  | proj typeName idx e ih => simp [Expr.getAppFn, Expr.looseBVarRange']
  | app f a ihf iha =>
    simpa [Expr.getAppFn, Expr.looseBVarRange'] using Nat.le_trans ihf (Nat.le_max_left _ _)
  | lam name type body bi iht ihb => simp [Expr.getAppFn, Expr.looseBVarRange']
  | forallE name type body bi iht ihb => simp [Expr.getAppFn, Expr.looseBVarRange']
  | letE name type value body nondep iht ihv ihb => simp [Expr.getAppFn, Expr.looseBVarRange']

private theorem appArg_range (e : Expr) (arg : Expr) (hmem : arg ∈ e.getAppArgs.toList) :
    arg.looseBVarRange' ≤ e.looseBVarRange' := by
  rw [Expr.getAppArgs_toList] at hmem
  have h := argsList_range e [] 0 (by simp) arg hmem
  simpa using h

private theorem nestedApp_range (name : Name) (levels : List Level) (As : Array Expr)
    (e : Expr) (start bound : Nat) (hstart : start ≤ e.getAppArgs.size)
    (hparams : ∀ arg ∈ As, arg.looseBVarRange' = 0)
    (he : e.looseBVarRange' ≤ bound) :
    (mkAppRange (mkAppN (.const name levels) As) start e.getAppArgs.size e.getAppArgs).looseBVarRange' ≤ bound := by
  apply mkAppRange_tail_range
  · exact hstart
  · apply mkAppN_range
    · simp [Expr.looseBVarRange']
    · intro arg hmem
      simp [hparams arg hmem]
  · intro arg hmem
    exact Nat.le_trans (appArg_range e arg (List.mem_of_mem_drop hmem)) he

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

theorem replaceIfNested.range (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State) (bound : Nat)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) (he : e.looseBVarRange' ≤ bound) :
    (replaceIfNested lctx sourceParams As e env state).WF
      fun returned => returned.2.NestedAuxScoped ∧ OptionExprRange bound returned.1 := by
  unfold replaceIfNested
  refine (isNestedInductiveApp?.scope e env state).bind ?_
  rintro ⟨selected, state'⟩ ⟨hframe, hselected⟩
  dsimp only at hframe hselected
  subst state'
  cases selected with
  | none => exact .pure ⟨hstate, trivial⟩
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
    | some auxI_name =>
      exact .pure ⟨hstate, nestedApp_range auxI_name state.lvls As e info.numParams bound
        hscope.2.1 hsource.params_noLooseBVars he⟩
    | none =>
      simp only
      simp only [pure_bind]
      rw [read_bind]
      refine (forIn_scope_range info.all none _ bound env state hstate trivial ?_).bind ?_
      · intro J_name result state' hloop hacc
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
              refine (lift_bind_any
                (instantiateForallParams (J_info.type.instantiateLevelParams J_info.levelParams headLevels)
                  info.numParams e.getAppArgs)
                (fun auxJ_type => _) env state'' _ ?_)
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
                  exact .pure ⟨hctors, by
                    simp [ForInStepOptionRange, OptionExprRange]
                    exact nestedApp_range auxJ_name state''.lvls As e info.numParams bound
                      hscope.2.1 hsource.params_noLooseBVars he⟩
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
                  exact .pure ⟨hctors, by
                    simpa [ForInStepOptionRange, OptionExprRange] using hacc⟩
          | _ => exact .pure ⟨hloop, hacc⟩
      · rintro ⟨result, state'⟩ hresult
        cases result with
        | none => exact .pure ⟨hresult.1, trivial⟩
        | some result =>
          dsimp
          exact .pure hresult

private theorem abstractRange_fvars_range (type : Expr) (n : Nat) (ids : List FVarId)
    (bound : Nat) (htype : type.looseBVarRange' ≤ bound) :
    (type.abstractRange n (ids.map Expr.fvar).toArray).looseBVarRange' ≤ max bound n := by
  rw [Expr.abstractRange_eq]
  have harray : ((ids.map Expr.fvar).toArray.extract 0 n) =
      ((ids.take n).map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simp
  rw [harray, Expr.abstract_eq]
  have hrange := Expr.abstractFVars_looseBVarRange type (ids.take n) 0
  apply Nat.le_trans hrange
  refine (Nat.max_le).2 ⟨?_, ?_⟩
  · exact Nat.le_trans htype (Nat.le_max_left _ _)
  · simpa only [Nat.zero_add, List.length_take] using
      Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_right _ _)

private theorem ParamContext.abstractRange_range {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params)
    (type : Expr) (index : Nat) (hindex : index < numParams)
    (htype : type.looseBVarRange' ≤ numParams) :
    (type.abstractRange index params).looseBVarRange' ≤ numParams := by
  rw [hcontext.params_eq_fvars]
  have hr := abstractRange_fvars_range type index
    (lctx.toList.reverse.map LocalDecl.fvarId) numParams htype
  simpa [LocalDecl.fvarId] using
    Nat.le_trans hr (Nat.max_le.2 ⟨Nat.le_refl _, Nat.le_of_lt hindex⟩)

private theorem paramForall_range_aux {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hcontext : ParamContext numParams lctx params)
    (decls : List LocalDecl) (body : Expr) (hbody : body.looseBVarRange' ≤ numParams)
    (hdecls : ∀ decl ∈ decls, decl.type.looseBVarRange' ≤ numParams)
    (hindices : ∀ decl ∈ decls, decl.index < numParams) :
    (paramForall decls params body).looseBVarRange' ≤ numParams := by
  induction decls with
  | nil =>
    exact Nat.le_trans (hcontext.abstract_range body) (Nat.max_le.2 ⟨hbody, Nat.le_refl _⟩)
  | cons decl decls ih =>
    simp only [paramForall, List.foldr]
    refine (Nat.max_le).2 ⟨?_, ?_⟩
    · exact hcontext.abstractRange_range decl.type decl.index
        (hindices decl (by simp)) (hdecls decl (by simp))
    · apply Nat.le_trans (Nat.sub_le _ _)
      apply ih
      · intro other hother
        exact hdecls other (by simp [hother])
      · intro other hother
        exact hindices other (by simp [hother])

private theorem ParamValidity.mkForall_range {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params)
    (hscope : ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ numParams) (body : Expr)
    (hbody : body.looseBVarRange' ≤ numParams) :
    (lctx.mkForall params body).looseBVarRange' ≤ numParams := by
  rw [hvalid.mkForall_eq]
  apply paramForall_range_aux hvalid.context
  · exact hbody
  · intro decl hdecl
    exact hscope decl (List.mem_reverse.mp hdecl)
  · intro decl hdecl
    have hmem : decl.index ∈ lctx.toList.reverse.map LocalDecl.index :=
      List.mem_map.mpr ⟨decl, hdecl, rfl⟩
    rw [hvalid.indices] at hmem
    exact List.mem_range.mp hmem

private theorem stripForall_loop (items : List Nat) (e : Expr) (bound : Nat)
    (step : Nat → Expr → Except Exception (ForInStep Expr))
    (hstep : ∀ i e, step i e = match e with
      | .forallE _ _ body _ => .ok (.yield body)
      | _ => .error illFormed)
    (he : e.looseBVarRange' ≤ bound) :
    (forIn items e step).WF fun result => result.looseBVarRange' ≤ bound + items.length := by
  induction items generalizing e bound with
  | nil => exact .pure (by simpa)
  | cons item items ih =>
    rw [List.forIn_cons]
    rw [hstep]
    cases e with
    | forallE name domain body bi =>
      change (forIn items body step).WF fun result =>
        result.looseBVarRange' ≤ bound + (items.length + 1)
      refine (ih body (bound + 1) ?_).mono ?_
      change max domain.looseBVarRange' (body.looseBVarRange' - 1) ≤ bound at he
      omega
      intro result hresult
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
    | _ => exact .throw

private def stripForallStep (_ : Nat) (e : Expr) : Except Exception (ForInStep Expr) :=
  match e with
  | .forallE _ _ body _ => .ok (.yield body)
  | _ => .error illFormed

private theorem stripForall_range (e : Expr) (hi bound : Nat)
    (he : e.looseBVarRange' ≤ bound) :
    (forIn [:hi] e stripForallStep).WF fun result =>
      result.looseBVarRange' ≤ bound + hi := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have h := stripForall_loop (List.range' 0 hi 1) e bound stripForallStep
    (by intro i e; rfl) he
  simpa using h

theorem Expr.instantiateRevRange_looseBVarRange (e : Expr) (hi : Nat) (params : Array Expr)
    (bound : Nat) (he : e.looseBVarRange' ≤ bound + (params.extract 0 hi).size)
    (hparams : ∀ param ∈ params.extract 0 hi, param.looseBVarRange' ≤ bound) :
    (e.instantiateRevRange 0 hi params).looseBVarRange' ≤ bound := by
  rw [Expr.instantiateRevRange_eq, Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply Expr.instantiateList_looseBVarRange (n := bound) (k := 0)
  · simpa using he
  · intro param hparam
    have hparam' : param ∈ List.take hi params.toList := by simpa using hparam
    have hmemExtract : param ∈ (params.extract 0 hi).toList := by
      rw [Array.toList_extract]
      simpa using hparam'
    exact hparams param (Array.mem_toList_iff.mp hmemExtract)

theorem instantiateForallParams.range (e : Expr) (hi : Nat) (params : Array Expr)
    (bound : Nat) (he : e.looseBVarRange' ≤ bound)
    (hparams : ∀ param ∈ params.extract 0 hi, param.looseBVarRange' ≤ bound)
    (hsize : hi ≤ params.size) :
    (instantiateForallParams e hi params).WF fun result =>
      result.looseBVarRange' ≤ bound := by
  unfold instantiateForallParams
  change (forIn [:hi] e stripForallStep >>= fun body =>
    pure (body.instantiateRevRange 0 hi params)).WF _
  refine (stripForall_range e hi bound he).bind ?_
  intro body hbody
  have hsize' : (params.extract 0 hi).size = hi := by
    simp [Array.size_extract]
    omega
  have hbound : bound + hi ≤ bound + (params.extract 0 hi).size := by
    simp [hsize']
  exact .pure (Expr.instantiateRevRange_looseBVarRange body hi params bound
    (Nat.le_trans hbody hbound) hparams)

theorem replaceIfNested.rangeWithNewTypes (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State) (bound index : Nat)
    (hsource : ParamValidity numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hlocalScope : ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ numParams)
    (hstate : state.NestedAuxScoped) (hrange : State.NewTypesRange numParams state)
    (hindex : index < state.newTypes.size)
    (hclosure : Lean4Lean.Environment.InductiveDeclRange env)
    (he : e.looseBVarRange' ≤ bound) :
    (replaceIfNested lctx sourceParams As e env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
        index < returned.2.newTypes.size ∧ OptionExprRange bound returned.1 := by
  unfold replaceIfNested
  refine (isNestedInductiveApp?.scope e env state).bind ?_
  rintro ⟨selected, state'⟩ ⟨hframe, hselected⟩
  dsimp only at hframe hselected
  subst state'
  cases selected with
  | none => exact .pure ⟨hstate, hrange, hindex, trivial⟩
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
      hsource.context htarget hprefix).bind ?_
    rintro ⟨Iparams, state'⟩ ⟨hIparams, hframe⟩
    dsimp only at hIparams hframe
    subst state'
    simp only
    rw [get_bind]
    generalize hfound : Array.findSome? _ state.nestedAux = found
    cases found with
    | some auxI_name =>
      exact .pure ⟨hstate, hrange, hindex, nestedApp_range auxI_name state.lvls As e info.numParams bound
        hscope.2.1 hsource.context.params_noLooseBVars he⟩
    | none =>
      simp only
      simp only [pure_bind]
      rw [read_bind]
      refine (forIn_scope_newTypesRange info.all none _ numParams bound index env state hstate hrange
        hindex trivial ?_).bind ?_
      · intro J_name result state' hloop hloopRange hloopIndex hacc hJmem
        generalize hget : env.get J_name = found
        cases found with
        | error exception => exact .throw
        | ok constant =>
          cases constant with
          | inductInfo J_info =>
            have hJtype := hclosure.inductiveType (levels := headLevels) hget
            have hJbody := instantiateForallParams.range
              (J_info.type.instantiateLevelParams J_info.levelParams headLevels)
              info.numParams e.getAppArgs 0 (Nat.le_of_eq hJtype)
              (fun param hparam => Nat.le_of_eq (hscope.prefixArgsRange param hparam)) harity
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
              have hrange' : State.NewTypesRange numParams state'' := by
                intro indType hmem
                apply hloopRange indType
                rw [← hnamed'.2.1]
                exact hmem
              have hindex' : index < state''.newTypes.size := by
                rw [hnamed'.2.1]
                exact hloopIndex
              simp only
              refine (lift_wf
                (instantiateForallParams
                  (J_info.type.instantiateLevelParams J_info.levelParams headLevels)
                  info.numParams e.getAppArgs) env state''
                (fun value => value.looseBVarRange' ≤ 0) hJbody).bind ?_
              rintro ⟨auxJ_type, state'''⟩ ⟨hauxJ_type, hstateFrame⟩
              change state''' = state'' at hstateFrame
              subst state'''
              have hauxJ_type' : auxJ_type.looseBVarRange' ≤ numParams :=
                Nat.le_trans hauxJ_type (Nat.zero_le _)
              have hJprefix :
                  (mkAppRange (.const J_name headLevels) 0 info.numParams e.getAppArgs).looseBVarRange' = 0 :=
                hscope.constPrefixRange J_name headLevels
              refine (replaceParams.noLooseBVars numParams lctx source As sourceParams _ env state''
                hsource.context htarget hJprefix).bind ?_
              rintro ⟨JAs', state'''⟩ ⟨hJscope, hframe⟩
              dsimp only at hJscope hframe
              subst state'''
              have hpush :
                  ({ state'' with nestedAux := state''.nestedAux.push (JAs', auxJ_name) } : State).NestedAuxScoped :=
                State.NestedAuxScoped.push hpre JAs' auxJ_name hJscope
              have hpushRange : State.NewTypesRange numParams
                  { state'' with nestedAux := state''.nestedAux.push (JAs', auxJ_name) } := by
                simpa using hrange'
              have hnewTypeType :
                  (lctx.mkForall As auxJ_type).looseBVarRange' ≤ numParams :=
                hsource.mkForall_range hlocalScope auxJ_type hauxJ_type'
              dsimp
              rw [modify_bind]
              split
              · rw [get_bind]
                refine (mapM_scope_newTypesRange J_info.ctors _
                  (pred := fun ctor => ConstructorRange numParams ctor) numParams index env _ hpush
                  hpushRange hindex' ?_).bind ?_
                · intro J_ctor_name state''' hctorScope hctorRange hctorIndex hctorMem
                  generalize hctor : env.get J_ctor_name = found
                  cases found with
                  | error exception => exact .throw
                  | ok J_ctor_info =>
                    rcases hclosure.constructorInfo hget J_ctor_name hctorMem with
                      ⟨J_ctor_val, hctorGet⟩
                    rw [hctorGet] at hctor
                    cases hctor
                    rw [liftM_ok_eq]
                    simp only [pure_bind]
                    have hJctor := hclosure.constructorType (levels := headLevels) hget
                      J_ctor_name hctorMem J_ctor_val hctorGet
                    have hJctorBody := instantiateForallParams.range
                      (J_ctor_val.type.instantiateLevelParams J_ctor_val.levelParams headLevels)
                      info.numParams e.getAppArgs 0 (Nat.le_of_eq hJctor)
                      (fun param hparam => Nat.le_of_eq (hscope.prefixArgsRange param hparam)) harity
                    refine (lift_wf
                      (instantiateForallParams
                        (J_ctor_val.type.instantiateLevelParams J_ctor_val.levelParams headLevels)
                        info.numParams e.getAppArgs) env state'''
                      (fun value => value.looseBVarRange' ≤ 0) hJctorBody).bind ?_
                    rintro ⟨auxJ_ctor_type, state''''⟩ ⟨hauxJ_ctor_type, hstateFrame⟩
                    change state'''' = state''' at hstateFrame
                    subst state''''
                    simp only
                    have hauxJ_ctor_type'' : auxJ_ctor_type.looseBVarRange' ≤ 0 := by
                      simpa using hauxJ_ctor_type
                    have hauxJ_ctor_type' : auxJ_ctor_type.looseBVarRange' ≤ numParams :=
                      Nat.le_trans hauxJ_ctor_type'' (Nat.zero_le _)
                    exact .pure ⟨hctorScope, hctorRange, hctorIndex,
                      hsource.mkForall_range hlocalScope auxJ_ctor_type hauxJ_ctor_type'⟩
                · rintro ⟨auxJ_ctors, state''''⟩ hctors
                  have hnewType : InductiveTypeRange numParams {
                      name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors } :=
                    ⟨hnewTypeType, hctors.2.2.2⟩
                  dsimp
                  rw [modify_bind]
                  have hrangeNew := State.NewTypesRange.push hctors.2.1
                    { name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors } hnewType
                  have hindexNew : index < (state''''.newTypes.push {
                      name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors }).size := by
                    have hindexBefore : index < state''''.newTypes.size := by
                      simpa using hctors.2.2.1
                    simp [Array.size_push]
                    omega
                  exact .pure ⟨hctors.1, hrangeNew, hindexNew, by
                    simp [ForInStepOptionRange, OptionExprRange]
                    exact nestedApp_range auxJ_name state''.lvls As e info.numParams bound
                      hscope.2.1 hsource.context.params_noLooseBVars he⟩
              · refine (mapM_scope_newTypesRange J_info.ctors _
                  (pred := fun ctor => ConstructorRange numParams ctor) numParams index env _ hpush
                  hpushRange hindex' ?_).bind ?_
                · intro J_ctor_name state''' hctorScope hctorRange hctorIndex hctorMem
                  generalize hctor : env.get J_ctor_name = found
                  cases found with
                  | error exception => exact .throw
                  | ok J_ctor_info =>
                    rcases hclosure.constructorInfo hget J_ctor_name hctorMem with
                      ⟨J_ctor_val, hctorGet⟩
                    rw [hctorGet] at hctor
                    cases hctor
                    rw [liftM_ok_eq]
                    simp only [pure_bind]
                    have hJctor := hclosure.constructorType (levels := headLevels) hget
                      J_ctor_name hctorMem J_ctor_val hctorGet
                    have hJctorBody := instantiateForallParams.range
                      (J_ctor_val.type.instantiateLevelParams J_ctor_val.levelParams headLevels)
                      info.numParams e.getAppArgs 0 (Nat.le_of_eq hJctor)
                      (fun param hparam => Nat.le_of_eq (hscope.prefixArgsRange param hparam)) harity
                    refine (lift_wf
                      (instantiateForallParams
                        (J_ctor_val.type.instantiateLevelParams J_ctor_val.levelParams headLevels)
                        info.numParams e.getAppArgs) env state'''
                      (fun value => value.looseBVarRange' ≤ 0) hJctorBody).bind ?_
                    rintro ⟨auxJ_ctor_type, state''''⟩ ⟨hauxJ_ctor_type, hstateFrame⟩
                    change state'''' = state''' at hstateFrame
                    subst state''''
                    simp only
                    have hauxJ_ctor_type'' : auxJ_ctor_type.looseBVarRange' ≤ 0 := by
                      simpa using hauxJ_ctor_type
                    have hauxJ_ctor_type' : auxJ_ctor_type.looseBVarRange' ≤ numParams :=
                      Nat.le_trans hauxJ_ctor_type'' (Nat.zero_le _)
                    exact .pure ⟨hctorScope, hctorRange, hctorIndex,
                      hsource.mkForall_range hlocalScope auxJ_ctor_type hauxJ_ctor_type'⟩
                · rintro ⟨auxJ_ctors, state''''⟩ hctors
                  have hnewType : InductiveTypeRange numParams {
                      name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors } :=
                    ⟨hnewTypeType, hctors.2.2.2⟩
                  dsimp
                  rw [modify_bind]
                  have hrangeNew := State.NewTypesRange.push hctors.2.1
                    { name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors } hnewType
                  have hindexNew : index < (state''''.newTypes.push {
                      name := auxJ_name, type := lctx.mkForall As auxJ_type, ctors := auxJ_ctors }).size := by
                    have hindexBefore : index < state''''.newTypes.size := by
                      simpa using hctors.2.2.1
                    simp [Array.size_push]
                    omega
                  exact .pure ⟨hctors.1, hrangeNew, hindexNew, by
                    simpa [ForInStepOptionRange, OptionExprRange] using hacc⟩
          | _ => exact .pure ⟨hloop, hloopRange, hloopIndex, hacc⟩
      · rintro ⟨result, state'⟩ hresult
        cases result with
        | none => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2.1, trivial⟩
        | some result =>
          dsimp
          exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2⟩

theorem replaceIfNested.scope (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceIfNested lctx sourceParams As e env state).WF
      fun returned => returned.2.NestedAuxScoped := by
  exact (replaceIfNested.range numParams source lctx sourceParams As e env state e.looseBVarRange'
    hsource htarget hstate (Nat.le_refl _)).mono fun _ hresult => hresult.1

private theorem replaceM_range (f? : Expr → M (Option Expr))
    (hstep : ∀ e env state, state.NestedAuxScoped →
      (f? e env state).WF fun returned =>
        returned.2.NestedAuxScoped ∧ OptionExprRange e.looseBVarRange' returned.1)
    (e : Expr) (env : Environment) (state : State) (hstate : state.NestedAuxScoped) :
    (e.replaceM f? env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ returned.1.looseBVarRange' ≤ e.looseBVarRange' := by
  unfold Expr.replaceM
  induction e generalizing state with
  | bvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | const =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | sort =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | fvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | mvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | lit =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | none => exact .pure ⟨hresult.1, by simp [Expr.looseBVarRange']⟩
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
  | mdata data e ih =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (ih state' hresult.1).bind ?_
      rintro ⟨eNew, state''⟩ hnew
      exact .pure ⟨hnew.1, by simpa [Expr.updateMData!, Expr.looseBVarRange'] using hnew.2⟩
  | proj typeName idx e ih =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (ih state' hresult.1).bind ?_
      rintro ⟨eNew, state''⟩ hnew
      exact .pure ⟨hnew.1, by simpa [Expr.updateProj!, Expr.looseBVarRange'] using hnew.2⟩
  | app f a ihf iha =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (ihf state' hresult.1).bind ?_
      rintro ⟨fNew, state''⟩ hf
      refine (iha state'' hf.1).bind ?_
      rintro ⟨aNew, state'''⟩ ha
      exact .pure ⟨ha.1, by
        simpa [Expr.updateApp!, Expr.looseBVarRange'] using
          (Nat.max_le).2 ⟨Nat.le_trans hf.2 (Nat.le_max_left _ _),
            Nat.le_trans ha.2 (Nat.le_max_right _ _)⟩⟩
  | lam name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (iht state' hresult.1).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihb state'' htype.1).bind ?_
      rintro ⟨bodyNew, state'''⟩ hbody
      exact .pure ⟨hbody.1, by
        simp [Expr.updateLambdaE!, Expr.updateLambda!, Expr.looseBVarRange']
        exact (Nat.max_le).2 ⟨Nat.le_trans htype.2 (Nat.le_max_left _ _),
          Nat.le_trans (Nat.sub_le_sub_right hbody.2 1) (Nat.le_max_right _ _)⟩⟩
  | forallE name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (iht state' hresult.1).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihb state'' htype.1).bind ?_
      rintro ⟨bodyNew, state'''⟩ hbody
      exact .pure ⟨hbody.1, by
        simp [Expr.updateForallE!, Expr.updateForall!, Expr.looseBVarRange']
        exact (Nat.max_le).2 ⟨Nat.le_trans htype.2 (Nat.le_max_left _ _),
          Nat.le_trans (Nat.sub_le_sub_right hbody.2 1) (Nat.le_max_right _ _)⟩⟩
  | letE name type value body nondep iht ihv ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _ _ hstate).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, by simpa [OptionExprRange] using hresult.2⟩
    | none =>
      refine (iht state' hresult.1).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihv state'' htype.1).bind ?_
      rintro ⟨valueNew, state'''⟩ hvalue
      refine (ihb state''' hvalue.1).bind ?_
      rintro ⟨bodyNew, state''''⟩ hbody
      exact .pure ⟨hbody.1, by
        simp [Expr.updateLet!, Expr.looseBVarRange']
        apply (Nat.max_le).2
        constructor
        · exact Nat.le_trans htype.2 (Nat.le_max_left _ _)
        · apply (Nat.max_le).2
          constructor
          · exact Nat.le_trans hvalue.2
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          · exact Nat.le_trans (Nat.sub_le_sub_right hbody.2 1)
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩

theorem replaceAllNested.range (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceAllNested lctx sourceParams As e env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ returned.1.looseBVarRange' ≤ e.looseBVarRange' := by
  exact replaceM_range (fun expression => replaceIfNested lctx sourceParams As expression)
    (fun expression env state hstate =>
      replaceIfNested.range numParams source lctx sourceParams As expression env state
        expression.looseBVarRange' hsource htarget hstate (Nat.le_refl _))
    e env state hstate

private theorem replaceM_newTypesRange (numParams index : Nat) (f? : Expr → M (Option Expr))
    (env : Environment)
    (hstep : ∀ e state, state.NestedAuxScoped → State.NewTypesRange numParams state →
      index < state.newTypes.size →
      (f? e env state).WF fun returned =>
        returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
          index < returned.2.newTypes.size)
    (e : Expr) (state : State) (hstate : state.NestedAuxScoped)
    (hrange : State.NewTypesRange numParams state) (hindex : index < state.newTypes.size) :
    (e.replaceM f? env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
        index < returned.2.newTypes.size := by
  unfold Expr.replaceM
  induction e generalizing state with
  | bvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | const =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | sort =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | fvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | mvar =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | lit =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result <;> exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
  | mdata data e ih =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (ih state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨eNew, state''⟩ hnew
      exact .pure ⟨hnew.1, hnew.2.1, hnew.2.2⟩
  | proj typeName idx e ih =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (ih state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨eNew, state''⟩ hnew
      exact .pure ⟨hnew.1, hnew.2.1, hnew.2.2⟩
  | app f a ihf iha =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (ihf state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨fNew, state''⟩ hfunction
      refine (iha state'' hfunction.1 hfunction.2.1 hfunction.2.2).bind ?_
      rintro ⟨aNew, state'''⟩ hargument
      exact .pure ⟨hargument.1, hargument.2.1, hargument.2.2⟩
  | lam name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (iht state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihb state'' htype.1 htype.2.1 htype.2.2).bind ?_
      rintro ⟨bodyNew, state'''⟩ hbody
      exact .pure ⟨hbody.1, hbody.2.1, hbody.2.2⟩
  | forallE name type body bi iht ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (iht state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihb state'' htype.1 htype.2.1 htype.2.2).bind ?_
      rintro ⟨bodyNew, state'''⟩ hbody
      exact .pure ⟨hbody.1, hbody.2.1, hbody.2.2⟩
  | letE name type value body nondep iht ihv ihb =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ state hstate hrange hindex).bind ?_
    rintro ⟨result, state'⟩ hresult
    cases result with
    | some eNew => exact .pure ⟨hresult.1, hresult.2.1, hresult.2.2⟩
    | none =>
      refine (iht state' hresult.1 hresult.2.1 hresult.2.2).bind ?_
      rintro ⟨typeNew, state''⟩ htype
      refine (ihv state'' htype.1 htype.2.1 htype.2.2).bind ?_
      rintro ⟨valueNew, state'''⟩ hvalue
      refine (ihb state''' hvalue.1 hvalue.2.1 hvalue.2.2).bind ?_
      rintro ⟨bodyNew, state''''⟩ hbody
      exact .pure ⟨hbody.1, hbody.2.1, hbody.2.2⟩

theorem replaceAllNested.scope (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceAllNested lctx sourceParams As e env state).WF
      fun returned => returned.2.NestedAuxScoped := by
  exact replaceM_scope (fun expression => replaceIfNested lctx sourceParams As expression)
    (fun expression env state hstate =>
      replaceIfNested.scope numParams source lctx sourceParams As expression env state
        hsource htarget hstate)
    e env state hstate

private theorem withParams_loop_context_scope (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hcontext : ParamContext params.size lctx params)
    (hstate : state.NestedAuxScoped)
    (hnext : ∀ lctx' remainder params' state',
      ParamContext (params.size + remaining) lctx' params' →
      state'.NestedAuxScoped →
      (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero =>
    exact hnext lctx type params state (by simpa using hcontext) hstate
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      apply ih
      · simpa using hcontext.push ⟨state.ngen.curr⟩ name domain bi
      · simpa [State.NestedAuxScoped] using hstate
      · intro lctx' remainder params' state' hcontext' hstate'
        apply hnext lctx' remainder params' state'
        · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcontext'
        · exact hstate'
    | _ => exact Except.WF.throw

theorem withParams.contextScope (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (hstate : state.NestedAuxScoped)
    (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamContext numParams lctx params →
      state'.NestedAuxScoped → (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  exact withParams_loop_context_scope numParams type {} #[] next env state post
    ParamContext.empty hstate (fun lctx remainder params state' hcontext' hstate' =>
      hnext lctx remainder params state' (by simpa using hcontext') hstate')

private theorem withParams_loop_context_range (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hvalid : ParamValidity params.size lctx params)
    (hreserved : ContextReserved lctx state.ngen)
    (hscope : ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ params.size + remaining)
    (htype : type.looseBVarRange' ≤ params.size + remaining)
    (hstate : state.NestedAuxScoped)
    (hnext : ∀ lctx' remainder params' state',
      ParamValidity (params.size + remaining) lctx' params' →
      ContextReserved lctx' state'.ngen →
      (∀ decl ∈ lctx'.toList, decl.type.looseBVarRange' ≤ params.size + remaining) →
      state'.NestedAuxScoped → remainder.looseBVarRange' ≤ params.size + remaining →
      (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero =>
    apply hnext
    · simpa using hvalid
    · simpa using hreserved
    · simpa using hscope
    · exact hstate
    · exact htype
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      have hparts : domain.looseBVarRange' ≤ params.size + remaining + 1 ∧
          body.looseBVarRange' ≤ params.size + remaining + 2 := by
        change max domain.looseBVarRange' (body.looseBVarRange' - 1) ≤
          params.size + remaining + 1 at htype
        omega
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      exact ih _ _ _ _ (by simpa using hvalid.push_current hreserved name domain bi)
        (by simpa using hreserved.push_current name domain bi)
        (by
          intro decl hdecl
          simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
          rcases hdecl with rfl | hdecl
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hparts.1
          · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hscope decl hdecl)
        (by
          simpa [Expr.instantiate1_eq, Array.size_push, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            (Expr.instantiate1'_looseBVarRange (n := params.size + remaining + 1) (k := 0)
              (by simpa [Nat.add_assoc] using hparts.2) (by simp [Expr.looseBVarRange'])))
        (by simpa [State.NestedAuxScoped] using hstate)
        (fun lctx' remainder params' state' hvalid' hreserved' hscope' hstate' htype' =>
          hnext lctx' remainder params' state'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid')
            hreserved'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hscope')
            hstate'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htype'))
    | _ => exact Except.WF.throw

theorem withParams.contextRange (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (htype : type.looseBVarRange' ≤ numParams)
    (hstate : state.NestedAuxScoped) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamValidity numParams lctx params →
      ContextReserved lctx state'.ngen →
      (∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ numParams) →
      state'.NestedAuxScoped → remainder.looseBVarRange' ≤ numParams →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  exact withParams_loop_context_range numParams type {} #[] next env state post
    ParamValidity.empty (ContextReserved.empty state.ngen)
    (by
      intro decl hdecl
      have hzero := ContextNoLooseBVars.empty decl hdecl
      omega)
    (by simpa [Nat.zero_add] using htype) hstate
    (fun lctx remainder params state' hvalid' hreserved' hscope' hstate' htype' =>
      hnext lctx remainder params state' (by simpa using hvalid') hreserved'
        (by simpa [Nat.add_zero] using hscope') hstate'
        (by simpa [Nat.add_zero] using htype'))

private theorem bindWF_nestedAuxScoped (action : M α) (next : α → M β)
    (env : Environment) (state : State) (post : β × State → Prop)
    (hnext : ∀ value state', (next value env state').WF post) :
    ((action >>= next) env state).WF post :=
  (show (action env state).WF fun _ => True from fun _ _ => trivial).bind
    (fun result _ => hnext result.1 result.2)

def Result.Aux2NestedScoped (numParams : Nat) (result : Result) : Prop :=
  ∀ name type, result.aux2nested.find? name = some type → type.looseBVarRange' ≤ numParams

private theorem state_newTypesRange_set (numParams index : Nat) (state : State)
    (newType : InductiveType)
    (hstate : State.NewTypesRange numParams state)
    (hnewType : InductiveTypeRange numParams newType) :
    State.NewTypesRange numParams { state with newTypes := state.newTypes.set! index newType } := by
  intro indType hmem
  have hmem' : indType ∈ state.newTypes ∨ indType = newType := by
    simpa only [Array.set!_eq_setIfInBounds] using
      (Array.mem_or_eq_of_mem_setIfInBounds (xs := state.newTypes) (i := index)
        (a := indType) (b := newType) hmem)
  rcases hmem' with hmem' | rfl
  · exact hstate indType hmem'
  · exact hnewType

private theorem withParams_loop_context_range_newTypes (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α) (bound : Nat)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hvalid : ParamValidity params.size lctx params)
    (hreserved : ContextReserved lctx state.ngen)
    (hscope : ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ params.size + remaining)
    (htype : type.looseBVarRange' ≤ params.size + remaining)
    (hstate : state.NestedAuxScoped)
    (hrange : State.NewTypesRange bound state)
    (hnext : ∀ lctx' remainder params' state',
      ParamValidity (params.size + remaining) lctx' params' →
      ContextReserved lctx' state'.ngen →
      (∀ decl ∈ lctx'.toList, decl.type.looseBVarRange' ≤ params.size + remaining) →
      state'.NestedAuxScoped → remainder.looseBVarRange' ≤ params.size + remaining →
      State.NewTypesRange bound state' →
      (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero =>
    apply hnext
    · simpa using hvalid
    · simpa using hreserved
    · simpa using hscope
    · exact hstate
    · exact htype
    · exact hrange
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      have hparts : domain.looseBVarRange' ≤ params.size + remaining + 1 ∧
          body.looseBVarRange' ≤ params.size + remaining + 2 := by
        change max domain.looseBVarRange' (body.looseBVarRange' - 1) ≤
          params.size + remaining + 1 at htype
        omega
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      exact ih _ _ _ _ (by simpa using hvalid.push_current hreserved name domain bi)
        (by simpa using hreserved.push_current name domain bi)
        (by
          intro decl hdecl
          simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
          rcases hdecl with rfl | hdecl
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hparts.1
          · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hscope decl hdecl)
        (by
          simpa [Expr.instantiate1_eq, Array.size_push, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            (Expr.instantiate1'_looseBVarRange (n := params.size + remaining + 1) (k := 0)
              (by simpa [Nat.add_assoc] using hparts.2) (by simp [Expr.looseBVarRange'])))
        (by simpa [State.NestedAuxScoped] using hstate)
        hrange
        (fun lctx' remainder params' state' hvalid' hreserved' hscope' hstate' htype' hrange' =>
          hnext lctx' remainder params' state'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid')
            hreserved'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hscope')
            hstate'
            (by simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htype')
            hrange')
    | _ => exact Except.WF.throw

theorem withParams.contextRangeNewTypes (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (htype : type.looseBVarRange' ≤ numParams)
    (hstate : state.NestedAuxScoped) (hrange : State.NewTypesRange numParams state)
    (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamValidity numParams lctx params →
      ContextReserved lctx state'.ngen →
      (∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ numParams) →
      state'.NestedAuxScoped → remainder.looseBVarRange' ≤ numParams →
      State.NewTypesRange numParams state' →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  exact withParams_loop_context_range_newTypes numParams type {} #[] next numParams env state post
    ParamValidity.empty (ContextReserved.empty state.ngen)
    (by
      intro decl hdecl
      have hzero := ContextNoLooseBVars.empty decl hdecl
      omega)
    (by simpa [Nat.zero_add] using htype) hstate hrange
    (fun lctx remainder params state' hvalid' hreserved' hscope' hstate' htype' hrange' =>
      hnext lctx remainder params state' (by simpa using hvalid') hreserved'
        (by simpa [Nat.add_zero] using hscope') hstate'
        (by simpa [Nat.add_zero] using htype') (by simpa using hrange'))

private theorem mapM_newTypesRange (numParams index : Nat) (items : List α)
    (step : α → M β) (pred : β → Prop) (env : Environment) (state : State)
    (hstate : state.NestedAuxScoped) (hrange : State.NewTypesRange numParams state)
    (hindex : index < state.newTypes.size)
    (hstep : ∀ item state', state'.NestedAuxScoped →
      State.NewTypesRange numParams state' → index < state'.newTypes.size →
      item ∈ items →
      (step item env state').WF fun returned =>
        returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
          index < returned.2.newTypes.size ∧ pred returned.1) :
    (items.mapM step env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
        index < returned.2.newTypes.size ∧ ∀ value ∈ returned.1, pred value := by
  induction items generalizing state with
  | nil => exact .pure ⟨hstate, hrange, hindex, by simp⟩
  | cons item items ih =>
    rw [List.mapM_cons]
    refine (hstep item state hstate hrange hindex (by simp)).bind ?_
    rintro ⟨value, state'⟩ hnext
    refine (ih state' hnext.1 hnext.2.1 hnext.2.2.1 (by
      intro other otherState otherScope otherRange otherIndex otherMem
      exact hstep other otherState otherScope otherRange otherIndex (by simp [otherMem]))).bind ?_
    intro returned hrest
    exact .pure ⟨hrest.1, hrest.2.1, hrest.2.2.1, by
      intro other hother
      rcases List.mem_cons.mp hother with rfl | hother
      · exact hnext.2.2.2
      · exact hrest.2.2.2 other hother⟩

theorem replaceAllNested.rangeWithNewTypes (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State) (bound index : Nat)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped)
    (hgenerated : (replaceAllNested lctx sourceParams As e env state).WF fun returned =>
      State.NewTypesRange numParams returned.2 ∧ index < returned.2.newTypes.size)
    (he : e.looseBVarRange' ≤ bound) :
    (replaceAllNested lctx sourceParams As e env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
        index < returned.2.newTypes.size ∧ returned.1.looseBVarRange' ≤ bound := by
  intro result hresult
  have hrange := replaceAllNested.range numParams source lctx sourceParams As e env state
    hsource htarget hstate result hresult
  have hnew := hgenerated result hresult
  exact ⟨hrange.1, hnew.1, hnew.2, Nat.le_trans hrange.2 he⟩

theorem replaceAllNested.rangeWithNewTypesStructural (numParams : Nat) (source : LocalContext)
    (lctx : LocalContext) (sourceParams As : Array Expr) (e : Expr)
    (env : Environment) (state : State) (bound index : Nat)
    (hsource : ParamValidity numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hlocalScope : ∀ decl ∈ lctx.toList, decl.type.looseBVarRange' ≤ numParams)
    (hstate : state.NestedAuxScoped) (hrange : State.NewTypesRange numParams state)
    (hindex : index < state.newTypes.size)
    (hclosure : Lean4Lean.Environment.InductiveDeclRange env)
    (he : e.looseBVarRange' ≤ bound) :
    (replaceAllNested lctx sourceParams As e env state).WF fun returned =>
      returned.2.NestedAuxScoped ∧ State.NewTypesRange numParams returned.2 ∧
        index < returned.2.newTypes.size ∧ returned.1.looseBVarRange' ≤ bound := by
  intro result hresult
  have hnew := replaceM_newTypesRange numParams index
    (fun expression => replaceIfNested lctx sourceParams As expression)
    env (fun expression state hstate hrange hindex =>
      (replaceIfNested.rangeWithNewTypes numParams source lctx sourceParams As expression env state
        expression.looseBVarRange' index hsource htarget hlocalScope hstate hrange hindex hclosure
        (Nat.le_refl _)).mono fun _ hstep => ⟨hstep.1, hstep.2.1, hstep.2.2.1⟩)
    e state hstate hrange hindex result hresult
  have hrange := replaceAllNested.range numParams source lctx sourceParams As e env state
    hsource.context htarget hstate result hresult
  exact ⟨hnew.1, hnew.2.1, hnew.2.2, Nat.le_trans hrange.2 he⟩

private def MapAux2NestedScoped (numParams : Nat) (map : NameMap Expr) : Prop :=
  ∀ name type, map.find? name = some type → type.looseBVarRange' ≤ numParams

private theorem foldAux2NestedScoped (numParams : Nat) (params : Array Expr)
    (entries : List (Expr × Name)) (map : NameMap Expr)
    (hcontext : ParamContext numParams lctx params)
    (hscope : MapAux2NestedScoped numParams map)
    (hentries : ∀ entry ∈ entries, entry.1.looseBVarRange' = 0) :
    MapAux2NestedScoped numParams
        (entries.foldl (fun map (entry : Expr × Name) =>
          map.insert entry.2 (entry.1.abstract params)) map) := by
  induction entries generalizing map with
  | nil => exact hscope
  | cons entry entries ih =>
    have hentry : entry.1.looseBVarRange' = 0 := hentries entry (by simp)
    have htail : ∀ item ∈ entries, item.1.looseBVarRange' = 0 := by
      intro item hitem
      exact hentries item (by simp [hitem])
    have hinsertScope : MapAux2NestedScoped numParams
        (map.insert entry.2 (entry.1.abstract params)) := by
      intro name type hfind
      change (Std.TreeMap.insert map entry.2 (entry.1.abstract params))[name]? = some type at hfind
      rw [Std.TreeMap.getElem?_insert] at hfind
      split at hfind
      · injection hfind with htype
        subst type
        exact hcontext.abstract_scopedRange entry.1 hentry
      · exact hscope name type hfind
    exact ih (map.insert entry.2 (entry.1.abstract params)) hinsertScope htail

private theorem stateAux2NestedScoped (numParams : Nat) (params : Array Expr)
    (state : State) (lctx : LocalContext) (hcontext : ParamContext numParams lctx params)
    (hstate : state.NestedAuxScoped) :
    MapAux2NestedScoped numParams
      (state.nestedAux.foldl (fun map (entry : Expr × Name) =>
        map.insert entry.2 (entry.1.abstract params)) {}) := by
  have hentries : ∀ entry ∈ state.nestedAux.toList, entry.1.looseBVarRange' = 0 := by
    intro entry hentry
    apply hstate entry
    simpa using hentry
  have hfold := foldAux2NestedScoped numParams params state.nestedAux.toList {} hcontext
    (by
      intro name type hfind
      change Std.TreeMap.get? ({} : Std.TreeMap Name Expr Name.quickCmp) name = some type at hfind
      rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_emptyc] at hfind
      simp at hfind) hentries
  simpa [Array.foldl_toList] using hfold

theorem run.loop.nestedAuxScoped (numParams : Nat) (lctx : LocalContext)
    (params : Array Expr) (index fuel : Nat) (env : Environment) (state : State)
    (hcontext : ParamContext numParams lctx params) (hstate : state.NestedAuxScoped) :
    (run.loop numParams lctx params index fuel env state).WF
      fun result => result.2.NestedAuxScoped ∧ Result.Aux2NestedScoped numParams result.1 := by
  induction fuel generalizing index state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · simp only [withParams.assert_size]
      refine (mapM_scope _ _ env state hstate ?_).bind ?_
      · intro ctor state' hctor
        refine withParams.contextScope ctor.type numParams _ env state' hctor _ ?_
        intro ctorLctx ctorType As state'' hctorContext hstate'
        refine (replaceAllNested.scope numParams lctx ctorLctx params As ctorType env state''
          hctorContext hcontext hstate').bind ?_
        rintro ⟨_, state'''⟩ hstate''
        exact .pure hstate''
      · rintro ⟨ctors, state'⟩ hctors
        simp only
        rw [modify_bind]
        exact ih (index + 1) { state' with
          newTypes := state'.newTypes.set! index {
            name := state.newTypes[index].name
            type := state.newTypes[index].type
            ctors } } hctors
    · exact .pure ⟨hstate, stateAux2NestedScoped numParams params state lctx hcontext hstate⟩

theorem run.loop.newTypesRange (numParams : Nat) (lctx : LocalContext)
    (params : Array Expr) (index fuel : Nat) (env : Environment) (state : State)
    (hcontext : ParamContext numParams lctx params) (hstate : state.NestedAuxScoped)
    (hrange : State.NewTypesRange numParams state)
    (hgenerated : ∀ (loopIndex : Nat) (ctorLctx : LocalContext) (ctorType : Expr) (As : Array Expr)
      (stepState : State), stepState.NestedAuxScoped →
      (replaceAllNested ctorLctx params As ctorType env stepState).WF fun returned =>
        State.NewTypesRange numParams returned.2 ∧ loopIndex < returned.2.newTypes.size) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      State.NewTypesRange numParams result.2 ∧ Result.TypesRange numParams result.1 := by
  induction fuel generalizing index state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · simp only [withParams.assert_size]
      have hindType : InductiveTypeRange numParams state.newTypes[index] :=
        hrange _ (Array.getElem_mem _)
      refine (mapM_newTypesRange numParams index state.newTypes[index].ctors _
        (pred := fun ctor => ConstructorRange numParams ctor) env state
        hstate hrange ?_ ?_).bind ?_
      · exact ‹index < state.newTypes.size›
      · intro ctor stepState hstep hstepRange hstepIndex hctorMem
        have hctorRange : ConstructorRange numParams ctor :=
          hindType.2 ctor hctorMem
        refine withParams.contextRange ctor.type numParams _ env stepState hctorRange hstep _ ?_
        intro ctorLctx ctorType As state' hvalid hreserved hscope hstate' htype'
        refine (replaceAllNested.rangeWithNewTypes numParams lctx ctorLctx params As ctorType env
          state' numParams index hvalid.context hcontext hstate'
          (hgenerated index ctorLctx ctorType As state' hstate') htype').bind ?_
        rintro ⟨newType, state''⟩ hnewType
        have hctor : ConstructorRange numParams { ctor with
          type := ctorLctx.mkForall As newType } :=
          by
            change (ctorLctx.mkForall As newType).looseBVarRange' ≤ numParams
            exact hvalid.mkForall_range hscope newType hnewType.2.2.2
        exact .pure ⟨hnewType.1, hnewType.2.1, hnewType.2.2.1, hctor⟩
      · rintro ⟨ctors, state'⟩ hctors
        simp only
        rw [modify_bind]
        have hnewType : InductiveTypeRange numParams {
            name := state.newTypes[index].name
            type := state.newTypes[index].type
            ctors } :=
          ⟨hindType.1, hctors.2.2.2⟩
        have hstate' := state_newTypesRange_set numParams index state'
          { name := state.newTypes[index].name, type := state.newTypes[index].type, ctors }
          hctors.2.1 hnewType
        exact ih (index + 1) { state' with
          newTypes := state'.newTypes.set! index {
            name := state.newTypes[index].name
            type := state.newTypes[index].type
            ctors } } hctors.1 hstate'
    · exact .pure ⟨hrange, by
        intro indType hmem
        exact hrange indType (by simpa using hmem)⟩

theorem run.nestedAuxScoped (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) (hstate : state.NestedAuxScoped) :
    (run fuel numParams types env state).WF fun result =>
      result.2.NestedAuxScoped ∧ Result.Aux2NestedScoped numParams result.1 := by
  cases types with
  | nil => exact Except.WF.throw
  | cons type types =>
    unfold run
    refine withParams.contextScope type.type numParams _ env state hstate _ ?_
    intro lctx remainder params state' hcontext hstate'
    exact run.loop.nestedAuxScoped numParams lctx params 0 fuel env state' hcontext hstate'

end Lean4Lean.ElimNestedInductive
