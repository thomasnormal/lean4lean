import Lean4Lean.Verify.ConstructorArity.Basic
import Lean4Lean.Environment

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace ElimNestedInductive

def ParamPrefix (numParams : Nat) (original remainder : Expr) (params : Array Expr) : Prop :=
  params.size = numParams ∧
    AddInductive.declareConstructors.arity 0 original =
      numParams + AddInductive.declareConstructors.arity 0 remainder ∧
    ∀ param ∈ params, param.isFVar = true

private theorem withParams_loop_prefix (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hfvars : ∀ param ∈ params, param.isFVar = true)
    (hnext : ∀ lctx' remainder params' state',
      params'.size = params.size + remaining →
      AddInductive.declareConstructors.arity 0 type =
        remaining + AddInductive.declareConstructors.arity 0 remainder →
      (∀ param ∈ params', param.isFVar = true) →
      (next lctx' remainder params' env state').WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero => exact hnext lctx type params state (by simp) (by simp) hfvars
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      change (withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next }).WF post
      apply ih
      · intro param hparam
        simp only [Array.mem_push] at hparam
        rcases hparam with hparam | rfl
        · exact hfvars param hparam
        · rfl
      · intro lctx' remainder params' state' hsize harity hfvars'
        apply hnext lctx' remainder params' state'
        · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize
        · change AddInductive.declareConstructors.arity 1 body = _
          rw [AddInductive.declareConstructors.arity_instantiate1_fvar] at harity
          rw [AddInductive.declareConstructors.arity_eq_add]
          omega
        · exact hfvars'
    | _ => exact Except.WF.throw

theorem withParams.prefix (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamPrefix numParams type remainder params →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post := by
  apply withParams_loop_prefix
  · simp
  · intro lctx remainder params state' hsize harity hfvars
    exact hnext lctx remainder params state' ⟨by simpa using hsize, harity, hfvars⟩

theorem withParams.paramArity (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Environment) (state : State) :
    (withParams type numParams next env state).WF fun _ =>
      numParams ≤ AddInductive.declareConstructors.arity 0 type :=
  withParams.prefix type numParams next env state _ fun _ _ _ _ hprefix _ _ => by
    have harity := hprefix.2.1
    omega

theorem withParams.getPrefix (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamPrefix numParams type result.1.2.1 result.1.2.2 :=
  withParams.prefix type numParams _ env state _ fun _ _ _ _ hprefix => .pure hprefix

private theorem withParams_loop_assert_size (remaining numParams : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next mismatch : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State) (hsize : params.size + remaining = numParams) :
    withParams.loop (fun lctx remainder params =>
      if params.size == numParams then next lctx remainder params else mismatch lctx remainder params)
      lctx type params remaining env state =
    withParams.loop next lctx type params remaining env state := by
  induction remaining generalizing type lctx params state with
  | zero =>
    simp only [Nat.add_zero] at hsize
    simp [withParams.loop, hsize]
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      change withParams.loop _
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next } = _
      apply ih
      simp only [Array.size_push]
      omega
    | _ => rfl

theorem withParams.assert_size (type : Expr) (numParams : Nat)
    (next mismatch : LocalContext → Expr → Array Expr → M α) :
    withParams type numParams (fun lctx remainder params =>
      if params.size == numParams then next lctx remainder params else mismatch lctx remainder params)
      = withParams type numParams next := by
  funext env state
  exact withParams_loop_assert_size numParams numParams type {} #[] next mismatch env state (by simp)

private theorem bindWF (action : M α) (next : α → M β)
    (env : Environment) (state : State) (post : β × State → Prop)
    (hnext : ∀ value state', (next value env state').WF post) :
    ((action >>= next) env state).WF post :=
  (show (action env state).WF fun _ => True from fun _ _ => trivial).bind
    fun result _ => hnext result.1 result.2

theorem run.loop.paramCount (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Environment) (state : State) (hsize : params.size = numParams) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      result.1.nparams = numParams := by
  induction fuel generalizing index state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    apply bindWF
    intro current state'
    split
    · simp only [withParams.assert_size]
      apply bindWF
      intro ctors state''
      apply bindWF
      intro _ state'''
      exact ih (index + 1) state'''
    · exact .pure hsize

theorem run.paramCount (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result => result.1.nparams = numParams := by
  cases types with
  | nil => exact Except.WF.throw
  | cons type types =>
    unfold run
    apply withParams.prefix
    intro lctx remainder params state' hprefix
    exact run.loop.paramCount numParams lctx params 0 fuel env state' hprefix.1

theorem run.paramCount_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      result.nparams = numParams :=
  (run.paramCount fuel numParams types env state).map fun _ hcount => hcount

private theorem withParams_loop_reject (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M α)
    (env : Environment) (state : State)
    (hsmall : AddInductive.declareConstructors.arity 0 type < remaining) :
    withParams.loop next lctx type params remaining env state =
      .error (.other "invalid inductive datatype declaration, incorrect number of parameters") := by
  induction remaining generalizing type lctx params state with
  | zero => omega
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      change withParams.loop next
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (params.push (.fvar ⟨state.ngen.curr⟩)) remaining env
        { state with ngen := state.ngen.next } = _
      apply ih
      rw [AddInductive.declareConstructors.arity_instantiate1_fvar]
      change AddInductive.declareConstructors.arity 1 body < remaining + 1 at hsmall
      rw [AddInductive.declareConstructors.arity_eq_add] at hsmall
      omega
    | _ => rfl

theorem withParams.reject_of_arity_lt (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Environment) (state : State)
    (hsmall : AddInductive.declareConstructors.arity 0 type < numParams) :
    withParams type numParams next env state =
      .error (.other "invalid inductive datatype declaration, incorrect number of parameters") :=
  withParams_loop_reject numParams type {} #[] next env state hsmall

theorem run.reject_of_paramArity (fuel numParams : Nat) (type : InductiveType)
    (types : List InductiveType) (env : Environment) (state : State)
    (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    run fuel numParams (type :: types) env state =
      .error (.other "invalid inductive datatype declaration, incorrect number of parameters") := by
  unfold run
  exact withParams.reject_of_arity_lt type.type numParams _ env state hsmall

end ElimNestedInductive

theorem Environment.addInductive.reject_of_paramArity (env : Environment)
    (lparams : List Name) (numParams : Nat) (type : InductiveType) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    addInductive env lparams numParams (type :: types) isUnsafe allowPrimitive fuel =
      .error (.other "invalid inductive datatype declaration, incorrect number of parameters") := by
  unfold addInductive
  simp only [StateT.run']
  rw [ElimNestedInductive.run.reject_of_paramArity _ _ _ _ _ _ hsmall]
  rfl

theorem addDecl.inductiveParamArity (env : Environment) (lparams : List Name)
    (numParams : Nat) (type : InductiveType) (types : List InductiveType)
    (isUnsafe check : Bool) (fuel : FuelConfig) :
    (addDecl env (.inductDecl lparams numParams (type :: types) isUnsafe) check fuel).WF fun _ =>
      numParams ≤ AddInductive.declareConstructors.arity 0 type.type := by
  by_cases hbound : numParams ≤ AddInductive.declareConstructors.arity 0 type.type
  · exact fun _ _ => hbound
  · have hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams := by omega
    unfold addDecl
    refine (show (Environment.checkPrimitiveInductive env lparams numParams
      (type :: types) isUnsafe).WF fun _ => True from fun _ _ => trivial).bind ?_
    intro allowPrimitive _
    rw [Environment.addInductive.reject_of_paramArity _ _ _ _ _ _ _ _ hsmall]
    exact Except.WF.throw

theorem addDecl.reject_inductive_of_paramArity (env result : Environment)
    (lparams : List Name) (numParams : Nat) (type : InductiveType) (types : List InductiveType)
    (isUnsafe check : Bool) (fuel : FuelConfig)
    (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    addDecl env (.inductDecl lparams numParams (type :: types) isUnsafe) check fuel ≠ .ok result := by
  intro hresult
  have hbound := addDecl.inductiveParamArity env lparams numParams type types isUnsafe check fuel
    result hresult
  omega

end Lean4Lean
