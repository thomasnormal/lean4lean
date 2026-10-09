import Lean4Lean.Verify.InductiveRestorationConstructors
import Lean4Lean.Verify.InductiveParamBinding

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel
open AddInductive.declareConstructors

theorem mkAppList_arity (head : Expr) (args : List Expr) (hhead : arity 0 head = 0) :
    arity 0 (Expr.mkAppList head args) = 0 := by
  induction args generalizing head with
  | nil => exact hhead
  | cons arg args ih => exact ih (.app head arg) rfl

theorem mkAppN_arity (head : Expr) (args : Array Expr) (hhead : arity 0 head = 0) :
    arity 0 (mkAppN head args) = 0 := by
  change arity 0 (args.foldl Expr.app head) = 0
  rw [← Array.foldl_toList, ← Expr.mkAppList_eq_foldl]
  exact mkAppList_arity head args.toList hhead

theorem mkAppRange_tail_arity (head : Expr) (args : Array Expr) (start : Nat)
    (hstart : start ≤ args.size) (hhead : arity 0 head = 0) :
    arity 0 (mkAppRange head start args.size args) = 0 := by
  rw [Expr.mkAppRange_eq (e := head) (args := args) (i := start) (j := args.size)
    (l₁ := args.toList.take start) (l₂ := args.toList.drop start) (l₃ := [])
    (by simp [List.take_append_drop])]
  · exact mkAppList_arity head _ hhead
  · simp [List.length_take, Nat.min_eq_left hstart]
  · simp

private def OptionArityZero : Option Expr → Prop
  | none => True
  | some type => arity 0 type = 0

private def StepArityZero : ForInStep (Option Expr) → Prop
  | .done result => OptionArityZero result
  | .yield result => OptionArityZero result

private theorem bindAny (action : M Value) (next : Value → M ResultValue)
    (env : Environment) (state : State) (post : ResultValue × State → Prop)
    (hnext : ∀ value current, (next value env current).WF post) :
    ((action >>= next) env state).WF post :=
  (show (action env state).WF (fun _ => True) from fun _ _ => trivial).bind
    fun current _ => hnext current.1 current.2

private theorem forInArityZero (items : List Value) (initial : Option Expr)
    (step : Value → Option Expr → M (ForInStep (Option Expr))) (env : Environment) (state : State)
    (hinitial : OptionArityZero initial)
    (hstep : ∀ item result current, OptionArityZero result →
      (step item result env current).WF fun returned => StepArityZero returned.1) :
    (forIn items initial step env state).WF fun returned => OptionArityZero returned.1 := by
  induction items generalizing initial state with
  | nil => exact .pure hinitial
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item initial state hinitial).bind ?_
    rintro ⟨next, current⟩ hnext
    cases next with
    | done result => exact .pure hnext
    | yield result => exact ih result current hnext

open private Lean4Lean.ElimNestedInductive.get_bind Lean4Lean.ElimNestedInductive.read_bind
  Lean4Lean.ElimNestedInductive.modify_bind Lean4Lean.ElimNestedInductive.liftM_ok_eq
  from Lean4Lean.Verify.InductiveNestedRewrite

private theorem nestedIterationArityZero (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (info : InductiveVal) (headName : Name) (levels : List Level)
    (name : Name) (result : Option Expr) (env : Environment) (state : State)
    (hstart : info.numParams ≤ type.getAppArgs.size) (hresult : OptionArityZero result) :
    ((do
      let .inductInfo nestedInfo ← env.get name | do
        (unreachable! : M PUnit)
        pure (.yield result)
      let nested := Expr.const name levels
      let nestedApp := mkAppRange nested 0 info.numParams type.getAppArgs
      let auxName ← mkUniqueName (`_nested ++ name)
      let auxType ← instantiateForallParams
        (nestedInfo.type.instantiateLevelParams nestedInfo.levelParams levels) info.numParams type.getAppArgs
      let nestedApp' ← replaceParams params nestedApp sourceParams
      modify fun current => { current with nestedAux := current.nestedAux.push (nestedApp', auxName) }
      let mut result := result
      if name == headName then
        result := some (mkAppRange (mkAppN (.const auxName (← get).lvls) sourceParams)
          info.numParams type.getAppArgs.size type.getAppArgs)
      let ctors ← nestedInfo.ctors.mapM fun ctorName => do
        let ctor ← env.get ctorName
        let ctorType ← instantiateForallParams
          (ctor.type.instantiateLevelParams ctor.levelParams levels) info.numParams type.getAppArgs
        pure { name := ctorName.replacePrefix name auxName, type := lctx.mkForall sourceParams ctorType }
      let newType : InductiveType := { name := auxName, type := lctx.mkForall sourceParams auxType, ctors }
      modify fun current => { current with newTypes := current.newTypes.push newType }
      pure (.yield result) : M (ForInStep (Option Expr))) env state).WF fun returned =>
      StepArityZero returned.1 := by
  generalize hget : env.get name = found
  cases found with
  | error exception => exact .throw
  | ok constant =>
    cases constant with
    | inductInfo nestedInfo =>
      rw [Lean4Lean.ElimNestedInductive.liftM_ok_eq]
      simp only [pure_bind]
      apply bindAny
      intro auxName current
      apply bindAny
      intro auxType current'
      apply bindAny
      intro nestedApp current''
      rw [Lean4Lean.ElimNestedInductive.modify_bind]
      split
      · rw [Lean4Lean.ElimNestedInductive.get_bind]
        dsimp only
        apply bindAny
        intro ctors next
        rw [Lean4Lean.ElimNestedInductive.modify_bind]
        exact .pure (mkAppRange_tail_arity _ _ _ hstart (mkAppN_arity _ _ rfl))
      · apply bindAny
        intro ctors next
        rw [Lean4Lean.ElimNestedInductive.modify_bind]
        exact .pure hresult
    | _ => exact .pure hresult

private theorem replaceIfNested.arityZero (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (env : Environment) (state : State) :
    (replaceIfNested lctx params sourceParams type env state).WF fun result => OptionArityZero result.1 := by
  unfold replaceIfNested
  refine (isNestedInductiveApp?.scope type env state).bind ?_
  rintro ⟨selected, current⟩ ⟨hframe, hselected⟩
  dsimp only at hframe hselected
  subst current
  cases selected with
  | none => exact .pure trivial
  | some info =>
    dsimp only
    rw [Expr.withApp_eq]
    obtain ⟨⟨headName, levels, hhead⟩, hstart, _⟩ := hselected info rfl
    rw [hhead]
    simp only [if_pos hstart]
    apply bindAny
    intro replaced current
    rw [Lean4Lean.ElimNestedInductive.get_bind]
    generalize hfound : Array.findSome? _ current.nestedAux = found
    cases found with
    | some auxName => exact .pure (mkAppRange_tail_arity _ _ _ hstart (mkAppN_arity _ _ rfl))
    | none =>
      dsimp only
      simp only [pure_bind]
      rw [Lean4Lean.ElimNestedInductive.read_bind]
      refine (forInArityZero info.all none _ env current trivial ?_).bind ?_
      · intro name result next hresult
        simpa only [panicWithPosWithDecl, panic, panicCore, pure_bind] using
          nestedIterationArityZero lctx params sourceParams type info headName levels name result env next
            hstart hresult
      · rintro ⟨returned, next⟩ hreturned
        cases returned <;> exact .pure hreturned

private theorem replaceMArity (step : Expr → M (Option Expr))
    (hstep : ∀ type current, (step type env current).WF fun result =>
      ∀ rewritten, result.1 = some rewritten → arity 0 rewritten = arity 0 type)
    (type : Expr) (state : State) :
    (type.replaceM step env state).WF fun result => arity 0 result.1 = arity 0 type := by
  unfold Expr.replaceM
  induction type generalizing state with
  | forallE name domain body bi ihDomain ihBody =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _).bind ?_
    rintro ⟨selected, current⟩ hselected
    cases selected with
    | some rewritten => exact .pure (hselected _ rfl)
    | none =>
      apply bindAny
      intro rewrittenDomain next
      refine (ihBody next).bind ?_
      rintro ⟨rewrittenBody, final⟩ harity
      exact .pure (by
        change arity 1 rewrittenBody = arity 1 body
        rw [arity_eq_add rewrittenBody 1, arity_eq_add body 1]
        exact congrArg (1 + ·) harity)
  | _ =>
    unfold Expr.replaceNoCacheT
    refine (hstep _ _).bind ?_
    rintro ⟨selected, current⟩ hselected
    cases selected
    all_goals
      repeat' first
      | exact .pure (hselected _ rfl)
      | exact .pure rfl
      | apply bindAny
        intro rewritten next

theorem replaceIfNested.arity (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (env : Environment) (state : State) :
    (replaceIfNested lctx params sourceParams type env state).WF fun result =>
      ∀ rewritten, result.1 = some rewritten → arity 0 rewritten = arity 0 type := by
  cases type with
  | forallE name domain body bi =>
    exact .pure (by intro rewritten heq; cases heq)
  | _ =>
    intro result hresult rewritten heq
    have hzero := replaceIfNested.arityZero lctx params sourceParams _ env state result hresult
    simpa only [heq, OptionArityZero, arity] using hzero

theorem replaceAllNested.arity (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (env : Environment) (state : State) :
    (replaceAllNested lctx params sourceParams type env state).WF fun result =>
      arity 0 result.1 = arity 0 type :=
  replaceMArity (replaceIfNested lctx params sourceParams)
    (fun type current => replaceIfNested.arity lctx params sourceParams type env current) type state

private theorem withParams_loop_bind (remaining : Nat) (type : Expr)
    (lctx : LocalContext) (params : Array Expr)
    (next : LocalContext → Expr → Array Expr → M Value) :
    withParams.loop next lctx type params remaining =
      (withParams.loop (fun lctx remainder params => pure (lctx, remainder, params))
        lctx type params remaining >>= fun result => next result.1 result.2.1 result.2.2) := by
  induction remaining generalizing type lctx params with
  | zero => simp only [withParams.loop, pure_bind]
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi => simp only [withParams.loop, ih, bind_assoc]
    | _ => rfl

theorem withParams.bind (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M Value) :
    withParams type numParams next =
      (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params)) >>=
        fun result => next result.1 result.2.1 result.2.2) :=
  withParams_loop_bind numParams type {} #[] next

theorem withParams.replaceAllNested_arity (type : Expr) (numParams : Nat) (params : Array Expr)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder sourceParams => do
      return lctx.mkForall sourceParams (← replaceAllNested lctx params sourceParams remainder))
      env state).WF fun result => arity 0 result.1 = arity 0 type := by
  rw [withParams.bind]
  have hgetter : (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamPrefix numParams type result.1.2.1 result.1.2.2 ∧
        ParamValidity numParams result.1.1 result.1.2.2 := by
    intro result hresult
    exact ⟨withParams.getPrefix type numParams env state result hresult,
      (withParams.getValidContext type numParams env state result hresult).1⟩
  refine hgetter.bind ?_
  rintro ⟨⟨lctx, remainder, sourceParams⟩, current⟩ ⟨hprefix, hvalid⟩
  refine (replaceAllNested.arity lctx params sourceParams remainder env current).bind ?_
  rintro ⟨rewritten, next⟩ harity
  exact .pure (by rw [hvalid.mkForall_arity, harity]; exact hprefix.2.1.symm)

theorem withParams.rewriteConstructor (ctor : Constructor) (numParams : Nat) (params : Array Expr)
    (env : Environment) (state : State) :
    (withParams ctor.type numParams (fun lctx remainder sourceParams => do
      return { ctor with type := lctx.mkForall sourceParams (← replaceAllNested lctx params sourceParams remainder) })
      env state).WF fun result =>
      result.1.name = ctor.name ∧ arity 0 result.1.type = arity 0 ctor.type ∧
        TypePrefix state.newTypes result.2.newTypes := by
  rw [withParams.bind]
  have hframe := withParams.typesPrefix ctor.type numParams
    (fun lctx remainder params => pure (lctx, remainder, params)) env state
    (fun _ _ _ _ => .pure (.refl _))
  have hgetter : (withParams ctor.type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamPrefix numParams ctor.type result.1.2.1 result.1.2.2 ∧
        ParamValidity numParams result.1.1 result.1.2.2 ∧ TypePrefix state.newTypes result.2.newTypes := by
    intro result hresult
    exact ⟨withParams.getPrefix ctor.type numParams env state result hresult,
      (withParams.getValidContext ctor.type numParams env state result hresult).1, hframe result hresult⟩
  refine hgetter.bind ?_
  rintro ⟨⟨lctx, remainder, sourceParams⟩, current⟩ ⟨hprefix, hvalid, htypes⟩
  have hreplace : (replaceAllNested lctx params sourceParams remainder env current).WF fun result =>
      arity 0 result.1 = arity 0 remainder ∧ TypePrefix current.newTypes result.2.newTypes := by
    intro result hresult
    exact ⟨replaceAllNested.arity lctx params sourceParams remainder env current result hresult,
      replaceAllNested.typesPrefix lctx params sourceParams remainder env current result hresult⟩
  refine hreplace.bind ?_
  rintro ⟨rewritten, next⟩ ⟨harity, hrewritten⟩
  exact .pure ⟨rfl, by rw [hvalid.mkForall_arity, harity]; exact hprefix.2.1.symm,
    htypes.trans hrewritten⟩

end Lean4Lean.ElimNestedInductive
