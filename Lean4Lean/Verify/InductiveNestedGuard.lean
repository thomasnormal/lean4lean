import Lean4Lean.Verify.InductiveNestedRebinding

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

private theorem read_bind (next : Environment → M α) (env : Environment) (state : State) :
    ((read >>= next) env state) = next env env state := rfl

private theorem get_bind (next : State → M α) (env : Environment) (state : State) :
    ((get >>= next) env state) = next state env state := rfl

private theorem scanScope (items : List Nat) (initial : MProd Bool Bool)
    (step : Nat → MProd Bool Bool → M (ForInStep (MProd Bool Bool)))
    (property : Nat → Prop) (env : Environment) (state : State)
    (hstep : ∀ index flags state', (step index flags env state').WF fun returned =>
      ∃ next, returned.1 = .yield next ∧ returned.2 = state' ∧
        (next.snd = false → flags.snd = false ∧ property index)) :
    (forIn items initial step env state).WF fun returned =>
      returned.2 = state ∧ (returned.1.snd = false →
        initial.snd = false ∧ ∀ index ∈ items, property index) := by
  induction items generalizing initial state with
  | nil => exact .pure ⟨rfl, fun hflag => ⟨hflag, by simp⟩⟩
  | cons index items ih =>
    rw [List.forIn_cons]
    refine (hstep index initial state).bind ?_
    rintro _ ⟨next, hyield, hstate, hscope⟩
    simp only [hyield, hstate]
    refine (ih next state).mono ?_
    intro returned hrest
    refine ⟨hrest.1, fun hflag => ?_⟩
    have htail := hrest.2 hflag
    have hhead := hscope htail.1
    refine ⟨hhead.1, fun other hmem => ?_⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hhead.2
    · exact htail.2 other hmem

def NestedAppScope (type : Expr) (info : InductiveVal) : Prop :=
  (∃ name levels, type.getAppFn = .const name levels) ∧
    info.numParams ≤ type.getAppArgs.size ∧
    ∀ index, index < info.numParams → type.getAppArgs[index]!.hasLooseBVars = false

theorem isNestedInductiveApp?.scope (type : Expr) (env : Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned =>
      returned.2 = state ∧ ∀ info, returned.1 = some info → NestedAppScope type info := by
  unfold isNestedInductiveApp?
  split
  · exact .pure ⟨rfl, by simp⟩
  · simp only [pure_bind]
    cases hhead : type.getAppFn with
    | const name levels =>
      dsimp only
      rw [read_bind]
      cases hlookup : env.find? name with
      | none => exact .pure ⟨rfl, by simp⟩
      | some constant =>
        cases constant with
        | inductInfo info =>
          dsimp only
          split
          · exact .pure ⟨rfl, by simp⟩
          · simp only [Std.Legacy.Range.forIn_eq_forIn_range',
              Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
            refine (scanScope _ _ _
              (fun index => type.getAppArgs[index]!.hasLooseBVars = false) env state ?_).bind ?_
            · intro index flags state'
              dsimp only
              split
              · rw [get_bind]
                generalize hfound : Expr.find? _ _ = found
                cases found <;> exact .pure ⟨_, rfl, rfl, by simp⟩
              · rename_i hflag
                have hloose : type.getAppArgs[index]!.hasLooseBVars = false := by simpa using hflag
                rw [get_bind]
                generalize hfound : Expr.find? _ _ = found
                cases found <;> exact .pure ⟨_, rfl, rfl, fun hnext => ⟨hnext, hloose⟩⟩
            · rintro ⟨flags, _⟩ ⟨rfl, hscope⟩
              dsimp only
              split
              · exact .pure ⟨rfl, by simp⟩
              · split
                · exact Except.WF.throw
                · rename_i hflag
                  refine .pure ⟨rfl, ?_⟩
                  intro accepted haccepted
                  cases haccepted
                  refine ⟨⟨name, levels, hhead⟩, by omega, ?_⟩
                  intro index hindex
                  have hflagsFalse : flags.snd = false := by simpa using hflag
                  exact (hscope hflagsFalse).2 index (by simp; omega)
        | _ => exact .pure ⟨rfl, by simp⟩
    | _ => exact .pure ⟨rfl, by simp⟩

theorem isNestedInductiveApp?.frame (type : Expr) (env : Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned => returned.2 = state :=
  (isNestedInductiveApp?.scope type env state).mono fun _ hscope => hscope.1

theorem NestedAppScope.argRange {type : Expr} {info : InductiveVal}
    (hscope : NestedAppScope type info) (index : Nat) (hindex : index < info.numParams) :
    type.getAppArgs[index]!.looseBVarRange' = 0 := by
  have hflag := hscope.2.2 index hindex
  simpa [Expr.hasLooseBVars] using hflag

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

theorem NestedAppScope.prefixRange {type : Expr} {info : InductiveVal}
    (hscope : NestedAppScope type info) :
    (mkAppRange type.getAppFn 0 info.numParams type.getAppArgs).looseBVarRange' = 0 := by
  have hlength : (type.getAppArgs.toList.take info.numParams).length = info.numParams := by
    simp [List.length_take, Nat.min_eq_left hscope.2.1]
  rw [Expr.mkAppRange_eq (e := type.getAppFn) (args := type.getAppArgs)
    (i := 0) (j := info.numParams)
    (l₁ := []) (l₂ := type.getAppArgs.toList.take info.numParams)
    (l₃ := type.getAppArgs.toList.drop info.numParams) (by simp) rfl (by simpa using hlength)]
  apply mkAppList_scope
  · rcases hscope.1 with ⟨name, levels, hhead⟩
    rw [hhead]
    rfl
  · intro arg hmem
    rcases List.mem_iff_getElem.mp hmem with ⟨index, hindex, heq⟩
    have hparam : index < info.numParams := hlength ▸ hindex
    have harg : index < type.getAppArgs.size := Nat.lt_of_lt_of_le hparam hscope.2.1
    rw [List.getElem_take, Array.getElem_toList harg] at heq
    rw [← heq, ← getElem!_pos type.getAppArgs index harg]
    exact hscope.argRange index hparam

theorem isNestedInductiveApp?.prefixScope (type : Expr) (env : Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned =>
      returned.2 = state ∧ ∀ info, returned.1 = some info →
        (mkAppRange type.getAppFn 0 info.numParams type.getAppArgs).looseBVarRange' = 0 :=
  (isNestedInductiveApp?.scope type env state).mono fun _ hscope =>
    ⟨hscope.1, fun info hinfo => (hscope.2 info hinfo).prefixRange⟩

theorem isNestedInductiveApp?.prefixScopeFlag (type : Expr) (env : Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned =>
      returned.2 = state ∧ ∀ info, returned.1 = some info →
        (mkAppRange type.getAppFn 0 info.numParams type.getAppArgs).hasLooseBVars = false :=
  (isNestedInductiveApp?.prefixScope type env state).mono fun _ hscope =>
    ⟨hscope.1, fun info hinfo => noLooseBVars_flag _ (hscope.2 info hinfo)⟩

theorem isNestedInductiveApp?.checkedRebinding (type : Expr) (numParams : Nat)
    (source : LocalContext) (sourceParams : Array Expr) (target : Result)
    (env : Environment) (state : State) (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamValidity numParams target.lctx target.params) :
    ((do
      let some info ← isNestedInductiveApp? type | return none
      let rebound ← replaceParams target.params
        (mkAppRange type.getAppFn 0 info.numParams type.getAppArgs) sourceParams
      return some rebound : M (Option Expr)) env state).WF fun returned =>
        returned.2 = state ∧ ∀ rebound, returned.1 = some rebound →
          (target.openAux (rebound.abstract target.params)).hasLooseBVars = false := by
  refine (isNestedInductiveApp?.scope type env state).bind ?_
  rintro ⟨selected, state'⟩ ⟨hstate, hselected⟩
  dsimp only at hstate hselected
  subst state'
  cases selected with
  | none => exact .pure ⟨rfl, by simp⟩
  | some info =>
    dsimp only
    refine (replaceParams.noLooseBVars numParams source target.lctx sourceParams target.params
      _ env state hsource htarget.context (hselected info rfl).prefixRange).bind ?_
    rintro ⟨rebound, _⟩ ⟨hrebound, rfl⟩
    refine .pure ⟨rfl, ?_⟩
    intro accepted haccepted
    cases haccepted
    exact target.openAux_scopeFlag numParams _ htarget
      (htarget.context.abstract_scopedRange rebound hrebound)

end Lean4Lean.ElimNestedInductive
