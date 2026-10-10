import Lean4Lean.Verify.ConstructorMetadata
import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

private theorem forIn'_preservesValues (items : List α) (initial : Kernel.Environment)
    (state : Nat) (ctx : Context)
    (step : (item : α) → item ∈ items → Kernel.Environment → StateT Nat M
      (ForInStep Kernel.Environment))
    (hwf : initial.constants.WF)
    (hstep : ∀ item hmem env state, env.constants.WF →
      (step item hmem env state ctx).WF fun result =>
        ∃ next, result.1 = .yield next ∧ NativeValueFrame env next) :
    (forIn' items initial step state ctx).WF fun result =>
      NativeValueFrame initial result.1 := by
  induction items generalizing initial state with
  | nil => exact .pure (.refl hwf)
  | cons item items ih =>
    rw [List.forIn'_cons]
    refine (hstep item (by simp) initial state hwf).bind ?_
    rintro ⟨_, nextState⟩ ⟨next, rfl, hnext⟩
    refine (ih next nextState (fun entry hmem env => step entry (by simp [hmem]) env)
      hnext.map_wf (fun entry hmem env state hwf => hstep entry (by simp [hmem]) env state hwf)).mono
        fun _ hrest => hnext.trans hrest

private theorem stateBindWF {action : StateT Nat M α} {next : α → StateT Nat M β}
    {state : Nat} {ctx : Context} {post : β × Nat → Prop}
    (hnext : ∀ result nextState, (next result nextState ctx).WF post) :
    ((action >>= next) state ctx).WF post := by
  exact (show (action state ctx).WF (fun _ => True) from fun _ _ => trivial).bind
    fun result _ => hnext result.1 result.2

private theorem stateExceptBindWF {action : Except Kernel.Exception α}
    {next : α → StateT Nat M β} {state : Nat} {ctx : Context}
    {invariant : α → Prop} {post : β × Nat → Prop}
    (haction : action.WF invariant)
    (hnext : ∀ result, invariant result → (next result state ctx).WF post) :
    ((liftM action >>= next) state ctx).WF post := by
  change ((action >>= fun result => pure (result, state)) >>=
    fun result => next result.1 result.2 ctx).WF post
  simpa only [bind_assoc, pure_bind] using haction.bind hnext

theorem declareRecursors.preservesValues (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (recInfos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats indTypes elimLevel recInfos lparams lctx isK isUnsafe ctx).WF
      (NativeValueFrame ctx.env) := by
  unfold declareRecursors
  dsimp only
  simp only [pure_bind, bind_pure]
  apply Except.WF.map
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_preservesValues
    · exact hwf
    · intro index hindex env state henv
      have hbound : index < indTypes.size := by simpa using hindex
      apply stateBindWF
      intro rules nextState
      refine stateExceptBindWF (Lean4Lean.checkName.WF env
        (mkRecName indTypes[index].name) ctx.allowPrimitive) ?_
      rintro _ ⟨hfresh, _⟩
      exact .pure ⟨_, rfl, NativeValueFrame.addConst henv hfresh rfl⟩
  · intro result hresult
    exact hresult

theorem declareRecursors.preserves (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (recInfos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats indTypes elimLevel recInfos lparams lctx isK isUnsafe ctx).WF
      fun env => env.constants.WF ∧
        ∀ name info, ctx.env.find? name = some info → env.find? name = some info := by
  refine (declareRecursors.preservesValues stats indTypes elimLevel recInfos lparams lctx
    isK isUnsafe ctx hwf).mono ?_
  intro env hframe
  refine ⟨hframe.map_wf, ?_⟩
  intro name info hold
  simpa only [Kernel.Environment.find?, hframe.map_wf.find?'_eq_find?] using
    hframe.lookups (by simpa only [Kernel.Environment.find?, hwf.find?'_eq_find?] using hold)

end Lean4Lean.AddInductive
