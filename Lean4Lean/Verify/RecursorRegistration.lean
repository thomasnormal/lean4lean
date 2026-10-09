import Lean4Lean.Verify.ConstructorMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata

private theorem forIn'_preserves (items : List α) (initial : Kernel.Environment)
    (state : Nat) (ctx : Context)
    (step : (item : α) → item ∈ items → Kernel.Environment → StateT Nat M
      (ForInStep Kernel.Environment))
    (hwf : initial.constants.WF)
    (hstep : ∀ item hmem env state, env.constants.WF →
      (step item hmem env state ctx).WF fun result =>
        ∃ next, result.1 = .yield next ∧ next.constants.WF ∧
          ∀ name info, env.find? name = some info → next.find? name = some info) :
    (forIn' items initial step state ctx).WF fun result =>
      result.1.constants.WF ∧
        ∀ name info, initial.find? name = some info → result.1.find? name = some info := by
  induction items generalizing initial state with
  | nil => exact .pure ⟨hwf, fun _ _ hold => hold⟩
  | cons item items ih =>
    rw [List.forIn'_cons]
    refine (hstep item (by simp) initial state hwf).bind ?_
    rintro ⟨_, nextState⟩ ⟨next, rfl, hnext, hkeep⟩
    refine (ih next nextState (fun entry hmem env => step entry (by simp [hmem]) env)
      hnext (fun entry hmem env state hwf => hstep entry (by simp [hmem]) env state hwf)).mono ?_
    rintro result ⟨hfinal, hrest⟩
    exact ⟨hfinal, fun name info hold => hrest name info (hkeep name info hold)⟩

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

theorem declareRecursors.preserves (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (recInfos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats indTypes elimLevel recInfos lparams lctx isK isUnsafe ctx).WF
      fun env => env.constants.WF ∧
        ∀ name info, ctx.env.find? name = some info → env.find? name = some info := by
  unfold declareRecursors
  dsimp only
  simp only [pure_bind, bind_pure]
  apply Except.WF.map
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_preserves
    · exact hwf
    · intro index hindex env state henv
      have hbound : index < indTypes.size := by simpa using hindex
      apply stateBindWF
      intro rules nextState
      refine stateExceptBindWF (Lean4Lean.checkName.WF env
        (mkRecName indTypes[index].name) ctx.allowPrimitive) ?_
      rintro _ ⟨hfresh, _⟩
      refine .pure ⟨_, rfl, ?_, ?_⟩
      · exact (Lean4Lean.AddInductive.addFresh env _ henv (by exact hfresh)).1
      · exact (Lean4Lean.AddInductive.addFresh env _ henv (by exact hfresh)).2.2
  · intro result hresult
    exact hresult

end Lean4Lean.AddInductive
