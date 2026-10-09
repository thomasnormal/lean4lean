import Lean4Lean.Verify.RecursorInfoScope

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.withLocalDecl_scope from Lean4Lean.Verify.RecursorInfoScope

theorem Context.RecursorScopeFrame.withEnv {original current : Context}
    (hframe : original.RecursorScopeFrame current) (env : Kernel.Environment) :
    ({ original with env } : Context).RecursorScopeFrame { current with env } :=
  ⟨⟨rfl, hframe.lparams, hframe.safety, hframe.allowPrimitive, hframe.fuel⟩,
    hframe.wf, hframe.reserved, hframe.declarations⟩

private theorem checkedHeader_loop_scope (nparams fuel : Nat) (stats : InductiveStats)
    (type : Expr) (index nindices : Nat) (next : Expr → InductiveStats → Nat → M ResultType)
    (ctx : Context) (post : ResultType → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ type stats nindices current, ctx.RecursorScopeFrame current →
      (next type stats nindices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next ctx).WF post := by
  induction fuel generalizing stats type index nindices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [checkInductiveTypes.loopInd.loop.eq_def]
    dsimp only
    split
    · split
      · split
        · apply Lean4Lean.AddInductive.withLocalDecl_scope
          · exact hwf
          · exact hreserved
          intro param current hframe
          apply Lean4Lean.AddInductive.bindWF
          intro normalized
          apply ih
          · exact hframe.wf
          · exact hframe.reserved
          intro type stats nindices final hfinal
          exact hnext type stats nindices final (hframe.trans hfinal)
        · apply Lean4Lean.AddInductive.bindWF
          intro paramType
          apply Lean4Lean.AddInductive.bindWF
          intro equal
          split
          · apply Lean4Lean.AddInductive.bindWF
            intro _
            apply Lean4Lean.AddInductive.bindWF
            intro normalized
            exact ih _ normalized _ _ ctx hwf hreserved hnext
          · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.withLocalDecl_scope
        · exact hwf
        · exact hreserved
        intro arg current hframe
        apply Lean4Lean.AddInductive.bindWF
        intro normalized
        apply ih
        · exact hframe.wf
        · exact hframe.reserved
        intro type stats nindices final hfinal
        exact hnext type stats nindices final (hframe.trans hfinal)
    · split
      · exact Except.WF.throw
      · exact hnext type stats nindices ctx (.refl ctx hwf hreserved)

private theorem checkedHeader_loopInd_scope (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (index : Nat) (stats : InductiveStats)
    (ctx : Context) (post : ResultType → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, ctx.RecursorScopeFrame current → (next stats current).WF post) :
    (checkInductiveTypes.loopInd nparams types next index stats ctx).WF post := by
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro _
    apply Lean4Lean.AddInductive.bindWF
    intro _
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro normalized
    apply checkedHeader_loop_scope
    · exact hwf
    · exact hreserved
    intro type stats nindices current hframe
    apply Lean4Lean.AddInductive.bindWF
    intro sort
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      apply checkedHeader_loopInd_scope
      · exact hframe.wf
      · exact hframe.reserved
      intro stats final hfinal
      exact hnext stats final (hframe.trans hfinal)
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        apply checkedHeader_loopInd_scope
        · exact hframe.wf
        · exact hframe.reserved
        intro stats final hfinal
        exact hnext stats final (hframe.trans hfinal)
  · apply Lean4Lean.AddInductive.readWF
    exact hnext _ ctx (.refl ctx hwf hreserved)
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.scope (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, ctx.RecursorScopeFrame current → (next stats current).WF post) :
    (checkInductiveTypes nparams types next ctx).WF post := by
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  exact checkedHeader_loopInd_scope nparams types next 0 _ ctx post hwf hreserved hnext

theorem checkInductiveTypes.getScopeStats (nparams : Nat) (types : Array InductiveType)
    (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx).WF
      fun result => ctx.RecursorScopeFrame result.2 ∧ result.1.HeaderSizes types.size ∧
        result.1.ParamsCount nparams types.size ∧ result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup := by
  have hscope : (checkInductiveTypes nparams types (fun stats => do
      return (stats, ← readThe Context)) ctx).WF fun result => ctx.RecursorScopeFrame result.2 := by
    apply checkInductiveTypes.scope
    · exact hwf
    · exact hreserved
    intro stats current hframe
    exact .pure hframe
  have hstats : (checkInductiveTypes nparams types (fun stats => do
      return (stats, ← readThe Context)) ctx).WF fun result => result.1.HeaderSizes types.size ∧
        result.1.ParamsCount nparams types.size ∧ result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup := by
    apply checkInductiveTypes.frameHeaderSizesParamsCountDistinct
    intro stats current hsizes hcount hfvars hnodup _
    exact .pure ⟨hsizes, hcount, hfvars, hnodup⟩
  intro result hresult
  exact ⟨hscope result hresult, hstats result hresult⟩

theorem checkInductiveTypes.constructorRootScope (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (next : InductiveStats → Context → M ResultType)
    (ctx : Context) (post : ResultType → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats root env,
      ({ ctx with env := root.env } : Context).RecursorScopeFrame root →
      (next stats root { root with env }).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested isUnsafe) do
        checkConstructors types stats isUnsafe
        let root ← readThe Context
        withEnv (← declareConstructors stats types isUnsafe) do
          next stats root) ctx).WF post := by
  apply checkInductiveTypes.scope
  · exact hwf
  · exact hreserved
  intro stats current hframe
  apply Lean4Lean.AddInductive.bindWF
  intro headers
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply Lean4Lean.AddInductive.readWF
  apply Lean4Lean.AddInductive.bindWF
  intro env
  exact hnext stats { current with env := headers } env (hframe.withEnv headers)

theorem checkInductiveTypes.getScopedConstructorRegistration (nparams : Nat)
    (types : Array InductiveType) (numNested : Nat) (ctx : Context)
    (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats types false) do
          return (stats, root, (← readThe Context).env)) ctx).WF fun result =>
      result.1.SafeConstructorRegistration nparams types numNested ctx result.2.1 result.2.2 ∧
      ({ ctx with env := result.2.1.env } : Context).RecursorScopeFrame result.2.1 := by
  have hscope : (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats types false) do
          return (stats, root, (← readThe Context).env)) ctx).WF fun result =>
        ({ ctx with env := result.2.1.env } : Context).RecursorScopeFrame result.2.1 := by
    apply checkInductiveTypes.constructorRootScope
    · exact hwf
    · exact hreserved
    intro stats root env hframe
    apply Lean4Lean.AddInductive.readWF
    exact .pure hframe
  intro result hresult
  exact ⟨checkInductiveTypes.getSafeConstructorRegistration nparams types numNested ctx hmap result hresult,
    hscope result hresult⟩

end Lean4Lean.AddInductive
