import Lean4Lean.Verify.RecursorFieldScope

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

private theorem withLocalDecl_scope {ctx : Context} {name : Name} {bi : BinderInfo} {type : Expr}
    {next : Expr → M α} {post : α → Prop} (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ arg current, ctx.RecursorScopeFrame current → (next arg current).WF post) :
    (withLocalDecl name bi type next ctx).WF post :=
  hnext _ _ (Context.RecursorScopeFrame.push ctx hwf hreserved name bi type)

private theorem loopArgs1_scope (stats : InductiveStats) (type : Expr) (index : Nat)
    (indices : Array Expr) (fuel : Nat) (next : Array Expr → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ indices current, ctx.RecursorScopeFrame current → (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats type index indices fuel next ctx).WF post := by
  induction fuel generalizing type index indices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopArgs1.eq_def]
    split
    · split
      · apply Lean4Lean.AddInductive.bindWF
        intro normalized
        exact ih normalized _ _ ctx hwf hreserved hnext
      · apply withLocalDecl_scope
        · exact hwf
        · exact hreserved
        intro arg current hframe
        apply Lean4Lean.AddInductive.bindWF
        intro normalized
        exact ih normalized _ _ current hframe.wf hframe.reserved fun indices final hfinal =>
          hnext indices final (hframe.trans hfinal)
    · exact hnext indices ctx (.refl ctx hwf hreserved)

private theorem loopInd1_scope (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → (next infos current).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd1.eq_def]
  split
  · apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro normalized
    apply loopArgs1_scope
    · exact hwf
    · exact hreserved
    intro indices current hframe
    apply withLocalDecl_scope
    · exact hframe.wf
    · exact hframe.reserved
    intro major majorCtx hmajor
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply withLocalDecl_scope
    · exact hmajor.wf
    · exact hmajor.reserved
    intro motive motiveCtx hmotive
    apply loopInd1_scope
    · exact hmotive.wf
    · exact hmotive.reserved
    intro infos final hfinal
    exact hnext infos final (hframe.trans (hmajor.trans (hmotive.trans hfinal)))
  · exact hnext infos ctx (.refl ctx hwf hreserved)
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

private theorem loopU_scope (stats : InductiveStats) (fields : Array Expr)
    (infos : Array RecInfo) (index : Nat) (hypotheses : Array Expr)
    (next : Array Expr → M α) (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ hypotheses current, ctx.RecursorScopeFrame current → (next hypotheses current).WF post) :
    (mkRecInfos.loopU stats fields infos index hypotheses next ctx).WF post := by
  rw [mkRecInfos.loopU.eq_def]
  split
  · apply Lean4Lean.AddInductive.bindWF
    intro hypothesisType
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply withLocalDecl_scope
    · exact hwf
    · exact hreserved
    intro hypothesis current hframe
    apply loopU_scope
    · exact hframe.wf
    · exact hframe.reserved
    intro hypotheses final hfinal
    exact hnext hypotheses final (hframe.trans hfinal)
  · exact hnext hypotheses ctx (.refl ctx hwf hreserved)
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

private theorem loopCtors_scope (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (ctors : List Constructor) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → (next infos current).WF post) :
    (mkRecInfos.loopCtors stats parent index infos ctors next ctx).WF post := by
  induction ctors generalizing infos ctx with
  | nil => exact hnext infos ctx (.refl ctx hwf hreserved)
  | cons ctor ctors ih =>
    rw [mkRecInfos.loopCtors.eq_def]
    apply mkRecInfos.loopCtorArgs.scope
    · exact hwf
    · exact hreserved
    intro type fields recursiveFields fieldCtx hfields _ _
    apply loopU_scope
    · exact hfields.wf
    · exact hfields.reserved
    intro hypotheses hypothesisCtx hhypotheses
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply withLocalDecl_scope
    · exact hhypotheses.wf
    · exact hhypotheses.reserved
    intro minor minorCtx hminor
    apply ih
    · exact hminor.wf
    · exact hminor.reserved
    intro infos final hfinal
    exact hnext infos final (hfields.trans (hhypotheses.trans (hminor.trans hfinal)))

private theorem loopInd2_scope (stats : InductiveStats) (types : Array InductiveType)
    (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → (next infos current).WF post) :
    (mkRecInfos.loopInd2 stats types index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd2.eq_def]
  split
  · apply loopCtors_scope
    · exact hwf
    · exact hreserved
    intro infos current hframe
    apply loopInd2_scope
    · exact hframe.wf
    · exact hframe.reserved
    intro infos final hfinal
    exact hnext infos final (hframe.trans hfinal)
  · exact hnext infos ctx (.refl ctx hwf hreserved)
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.scope (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  unfold mkRecInfos
  apply loopInd1_scope
  · exact hwf
  · exact hreserved
  intro infos current hframe
  apply loopInd2_scope
  · exact hframe.wf
  · exact hframe.reserved
  intro infos final hfinal
  exact hnext infos final (hframe.trans hfinal)

theorem mkRecInfos.getScopeCounts (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do
      return (infos, ← readThe Context)) ctx).WF fun result =>
        ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 := by
  have hscope : (mkRecInfos stats types elimLevel (fun infos => do
      return (infos, ← readThe Context)) ctx).WF fun result => ctx.RecursorScopeFrame result.2 := by
    apply mkRecInfos.scope
    · exact hwf
    · exact hreserved
    intro infos current hframe
    exact .pure hframe
  intro result hresult
  exact ⟨hscope result hresult, (mkRecInfos.getCounts stats types elimLevel ctx result hresult).2⟩

def mkRecInfos.scopeRegistration (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) :
    M (Kernel.Environment × Array RecInfo × Context) :=
  mkRecInfos stats types elimLevel fun infos => do
    let current ← readThe Context
    let env ← declareRecursors stats types elimLevel infos lparams current.lctx isK isUnsafe
    return (env, infos, current)

theorem mkRecInfos.registeredScope (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have hscope : (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.scope
    · exact hwf
    · exact hreserved
    intro infos current hframe
    apply Lean4Lean.AddInductive.readWF
    refine Except.WF.bind (declareRecursors.offsetMetadata stats types elimLevel infos lparams current.lctx
      isK isUnsafe current (by simpa only [hframe.env] using henv)) ?_
    intro env hmetadata
    refine .pure ⟨hframe, hmetadata.1, ?_, hmetadata.2.2⟩
    intro name info hold
    apply hmetadata.2.1 name info
    simpa only [hframe.env] using hold
  have hcounts : (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF
      fun result => RecursorInfoCounts types result.2.1 := by
    unfold mkRecInfos.scopeRegistration
    apply mkRecInfos.frameCounts
    intro infos current _ hcounts
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro env
    exact .pure hcounts
  intro result hresult
  obtain ⟨hframe, henv, hkeep, hmetadata⟩ := hscope result hresult
  have hcounts := hcounts result hresult
  exact ⟨hframe, hcounts, henv, hkeep, hmetadata,
    hmetadata.localRuleRhsScope hcounts hframe.wf hframe.reserved⟩

end Lean4Lean.AddInductive
