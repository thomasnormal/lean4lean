import Lean4Lean.Verify.InductiveStats

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  Lean4Lean.AddInductive.withLocalDeclWF from Lean4Lean.Verify.InductiveStats

private theorem loopArgs1_frame (stats : InductiveStats) (type : Expr) (index : Nat)
    (indices : Array Expr) (fuel : Nat) (next : Array Expr → M α)
    (ctx : Context) (post : α → Prop)
    (hnext : ∀ indices current, ctx.HeaderFrame current → (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats type index indices fuel next ctx).WF post := by
  induction fuel generalizing type index indices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopArgs1.eq_def]
    split
    · split
      · apply Lean4Lean.AddInductive.bindWF
        intro normalized
        exact ih normalized _ _ ctx hnext
      · apply Lean4Lean.AddInductive.withLocalDeclWF
        intro arg current _ _ _ hframe
        apply Lean4Lean.AddInductive.bindWF
        intro normalized
        exact ih normalized _ _ current fun indices final hfinal =>
          hnext indices final (hframe.trans hfinal)
    · exact hnext indices ctx (.refl ctx)

private theorem loopInd1_frame (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → (next infos current).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd1.eq_def]
  split
  · apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro normalized
    apply loopArgs1_frame
    intro indices current hframe
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro major majorCtx _ _ _ hmajor
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro motive motiveCtx _ _ _ hmotive
    apply loopInd1_frame
    intro infos final hfinal
    exact hnext infos final (hframe.trans (hmajor.trans (hmotive.trans hfinal)))
  · exact hnext infos ctx (.refl ctx)
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

private theorem loopCtorArgs_loop_frame (stats : InductiveStats) (type : Expr) (index : Nat)
    (fields recursiveFields : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ type fields recursiveFields current, ctx.HeaderFrame current →
      (next type fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx).WF post := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · split
      · exact ih _ _ _ _ ctx hnext
      · apply Lean4Lean.AddInductive.withLocalDeclWF
        intro arg current _ _ _ hframe
        apply Lean4Lean.AddInductive.bindWF
        intro recursive
        exact ih _ _ _ _ current fun type fields recursiveFields final hfinal =>
          hnext type fields recursiveFields final (hframe.trans hfinal)
    · exact hnext type fields recursiveFields ctx (.refl ctx)

private theorem loopCtorArgs_frame (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ type fields recursiveFields current, ctx.HeaderFrame current →
      (next type fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  exact loopCtorArgs_loop_frame stats type 0 #[] #[] ctx.fuel.inductiveFuel next ctx post hnext

private theorem loopU_frame (stats : InductiveStats) (fields : Array Expr)
    (infos : Array RecInfo) (index : Nat) (hypotheses : Array Expr)
    (next : Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ hypotheses current, ctx.HeaderFrame current → (next hypotheses current).WF post) :
    (mkRecInfos.loopU stats fields infos index hypotheses next ctx).WF post := by
  rw [mkRecInfos.loopU.eq_def]
  split
  · apply Lean4Lean.AddInductive.bindWF
    intro hypothesisType
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro hypothesis current _ _ _ hframe
    apply loopU_frame
    intro hypotheses final hfinal
    exact hnext hypotheses final (hframe.trans hfinal)
  · exact hnext hypotheses ctx (.refl ctx)
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

private theorem loopCtors_frame (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (ctors : List Constructor) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → (next infos current).WF post) :
    (mkRecInfos.loopCtors stats parent index infos ctors next ctx).WF post := by
  induction ctors generalizing infos ctx with
  | nil => exact hnext infos ctx (.refl ctx)
  | cons ctor ctors ih =>
    rw [mkRecInfos.loopCtors.eq_def]
    apply loopCtorArgs_frame
    intro type fields recursiveFields fieldCtx hfields
    apply loopU_frame
    intro hypotheses hypothesisCtx hhypotheses
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro minor minorCtx _ _ _ hminor
    apply ih
    intro infos final hfinal
    exact hnext infos final (hfields.trans (hhypotheses.trans (hminor.trans hfinal)))

private theorem loopInd2_frame (stats : InductiveStats) (types : Array InductiveType)
    (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → (next infos current).WF post) :
    (mkRecInfos.loopInd2 stats types index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd2.eq_def]
  split
  · apply loopCtors_frame
    intro infos current hframe
    apply loopInd2_frame
    intro infos final hfinal
    exact hnext infos final (hframe.trans hfinal)
  · exact hnext infos ctx (.refl ctx)
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.frame (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  unfold mkRecInfos
  apply loopInd1_frame
  intro infos current hframe
  apply loopInd2_frame
  intro infos final hfinal
  exact hnext infos final (hframe.trans hfinal)

end Lean4Lean.AddInductive
