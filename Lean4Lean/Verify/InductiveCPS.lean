import Lean4Lean.Verify.InductiveHeaderScope

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)

private theorem bind_morphism {action : M InputType} {next : InputType → M ResultType}
    {collect : InputType → M CaptureType} {resume : CaptureType → Except Exception ResultType}
    {ctx : Context} (hnext : ∀ result, next result ctx = (collect result ctx).bind resume) :
    ((action >>= next) ctx) = ((action >>= collect) ctx).bind resume := by
  change (action ctx).bind _ = ((action ctx).bind _).bind _
  cases action ctx with
  | error error => rfl
  | ok result => exact hnext result

private theorem read_morphism {next : Context → M ResultType} {collect : Context → M CaptureType}
    {resume : CaptureType → Except Exception ResultType} {ctx : Context}
    (hnext : next ctx ctx = (collect ctx ctx).bind resume) :
    ((readThe Context >>= next) ctx) = ((readThe Context >>= collect) ctx).bind resume := hnext

private theorem withLocalDecl_morphism {next : Expr → M ResultType} {collect : Expr → M CaptureType}
    {resume : CaptureType → Except Exception ResultType} {ctx : Context}
    {name : Name} {bi : BinderInfo} {type : Expr}
    (hnext : ∀ arg current, next arg current = (collect arg current).bind resume) :
    (withLocalDecl name bi type next ctx) = (withLocalDecl name bi type collect ctx).bind resume :=
  hnext _ _

private theorem header_loop_morphism (nparams fuel : Nat) (stats : InductiveStats)
    (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M ResultType)
    (collect : Expr → InductiveStats → Nat → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (ctx : Context)
    (hnext : ∀ type stats nindices current,
      next type stats nindices current = (collect type stats nindices current).bind resume) :
    checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next ctx =
      (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel collect ctx).bind resume := by
  induction fuel generalizing stats type index nindices ctx with
  | zero => rfl
  | succ fuel ih =>
    rw [checkInductiveTypes.loopInd.loop.eq_def, checkInductiveTypes.loopInd.loop.eq_def]
    dsimp only
    split
    · split
      · split
        · apply withLocalDecl_morphism
          intro param current
          apply bind_morphism
          intro normalized
          exact ih _ normalized _ _ current
        · apply bind_morphism
          intro paramType
          apply bind_morphism
          intro equal
          split
          · apply bind_morphism
            intro _
            apply bind_morphism
            intro normalized
            exact ih _ normalized _ _ ctx
          · rfl
      · apply withLocalDecl_morphism
        intro arg current
        apply bind_morphism
        intro normalized
        exact ih _ normalized _ _ current
    · split
      · rfl
      · exact hnext type stats nindices ctx

private theorem header_loopInd_morphism (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (collect : InductiveStats → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (index : Nat) (stats : InductiveStats)
    (ctx : Context) (hnext : ∀ stats current, next stats current = (collect stats current).bind resume) :
    checkInductiveTypes.loopInd nparams types next index stats ctx =
      (checkInductiveTypes.loopInd nparams types collect index stats ctx).bind resume := by
  rw [checkInductiveTypes.loopInd.eq_def, checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · apply read_morphism
    apply bind_morphism
    intro _
    apply bind_morphism
    intro _
    apply read_morphism
    apply bind_morphism
    intro normalized
    apply header_loop_morphism
    intro type stats nindices current
    apply bind_morphism
    intro sort
    split
    · apply read_morphism
      apply bind_morphism
      intro _
      exact header_loopInd_morphism nparams types next collect resume (index + 1) _ current hnext
    · split
      · rfl
      · apply bind_morphism
        intro _
        exact header_loopInd_morphism nparams types next collect resume (index + 1) _ current hnext
  · apply read_morphism
    exact hnext _ ctx
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.morphism (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (collect : InductiveStats → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (ctx : Context)
    (hnext : ∀ stats current, next stats current = (collect stats current).bind resume) :
    checkInductiveTypes nparams types next ctx =
      (checkInductiveTypes nparams types collect ctx).bind resume := by
  unfold checkInductiveTypes
  apply read_morphism
  exact header_loopInd_morphism nparams types next collect resume 0 _ ctx hnext

theorem checkInductiveTypes.scopedStats (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, ctx.RecursorScopeFrame current → stats.HeaderSizes types.size →
      stats.ParamsCount nparams types.size → stats.ParamsAreFVars → stats.params.toList.Nodup →
      (next stats current).WF post) : (checkInductiveTypes nparams types next ctx).WF post := by
  rw [checkInductiveTypes.morphism nparams types next (fun stats => do return (stats, ← readThe Context))
    (fun result => next result.1 result.2) ctx (fun _ _ => rfl)]
  refine (checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved).bind ?_
  rintro ⟨stats, current⟩ ⟨hframe, hsizes, hcount, hfvars, hnodup⟩
  exact hnext stats current hframe hsizes hcount hfvars hnodup

private theorem recArgs_morphism (stats : InductiveStats) (fuel : Nat) (type : Expr)
    (index : Nat) (indices : Array Expr) (next : Array Expr → M ResultType)
    (collect : Array Expr → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (ctx : Context) (hnext : ∀ indices current, next indices current = (collect indices current).bind resume) :
    mkRecInfos.loopArgs1 stats type index indices fuel next ctx =
      (mkRecInfos.loopArgs1 stats type index indices fuel collect ctx).bind resume := by
  induction fuel generalizing type index indices ctx with
  | zero => rfl
  | succ fuel ih =>
    rw [mkRecInfos.loopArgs1.eq_def, mkRecInfos.loopArgs1.eq_def]
    split
    · split
      · apply bind_morphism
        intro normalized
        exact ih normalized _ _ ctx
      · apply withLocalDecl_morphism
        intro arg current
        apply bind_morphism
        intro normalized
        exact ih normalized _ _ current
    · exact hnext indices ctx

private theorem recInd1_morphism (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (collect : Array RecInfo → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (ctx : Context) (hnext : ∀ infos current, next infos current = (collect infos current).bind resume) :
    mkRecInfos.loopInd1 stats types elimLevel index infos next ctx =
      (mkRecInfos.loopInd1 stats types elimLevel index infos collect ctx).bind resume := by
  rw [mkRecInfos.loopInd1.eq_def, mkRecInfos.loopInd1.eq_def]
  split
  · apply read_morphism
    apply bind_morphism
    intro normalized
    apply recArgs_morphism
    intro indices current
    apply withLocalDecl_morphism
    intro major majorCtx
    apply bind_morphism
    intro lctx
    apply withLocalDecl_morphism
    intro motive motiveCtx
    exact recInd1_morphism stats types elimLevel (index + 1) _ next collect resume motiveCtx hnext
  · exact hnext infos ctx
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

private theorem recCtor_loop_morphism (stats : InductiveStats) (fuel : Nat) (type : Expr)
    (index : Nat) (fields recursiveFields : Array Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType)
    (collect : Expr → Array Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (ctx : Context)
    (hnext : ∀ type fields recursiveFields current,
      next type fields recursiveFields current = (collect type fields recursiveFields current).bind resume) :
    mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx =
      (mkRecInfos.loopCtorArgs.loop stats collect type index fields recursiveFields fuel ctx).bind resume := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => rfl
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def, mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · split
      · exact ih _ _ _ _ ctx
      · apply withLocalDecl_morphism
        intro arg current
        apply bind_morphism
        intro recursive
        exact ih _ _ _ _ current
    · exact hnext type fields recursiveFields ctx

private theorem recCtor_morphism (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType)
    (collect : Expr → Array Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (ctx : Context)
    (hnext : ∀ type fields recursiveFields current,
      next type fields recursiveFields current = (collect type fields recursiveFields current).bind resume) :
    mkRecInfos.loopCtorArgs stats type next ctx =
      (mkRecInfos.loopCtorArgs stats type collect ctx).bind resume := by
  unfold mkRecInfos.loopCtorArgs
  apply read_morphism
  exact recCtor_loop_morphism stats ctx.fuel.inductiveFuel type 0 #[] #[] next collect resume ctx hnext

private theorem recU_morphism (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (next : Array Expr → M ResultType)
    (collect : Array Expr → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (ctx : Context) (hnext : ∀ hypotheses current, next hypotheses current = (collect hypotheses current).bind resume) :
    mkRecInfos.loopU stats fields infos index hypotheses next ctx =
      (mkRecInfos.loopU stats fields infos index hypotheses collect ctx).bind resume := by
  rw [mkRecInfos.loopU.eq_def, mkRecInfos.loopU.eq_def]
  split
  · apply bind_morphism
    intro hypothesisType
    apply bind_morphism
    intro lctx
    apply withLocalDecl_morphism
    intro hypothesis current
    exact recU_morphism stats fields infos (index + 1) _ next collect resume current hnext
  · exact hnext hypotheses ctx
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

private theorem recCtors_morphism (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (ctors : List Constructor) (next : Array RecInfo → M ResultType)
    (collect : Array RecInfo → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (ctx : Context) (hnext : ∀ infos current, next infos current = (collect infos current).bind resume) :
    mkRecInfos.loopCtors stats parent index infos ctors next ctx =
      (mkRecInfos.loopCtors stats parent index infos ctors collect ctx).bind resume := by
  induction ctors generalizing infos ctx with
  | nil => exact hnext infos ctx
  | cons ctor ctors ih =>
    rw [mkRecInfos.loopCtors.eq_def, mkRecInfos.loopCtors.eq_def]
    apply recCtor_morphism
    intro type fields recursiveFields current
    apply recU_morphism
    intro hypotheses hypothesisCtx
    apply bind_morphism
    intro lctx
    apply withLocalDecl_morphism
    intro minor minorCtx
    exact ih _ minorCtx

private theorem recInd2_morphism (stats : InductiveStats) (types : Array InductiveType)
    (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (collect : Array RecInfo → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (ctx : Context) (hnext : ∀ infos current, next infos current = (collect infos current).bind resume) :
    mkRecInfos.loopInd2 stats types index infos next ctx =
      (mkRecInfos.loopInd2 stats types index infos collect ctx).bind resume := by
  rw [mkRecInfos.loopInd2.eq_def, mkRecInfos.loopInd2.eq_def]
  split
  · apply recCtors_morphism
    intro infos current
    exact recInd2_morphism stats types (index + 1) infos next collect resume current hnext
  · exact hnext infos ctx
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.morphism (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (collect : Array RecInfo → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (ctx : Context)
    (hnext : ∀ infos current, next infos current = (collect infos current).bind resume) :
    mkRecInfos stats types elimLevel next ctx = (mkRecInfos stats types elimLevel collect ctx).bind resume := by
  unfold mkRecInfos
  apply recInd1_morphism
  intro infos current
  exact recInd2_morphism stats types 0 infos next collect resume current hnext

theorem mkRecInfos.scopedCounts (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → RecursorInfoCounts types infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next (fun infos => do return (infos, ← readThe Context))
    (fun result => next result.1 result.2) ctx (fun _ _ => rfl)]
  refine (mkRecInfos.getScopeCounts stats types elimLevel ctx hwf hreserved).bind ?_
  rintro ⟨infos, current⟩ ⟨hframe, hcounts⟩
  exact hnext infos current hframe hcounts

end Lean4Lean.AddInductive
