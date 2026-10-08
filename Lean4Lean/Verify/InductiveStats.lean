import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def InductiveStats.HeaderSizes (stats : InductiveStats) (numTypes : Nat) : Prop :=
  stats.nindices.size = numTypes ∧ stats.indConsts.size = numTypes

def InductiveStats.ParamsAreFVars (stats : InductiveStats) : Prop :=
  ∀ param ∈ stats.params, param.isFVar = true

theorem InductiveStats.ParamsAreFVars.push {stats : InductiveStats}
    (hstats : stats.ParamsAreFVars) {param : Expr} (hparam : param.isFVar = true) :
    ({ stats with params := stats.params.push param }).ParamsAreFVars := by
  intro entry hentry
  simp only [Array.mem_push] at hentry
  obtain hentry | rfl := hentry
  · exact hstats entry hentry
  · exact hparam

structure Context.HeaderFrame (original current : Context) : Prop where
  env : current.env = original.env
  lparams : current.lparams = original.lparams
  safety : current.safety = original.safety
  allowPrimitive : current.allowPrimitive = original.allowPrimitive
  fuel : current.fuel = original.fuel

theorem Context.HeaderFrame.refl (ctx : Context) : ctx.HeaderFrame ctx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Context.HeaderFrame.trans {original middle current : Context}
    (hfirst : original.HeaderFrame middle) (hsecond : middle.HeaderFrame current) :
    original.HeaderFrame current :=
  ⟨hsecond.env.trans hfirst.env, hsecond.lparams.trans hfirst.lparams,
    hsecond.safety.trans hfirst.safety, hsecond.allowPrimitive.trans hfirst.allowPrimitive,
    hsecond.fuel.trans hfirst.fuel⟩

private structure PrefixSizes (stats : InductiveStats) (numTypes numParams numLevels : Nat) : Prop where
  nindices : stats.nindices.size = numTypes
  indConsts : stats.indConsts.size = numTypes
  levels : stats.levels.length = numLevels
  params : stats.params.size = numParams
  paramsAreFVars : stats.ParamsAreFVars

private theorem bindWF {ctx : Context} {action : M α} {next : α → M β} {post : β → Prop}
    (hnext : ∀ result, (next result ctx).WF post) : ((action >>= next) ctx).WF post :=
  Except.WF.bind (fun _ _ => True.intro) fun result _ => hnext result

private theorem readWF {ctx : Context} {next : Context → M α} {post : α → Prop}
    (hnext : (next ctx ctx).WF post) : ((read >>= next) ctx).WF post :=
  hnext

private theorem withLocalDeclWF {ctx : Context} {name : Name} {bi : BinderInfo} {type : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : ∀ param ctx', param.isFVar = true →
      ctx.HeaderFrame ctx' → (next param ctx').WF post) :
    (withLocalDecl name bi type next ctx).WF post :=
  hnext _ _ rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_headerSizes (nparams numTypes : Nat) (fuel : Nat)
    (stats : InductiveStats) (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M α) (ctx : Context) (post : α → Prop)
    (hstats : PrefixSizes stats numTypes (if numTypes = 0 then index else nparams)
      ctx.lparams.length)
    (hnext : ∀ type stats nindices ctx',
      PrefixSizes stats numTypes nparams ctx'.lparams.length →
      ctx.HeaderFrame ctx' →
      (next type stats nindices ctx').WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next ctx).WF post := by
  induction fuel generalizing stats type index nindices ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [checkInductiveTypes.loopInd.loop.eq_def]
    dsimp only
    split
    · rename_i name dom body bi
      split
      · split
        · apply withLocalDeclWF
          intro param ctx' hfvar hframe
          apply bindWF
          intro type'
          apply ih _ type' (index + 1) nindices ctx'
          · have hzero : numTypes = 0 := by
              simpa [Array.isEmpty, hstats.indConsts] using ‹stats.indConsts.isEmpty = true›
            subst numTypes
            exact ⟨hstats.nindices, hstats.indConsts,
              by simpa [hframe.lparams] using hstats.levels, by simpa using hstats.params,
              hstats.paramsAreFVars.push hfvar⟩
          · intro type stats nindices ctx'' hsizes hframe'
            exact hnext type stats nindices ctx'' hsizes (hframe.trans hframe')
        · apply bindWF
          intro type'
          apply bindWF
          intro equal
          split
          · apply bindWF
            intro _
            apply bindWF
            intro type''
            apply ih _ type'' (index + 1) nindices ctx
            · have hnonzero : numTypes ≠ 0 := by
                simpa [Array.isEmpty, hstats.indConsts] using ‹¬stats.indConsts.isEmpty = true›
              simpa [hnonzero] using hstats
            · exact hnext
          · exact Except.WF.throw
      · apply withLocalDeclWF
        intro param ctx' _ hframe
        apply bindWF
        intro type'
        apply ih stats type' index (nindices + 1) ctx'
        · simpa [hframe.lparams] using hstats
        · intro type stats nindices ctx'' hsizes hframe'
          exact hnext type stats nindices ctx'' hsizes (hframe.trans hframe')
    · split
      · exact Except.WF.throw
      · have hindex : index = nparams := by simpa using ‹¬(index != nparams) = true›
        subst index
        exact hnext type stats nindices ctx (by simpa using hstats) (.refl ctx)

private theorem loopInd_headerSizes (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (ctx : Context) (post : α → Prop) (hbound : processed ≤ indTypes.size)
    (hstats : PrefixSizes stats processed (if processed = 0 then 0 else nparams)
      ctx.lparams.length)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → stats.ParamsAreFVars →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes.loopInd nparams indTypes next processed stats ctx).WF post := by
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · apply readWF
    apply bindWF
    intro _
    apply bindWF
    intro _
    apply readWF
    apply bindWF
    intro type
    apply loop_headerSizes nparams processed _ stats type 0 0 _ ctx post hstats
    intro type stats' nindices ctx' hsizes hframe
    apply bindWF
    intro sort
    split
    · apply readWF
      apply bindWF
      intro _
      apply loopInd_headerSizes nparams indTypes next (processed + 1) _ ctx' post
      · omega
      · exact ⟨by simpa using hsizes.nindices,
          by simpa using hsizes.indConsts,
          hsizes.levels, by simpa using hsizes.params, hsizes.paramsAreFVars⟩
      · intro stats ctx'' hsizes hfvars hframe'
        exact hnext stats ctx'' hsizes hfvars (hframe.trans hframe')
    · split
      · exact Except.WF.throw
      · apply bindWF
        intro _
        apply loopInd_headerSizes nparams indTypes next (processed + 1) _ ctx' post
        · omega
        · exact ⟨by simpa using hsizes.nindices,
            by simpa using hsizes.indConsts,
            hsizes.levels, by simpa using hsizes.params, hsizes.paramsAreFVars⟩
        · intro stats ctx'' hsizes hfvars hframe'
          exact hnext stats ctx'' hsizes hfvars (hframe.trans hframe')
  · apply readWF
    have hcount : processed = indTypes.size := by omega
    refine hnext _ ctx ?_ ?_ (.refl ctx)
    · simp only [InductiveStats.HeaderSizes, hstats.levels, hstats.nindices,
        hstats.indConsts, hcount, beq_self_eq_true, ite_true]
      split
      · exact ⟨hstats.nindices.trans hcount, hstats.indConsts.trans hcount⟩
      · have hzero : indTypes.size = 0 := by
          by_contra hnonzero
          have hparams : stats.params.size = nparams := by
            simpa [hcount, hnonzero] using hstats.params
          simp [hparams] at ‹¬(stats.params.size == nparams) = true›
        simp [panicWithPosWithDecl, panic, panicCore, hzero]
        exact ⟨rfl, rfl⟩
    · simp only [hstats.levels, hstats.nindices, hstats.indConsts, hcount,
        beq_self_eq_true, ite_true]
      split
      · exact hstats.paramsAreFVars
      · simp only [panicWithPosWithDecl, panic, panicCore]
        change ∀ param ∈ (#[] : Array Expr), param.isFVar = true
        simp
termination_by indTypes.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.frameHeaderSizesParamsFVars
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → stats.ParamsAreFVars →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post := by
  unfold checkInductiveTypes
  apply readWF
  apply loopInd_headerSizes nparams indTypes next 0 _ ctx post (Nat.zero_le _)
  · refine ⟨rfl, rfl, by simp, rfl, ?_⟩
    change ∀ param ∈ (#[] : Array Expr), param.isFVar = true
    simp
  · exact hnext

theorem checkInductiveTypes.frameHeaderSizes (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsFVars nparams indTypes next ctx post
    fun stats ctx' hsizes _ hframe => hnext stats ctx' hsizes hframe

theorem checkInductiveTypes.paramsFVars (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.ParamsAreFVars → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsFVars nparams indTypes next ctx post
    fun stats ctx' _ hfvars _ => hnext stats ctx' hfvars

theorem checkInductiveTypes.getParamsFVars (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF InductiveStats.ParamsAreFVars :=
  checkInductiveTypes.paramsFVars nparams indTypes pure ctx _ fun _ _ hfvars => .pure hfvars

theorem checkInductiveTypes.headerSizes (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizes nparams indTypes next ctx post fun stats ctx' hsizes _ =>
    hnext stats ctx' hsizes

theorem checkInductiveTypes.frame (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizes nparams indTypes next ctx post fun stats ctx' _ hframe =>
    hnext stats ctx' hframe

theorem checkInductiveTypes.getHeaderSizes (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats =>
      stats.HeaderSizes indTypes.size :=
  checkInductiveTypes.headerSizes nparams indTypes pure ctx _ fun _ _ hsizes => .pure hsizes

theorem checkInductiveTypes.getFrameHeaderSizes (nparams : Nat)
    (indTypes : Array InductiveType) (ctx : Context) :
    (checkInductiveTypes nparams indTypes (fun stats => do return (stats, ← read)) ctx).WF
      fun result => result.1.HeaderSizes indTypes.size ∧ ctx.HeaderFrame result.2 :=
  checkInductiveTypes.frameHeaderSizes nparams indTypes _ ctx _ fun _ _ hsizes hframe =>
    .pure ⟨hsizes, hframe⟩

end Lean4Lean.AddInductive
