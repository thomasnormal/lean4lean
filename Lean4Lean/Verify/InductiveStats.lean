import Lean4Lean.Verify.ConstructorArity.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def InductiveStats.HeaderSizes (stats : InductiveStats) (numTypes : Nat) : Prop :=
  stats.nindices.size = numTypes ∧ stats.indConsts.size = numTypes

def InductiveStats.ParamsCount (stats : InductiveStats) (numParams numTypes : Nat) : Prop :=
  stats.params.size = if numTypes = 0 then 0 else numParams

def InductiveStats.HeaderArities (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) : Prop :=
  ∀ (index : Nat) (hindex : index < indTypes.size),
    declareConstructors.arity 0 indTypes[index].type ≤ numParams + stats.nindices[index]!

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

private def ParamsReserved (stats : InductiveStats) (ngen : NameGenerator) : Prop :=
  ∀ fvar, Expr.fvar fvar ∈ stats.params → ngen.Reserves fvar

private theorem ParamsReserved.mono {stats : InductiveStats} {ngen next : NameGenerator}
    (hparams : ParamsReserved stats ngen) (hgen : ngen ≤ next) :
    ParamsReserved stats next :=
  fun fvar hmem => NameGenerator.Reserves.mono hgen (hparams fvar hmem)

private theorem ParamsReserved.not_mem_current {stats : InductiveStats} {ngen : NameGenerator}
    (hparams : ParamsReserved stats ngen) : Expr.fvar ⟨ngen.curr⟩ ∉ stats.params :=
  fun hmem => NameGenerator.not_reserves_self (hparams _ hmem)

private theorem ParamsReserved.push_current {stats : InductiveStats} {ngen : NameGenerator}
    (hparams : ParamsReserved stats ngen) :
    ParamsReserved { stats with params := stats.params.push (.fvar ⟨ngen.curr⟩) } ngen.next := by
  intro fvar hmem
  simp only [Array.mem_push, Expr.fvar.injEq] at hmem
  obtain hmem | rfl := hmem
  · exact NameGenerator.Reserves.mono .next (hparams fvar hmem)
  · exact NameGenerator.next_reserves_self

private theorem params_push_current_nodup {stats : InductiveStats} {ngen : NameGenerator}
    (hnodup : stats.params.toList.Nodup) (hparams : ParamsReserved stats ngen) :
    (stats.params.push (.fvar ⟨ngen.curr⟩)).toList.Nodup := by
  rw [Array.toList_push, List.nodup_append]
  refine ⟨hnodup, by simp, ?_⟩
  intro entry hentry other hother
  have hother : other = Expr.fvar ⟨ngen.curr⟩ := by simpa using hother
  subst other
  intro heq
  apply hparams.not_mem_current
  simpa only [Array.mem_toList_iff, heq] using hentry

private structure PrefixSizes (stats : InductiveStats) (numTypes numParams numLevels : Nat)
    (ngen : NameGenerator) : Prop where
  nindices : stats.nindices.size = numTypes
  indConsts : stats.indConsts.size = numTypes
  levels : stats.levels.length = numLevels
  params : stats.params.size = numParams
  paramsAreFVars : stats.ParamsAreFVars
  paramsNodup : stats.params.toList.Nodup
  paramsReserved : ParamsReserved stats ngen

private structure HeaderMeasure where
  value : Expr → Nat
  whnf : ∀ type ctx, ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF fun result =>
    value type ≤ value result
  instantiate : ∀ name domain body bi param, param.isFVar = true →
    value (.forallE name domain body bi) ≤ 1 + value (body.instantiate1 param)
  nonForall : ∀ type, (∀ name domain body bi, type ≠ .forallE name domain body bi) → value type = 0

private def HeaderMeasure.zero : HeaderMeasure := {
  value := fun _ => 0
  whnf := fun _ _ _ _ => Nat.le_refl _
  instantiate := fun _ _ _ _ _ _ => Nat.zero_le _
  nonForall := fun _ _ => rfl }

private def HeaderMeasure.raw : HeaderMeasure := {
  value := declareConstructors.arity 0
  whnf := whnf_arity
  instantiate := by
    intro name domain body bi param hfvar
    change declareConstructors.arity 1 body ≤ _
    rw [declareConstructors.arity_eq_add,
      declareConstructors.arity_instantiate1_of_isFVar body param 0 hfvar]
    exact Nat.le_refl _
  nonForall := by
    intro type htype
    cases type with
    | forallE name domain body bi => exact (htype name domain body bi rfl).elim
    | _ => rfl }

private theorem HeaderMeasure.step (measure : HeaderMeasure)
    (name : Name) (domain body : Expr) (bi : BinderInfo) (param : Expr) (ctx : Context)
    (hfvar : param.isFVar = true) :
    ((monadLift (TypeChecker.whnf (body.instantiate1 param)) : M Expr) ctx).WF fun result =>
      measure.value (.forallE name domain body bi) ≤ 1 + measure.value result :=
  (measure.whnf (body.instantiate1 param) ctx).mono fun _ hbound =>
    Nat.le_trans (measure.instantiate name domain body bi param hfvar)
      (Nat.add_le_add_left hbound 1)

private def PrefixArities (stats : InductiveStats) (measure : HeaderMeasure) (numParams : Nat)
    (indTypes : Array InductiveType) (processed : Nat) : Prop :=
  ∀ (index : Nat) (hindex : index < indTypes.size), index < processed →
    measure.value indTypes[index].type ≤ numParams + stats.nindices[index]!

private theorem PrefixArities.push {stats : InductiveStats} {numParams processed : Nat}
    {indTypes : Array InductiveType} {measure : HeaderMeasure}
    (hprefix : PrefixArities stats measure numParams indTypes processed)
    (hsize : stats.nindices.size = processed) (hprocessed : processed < indTypes.size)
    (nindices : Nat)
    (harity : measure.value indTypes[processed].type ≤ numParams + nindices) :
    PrefixArities { stats with nindices := stats.nindices.push nindices }
      measure numParams indTypes (processed + 1) := by
  intro index hindex hbound
  by_cases hprevious : index < processed
  · have hvalid : index < stats.nindices.size := by omega
    have hpush : index < (stats.nindices.push nindices).size := by simp; omega
    simpa only [getElem!_pos (stats.nindices.push nindices) index hpush,
      getElem!_pos stats.nindices index hvalid,
      Array.getElem_push_lt hvalid] using
      hprefix index hindex hprevious
  · have heq : index = processed := by omega
    subst index
    simpa [getElem!_pos, Array.getElem_push, hsize] using harity

private theorem bindWF {ctx : Context} {action : M α} {next : α → M β} {post : β → Prop}
    (hnext : ∀ result, (next result ctx).WF post) : ((action >>= next) ctx).WF post :=
  Except.WF.bind (fun _ _ => True.intro) fun result _ => hnext result

private theorem readWF {ctx : Context} {next : Context → M α} {post : α → Prop}
    (hnext : (next ctx ctx).WF post) : ((read >>= next) ctx).WF post :=
  hnext

private theorem withLocalDeclWF {ctx : Context} {name : Name} {bi : BinderInfo} {type : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : ∀ param ctx', param.isFVar = true →
      param = .fvar ⟨ctx.ngen.curr⟩ → ctx'.ngen = ctx.ngen.next →
      ctx.HeaderFrame ctx' → (next param ctx').WF post) :
    (withLocalDecl name bi type next ctx).WF post :=
  hnext _ _ rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_headerSizes (measure : HeaderMeasure)
    (nparams numTypes : Nat) (indTypes : Array InductiveType)
    (fuel bound : Nat)
    (stats : InductiveStats) (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M α) (ctx : Context) (post : α → Prop)
    (hstats : PrefixSizes stats numTypes (if numTypes = 0 then index else nparams)
      ctx.lparams.length ctx.ngen)
    (hbound : bound ≤ index + nindices + measure.value type)
    (harities : PrefixArities stats measure nparams indTypes numTypes)
    (hnext : ∀ type stats nindices ctx',
      PrefixSizes stats numTypes nparams ctx'.lparams.length ctx'.ngen →
      bound ≤ nparams + nindices → PrefixArities stats measure nparams indTypes numTypes →
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
          intro param ctx' hfvar hparam hgen hframe
          refine (measure.step name dom body bi param ctx' hfvar).bind ?_
          intro type' hstep
          apply ih _ type' (index + 1) nindices ctx'
          · have hzero : numTypes = 0 := by
              simpa [Array.isEmpty, hstats.indConsts] using ‹stats.indConsts.isEmpty = true›
            subst numTypes
            exact ⟨hstats.nindices, hstats.indConsts,
              by simpa [hframe.lparams] using hstats.levels, by simpa using hstats.params,
              hstats.paramsAreFVars.push hfvar,
              by simpa [hparam] using
                (params_push_current_nodup hstats.paramsNodup hstats.paramsReserved),
              by simpa [hparam, hgen] using hstats.paramsReserved.push_current⟩
          · omega
          · exact harities
          · intro type stats nindices ctx'' hsizes hbound harities hframe'
            exact hnext type stats nindices ctx'' hsizes hbound harities (hframe.trans hframe')
        · apply bindWF
          intro type'
          apply bindWF
          intro equal
          split
          · apply bindWF
            intro _
            have hnonzero : numTypes ≠ 0 := by
              simpa [Array.isEmpty, hstats.indConsts] using ‹¬stats.indConsts.isEmpty = true›
            have hvalid : index < stats.params.size := by
              have hsize : stats.params.size = nparams := by simpa [hnonzero] using hstats.params
              omega
            have hfvar : (stats.params[index]!).isFVar = true := by
              apply hstats.paramsAreFVars
              simp only [getElem!_pos stats.params index hvalid]
              exact Array.getElem_mem hvalid
            refine (measure.step name dom body bi stats.params[index]! ctx hfvar).bind ?_
            intro type'' hstep
            apply ih _ type'' (index + 1) nindices ctx
            · simpa [hnonzero] using hstats
            · omega
            · exact harities
            · exact hnext
          · exact Except.WF.throw
      · apply withLocalDeclWF
        intro param ctx' hfvar _ hgen hframe
        refine (measure.step name dom body bi param ctx' hfvar).bind ?_
        intro type' hstep
        apply ih stats type' index (nindices + 1) ctx'
        · exact ⟨hstats.nindices, hstats.indConsts,
            by simpa [hframe.lparams] using hstats.levels, hstats.params,
            hstats.paramsAreFVars, hstats.paramsNodup,
            by simpa [hgen] using hstats.paramsReserved.mono NameGenerator.LE.next⟩
        · omega
        · exact harities
        · intro type stats nindices ctx'' hsizes hbound harities hframe'
          exact hnext type stats nindices ctx'' hsizes hbound harities (hframe.trans hframe')
    · split
      · exact Except.WF.throw
      · have hindex : index = nparams := by simpa using ‹¬(index != nparams) = true›
        subst index
        refine hnext type stats nindices ctx (by simpa using hstats) ?_ harities (.refl ctx)
        have hzero : measure.value type = 0 :=
          measure.nonForall type (by assumption)
        omega

private theorem loopInd_headerSizes (measure : HeaderMeasure)
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (ctx : Context) (post : α → Prop) (hbound : processed ≤ indTypes.size)
    (hstats : PrefixSizes stats processed (if processed = 0 then 0 else nparams)
      ctx.lparams.length ctx.ngen)
    (harities : PrefixArities stats measure nparams indTypes processed)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size →
      PrefixArities stats measure nparams indTypes indTypes.size →
      stats.ParamsCount nparams indTypes.size →
      stats.ParamsAreFVars →
      stats.params.toList.Nodup →
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
    refine (measure.whnf indTypes[processed].type ctx).bind ?_
    intro type hstep
    apply loop_headerSizes measure nparams processed indTypes _
      (measure.value indTypes[processed].type) stats type 0 0 _ ctx post hstats
      (by simpa using hstep) harities
    intro type stats' nindices ctx' hsizes hcurrent harities hframe
    apply bindWF
    intro sort
    split
    · apply readWF
      apply bindWF
      intro _
      apply loopInd_headerSizes measure nparams indTypes next (processed + 1) _ ctx' post
      · omega
      · exact ⟨by simpa using hsizes.nindices,
          by simpa using hsizes.indConsts,
          hsizes.levels, by simpa using hsizes.params, hsizes.paramsAreFVars,
          hsizes.paramsNodup, hsizes.paramsReserved⟩
      · exact harities.push hsizes.nindices (by omega) nindices hcurrent
      · intro stats ctx'' hsizes harities hparams hfvars hnodup hframe'
        exact hnext stats ctx'' hsizes harities hparams hfvars hnodup (hframe.trans hframe')
    · split
      · exact Except.WF.throw
      · apply bindWF
        intro _
        apply loopInd_headerSizes measure nparams indTypes next (processed + 1) _ ctx' post
        · omega
        · exact ⟨by simpa using hsizes.nindices,
            by simpa using hsizes.indConsts,
            hsizes.levels, by simpa using hsizes.params, hsizes.paramsAreFVars,
            hsizes.paramsNodup, hsizes.paramsReserved⟩
        · exact harities.push hsizes.nindices (by omega) nindices hcurrent
        · intro stats ctx'' hsizes harities hparams hfvars hnodup hframe'
          exact hnext stats ctx'' hsizes harities hparams hfvars hnodup (hframe.trans hframe')
  · apply readWF
    have hcount : processed = indTypes.size := by omega
    refine hnext _ ctx ?_ ?_ ?_ ?_ ?_ (.refl ctx)
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
    · simp only [PrefixArities, hstats.levels, hstats.nindices,
        hstats.indConsts, hcount, beq_self_eq_true, ite_true]
      split
      · intro index hindex _
        exact harities index hindex (by omega)
      · have hzero : indTypes.size = 0 := by
          by_contra hnonzero
          have hparams : stats.params.size = nparams := by
            simpa [hcount, hnonzero] using hstats.params
          simp [hparams] at ‹¬(stats.params.size == nparams) = true›
        intro index hindex
        omega
    · simp only [InductiveStats.ParamsCount, hstats.levels, hstats.nindices,
        hstats.indConsts, hcount, beq_self_eq_true, ite_true]
      split
      · simpa only [hcount] using hstats.params
      · have hzero : indTypes.size = 0 := by
          by_contra hnonzero
          have hparams : stats.params.size = nparams := by
            simpa [hcount, hnonzero] using hstats.params
          simp [hparams] at ‹¬(stats.params.size == nparams) = true›
        simp [panicWithPosWithDecl, panic, panicCore, hzero]
        rfl
    · simp only [hstats.levels, hstats.nindices, hstats.indConsts, hcount,
        beq_self_eq_true, ite_true]
      split
      · exact hstats.paramsAreFVars
      · simp only [panicWithPosWithDecl, panic, panicCore]
        change ∀ param ∈ (#[] : Array Expr), param.isFVar = true
        simp
    · simp only [hstats.levels, hstats.nindices, hstats.indConsts, hcount,
        beq_self_eq_true, ite_true]
      split
      · exact hstats.paramsNodup
      · simp only [panicWithPosWithDecl, panic, panicCore]
        change ([] : List Expr).Nodup
        simp
termination_by indTypes.size - processed
decreasing_by all_goals simp_wf; omega

private theorem checkInductiveTypes.frameMeasured (measure : HeaderMeasure)
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size →
      PrefixArities stats measure nparams indTypes indTypes.size →
      stats.ParamsCount nparams indTypes.size →
      stats.ParamsAreFVars →
      stats.params.toList.Nodup →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post := by
  unfold checkInductiveTypes
  apply readWF
  apply loopInd_headerSizes measure nparams indTypes next 0 _ ctx post (Nat.zero_le _)
  · refine ⟨rfl, rfl, by simp, rfl, ?_, ?_, ?_⟩
    · change ∀ param ∈ (#[] : Array Expr), param.isFVar = true
      simp
    · change ([] : List Expr).Nodup
      simp
    · intro fvar hmem
      change Expr.fvar fvar ∈ (#[] : Array Expr) at hmem
      simp at hmem
  · intro index hindex hprocessed
    omega
  · exact hnext

theorem checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size →
      stats.HeaderArities nparams indTypes → stats.ParamsCount nparams indTypes.size →
      stats.ParamsAreFVars → stats.params.toList.Nodup →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameMeasured .raw nparams indTypes next ctx post
    fun stats ctx' hsizes harities hcount hfvars hnodup hframe =>
      hnext stats ctx' hsizes (fun index hindex => harities index hindex hindex)
        hcount hfvars hnodup hframe

theorem checkInductiveTypes.frameHeaderSizesParamsCountDistinct
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size →
      stats.ParamsCount nparams indTypes.size → stats.ParamsAreFVars →
      stats.params.toList.Nodup → ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameMeasured .zero nparams indTypes next ctx post
    fun stats ctx' hsizes _ hcount hfvars hnodup hframe =>
      hnext stats ctx' hsizes hcount hfvars hnodup hframe

theorem checkInductiveTypes.headerArities (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderArities nparams indTypes → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct nparams indTypes next ctx post
    fun stats ctx' _ harities _ _ _ _ => hnext stats ctx' harities

theorem checkInductiveTypes.getHeaderArities (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats =>
      stats.HeaderArities nparams indTypes :=
  checkInductiveTypes.headerArities nparams indTypes pure ctx _ fun _ _ harities => .pure harities

theorem checkInductiveTypes.frameHeaderSizesParamsDistinct
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → stats.ParamsAreFVars →
      stats.params.toList.Nodup →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsCountDistinct nparams indTypes next ctx post
    fun stats ctx' hsizes _ hfvars hnodup hframe => hnext stats ctx' hsizes hfvars hnodup hframe

theorem checkInductiveTypes.paramsCount (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.ParamsCount nparams indTypes.size →
      (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsCountDistinct nparams indTypes next ctx post
    fun stats ctx' _ hcount _ _ _ => hnext stats ctx' hcount

theorem checkInductiveTypes.getParamsCount (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats =>
      stats.ParamsCount nparams indTypes.size :=
  checkInductiveTypes.paramsCount nparams indTypes pure ctx _ fun _ _ hcount => .pure hcount

theorem checkInductiveTypes.getParamsCount_of_nonempty (nparams : Nat)
    (indTypes : Array InductiveType) (ctx : Context) (hnonempty : indTypes.size ≠ 0) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats => stats.params.size = nparams :=
  (checkInductiveTypes.getParamsCount nparams indTypes ctx).mono fun _ hcount =>
    by simpa only [InductiveStats.ParamsCount, if_neg hnonempty] using hcount

theorem checkInductiveTypes.frameHeaderSizesParamsFVars
    (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → stats.ParamsAreFVars →
      ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsDistinct nparams indTypes next ctx post
    fun stats ctx' hsizes hfvars _ hframe => hnext stats ctx' hsizes hfvars hframe

theorem checkInductiveTypes.paramsNodup (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.params.toList.Nodup → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsDistinct nparams indTypes next ctx post
    fun stats ctx' _ _ hnodup _ => hnext stats ctx' hnodup

theorem checkInductiveTypes.getParamsNodup (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats => stats.params.toList.Nodup :=
  checkInductiveTypes.paramsNodup nparams indTypes pure ctx _ fun _ _ hnodup => .pure hnodup

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
