import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def InductiveStats.HeaderSizes (stats : InductiveStats) (numTypes : Nat) : Prop :=
  stats.nindices.size = numTypes ∧ stats.indConsts.size = numTypes

private structure PrefixSizes (stats : InductiveStats) (numTypes numParams numLevels : Nat) : Prop where
  nindices : stats.nindices.size = numTypes
  indConsts : stats.indConsts.size = numTypes
  levels : stats.levels.length = numLevels
  params : stats.params.size = numParams

private theorem bindWF {ctx : Context} {action : M α} {next : α → M β} {post : β → Prop}
    (hnext : ∀ result, (next result ctx).WF post) : ((action >>= next) ctx).WF post :=
  Except.WF.bind (fun _ _ => True.intro) fun result _ => hnext result

private theorem readWF {ctx : Context} {next : Context → M α} {post : α → Prop}
    (hnext : (next ctx ctx).WF post) : ((read >>= next) ctx).WF post :=
  hnext

private theorem withLocalDeclWF {ctx : Context} {name : Name} {bi : BinderInfo} {type : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : ∀ param ctx', ctx'.lparams = ctx.lparams → (next param ctx').WF post) :
    (withLocalDecl name bi type next ctx).WF post :=
  hnext _ _ rfl

private theorem loop_headerSizes (nparams numTypes : Nat) (fuel : Nat)
    (stats : InductiveStats) (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M α) (ctx : Context) (post : α → Prop)
    (hstats : PrefixSizes stats numTypes (if numTypes = 0 then index else nparams)
      ctx.lparams.length)
    (hnext : ∀ type stats nindices ctx',
      PrefixSizes stats numTypes nparams ctx'.lparams.length →
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
          intro param ctx' hlparams
          apply bindWF
          intro type'
          apply ih _ type' (index + 1) nindices ctx'
          · have hzero : numTypes = 0 := by
              simpa [Array.isEmpty, hstats.indConsts] using ‹stats.indConsts.isEmpty = true›
            subst numTypes
            exact ⟨hstats.nindices, hstats.indConsts,
              by simpa [hlparams] using hstats.levels, by simpa using hstats.params⟩
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
          · exact Except.WF.throw
      · apply withLocalDeclWF
        intro param ctx' hlparams
        apply bindWF
        intro type'
        exact ih stats type' index (nindices + 1) ctx' (by simpa [hlparams] using hstats)
    · split
      · exact Except.WF.throw
      · have hindex : index = nparams := by simpa using ‹¬(index != nparams) = true›
        subst index
        exact hnext type stats nindices ctx (by simpa using hstats)

private theorem loopInd_headerSizes (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (ctx : Context) (post : α → Prop) (hbound : processed ≤ indTypes.size)
    (hstats : PrefixSizes stats processed (if processed = 0 then 0 else nparams)
      ctx.lparams.length)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → (next stats ctx').WF post) :
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
    intro type stats' nindices ctx' hsizes
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
          hsizes.levels, by simpa using hsizes.params⟩
      · exact hnext
    · split
      · exact Except.WF.throw
      · apply bindWF
        intro _
        apply loopInd_headerSizes nparams indTypes next (processed + 1) _ ctx' post
        · omega
        · exact ⟨by simpa using hsizes.nindices,
            by simpa using hsizes.indConsts,
            hsizes.levels, by simpa using hsizes.params⟩
        · exact hnext
  · apply readWF
    apply hnext
    have hcount : processed = indTypes.size := by omega
    simp only [InductiveStats.HeaderSizes, hstats.levels, hstats.nindices,
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
termination_by indTypes.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.headerSizes (nparams : Nat) (indTypes : Array InductiveType)
    (next : InductiveStats → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes indTypes.size → (next stats ctx').WF post) :
    (checkInductiveTypes nparams indTypes next ctx).WF post := by
  unfold checkInductiveTypes
  apply readWF
  apply loopInd_headerSizes nparams indTypes next 0 _ ctx post (Nat.zero_le _)
  · exact ⟨rfl, rfl, by simp, rfl⟩
  · exact hnext

theorem checkInductiveTypes.getHeaderSizes (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats =>
      stats.HeaderSizes indTypes.size :=
  checkInductiveTypes.headerSizes nparams indTypes pure ctx _ fun _ _ hsizes => .pure hsizes

end Lean4Lean.AddInductive
