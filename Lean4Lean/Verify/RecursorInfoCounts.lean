import Lean4Lean.Verify.RecursorInfoFrame
import Lean4Lean.Verify.RecursorMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  Lean4Lean.AddInductive.withLocalDeclWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.loopArgs1_frame Lean4Lean.AddInductive.loopCtorArgs_frame
  Lean4Lean.AddInductive.loopU_frame from Lean4Lean.Verify.RecursorInfoFrame

structure RecursorInfoCounts (types : Array InductiveType) (infos : Array RecInfo) : Prop where
  size : infos.size = types.size
  minors : ∀ index, index < types.size → infos[index]!.minors.size = types[index]!.ctors.length

theorem RecursorInfoCounts.motiveTotal {types : Array InductiveType} {infos : Array RecInfo}
    (hcounts : RecursorInfoCounts types infos) :
    (infos.map (·.motive)).size = types.size := by
  simpa using hcounts.size

theorem RecursorInfoCounts.minorTotal {types : Array InductiveType} {infos : Array RecInfo}
    (hcounts : RecursorInfoCounts types infos) :
    (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length := by
  rw [Array.size_flatMap, List.length_flatMap]
  have hmap : infos.map (fun info => info.minors.size) = types.map (fun type => type.ctors.length) := by
    apply Array.ext
    · simpa using hcounts.size
    · intro index hinfo htype
      have hbound : index < types.size := by simpa using htype
      simpa only [Array.getElem_map, getElem!_pos, hcounts.size, hbound] using hcounts.minors index hbound
  rw [hmap, ← Array.sum_toList]
  simp

private def EmptyMinors (infos : Array RecInfo) : Prop := ∀ info ∈ infos, info.minors.size = 0

private theorem loopInd1_counts (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hbound : index ≤ types.size)
    (hsize : infos.size = index) (hempty : EmptyMinors infos)
    (hnext : ∀ infos current, ctx.HeaderFrame current → infos.size = types.size →
      EmptyMinors infos → (next infos current).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd1.eq_def]
  split
  · apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindWF
    intro normalized
    apply Lean4Lean.AddInductive.loopArgs1_frame
    intro indices current hframe
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro major majorCtx _ _ _ hmajor
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro motive motiveCtx _ _ _ hmotive
    apply loopInd1_counts
    · omega
    · simpa using hsize
    · intro info hinfo
      rcases Array.mem_push.mp hinfo with hinfo | rfl
      · exact hempty info hinfo
      · rfl
    · intro infos final hfinal hsize hempty
      exact hnext infos final (hframe.trans (hmajor.trans (hmotive.trans hfinal))) hsize hempty
  · apply hnext infos ctx (.refl ctx)
    · omega
    · exact hempty
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

private theorem modify_minor_self (infos : Array RecInfo) (index : Nat) (minor : Expr)
    (hindex : index < infos.size) :
    (infos.modify index fun info => { info with minors := info.minors.push minor })[index]!.minors.size =
      infos[index]!.minors.size + 1 := by
  simp [getElem!_pos, hindex, Array.getElem_modify]

private theorem modify_minor_other (infos : Array RecInfo) (index other : Nat) (minor : Expr)
    (hother : other < infos.size) (hne : other ≠ index) :
    (infos.modify index fun info => { info with minors := info.minors.push minor })[other]!.minors.size =
      infos[other]!.minors.size := by
  simp [getElem!_pos, hother, Array.getElem_modify, Ne.symm hne]

private theorem loopCtors_counts (stats : InductiveStats) (parent : Name) (index : Nat)
    (infos : Array RecInfo) (ctors : List Constructor) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hindex : index < infos.size)
    (hnext : ∀ final current, ctx.HeaderFrame current → final.size = infos.size →
      final[index]!.minors.size = infos[index]!.minors.size + ctors.length →
      (∀ other, other < infos.size → other ≠ index → final[other]!.minors.size = infos[other]!.minors.size) →
      (next final current).WF post) :
    (mkRecInfos.loopCtors stats parent index infos ctors next ctx).WF post := by
  induction ctors generalizing infos ctx with
  | nil => exact hnext infos ctx (.refl ctx) rfl (by simp) (fun _ _ _ => rfl)
  | cons ctor ctors ih =>
    rw [mkRecInfos.loopCtors.eq_def]
    apply Lean4Lean.AddInductive.loopCtorArgs_frame
    intro type fields recursiveFields fieldCtx hfields
    apply Lean4Lean.AddInductive.loopU_frame
    intro hypotheses hypothesisCtx hhypotheses
    apply Lean4Lean.AddInductive.bindWF
    intro lctx
    apply Lean4Lean.AddInductive.withLocalDeclWF
    intro minor minorCtx _ _ _ hminor
    apply ih
    · simpa using hindex
    · intro final finalCtx hfinal hsize hhere hother
      apply hnext final finalCtx (hfields.trans (hhypotheses.trans (hminor.trans hfinal)))
      · simpa using hsize
      · rw [modify_minor_self infos index minor hindex] at hhere
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhere
      · intro other hbound hne
        exact (hother other (by simpa using hbound) hne).trans
          (modify_minor_other infos index other minor hbound hne)

private def PrefixMinorCounts (types : Array InductiveType) (infos : Array RecInfo)
    (processed : Nat) : Prop :=
  infos.size = types.size ∧ ∀ index, index < types.size → infos[index]!.minors.size =
    if index < processed then types[index]!.ctors.length else 0

private theorem loopInd2_counts (stats : InductiveStats) (types : Array InductiveType)
    (index : Nat) (infos : Array RecInfo) (next : Array RecInfo → M α)
    (ctx : Context) (post : α → Prop) (hcounts : PrefixMinorCounts types infos index)
    (hnext : ∀ infos current, ctx.HeaderFrame current → RecursorInfoCounts types infos →
      (next infos current).WF post) :
    (mkRecInfos.loopInd2 stats types index infos next ctx).WF post := by
  rw [mkRecInfos.loopInd2.eq_def]
  split
  · apply loopCtors_counts
    · simpa only [hcounts.1] using ‹index < types.size›
    · intro final current hframe hsize hhere hother
      apply loopInd2_counts
      · refine ⟨hsize.trans hcounts.1, ?_⟩
        intro other hbound
        by_cases heq : other = index
        · subst other
          simpa [hcounts.2 index hbound, getElem!_pos, hbound] using hhere
        · rw [hother other (by simpa only [hcounts.1] using hbound) heq, hcounts.2 other hbound]
          have hlt : other < index + 1 ↔ other < index := by omega
          simp only [hlt]
      · intro infos finalCtx hfinal hcounts
        exact hnext infos finalCtx (hframe.trans hfinal) hcounts
  · apply hnext infos ctx (.refl ctx)
    refine ⟨hcounts.1, ?_⟩
    intro other hbound
    have hprocessed : other < index := by omega
    simpa only [if_pos hprocessed] using hcounts.2 other hbound
termination_by types.size - index
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.frameCounts (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → RecursorInfoCounts types infos →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post := by
  unfold mkRecInfos
  apply loopInd1_counts
  · exact Nat.zero_le _
  · rfl
  · intro info hinfo
    simp at hinfo
  · intro infos current hframe hsize hempty
    apply loopInd2_counts
    · refine ⟨hsize, ?_⟩
      intro index hindex
      have hbound : index < infos.size := by omega
      have hinfo : infos[index]! ∈ infos := by
        simpa only [getElem!_pos, hbound] using (Array.getElem_mem (xs := infos) (i := index) hbound)
      simpa using hempty _ hinfo
    · intro infos final hfinal hcounts
      exact hnext infos final (hframe.trans hfinal) hcounts

theorem mkRecInfos.getCounts (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (ctx : Context) :
    (mkRecInfos stats types elimLevel (fun infos => do
      return (infos, ← readThe Context)) ctx).WF fun result =>
        ctx.HeaderFrame result.2 ∧ RecursorInfoCounts types result.1 := by
  apply mkRecInfos.frameCounts
  intro infos current hframe hcounts
  exact .pure ⟨hframe, hcounts⟩

theorem mkRecInfos.registerCounts (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (nparams : Nat)
    (ctx : Context) (hwf : ctx.env.constants.WF) (hparams : stats.ParamsCount nparams types.size) :
    (mkRecInfos stats types elimLevel (fun infos => do
      let lctx ← getLCtx
      declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe) ctx).WF fun env =>
        env.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
        stats.DeclaredRecursorCounts nparams types env := by
  apply mkRecInfos.frameCounts
  intro infos current hframe hcounts
  apply Lean4Lean.AddInductive.bindWF
  intro lctx
  refine (declareRecursors.metadata stats types elimLevel infos lparams lctx isK isUnsafe current
    (by simpa only [hframe.env] using hwf)).mono ?_
  rintro env ⟨hfinal, hkeep, hmetadata⟩
  refine ⟨hfinal, ?_, hmetadata.declaredCounts hparams hcounts.size hcounts.minorTotal⟩
  intro name info hold
  apply hkeep name info
  simpa only [hframe.env] using hold

end Lean4Lean.AddInductive
