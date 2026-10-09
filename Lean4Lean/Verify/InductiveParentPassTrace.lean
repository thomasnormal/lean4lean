import Lean4Lean.Verify.InductiveMotiveContextTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.readWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata
open private Lean4Lean.AddInductive.bindResultWF Lean4Lean.AddInductive.withIndexDeclWF
  from Lean4Lean.Verify.RecursorInfoIndices
open private Lean4Lean.AddInductive.recInd1_morphism from Lean4Lean.Verify.InductiveCPS

def recursorParentPassInfo (stats : InductiveStats) (parent : Nat)
    (indices : Array Expr) (reader : Context) : RecInfo :=
  { indices
    major := .fvar ⟨reader.ngen.curr⟩
    motive := .fvar ⟨(recursorIndexContext reader `t .default
      (recursorMajorDomain stats parent indices)).ngen.curr⟩
    minors := #[] }

inductive RecursorParentPassTrace (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) : Nat → Array RecInfo → Context → Array RecInfo → Context → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context}
      (complete : ¬ parent < types.size) :
      RecursorParentPassTrace stats types elimLevel parent infos reader infos reader
  | step {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader indexReader : Context}
      {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
      (bound : parent < types.size)
      (initialNormalization :
        ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) reader) = .ok normalized)
      (indicesTrace : RecursorIndexTrace stats normalized 0 #[] reader
        terminal finalIndex indices indexReader)
      (tail : RecursorParentPassTrace stats types elimLevel (parent + 1)
        (infos.push (recursorParentPassInfo stats parent indices indexReader))
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent))
        finalInfos finalReader) :
      RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader

theorem RecursorParentPassTrace.scope {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  induction trace with
  | stop => exact .refl _ readerWF reserved
  | @step parent infos finalInfos reader finalReader indexReader normalized terminal finalIndex indices
      bound initialNormalization indicesTrace tail tailInduction =>
    have indexFrame := indicesTrace.scope readerWF reserved
    have majorFrame := Context.RecursorScopeFrame.push indexReader indexFrame.wf indexFrame.reserved
      `t .default (recursorMajorDomain stats parent indices)
    have motiveFrame := Context.RecursorScopeFrame.push
      (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices))
      majorFrame.wf majorFrame.reserved (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel indices (.fvar ⟨indexReader.ngen.curr⟩)
        (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices)))
    exact indexFrame.trans (majorFrame.trans (motiveFrame.trans
      (tailInduction motiveFrame.wf motiveFrame.reserved)))

theorem RecursorParentPassTrace.counts {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader) :
    finalInfos.size = infos.size + (types.size - parent) := by
  induction trace with
  | stop complete => simp only [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt complete), Nat.add_zero]
  | step bound _ _ _ tailInduction =>
    simp only [Array.size_push] at tailInduction
    omega

theorem RecursorParentPassTrace.prefix {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader) :
    ∃ appended,
      finalInfos.toList = infos.toList ++ appended ∧ appended.length = types.size - parent ∧
      ∀ info ∈ appended, info.minors = #[] := by
  induction trace with
  | stop complete =>
    exact ⟨[], by simp only [List.append_nil],
      by simp only [List.length_nil, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt complete)],
      by intro info member; cases member⟩
  | @step parent infos finalInfos reader finalReader indexReader normalized terminal finalIndex indices
      bound initialNormalization indicesTrace tail tailInduction =>
    obtain ⟨appended, array, count, minors⟩ := tailInduction
    refine ⟨recursorParentPassInfo stats parent indices indexReader :: appended, ?_, ?_, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using array
    · simp only [List.length_cons]
      omega
    · intro info member
      rcases List.mem_cons.mp member with equality | member
      · subst info
        rfl
      · exact minors info member

theorem mkRecInfos.loopInd1.scopedParentPassTrace {ResultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ finalInfos finalReader,
      RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader →
      reader.RecursorScopeFrame finalReader → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos next reader).WF post := by
  rw [mkRecInfos.loopInd1.eq_def]
  split
  · rename_i bound
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindResultWF
    intro normalized initialNormalization
    apply mkRecInfos.loopArgs1.scopedTrace
    · exact readerWF
    · exact reserved
    intro terminal finalIndex indices indexReader indicesTrace indexFrame
    apply Lean4Lean.AddInductive.withIndexDeclWF
    let majorReader := recursorIndexContext indexReader `t .default
      (recursorMajorDomain stats parent indices)
    have majorFrame := Context.RecursorScopeFrame.push indexReader indexFrame.wf indexFrame.reserved
      `t .default (recursorMajorDomain stats parent indices)
    apply Lean4Lean.AddInductive.getLCtxWF
    dsimp only
    apply Lean4Lean.AddInductive.withIndexDeclWF
    have motiveFrame := Context.RecursorScopeFrame.push majorReader majorFrame.wf majorFrame.reserved
      (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel indices (.fvar ⟨indexReader.ngen.curr⟩) majorReader)
    apply mkRecInfos.loopInd1.scopedParentPassTrace
    · exact motiveFrame.wf
    · exact motiveFrame.reserved
    intro finalInfos finalReader tail tailFrame
    apply nextWF finalInfos finalReader
    · exact .step bound (by simpa only [getElem!_pos, bound] using initialNormalization) indicesTrace tail
    · exact indexFrame.trans (majorFrame.trans (motiveFrame.trans tailFrame))
  · exact nextWF infos reader (.stop (by assumption)) (.refl reader readerWF reserved)
termination_by types.size - parent
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.loopInd1.getParentPassTrace
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2 ∧
      reader.RecursorScopeFrame result.2 ∧
      result.1.size = infos.size + (types.size - parent) := by
  refine mkRecInfos.loopInd1.scopedParentPassTrace stats types elimLevel parent infos _ reader _
    readerWF reserved ?_
  intro finalInfos finalReader trace frame
  exact .pure ⟨trace, frame, trace.counts⟩

theorem mkRecInfos.loopInd1.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (collect : Array RecInfo → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (reader : Context)
    (nextEq : ∀ finalInfos finalReader,
      next finalInfos finalReader = (collect finalInfos finalReader).bind resume) :
    mkRecInfos.loopInd1 stats types elimLevel parent infos next reader =
      (mkRecInfos.loopInd1 stats types elimLevel parent infos collect reader).bind resume :=
  Lean4Lean.AddInductive.recInd1_morphism stats types elimLevel parent infos next collect resume reader nextEq

end Lean4Lean.AddInductive
