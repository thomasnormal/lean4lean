import Lean4Lean.Verify.InductiveMinorTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.recInd2_morphism from Lean4Lean.Verify.InductiveCPS

inductive RecursorMinorPassTrace (stats : InductiveStats) (types : Array InductiveType) :
    Nat → Array RecInfo → Context → Array RecInfo → Context → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context}
      (complete : ¬ parent < types.size) :
      RecursorMinorPassTrace stats types parent infos reader infos reader
  | step {parent : Nat} {infos middleInfos finalInfos : Array RecInfo}
      {reader middleReader finalReader : Context}
      (bound : parent < types.size)
      (constructors : RecursorMinorTrace stats types[parent]!.name parent infos
        types[parent]!.ctors reader middleInfos middleReader)
      (tail : RecursorMinorPassTrace stats types (parent + 1)
        middleInfos middleReader finalInfos finalReader) :
      RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader

theorem RecursorMinorPassTrace.scope {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  revert readerWF reserved
  induction trace with
  | stop => intro readerWF reserved; exact .refl _ readerWF reserved
  | step _ constructors _ tailInduction =>
    intro readerWF reserved
    have frame := constructors.scope readerWF reserved
    exact frame.trans (tailInduction frame.wf frame.reserved)

theorem RecursorMinorPassTrace.infoSize {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader) :
    finalInfos.size = infos.size := by
  induction trace with
  | stop => rfl
  | step _ constructors _ tailInduction => exact tailInduction.trans constructors.infoSize

theorem RecursorMinorPassTrace.before {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (bound : index < infos.size) (before : index < parent) :
    finalInfos[index]! = infos[index]! := by
  revert bound before
  induction trace with
  | stop => intro bound before; rfl
  | step _ constructors _ tailInduction =>
    intro bound before
    have middleBound := constructors.infoSize ▸ bound
    exact (tailInduction middleBound (by omega)).trans (constructors.other index bound (by omega))

theorem RecursorMinorPassTrace.after {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (bound : index < infos.size) (after : types.size ≤ index) :
    finalInfos[index]! = infos[index]! := by
  revert bound
  induction trace with
  | stop => intro bound; rfl
  | step parentBound constructors _ tailInduction =>
    intro bound
    have middleBound := constructors.infoSize ▸ bound
    exact (tailInduction middleBound).trans (constructors.other index bound (by omega))

theorem RecursorMinorPassTrace.minorPrefix {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (pending : parent ≤ index) (within : index < types.size) (bound : index < infos.size) :
    ∃ appended, finalInfos[index]!.minors.toList = infos[index]!.minors.toList ++ appended ∧
      appended.length = types[index]!.ctors.length := by
  revert pending within bound
  induction trace with
  | stop complete => intro pending within bound; omega
  | @step parent infos middleInfos finalInfos reader middleReader finalReader
      parentBound constructors tail tailInduction =>
    intro pending within bound
    have middleBound : index < middleInfos.size := by simpa only [constructors.infoSize] using bound
    by_cases selected : index = parent
    · subst index
      obtain ⟨appended, array, count⟩ := constructors.minorPrefix bound
      have preserved := tail.before parent middleBound (by omega)
      rw [preserved]
      exact ⟨appended, array, count⟩
    · obtain ⟨appended, array, count⟩ := tailInduction (by omega) within middleBound
      rw [constructors.other index bound selected] at array
      exact ⟨appended, array, count⟩

theorem RecursorMinorPassTrace.minorCounts {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (index : Nat) (pending : parent ≤ index) (within : index < types.size) (bound : index < infos.size) :
    finalInfos[index]!.minors.size = infos[index]!.minors.size + types[index]!.ctors.length := by
  obtain ⟨_, array, count⟩ := trace.minorPrefix index pending within bound
  have lengths := congrArg List.length array
  simpa only [List.length_append, Array.length_toList, count] using lengths

theorem mkRecInfos.loopInd2.scopedMinorPassTrace {ResultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ finalInfos finalReader,
      RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader →
      reader.RecursorScopeFrame finalReader → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd2 stats types parent infos next reader).WF post := by
  rw [mkRecInfos.loopInd2.eq_def]
  split
  · rename_i bound
    apply mkRecInfos.loopCtors.scopedTrace
    · exact readerWF
    · exact reserved
    intro middleInfos middleReader constructors constructorFrame
    apply mkRecInfos.loopInd2.scopedMinorPassTrace
    · exact constructorFrame.wf
    · exact constructorFrame.reserved
    intro finalInfos finalReader tail tailFrame
    apply nextWF finalInfos finalReader
    · exact .step bound (by simpa only [getElem!_pos, bound] using constructors) tail
    · exact constructorFrame.trans tailFrame
  · exact nextWF infos reader (.stop (by assumption)) (.refl reader readerWF reserved)
termination_by types.size - parent
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.loopInd2.getMinorPassTrace
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopInd2 stats types parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      RecursorMinorPassTrace stats types parent infos reader result.1 result.2 ∧
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size := by
  refine mkRecInfos.loopInd2.scopedMinorPassTrace stats types parent infos _ reader _
    readerWF reserved ?_
  intro finalInfos finalReader trace frame
  exact .pure ⟨trace, frame, trace.infoSize⟩

theorem mkRecInfos.loopInd2.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (collect : Array RecInfo → M CaptureType) (resume : CaptureType → Except Exception ResultType)
    (reader : Context)
    (nextEq : ∀ finalInfos finalReader,
      next finalInfos finalReader = (collect finalInfos finalReader).bind resume) :
    mkRecInfos.loopInd2 stats types parent infos next reader =
      (mkRecInfos.loopInd2 stats types parent infos collect reader).bind resume :=
  Lean4Lean.AddInductive.recInd2_morphism stats types parent infos next collect resume reader nextEq

end Lean4Lean.AddInductive
