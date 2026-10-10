import Lean4Lean.Verify.InductiveCtorFieldTrace
import Lean4Lean.Verify.InductiveIHTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata
open private Lean4Lean.AddInductive.withIndexDeclWF from Lean4Lean.Verify.RecursorInfoIndices
open private Lean4Lean.AddInductive.recCtors_morphism from Lean4Lean.Verify.InductiveCPS

def recursorMinorBody (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (terminal : Expr) (fields : Array Expr) : Expr :=
  let (parent, indices) := getIIndices stats terminal
  let introduction := mkAppN (mkAppN (.const constructor.name stats.levels) stats.params) fields
  .app (mkAppN infos[parent]!.motive indices) introduction

def recursorMinorDomain (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (terminal : Expr) (fields hypotheses : Array Expr)
    (domainReader : Context) : Expr :=
  domainReader.lctx.mkForall fields
    (domainReader.lctx.mkForall hypotheses (recursorMinorBody stats infos constructor terminal fields))

def recursorMinorName (parentName : Name) (constructor : Constructor) : Name :=
  constructor.name.replacePrefix parentName .anonymous

def recursorMinorContext (reader : Context) (parentName : Name) (constructor : Constructor)
    (domain : Expr) : Context :=
  recursorIndexContext reader (recursorMinorName parentName constructor) .default (peelTypeAnnotations domain)

def recursorMinorUpdate (parentIndex : Nat) (infos : Array RecInfo) (minor : Expr) : Array RecInfo :=
  infos.modify parentIndex fun info => { info with minors := info.minors.push minor }

theorem recursorMinorUpdate.size (parentIndex : Nat) (infos : Array RecInfo) (minor : Expr) :
    (recursorMinorUpdate parentIndex infos minor).size = infos.size := by
  simp only [recursorMinorUpdate, Array.size_modify]

theorem recursorMinorUpdate.selected (parentIndex : Nat) (infos : Array RecInfo) (minor : Expr)
    (bound : parentIndex < infos.size) :
    (recursorMinorUpdate parentIndex infos minor)[parentIndex]! =
      { infos[parentIndex]! with minors := infos[parentIndex]!.minors.push minor } := by
  simp [recursorMinorUpdate, getElem!_pos, bound, Array.getElem_modify]

theorem recursorMinorUpdate.other (parentIndex index : Nat) (infos : Array RecInfo) (minor : Expr)
    (bound : index < infos.size) (different : index ≠ parentIndex) :
    (recursorMinorUpdate parentIndex infos minor)[index]! = infos[index]! := by
  simp [recursorMinorUpdate, getElem!_pos, bound, Array.getElem_modify, Ne.symm different]

def RecursorMinorDomainSource (stats : InductiveStats) (infos : Array RecInfo)
    (constructor : Constructor) (reader : Context) (domain : Expr) (domainReader : Context) : Prop :=
  ∃ terminal finalIndex fields recursiveFields fieldReader hypotheses,
    RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader ∧
    RecursorIHTrace stats recursiveFields infos 0 #[] fieldReader hypotheses domainReader ∧
    domain = recursorMinorDomain stats infos constructor terminal fields hypotheses domainReader

theorem RecursorMinorDomainSource.scope {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame domainReader := by
  obtain ⟨_, _, _, _, _, _, fields, hypotheses, _⟩ := source
  have fieldFrame := fields.scope readerWF reserved
  exact fieldFrame.trans (hypotheses.scope fieldFrame.wf fieldFrame.reserved)

inductive RecursorMinorTrace (stats : InductiveStats) (parentName : Name) (parentIndex : Nat) :
    Array RecInfo → List Constructor → Context → Array RecInfo → Context → Prop where
  | stop {infos : Array RecInfo} {reader : Context} :
      RecursorMinorTrace stats parentName parentIndex infos [] reader infos reader
  | step {infos finalInfos : Array RecInfo} {constructor : Constructor} {constructors : List Constructor}
      {reader domainReader finalReader : Context} {domain : Expr}
      (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
      (tail : RecursorMinorTrace stats parentName parentIndex
        (recursorMinorUpdate parentIndex infos (.fvar ⟨domainReader.ngen.curr⟩)) constructors
        (recursorMinorContext domainReader parentName constructor domain) finalInfos finalReader) :
      RecursorMinorTrace stats parentName parentIndex infos (constructor :: constructors) reader finalInfos finalReader

theorem RecursorMinorTrace.scope {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  revert readerWF reserved
  induction trace with
  | stop => intro readerWF reserved; exact .refl _ readerWF reserved
  | @step infos finalInfos constructor constructors reader domainReader finalReader domain
      source tail tailInduction =>
    intro readerWF reserved
    have domainFrame := source.scope readerWF reserved
    have minorFrame := Context.RecursorScopeFrame.push domainReader domainFrame.wf domainFrame.reserved
      (recursorMinorName parentName constructor) .default (peelTypeAnnotations domain)
    exact domainFrame.trans (minorFrame.trans (tailInduction minorFrame.wf minorFrame.reserved))

theorem RecursorMinorTrace.infoSize {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader) :
    finalInfos.size = infos.size := by
  induction trace with
  | stop => rfl
  | step _ _ tailInduction => simpa only [recursorMinorUpdate.size] using tailInduction

theorem RecursorMinorTrace.other {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
    (index : Nat) (bound : index < infos.size) (different : index ≠ parentIndex) :
    finalInfos[index]! = infos[index]! := by
  revert bound
  induction trace with
  | stop => intro bound; rfl
  | @step infos finalInfos constructor constructors reader domainReader finalReader domain
      source tail tailInduction =>
    intro bound
    exact (tailInduction (by simpa only [recursorMinorUpdate.size] using bound)).trans
      (recursorMinorUpdate.other parentIndex index infos (.fvar ⟨domainReader.ngen.curr⟩) bound different)

theorem RecursorMinorTrace.minorPrefix {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
    (bound : parentIndex < infos.size) :
    ∃ appended, finalInfos[parentIndex]!.minors.toList = infos[parentIndex]!.minors.toList ++ appended ∧
      appended.length = constructors.length := by
  revert bound
  induction trace with
  | stop => intro bound; exact ⟨[], by simp only [List.append_nil], rfl⟩
  | @step infos finalInfos constructor constructors reader domainReader finalReader domain
      source tail tailInduction =>
    intro bound
    obtain ⟨appended, array, count⟩ := tailInduction (by simpa only [recursorMinorUpdate.size] using bound)
    rw [recursorMinorUpdate.selected parentIndex infos (.fvar ⟨domainReader.ngen.curr⟩) bound] at array
    refine ⟨.fvar ⟨domainReader.ngen.curr⟩ :: appended, ?_, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using array
    · simp only [List.length_cons, count]

theorem RecursorMinorTrace.minorCounts {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
    (bound : parentIndex < infos.size) :
    finalInfos[parentIndex]!.minors.size = infos[parentIndex]!.minors.size + constructors.length := by
  obtain ⟨_, array, count⟩ := trace.minorPrefix bound
  have lengths := congrArg List.length array
  simpa only [List.length_append, Array.length_toList, count] using lengths

theorem mkRecInfos.loopCtors.scopedTrace {ResultType : Type}
    (stats : InductiveStats) (parentName : Name) (parentIndex : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ finalInfos finalReader,
      RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader →
      reader.RecursorScopeFrame finalReader → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopCtors stats parentName parentIndex infos constructors next reader).WF post := by
  induction constructors generalizing infos reader with
  | nil => exact nextWF infos reader .stop (.refl _ readerWF reserved)
  | cons constructor constructors tailInduction =>
    rw [mkRecInfos.loopCtors.eq_def]
    refine mkRecInfos.loopCtorArgs.scopedTrace stats constructor.type _ reader _ readerWF reserved ?_
    intro terminal finalIndex fields recursiveFields fieldReader fieldTrace fieldFrame
    refine mkRecInfos.loopU.scopedTrace stats recursiveFields infos 0 #[] _ fieldReader _
      fieldFrame.wf fieldFrame.reserved ?_
    intro hypotheses domainReader hypothesisTrace hypothesisFrame
    apply Lean4Lean.AddInductive.getLCtxWF
    apply Lean4Lean.AddInductive.withIndexDeclWF
    let domain := recursorMinorDomain stats infos constructor terminal fields hypotheses domainReader
    have minorFrame := Context.RecursorScopeFrame.push domainReader hypothesisFrame.wf hypothesisFrame.reserved
      (recursorMinorName parentName constructor) .default (peelTypeAnnotations domain)
    refine tailInduction (recursorMinorUpdate parentIndex infos (.fvar ⟨domainReader.ngen.curr⟩))
      (recursorMinorContext domainReader parentName constructor domain) minorFrame.wf minorFrame.reserved ?_
    intro finalInfos finalReader trace frame
    exact nextWF finalInfos finalReader
      (.step ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
        fieldTrace, hypothesisTrace, rfl⟩ trace)
      (fieldFrame.trans (hypothesisFrame.trans (minorFrame.trans frame)))

theorem mkRecInfos.loopCtors.getTrace (stats : InductiveStats) (parentName : Name) (parentIndex : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopCtors stats parentName parentIndex infos constructors
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      RecursorMinorTrace stats parentName parentIndex infos constructors reader result.1 result.2 ∧
        reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size := by
  refine mkRecInfos.loopCtors.scopedTrace stats parentName parentIndex infos constructors _ reader _
    readerWF reserved ?_
  intro finalInfos finalReader trace frame
  exact .pure ⟨trace, frame, trace.infoSize⟩

theorem mkRecInfos.loopCtors.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (parentName : Name) (parentIndex : Nat)
    (infos : Array RecInfo) (constructors : List Constructor)
    (next : Array RecInfo → M ResultType) (collect : Array RecInfo → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ finalInfos finalReader,
      next finalInfos finalReader = (collect finalInfos finalReader).bind resume) :
    mkRecInfos.loopCtors stats parentName parentIndex infos constructors next reader =
      (mkRecInfos.loopCtors stats parentName parentIndex infos constructors collect reader).bind resume :=
  Lean4Lean.AddInductive.recCtors_morphism stats parentName parentIndex infos constructors next collect resume reader nextEq

end Lean4Lean.AddInductive
