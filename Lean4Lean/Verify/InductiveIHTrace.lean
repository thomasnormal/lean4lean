import Lean4Lean.Verify.InductiveUArgTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata
open private Lean4Lean.AddInductive.withIndexDeclWF from Lean4Lean.Verify.RecursorInfoIndices
open private Lean4Lean.AddInductive.recU_morphism from Lean4Lean.Verify.InductiveCPS

def recursorIHBody (stats : InductiveStats) (infos : Array RecInfo)
    (argument terminal : Expr) (arguments : Array Expr) : Expr :=
  let (parent, indices) := getIIndices stats terminal
  .app (mkAppN infos[parent]!.motive indices) (mkAppN argument arguments)

def recursorIHDomain (stats : InductiveStats) (infos : Array RecInfo)
    (argument terminal : Expr) (arguments : Array Expr) (argumentReader : Context) : Expr :=
  argumentReader.lctx.mkForall arguments (recursorIHBody stats infos argument terminal arguments)

def recursorIHName (reader : Context) (argument : Expr) : Name :=
  (reader.lctx.get! argument.fvarId!).userName.appendAfter "_ih"

def recursorIHContext (reader : Context) (argument domain : Expr) : Context :=
  recursorIndexContext reader (recursorIHName reader argument) .default (peelTypeAnnotations domain)

def RecursorIHDomainSource (stats : InductiveStats) (infos : Array RecInfo)
    (argument : Expr) (reader : Context) (domain : Expr) : Prop :=
  ∃ terminal arguments argumentReader,
    RecursorUArgOpeningTrace argument reader terminal arguments argumentReader ∧
      domain = recursorIHDomain stats infos argument terminal arguments argumentReader

inductive RecursorIHTrace (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo) :
    Nat → Array Expr → Context → Array Expr → Context → Prop where
  | stop {index : Nat} {hypotheses : Array Expr} {reader : Context}
      (complete : ¬ index < fields.size) :
      RecursorIHTrace stats fields infos index hypotheses reader hypotheses reader
  | step {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
      {domain : Expr}
      (bound : index < fields.size)
      (source : RecursorIHDomainSource stats infos fields[index]! reader domain)
      (tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader) :
      RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader

theorem RecursorIHTrace.scope {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  revert readerWF reserved
  induction trace with
  | stop _ => intro readerWF reserved; exact .refl _ readerWF reserved
  | @step index hypotheses finalHypotheses reader finalReader domain bound source tail tailInduction =>
    intro readerWF reserved
    have pushed := Context.RecursorScopeFrame.push reader readerWF reserved
      (recursorIHName reader fields[index]!) .default (peelTypeAnnotations domain)
    exact pushed.trans (tailInduction pushed.wf pushed.reserved)

theorem RecursorIHTrace.counts {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    finalHypotheses.size = hypotheses.size + (fields.size - index) := by
  induction trace with
  | stop complete => simp only [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt complete), Nat.add_zero]
  | step bound _ _ tailInduction =>
    simp only [Array.size_push] at tailInduction
    omega

theorem RecursorIHTrace.declared {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (declared : RecursorFieldsDeclared reader.lctx hypotheses) :
    RecursorFieldsDeclared finalReader.lctx finalHypotheses := by
  revert declared
  induction trace with
  | stop _ => exact id
  | @step index hypotheses finalHypotheses reader finalReader domain bound source tail tailInduction =>
    intro declared
    exact tailInduction (declared.push ⟨reader.ngen.curr⟩ (recursorIHName reader fields[index]!)
      (peelTypeAnnotations domain) .default)

theorem RecursorIHTrace.prefix {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    ∃ appended, finalHypotheses.toList = hypotheses.toList ++ appended ∧
      appended.length = fields.size - index := by
  induction trace with
  | stop complete =>
    exact ⟨[], by simp only [List.append_nil],
      by simp only [List.length_nil, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt complete)]⟩
  | @step index hypotheses finalHypotheses reader finalReader domain bound source tail tailInduction =>
    obtain ⟨appended, array, count⟩ := tailInduction
    refine ⟨.fvar ⟨reader.ngen.curr⟩ :: appended, ?_, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using array
    · simp only [List.length_cons]
      omega

theorem RecursorIHTrace.allocations {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) :
    ∃ allocated : List LocalDecl,
      finalReader.lctx.toList = allocated.reverse ++ reader.lctx.toList ∧
      finalHypotheses.toList = hypotheses.toList ++ allocated.map LocalDecl.toExpr ∧
      ∀ declaration ∈ allocated,
        declaration.value? (allowNondep := true) = none ∧ declaration.kind = .default := by
  induction trace with
  | stop _ => exact ⟨[], rfl, by simp only [List.map_nil, List.append_nil], by simp⟩
  | @step index hypotheses finalHypotheses reader finalReader domain bound source tail tailInduction =>
    obtain ⟨allocated, declarations, array, shapes⟩ := tailInduction
    let declaration := LocalDecl.cdecl reader.lctx.decls.size ⟨reader.ngen.curr⟩
      (recursorIHName reader fields[index]!) (peelTypeAnnotations domain) .default .default
    refine ⟨declaration :: allocated, ?_, ?_, ?_⟩
    · simpa only [recursorIHContext, recursorIndexContext, LocalContext.mkLocalDecl_toList,
        List.reverse_cons, List.append_assoc, List.singleton_append] using declarations
    · simpa only [List.map_cons, Array.toList_push, List.append_assoc, List.singleton_append,
        declaration, LocalDecl.toExpr] using array
    · intro current member
      rcases List.mem_cons.mp member with equality | member
      · subst current
        exact ⟨rfl, rfl⟩
      · exact shapes current member

theorem mkRecInfos.loopUArgs.ihDomainSource (stats : InductiveStats) (infos : Array RecInfo)
    (argument : Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopUArgs argument (fun terminal arguments => do
      let (parent, indices) := getIIndices stats terminal
      return (← getLCtx).mkForall arguments
        (.app (mkAppN infos[parent]!.motive indices) (mkAppN argument arguments))) reader).WF
      (RecursorIHDomainSource stats infos argument reader) := by
  refine mkRecInfos.loopUArgs.scopedTrace argument _ reader _ readerWF reserved ?_
  intro terminal arguments argumentReader opening frame
  apply Lean4Lean.AddInductive.getLCtxWF
  exact .pure ⟨terminal, arguments, argumentReader, opening, rfl⟩

theorem mkRecInfos.loopU.scopedTrace {ResultType : Type}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (next : Array Expr → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ finalHypotheses finalReader,
      RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader →
      reader.RecursorScopeFrame finalReader → (next finalHypotheses finalReader).WF post) :
    (mkRecInfos.loopU stats fields infos index hypotheses next reader).WF post := by
  rw [mkRecInfos.loopU.eq_def]
  split
  · rename_i bound
    refine (mkRecInfos.loopUArgs.ihDomainSource stats infos fields[index] reader readerWF reserved).bind ?_
    intro domain source
    apply Lean4Lean.AddInductive.getLCtxWF
    apply Lean4Lean.AddInductive.withIndexDeclWF
    have pushed := Context.RecursorScopeFrame.push reader readerWF reserved
      (recursorIHName reader fields[index]) .default (peelTypeAnnotations domain)
    refine mkRecInfos.loopU.scopedTrace stats fields infos (index + 1)
      (hypotheses.push (.fvar ⟨reader.ngen.curr⟩)) next
      (recursorIHContext reader fields[index] domain) post pushed.wf pushed.reserved ?_
    intro finalHypotheses finalReader trace frame
    exact nextWF finalHypotheses finalReader
      (.step bound (by simpa only [getElem!_pos, bound] using source)
        (by simpa only [getElem!_pos, bound] using trace)) (pushed.trans frame)
  · exact nextWF hypotheses reader (.stop (by assumption)) (.refl _ readerWF reserved)
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

theorem mkRecInfos.loopU.getTrace (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopU stats fields infos index hypotheses
      (fun finalHypotheses => do return (finalHypotheses, ← readThe Context)) reader).WF fun result =>
      RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2 ∧
        reader.RecursorScopeFrame result.2 ∧
        result.1.size = hypotheses.size + (fields.size - index) := by
  refine mkRecInfos.loopU.scopedTrace stats fields infos index hypotheses _ reader _
    readerWF reserved ?_
  intro finalHypotheses finalReader trace frame
  exact .pure ⟨trace, frame, trace.counts⟩

theorem mkRecInfos.loopU.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr)
    (next : Array Expr → M ResultType) (collect : Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ finalHypotheses finalReader,
      next finalHypotheses finalReader = (collect finalHypotheses finalReader).bind resume) :
    mkRecInfos.loopU stats fields infos index hypotheses next reader =
      (mkRecInfos.loopU stats fields infos index hypotheses collect reader).bind resume :=
  Lean4Lean.AddInductive.recU_morphism stats fields infos index hypotheses next collect resume reader nextEq

end Lean4Lean.AddInductive
