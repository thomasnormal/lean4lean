import Lean4Lean.Verify.RecursorInfoIndices
import Lean4Lean.Verify.InductiveCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.readWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindResultWF Lean4Lean.AddInductive.withIndexDeclWF
  from Lean4Lean.Verify.RecursorInfoIndices
open private Lean4Lean.AddInductive.recCtor_loop_morphism Lean4Lean.AddInductive.recCtor_morphism
  from Lean4Lean.Verify.InductiveCPS

inductive RecursorCtorFieldTrace (stats : InductiveStats) :
    Expr → Nat → Array Expr → Array Expr → Context →
      Expr → Nat → Array Expr → Array Expr → Context → Prop where
  | stop {type : Expr} {index : Nat} {fields recursiveFields : Array Expr} {reader : Context}
      (terminal : ∀ name domain body binderInfo, type ≠ .forallE name domain body binderInfo) :
      RecursorCtorFieldTrace stats type index fields recursiveFields reader
        type index fields recursiveFields reader
  | parameter {name : Name} {domain body parameter : Expr} {binderInfo : BinderInfo}
      {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
      {reader finalReader : Context} {terminal : Expr}
      (selected : stats.params[index]? = some parameter)
      (tail : RecursorCtorFieldTrace stats (body.instantiate1 parameter) (index + 1)
        fields recursiveFields reader terminal finalIndex finalFields finalRecursive finalReader) :
      RecursorCtorFieldTrace stats (.forallE name domain body binderInfo) index
        fields recursiveFields reader terminal finalIndex finalFields finalRecursive finalReader
  | field {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
      {reader finalReader : Context} {terminal : Expr} {recursive : Option Nat}
      (selected : stats.params[index]? = none)
      (classified : isRecArg stats domain
        (recursorIndexContext reader name binderInfo (peelTypeAnnotations domain)) = .ok recursive)
      (tail : RecursorCtorFieldTrace stats (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))
        (index + 1) (fields.push (.fvar ⟨reader.ngen.curr⟩))
        (if recursive.isSome then recursiveFields.push (.fvar ⟨reader.ngen.curr⟩) else recursiveFields)
        (recursorIndexContext reader name binderInfo (peelTypeAnnotations domain))
        terminal finalIndex finalFields finalRecursive finalReader) :
      RecursorCtorFieldTrace stats (.forallE name domain body binderInfo) index
        fields recursiveFields reader terminal finalIndex finalFields finalRecursive finalReader

theorem RecursorCtorFieldTrace.scope {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  revert readerWF reserved
  induction trace with
  | stop _ => intro readerWF reserved; exact .refl _ readerWF reserved
  | parameter _ _ tailInduction => exact tailInduction
  | @field name domain body binderInfo index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader terminal recursive selected classified tail tailInduction =>
    intro readerWF reserved
    have pushed := Context.RecursorScopeFrame.push reader readerWF reserved name binderInfo
      (peelTypeAnnotations domain)
    exact pushed.trans (tailInduction pushed.wf pushed.reserved)

theorem RecursorCtorFieldTrace.declared {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (declared : RecursorFieldsDeclared reader.lctx fields) :
    RecursorFieldsDeclared finalReader.lctx finalFields := by
  revert declared
  induction trace with
  | stop _ => exact id
  | parameter _ _ tailInduction => exact tailInduction
  | @field name domain body binderInfo index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader terminal recursive selected classified tail tailInduction =>
    intro declared
    exact tailInduction (declared.push ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) binderInfo)

theorem RecursorCtorFieldTrace.recursiveSublist {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (selected : recursiveFields.toList.Sublist fields.toList) :
    finalRecursive.toList.Sublist finalFields.toList := by
  revert selected
  induction trace with
  | stop _ => exact id
  | parameter _ _ tailInduction => exact tailInduction
  | @field name domain body binderInfo index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader terminal recursive parameterSelected classified tail tailInduction =>
    intro selected
    apply tailInduction
    split
    · simpa only [Array.toList_push] using selected.append
        (List.Sublist.refl [.fvar ⟨reader.ngen.curr⟩])
    · simpa only [Array.toList_push] using
        (List.sublist_append_of_sublist_left selected (l₂ := [.fvar ⟨reader.ngen.curr⟩]))

theorem RecursorCtorFieldTrace.fieldsPrefix {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    ∃ appended, finalFields.toList = fields.toList ++ appended := by
  induction trace with
  | stop _ => exact ⟨[], by simp only [List.append_nil]⟩
  | parameter _ _ tailInduction => exact tailInduction
  | @field name domain body binderInfo index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader terminal recursive selected classified tail tailInduction =>
    obtain ⟨appended, array⟩ := tailInduction
    refine ⟨.fvar ⟨reader.ngen.curr⟩ :: appended, ?_⟩
    simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using array

theorem RecursorCtorFieldTrace.allocations {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    ∃ allocated : List LocalDecl,
      finalReader.lctx.toList = allocated.reverse ++ reader.lctx.toList ∧
      finalFields.toList = fields.toList ++ allocated.map LocalDecl.toExpr ∧
      ∀ declaration ∈ allocated,
        declaration.value? (allowNondep := true) = none ∧ declaration.kind = .default := by
  induction trace with
  | stop _ => exact ⟨[], rfl, by simp only [List.map_nil, List.append_nil], by simp⟩
  | parameter _ _ tailInduction => exact tailInduction
  | @field name domain body binderInfo index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader terminal recursive selected classified tail tailInduction =>
    obtain ⟨allocated, declarations, array, shapes⟩ := tailInduction
    let declaration := LocalDecl.cdecl reader.lctx.decls.size ⟨reader.ngen.curr⟩ name
      (peelTypeAnnotations domain) binderInfo .default
    refine ⟨declaration :: allocated, ?_, ?_, ?_⟩
    · simpa only [recursorIndexContext, LocalContext.mkLocalDecl_toList, List.reverse_cons,
        List.append_assoc, List.singleton_append] using declarations
    · simpa only [List.map_cons, Array.toList_push, List.append_assoc, List.singleton_append,
        declaration, LocalDecl.toExpr] using array
    · intro current member
      rcases List.mem_cons.mp member with equality | member
      · subst current
        exact ⟨rfl, rfl⟩
      · exact shapes current member

theorem RecursorCtorFieldTrace.terminal {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats type index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    ∀ name domain body binderInfo, terminal ≠ .forallE name domain body binderInfo := by
  induction trace with
  | stop terminal => exact terminal
  | parameter _ _ tailInduction => exact tailInduction
  | field _ _ _ tailInduction => exact tailInduction

theorem mkRecInfos.loopCtorArgs.loop.scopedTrace {ResultType : Type}
    (stats : InductiveStats) (type : Expr) (index : Nat) (fields recursiveFields : Array Expr)
    (fuel : Nat) (next : Expr → Array Expr → Array Expr → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ terminal finalIndex finalFields finalRecursive finalReader,
      RecursorCtorFieldTrace stats type index fields recursiveFields reader
        terminal finalIndex finalFields finalRecursive finalReader →
      reader.RecursorScopeFrame finalReader → (next terminal finalFields finalRecursive finalReader).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel reader).WF post := by
  induction fuel generalizing type index fields recursiveFields reader with
  | zero => exact Except.WF.throw
  | succ fuel tailInduction =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · rename_i name domain body binderInfo
      split
      · rename_i parameter selected
        apply tailInduction
        · exact readerWF
        · exact reserved
        intro terminal finalIndex finalFields finalRecursive finalReader trace frame
        exact nextWF terminal finalIndex finalFields finalRecursive finalReader (.parameter selected trace) frame
      · rename_i selected
        have noParameter : stats.params[index]? = none := by
          cases parameterValue : stats.params[index]? with
          | none => rfl
          | some parameter => exact False.elim (selected parameter parameterValue)
        apply Lean4Lean.AddInductive.withIndexDeclWF
        have pushed := Context.RecursorScopeFrame.push reader readerWF reserved name binderInfo
          (peelTypeAnnotations domain)
        apply Lean4Lean.AddInductive.bindResultWF
        intro recursive classified
        apply tailInduction
        · exact pushed.wf
        · exact pushed.reserved
        intro terminal finalIndex finalFields finalRecursive finalReader trace frame
        exact nextWF terminal finalIndex finalFields finalRecursive finalReader
          (.field noParameter classified trace) (pushed.trans frame)
    · rename_i terminal
      exact nextWF type index fields recursiveFields reader (.stop terminal) (.refl _ readerWF reserved)

theorem mkRecInfos.loopCtorArgs.scopedTrace {ResultType : Type}
    (stats : InductiveStats) (type : Expr) (next : Expr → Array Expr → Array Expr → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ terminal finalIndex fields recursiveFields finalReader,
      RecursorCtorFieldTrace stats type 0 #[] #[] reader
        terminal finalIndex fields recursiveFields finalReader →
      reader.RecursorScopeFrame finalReader → (next terminal fields recursiveFields finalReader).WF post) :
    (mkRecInfos.loopCtorArgs stats type next reader).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  exact mkRecInfos.loopCtorArgs.loop.scopedTrace stats type 0 #[] #[] reader.fuel.inductiveFuel
    next reader post readerWF reserved nextWF

theorem mkRecInfos.loopCtorArgs.getTrace (stats : InductiveStats) (type : Expr)
    (reader : Context) (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopCtorArgs stats type
      (fun terminal fields recursiveFields => do return (terminal, fields, recursiveFields, ← readThe Context))
      reader).WF fun result =>
      ∃ finalIndex, RecursorCtorFieldTrace stats type 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2 ∧
        reader.RecursorScopeFrame result.2.2.2 ∧
        RecursorFieldsDeclared result.2.2.2.lctx result.2.1 ∧
        result.2.2.1.toList.Sublist result.2.1.toList := by
  refine mkRecInfos.loopCtorArgs.scopedTrace stats type _ reader _ readerWF reserved ?_
  intro terminal finalIndex fields recursiveFields finalReader trace frame
  refine .pure ⟨finalIndex, trace, frame, trace.declared ?_, trace.recursiveSublist (.refl [])⟩
  intro field member
  simp at member

theorem mkRecInfos.loopCtorArgs.loop.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (fuel : Nat) (type : Expr) (index : Nat) (fields recursiveFields : Array Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType)
    (collect : Expr → Array Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ terminal finalFields finalRecursive finalReader,
      next terminal finalFields finalRecursive finalReader =
        (collect terminal finalFields finalRecursive finalReader).bind resume) :
    mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel reader =
      (mkRecInfos.loopCtorArgs.loop stats collect type index fields recursiveFields fuel reader).bind resume :=
  Lean4Lean.AddInductive.recCtor_loop_morphism stats fuel type index fields recursiveFields
    next collect resume reader nextEq

theorem mkRecInfos.loopCtorArgs.morphism {ResultType CaptureType : Type}
    (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType)
    (collect : Expr → Array Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ terminal fields recursiveFields finalReader,
      next terminal fields recursiveFields finalReader =
        (collect terminal fields recursiveFields finalReader).bind resume) :
    mkRecInfos.loopCtorArgs stats type next reader =
      (mkRecInfos.loopCtorArgs stats type collect reader).bind resume :=
  Lean4Lean.AddInductive.recCtor_morphism stats type next collect resume reader nextEq

end Lean4Lean.AddInductive
