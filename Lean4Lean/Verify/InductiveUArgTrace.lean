import Lean4Lean.Verify.RecursorInfoIndices
import Lean4Lean.Verify.InductiveCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.readWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindResultWF Lean4Lean.AddInductive.withIndexDeclWF
  from Lean4Lean.Verify.RecursorInfoIndices
open private Lean4Lean.AddInductive.bind_morphism Lean4Lean.AddInductive.read_morphism
  Lean4Lean.AddInductive.withLocalDecl_morphism from Lean4Lean.Verify.InductiveCPS

def recursorUArgStats : InductiveStats :=
  { levels := [], resultLevel := .zero, indConsts := #[], params := #[], isNotZero := false }

abbrev RecursorUArgTrace (source : Expr) (arguments : Array Expr) (reader : Context)
    (terminal : Expr) (finalArguments : Array Expr) (finalReader : Context) : Prop :=
  RecursorIndexTrace recursorUArgStats source 0 arguments reader terminal 0 finalArguments finalReader

inductive RecursorUArgOpeningTrace (argument : Expr) (reader : Context) :
    Expr → Array Expr → Context → Prop where
  | mk {inferred normalized terminal : Expr} {arguments : Array Expr} {finalReader : Context}
      (inference : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
      (initialNormalization : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
      (argumentsTrace : RecursorUArgTrace normalized #[] reader terminal arguments finalReader) :
      RecursorUArgOpeningTrace argument reader terminal arguments finalReader

theorem RecursorUArgOpeningTrace.scope {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  cases opening with
  | mk _ _ trace => exact trace.scope readerWF reserved

theorem RecursorUArgOpeningTrace.declared {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader) :
    RecursorFieldsDeclared finalReader.lctx arguments := by
  cases opening with
  | mk _ _ trace =>
    apply trace.declared
    intro field member
    simp at member

theorem mkRecInfos.loopUArgs.loop.scopedTrace {ResultType : Type}
    (source : Expr) (arguments : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ terminal finalArguments finalReader,
      RecursorUArgTrace source arguments reader terminal finalArguments finalReader →
      reader.RecursorScopeFrame finalReader → (next terminal finalArguments finalReader).WF post) :
    (mkRecInfos.loopUArgs.loop next source arguments fuel reader).WF post := by
  induction fuel generalizing source arguments reader with
  | zero => exact Except.WF.throw
  | succ fuel tailInduction =>
    rw [mkRecInfos.loopUArgs.loop.eq_def]
    split
    · rename_i name domain body binderInfo
      apply Lean4Lean.AddInductive.withIndexDeclWF
      have pushed := Context.RecursorScopeFrame.push reader readerWF reserved name binderInfo
        (peelTypeAnnotations domain)
      apply Lean4Lean.AddInductive.bindResultWF
      intro normalized normalization
      apply tailInduction
      · exact pushed.wf
      · exact pushed.reserved
      intro terminal finalArguments finalReader trace frame
      exact nextWF terminal finalArguments finalReader
        (.index (by simp [recursorUArgStats]) normalization trace)
        (pushed.trans frame)
    · rename_i terminal
      exact nextWF source arguments reader (.stop terminal) (.refl _ readerWF reserved)

theorem mkRecInfos.loopUArgs.scopedTrace {ResultType : Type}
    (argument : Expr) (next : Expr → Array Expr → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nextWF : ∀ terminal arguments finalReader,
      RecursorUArgOpeningTrace argument reader terminal arguments finalReader →
      reader.RecursorScopeFrame finalReader → (next terminal arguments finalReader).WF post) :
    (mkRecInfos.loopUArgs argument next reader).WF post := by
  unfold mkRecInfos.loopUArgs
  apply Lean4Lean.AddInductive.bindResultWF
  intro inferred inference
  apply Lean4Lean.AddInductive.bindResultWF
  intro normalized normalization
  apply Lean4Lean.AddInductive.readWF
  refine mkRecInfos.loopUArgs.loop.scopedTrace normalized #[] reader.fuel.inductiveFuel
    next reader post readerWF reserved ?_
  intro terminal arguments finalReader trace frame
  exact nextWF terminal arguments finalReader (.mk inference normalization trace) frame

theorem mkRecInfos.loopUArgs.getTrace (argument : Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopUArgs argument
      (fun terminal arguments => do return (terminal, arguments, ← readThe Context)) reader).WF fun result =>
      RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2 ∧
        reader.RecursorScopeFrame result.2.2 ∧ RecursorFieldsDeclared result.2.2.lctx result.2.1 := by
  refine mkRecInfos.loopUArgs.scopedTrace argument _ reader _ readerWF reserved ?_
  intro terminal arguments finalReader opening frame
  exact .pure ⟨opening, frame, opening.declared⟩

theorem mkRecInfos.loopUArgs.loop.morphism {ResultType CaptureType : Type}
    (fuel : Nat) (source : Expr) (arguments : Array Expr)
    (next : Expr → Array Expr → M ResultType) (collect : Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ terminal finalArguments finalReader,
      next terminal finalArguments finalReader = (collect terminal finalArguments finalReader).bind resume) :
    mkRecInfos.loopUArgs.loop next source arguments fuel reader =
      (mkRecInfos.loopUArgs.loop collect source arguments fuel reader).bind resume := by
  induction fuel generalizing source arguments reader with
  | zero => rfl
  | succ fuel tailInduction =>
    rw [mkRecInfos.loopUArgs.loop.eq_def, mkRecInfos.loopUArgs.loop.eq_def]
    split
    · apply Lean4Lean.AddInductive.withLocalDecl_morphism
      intro argument current
      apply Lean4Lean.AddInductive.bind_morphism
      intro normalized
      exact tailInduction normalized _ current
    · exact nextEq source arguments reader

theorem mkRecInfos.loopUArgs.morphism {ResultType CaptureType : Type}
    (argument : Expr)
    (next : Expr → Array Expr → M ResultType) (collect : Expr → Array Expr → M CaptureType)
    (resume : CaptureType → Except Exception ResultType) (reader : Context)
    (nextEq : ∀ terminal arguments finalReader,
      next terminal arguments finalReader = (collect terminal arguments finalReader).bind resume) :
    mkRecInfos.loopUArgs argument next reader = (mkRecInfos.loopUArgs argument collect reader).bind resume := by
  unfold mkRecInfos.loopUArgs
  apply Lean4Lean.AddInductive.bind_morphism
  intro inferred
  apply Lean4Lean.AddInductive.bind_morphism
  intro normalized
  apply Lean4Lean.AddInductive.read_morphism
  exact mkRecInfos.loopUArgs.loop.morphism reader.fuel.inductiveFuel normalized #[]
    next collect resume reader nextEq

end Lean4Lean.AddInductive
