import Lean4Lean.Verify.InductiveParentPassTrace
import Lean4Lean.Verify.InductiveMinorPassTrace
import Lean4Lean.Verify.InductiveCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem mkRecInfos.getNativePassTraces
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (reader : Context) (readerWF : reader.lctx.WF)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∃ parentInfos parentReader,
        ∃ _parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader
          parentInfos parentReader,
          ∃ _minorTrace : RecursorMinorPassTrace stats types 0 parentInfos parentReader
            result.1 result.2,
            reader.RecursorScopeFrame parentReader ∧
            parentInfos.size = types.size ∧
            parentReader.RecursorScopeFrame result.2 ∧
            result.1.size = parentInfos.size := by
  unfold mkRecInfos
  rw [mkRecInfos.loopInd1.morphism stats types elimLevel 0 #[]
      (fun parentInfos => mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)))
      (fun parentInfos => do return (parentInfos, ← readThe Context))
      (fun result => mkRecInfos.loopInd2 stats types 0 result.1
        (fun finalInfos => do return (finalInfos, ← readThe Context)) result.2)
      reader (fun _ _ => rfl)]
  refine (mkRecInfos.loopInd1.getParentPassTrace stats types elimLevel 0 #[] reader
    readerWF reserved).bind ?_
  rintro ⟨parentInfos, parentReader⟩ ⟨parentTrace, parentFrame, parentSize⟩
  refine (mkRecInfos.loopInd2.getMinorPassTrace stats types 0 parentInfos parentReader
    parentFrame.wf parentFrame.reserved).mono ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨minorTrace, minorFrame, minorSize⟩
  exact ⟨parentInfos, parentReader, parentTrace, minorTrace, parentFrame, by simpa using parentSize,
    minorFrame, minorSize⟩

end Lean4Lean.AddInductive
