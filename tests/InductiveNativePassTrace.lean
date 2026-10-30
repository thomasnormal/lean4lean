import Lean4Lean.Verify.InductiveNativePassTrace
import Lean.Util.CollectAxioms

namespace InductiveNativePassTraceTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open ElimNestedInductive (ContextReserved)

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
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
            result.1.size = parentInfos.size :=
  mkRecInfos.getNativePassTraces stats types elimLevel reader readerWF reserved

run_meta
  let theoremName := ``mkRecInfos.getNativePassTraces
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "native pass trace extractor is primitive"
  let some proof := information.value? (allowOpaque := true) |
    throwError "native pass trace extractor proof missing"
  if proof.hasSorry then
    throwError "native pass trace extractor has an admission"
  logInfo "native mkRecInfos parent/minor traces are theorem-backed"

end InductiveNativePassTraceTest
