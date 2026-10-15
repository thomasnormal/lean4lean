import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveRestorationMetadata

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace NativeInductive

structure RestoredRecordEvidence (preprocessing : ElimNestedInductive.Result)
    (staged : Environment) (allIndNames : List Name) (recNameMap : NameMap Name)
    (original result : Environment) (records : List ConstantInfo) where
  entries : List RegistrationEntry
  records_eq : records = entries.map RegistrationEntry.toConstantInfo
  typed : ∀ entry ∈ entries,
    RestoredInductiveRecord preprocessing staged allIndNames recNameMap
      entry.toConstantInfo
  receipt : RestoredRegistrationReceipt original records result

 theorem RestoredRecordEvidence.map
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = NativeInductive.insertInfos original.constants
      (evidence.entries.map RegistrationEntry.toConstantInfo).reverse := by
  calc
    result.constants = NativeInductive.insertInfos original.constants records.reverse := evidence.receipt.map
    _ = NativeInductive.insertInfos original.constants
        (evidence.entries.map RegistrationEntry.toConstantInfo).reverse := by
      rw [congrArg List.reverse evidence.records_eq]

 theorem RestoredRecordEvidence.installed
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    RestoredRecordsInstalled records result :=
  evidence.receipt.installed

end NativeInductive

end Lean4Lean
