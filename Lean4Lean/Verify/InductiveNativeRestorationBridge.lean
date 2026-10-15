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

 theorem RestoredRecordEvidence.orderedMap
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = insertOrdered original.constants evidence.entries := by
  calc
    result.constants = insertInfos original.constants
        (evidence.entries.map RegistrationEntry.toConstantInfo).reverse := evidence.map
    _ = insertOrdered original.constants evidence.entries := by
      rw [insertOrdered_toConstantInfos]

 theorem RestoredRecordEvidence.entryInstalled
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : RegistrationEntry} (hmem : entry ∈ evidence.entries) :
    result.find? entry.toConstantInfo.name = some entry.toConstantInfo := by
  apply evidence.receipt.installed entry.toConstantInfo
  rw [evidence.records_eq]
  exact List.mem_map.mpr ⟨entry, hmem, rfl⟩

 theorem RestoredRecordEvidence.typedRecord
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {info : ConstantInfo} (hmem : info ∈ records) :
    ∃ entry ∈ evidence.entries, info = entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info := by
  rw [evidence.records_eq] at hmem
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
  exact ⟨entry, hentry, rfl, evidence.typed entry hentry⟩

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
