import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveRestorationMetadata

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace NativeInductive

theorem RestoredInductiveRecord.sourceLookup
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {info : ConstantInfo}
    (record : RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :
    ∃ name source, staged.find? name = some source := by
  cases record with
  | header name info lookup => exact ⟨name, .inductInfo info, lookup⟩
  | constructor name info lookup => exact ⟨name, .ctorInfo info, lookup⟩
  | recursor name info lookup => exact ⟨name, .recInfo info, lookup⟩

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

theorem RestoredRecordEvidence.sourceLookup
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : RegistrationEntry} (hmem : entry ∈ evidence.entries) :
    ∃ name info, staged.find? name = some info := by
  exact RestoredInductiveRecord.sourceLookup (evidence.typed entry hmem)

theorem RestoredRecordEvidence.entryModelReceipt
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : RegistrationEntry} (hmem : entry ∈ evidence.entries)
    (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
      result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
      ∃ name info, staged.find? name = some info := by
  exact ⟨hshape.toConstantInfo.1, hshape.toConstantInfo.2,
    evidence.entryInstalled hmem, evidence.typed entry hmem, evidence.sourceLookup hmem⟩

theorem RestoredRecordEvidence.orderedModelReceipt
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (evidence : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) (hshape : ∀ entry ∈ evidence.entries, entry.ModelShape) :
    ∀ entry ∈ evidence.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info := by
  intro entry hmem
  exact evidence.entryModelReceipt hmem (hshape entry hmem)

theorem RestoredRecordEvidence.fromRegistrationEvidence
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info := by
  apply restored.orderedModelReceipt
  intro entry hmem
  apply producer.orderedModelShape entry
  rw [← halign]
  exact hmem

theorem RestoredRecordEvidence.registrationReceipt
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.Semantic semanticEnv producer.headerEnv producer.constructorEnv ∧
        entry.Metadata decl producer.constructors ∧
        entry.RuleSemantics semanticResult ∧
        entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap
          entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info := by
  intro entry hmem
  have hproducer : entry ∈ producer.orderedEntries := by
    rw [← halign]
    exact hmem
  have hsemantic := producer.orderedSemantic entry hproducer
  have hmetadata := producer.orderedMetadata entry hproducer
  have hrules := producer.orderedRuleSemantics entry hproducer
  have hshape := producer.orderedModelShape entry hproducer
  rcases restored.entryModelReceipt hmem hshape with
    ⟨hname, huvars, hinstalled, htyped, hsource⟩
  exact ⟨hsemantic, hmetadata, hrules, hname, huvars, hinstalled, htyped, hsource⟩

theorem RestoredRecordEvidence.registrationMap
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants) :
    result.constants = insertOrdered constants restored.entries := by
  calc
    result.constants = resultConstants := hresultConstants
    _ = insertOrdered constants producer.orderedEntries := producer.orderedMap
    _ = insertOrdered constants restored.entries :=
      congrArg (insertOrdered constants) halign.symm
    _ = insertOrdered original.constants restored.entries :=
      congrArg (fun c => insertOrdered c restored.entries) hconstants.symm
    _ = insertOrdered constants restored.entries :=
      congrArg (fun c => insertOrdered c restored.entries) hconstants

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
