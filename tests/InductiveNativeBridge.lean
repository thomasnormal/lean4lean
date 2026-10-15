import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveNativeTrace
import Lean4Lean.Verify.InductiveRestorationMetadata
import Lean4Lean.Verify.InductiveNativeRestorationBridge

namespace Lean4Lean.Tests.InductiveNativeBridge

open Lean Lean4Lean Lean4Lean.NativeInductive

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result :=
  evidence.to_addInduct

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertRecursors (insertConstructors (insertHeaders constants evidence.headers)
      evidence.constructors) evidence.recursors :=
  evidence.native_map

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    FreshOrdered constants evidence.orderedEntries :=
  evidence.orderedFresh

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrdered constants evidence.orderedEntries :=
  evidence.orderedMap

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, entry.ModelShape :=
  evidence.orderedModelShape

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry =>
        TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry =>
        TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic :=
  evidence.orderedTypeTranslation

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertInfos constants
      ((evidence.headers.map HeaderEntry.toConstantInfo ++
        evidence.constructors.map ConstructorEntry.toConstantInfo ++
        evidence.recursors.map RecursorEntry.toConstantInfo).reverse) :=
  evidence.native_map_records

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv :=
  evidence.orderedSemantic

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Metadata decl evidence.constructors :=
  evidence.orderedMetadata

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics evidence.constructorEnv :=
  evidence.orderedRuleSemantics

example {entry : RegistrationEntry} {env headerEnv constructorEnv : VEnv}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    entry.ModelShape :=
  hsemantic.modelShape

example {entry : RegistrationEntry} {env headerEnv constructorEnv : VEnv}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry => TrExprS headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry => TrExprS constructorEnv entry.info.levelParams [] entry.info.type semantic :=
  hsemantic.typeTranslation

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors,
      TrConstVal .safe evidence.constructorEnv (.recInfo entry.info) entry.model :=
  evidence.recursor_translation_receipt

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] rule.rhs semantic :=
  evidence.recursorRuleTranslation

private def receiptRecursor : RecursorVal := {
  name := `Receipt.rec
  levelParams := []
  type := .sort .zero
  all := []
  numParams := 0
  numIndices := 0
  numMotives := 0
  numMinors := 0
  rules := []
  k := false
  isUnsafe := false }

example (env : VEnv) :
    TrConstVal .safe env (.recInfo receiptRecursor)
      { name := `Receipt.rec, uvars := 0, type := .sort .zero } := by
  refine ⟨⟨DefinitionSafety.le_rfl, rfl, .sort rfl⟩, rfl⟩

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) :
    ∃ infos, result.constants = NativeInductive.insertInfos original.constants infos :=
  NativeInductive.FreshRegistrationTrace.constants_eq trace

example (env : Kernel.Environment) (hwf : env.constants.WF) :
    env.constants = NativeInductive.insertInfos env.constants [].reverse :=
  (RestoredRegistrationReceipt.empty env hwf).map

example {original current result : Kernel.Environment} {first second : List ConstantInfo}
    (left : RestoredRegistrationReceipt original first current)
    (right : RestoredRegistrationReceipt current second result) :
    result.constants = NativeInductive.insertInfos original.constants (first ++ second).reverse :=
  (left.trans right).map

example {original result : Kernel.Environment} {headers constructors recursors : List ConstantInfo}
    (receipt : RestoredRegistrationReceipt original (headers ++ constructors ++ recursors) result) :
    result.constants =
      NativeInductive.insertInfos
        (NativeInductive.insertInfos
          (NativeInductive.insertInfos original.constants headers.reverse) constructors.reverse)
        recursors.reverse :=
  receipt.mapPhases

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {types : List InductiveType} {info : ConstantInfo}
    (hmem : info ∈ restoredEnvironmentRecords preprocessing staged types) :
    RestoredInductiveRecord preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 info :=
  restoredEnvironmentRecords.typedPartition preprocessing staged types hmem

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hsources : RestorationSources staged types) (env : Kernel.Environment)
    (hwf : env.constants.WF) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      RestoredRegistrationEvidence preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2 env (restoredEnvironmentRecords preprocessing staged types) result.2 :=
  restoreInductiveEnvironment.evidence preprocessing staged types lparams allowPrimitive fuel hsources env hwf

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = NativeInductive.insertInfos original.constants
      (evidence.entries.map NativeInductive.RegistrationEntry.toConstantInfo).reverse :=
  evidence.map

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = NativeInductive.insertOrdered original.constants evidence.entries :=
  evidence.orderedMap

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) :
    result.find? entry.toConstantInfo.name = some entry.toConstantInfo :=
  evidence.entryInstalled hmem

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {info : ConstantInfo} (hmem : info ∈ records) :
    ∃ entry ∈ evidence.entries, info = entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.typedRecord hmem

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) :
    ∃ name info, staged.find? name = some info :=
  evidence.sourceLookup hmem

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (hlookup : result.find? name = some info) :
    original.find? name = some info ∨
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.lookup hwf name info hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (habsent : original.find? name = none)
    (hlookup : result.find? name = some info) :
    RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newLookup hwf name info habsent hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) :
    original.find? info.name = some info ∨
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.recordClassification hwf hmem

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) (habsent : original.find? info.name = none) :
    RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newRecordClassification hwf hmem habsent

end Lean4Lean.Tests.InductiveNativeBridge
