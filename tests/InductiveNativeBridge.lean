import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveNativeAlignment
import Lean4Lean.Verify.InductiveNativeTrace
import Lean4Lean.Verify.InductiveRestorationMetadata
import Lean4Lean.Verify.InductiveNativeRestorationBridge
import Lean4Lean.Verify.InductiveFrontendCheckerBridge
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.InductiveNativeBridge

open Lean Lean4Lean Lean4Lean.NativeInductive
open Lean4Lean.AddInductive.declareConstructors

#check AddInductive.LocalRecursorRuleRhsScope.ruleResultSemanticsAndIota

example {env : VEnv} {universes : List Name} {stats : AddInductive.InductiveStats}
    {motives minors : Array Expr} {ctx : AddInductive.Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : AddInductive.GeneratedRecursorRuleResult env universes stats motives minors
      ctx constructor minor rule) :
    AddInductive.GeneratedRecursorRuleIotaKind env universes stats motives minors
      ctx constructor minor rule :=
  result.iotaKind

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules,
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.recursorGeneratedRuleIotaKind ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules,
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.recursorGeneratedRuleIotaBaseAndTargetResults ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleIotaKinds ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleIotaBaseAndTargetResults ruleResults

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result :=
  evidence.to_addInduct

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    AddInductEvidence .safe constants env decl evidence.constructorConstants
      evidence.constructorEnv :=
  evidence.to_addInductEvidence hconstants

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
    resultConstants = insertOrderedModel constants evidence.orderedEntries :=
  evidence.orderedModelMap

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : HeaderEntry} (hmem : entry ∈ evidence.headers) :
    ∃ type ∈ decl.types, entry.model = type.toVConstVal :=
  evidence.headerModelMembership hmem

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : ConstructorEntry} (hmem : entry ∈ evidence.constructors) :
    ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor :=
  evidence.constructorModelMembership hmem

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, match entry with
      | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
      | .constructor entry => ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
      | .recursor _ => True :=
  evidence.orderedModelMembership

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv ∧
        entry.ModelShape ∧
        (∃ semantic, match entry with
          | .header entry =>
            TrExprS env entry.info.levelParams [] entry.info.type semantic
          | .constructor entry =>
            TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
          | .recursor entry =>
            TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic) ∧
        match entry with
          | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
          | .constructor entry =>
            ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
          | .recursor _ => True :=
  evidence.orderedEntryReceipt

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, entry.ModelShape :=
  evidence.orderedModelShape

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length :=
  evidence.orderedModelShapeToConstantInfo

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
      entry.RuleSemantics result :=
  evidence.orderedRuleSemantics

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics result ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True :=
  evidence.orderedRuleResultsOf ruleResults

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS result entry.info.levelParams [] rule.rhs semantic ∧ True :=
  evidence.recursorRuleResult ruleResults

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

example {entry : RegistrationEntry} (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length :=
  hshape.toConstantInfo

example {entry : RegistrationEntry} {constants : ConstMap} (hshape : entry.ModelShape) :
    entry.insert constants = constants.insert entry.model.name entry.toConstantInfo :=
  entry.insert_modelShape hshape

example {constants : ConstMap} {entries : List RegistrationEntry}
    (hshape : ∀ entry ∈ entries, entry.ModelShape) :
    insertOrdered constants entries = insertOrderedModel constants entries :=
  insertOrdered_modelShape constants entries hshape

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors,
      TrConstVal .safe evidence.constructorEnv (.recInfo entry.info) entry.model :=
  evidence.recursor_translation_receipt

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS result entry.info.levelParams [] rule.rhs semantic :=
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

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
      result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
      ∃ name info, staged.find? name = some info :=
  evidence.entryModelReceipt hmem hshape

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) (hshape : ∀ entry ∈ evidence.entries, entry.ModelShape) :
    ∀ entry ∈ evidence.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info :=
  evidence.orderedModelReceipt hshape

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaBaseAndTargetResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaBaseAndTargetResults producer halign
    hconstants history hrecursors hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.registrationIotaBaseAndTargetResults producer halign ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info :=
  restored.fromRegistrationEvidence producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
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
        ∃ name info, staged.find? name = some info :=
  restored.registrationReceipt producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants) :
    result.constants = NativeInductive.insertOrdered constants restored.entries :=
  restored.registrationMap producer halign hconstants hresultConstants

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) :
    result.constants = resultConstants :=
  restored.registrationConstants producer halign hconstants

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (haligned : Aligned safety constants semanticEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = NativeInductive.insertOrdered original.constants restored.entries :=
  restored.registrationAlignment producer halign hconstants hresultConstants haligned

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q :=
  restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues

example {Result : RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) :=
  restored.toCheckerEnvInductive_and_registrationRuleResults producer halign hconstants history
    hrecursors hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationIotaKinds producer halign hconstants history
    hrecursors hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaTargetResults producer halign
    hconstants history hrecursors hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationIotaKinds_of_sourceTypehood producer halign
    hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaKinds_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_ruleResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  restored.registrationHistory producer halign hconstants history hrecursors

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (haligned : Aligned safety constants semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult :=
  restored.registrationAlignmentHistory producer halign hconstants history haligned hrecursors

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult :=
  restored.registrationAlignmentHistory_of_sourceTypehood producer halign hconstants history hsource

example {Result : RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ entry ∈ restored.entries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule :=
  restored.registrationRuleResults producer halign ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ restored.entries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  restored.registrationIotaKinds producer halign ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.ModelShape :=
  restored.registrationModelShapes producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.Metadata decl producer.constructors :=
  restored.registrationMetadata producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {entry : RecursorEntry} (hentry : .recursor entry ∈ restored.entries)
    {rule : RecursorRule} (hrule : rule ∈ entry.info.rules) :
    ∃ semantic, TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.registrationRecursorRuleTranslation producer halign hentry hrule

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q :=
  restored.toCheckerEnvInductive_of_sourceTypehood producer halign hconstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationIotaBaseAndTargetResults (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := h
  trivial


example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ (allowPrimitive : Bool),
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ (allowPrimitive : Bool),
      ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationIotaBaseAndTargetResults_of_restorationStages
    (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) :=
  metadata.toRestoredRecordEvidence coverage entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) :=
  metadata.sourceRecursorRulesAndRestoredRecordEvidence coverage entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context)
      (constructors : Kernel.Environment) (elimLevel : Level) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
      AddInductive.RecursorMinorIndexing preprocessing.types.toArray infos ∧
      AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) :=
  metadata.sourceRecursorRuleStagesAndRestoredRecordEvidence coverage entries records_eq

example {Result : RecursorEntry → RecursorRule → Prop}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) ∧
      (preprocessing.aux2nested.size ≠ 0 →
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
            result.find? recursor.name = some (.recInfo recursor) ∧
            entry.info.name = mkRecName types[index].name ∧
            recursor.rules.length = types[index].ctors.length ∧
            recursor.rules[ctorIndex]? = some rule ∧
            staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
            SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
            SourceConstructorFields nparams types[index] ctorIndex info ∧
            rule.nfields = info.numFields ∧
            rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
            nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            Result entry rule) :=
  metadata.sourceRecursorRuleResultsAndRestoredRecordEvidence coverage entries records_eq producer
    entry_eq hrecursor hentry ruleResult

example {Result : RecursorEntry → RecursorRule → Prop}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (producer : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) : True := by
  have h := metadata.sourceRecursorRuleStagesResultsAndRestoredRecordEvidence coverage entries
    records_eq producer entry_eq hrecursor hentry ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨allowPrimitive, metadata, haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_restorationStages
      hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∃ (allowPrimitive : Bool), Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_checkedPrimitive
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_checkedPrimitive
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∃ allowPrimitive,
      SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result ∧
      Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    SafeInductiveRestorationMetadata env lparams nparams types true fuel result ∧
      Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) :
    ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result)
      (staged : Kernel.Environment) (stats : AddInductive.InductiveStats)
      (root : AddInductive.Context) (constructors : Kernel.Environment)
      (elimLevel : Level) (infos : Array AddInductive.RecInfo) (source : AddInductive.Context),
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Aligned .safe resultConstants semanticResult ∧
        CheckerEnvInductive .safe result semanticResult Q) := by
  have hIota := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hlookups,
      hbranch, hfinal⟩ :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  exact ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hlookups, fun hnested => ⟨(hfinal hnested).1, (hfinal hnested).2.2.2.1⟩⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) :
    ∃ preprocessing staged stats root constructors elimLevel infos source,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) root constructors staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Aligned .safe resultConstants semanticResult ∧
        CheckerEnvInductive .safe result semanticResult Q) := by
  have hIota := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, _, _, _, _, _, hsources, _, _, hfinal⟩ :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  exact ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hsources, fun hnested =>
      ⟨(hfinal hnested).1, (hfinal hnested).2.2.2.1⟩⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q) :=
  metadata.toCheckerEnvInductive coverage entries records_eq producer entry_eq hconstants history
    hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q) :=
  metadata.toCheckerEnvInductive_of_sourceTypehood coverage entries records_eq producer entry_eq
    hconstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q := by
  exact metadata.toCheckerEnvInductive_of_frontendSourceTypehood producer hconstants
    hresultConstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaKinds
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaBaseAndTargetResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood_and_generatedRuleResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota := metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hSemanticIota :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResult
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult :=
  restored.registrationConstructive producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants.WF :=
  restored.registrationMapWF producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF) (hsemanticEnvWF : semanticEnv.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants.WF :=
  restored.registrationMapWF_of_sourceTypehood producer halign hconstants hconstantsWF
    hsemanticEnvWF hsource

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveAndMapWF producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) (hconstantsWF : constants.WF)
    (hsemanticEnvWF : semanticEnv.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveAndMapWF_of_sourceTypehood producer halign hconstants
    hconstantsWF hsemanticEnvWF hsource

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult :=
  restored.registrationConstructiveHistory producer halign hconstants history
    hconstantsWF hrecursors

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveHistoryAndMapWF producer halign hconstants history
    hconstantsWF hrecursors

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveHistoryAndMapWF_of_sourceTypehood producer halign hconstants
    history hconstantsWF hsource

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule,
      rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      Aligned .safe resultConstants semanticResult ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  exact restored.registrationConstructiveCheckerIotaBaseAndTargetResults producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.ModelShape ∧ entry.Metadata decl producer.constructors ∧
      match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.registrationStructuralReceipts producer halign

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

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) :
    result.find? info.name = some info ∧
      (original.find? info.name = some info ∨
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :=
  evidence.recordReceipt hwf hmem

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) (habsent : original.find? info.name = none) :
    result.find? info.name = some info ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newRecordReceipt hwf hmem habsent

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) :
    ∀ info ∈ records,
      result.find? info.name = some info ∧
        (original.find? info.name = some info ∨
          RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :=
  evidence.recordsReceipt hwf

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {original result : Kernel.Environment} {types : List InductiveType}
    (evidence : RestoredRegistrationEvidence preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2
      original (restoredEnvironmentRecords preprocessing staged types) result)
    (entries : List RegistrationEntry)
    (records_eq : restoredEnvironmentRecords preprocessing staged types =
      entries.map RegistrationEntry.toConstantInfo) :
    NativeInductive.RestoredRecordEvidence preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 original result
      (restoredEnvironmentRecords preprocessing staged types) :=
  NativeInductive.RestoredRegistrationEvidence.toRestoredRecordEvidence evidence entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q :=
  scope.toCheckerEnvInductive history producer hconstants hresultConstants hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_and_ruleResults history producer hconstants hresultConstants
    hrecursors hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_of_sourceTypehood_and_ruleResults history producer hconstants
    hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = mkRecName types[index].name)
    (hrecursorName : ∀ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = entry.info.name) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
      result.find? recursor.name = some (.recInfo recursor) ∧
      entry.info.name = mkRecName types[index].name ∧
      recursor.rules.length = types[index].ctors.length ∧
      recursor.rules[ctorIndex]? = some rule ∧
      staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧
      rule.nfields = info.numFields ∧
      rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.sourceRecursorRuleTranslation producer halign hlookups index hindex ctorIndex hctor
    hentry hname hrecursorName

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = mkRecName types[index].name)
    (hrecursorName : ∀ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = entry.info.name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
      result.find? recursor.name = some (.recInfo recursor) ∧
      entry.info.name = mkRecName types[index].name ∧
      recursor.rules.length = types[index].ctors.length ∧
      recursor.rules[ctorIndex]? = some rule ∧
      staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧
      rule.nfields = info.numFields ∧
      rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      True :=
  restored.sourceRecursorRuleResults producer halign hlookups index hindex ctorIndex hctor
    hentry hname hrecursorName ruleResult

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry,
        (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
      (hctor : ctorIndex < types[index].ctors.length),
      ∃ (entry : RecursorEntry) (recursor : RecursorVal) (rule : RecursorRule)
        (info : ConstructorVal) (semantic : VExpr),
        result.find? recursor.name = some (.recInfo recursor) ∧
        entry.info.name = mkRecName types[index].name ∧
        recursor.rules.length = types[index].ctors.length ∧
        recursor.rules[ctorIndex]? = some rule ∧
        staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
        SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
        SourceConstructorFields nparams types[index] ctorIndex info ∧
        rule.nfields = info.numFields ∧
        rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
        nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
        TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
        True :=
  restored.sourceRecursorRules producer halign hlookups hrecursor hentry ruleResult

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleResults producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleIotaKinds producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleIotaBaseAndTargetResults producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants.WF := by
  exact (restored.registrationConstructiveCheckerAndMapWFIotaBaseAndTargetResults producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults).2.2.2.2.2.2

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants.WF := by
  exact (restored.registrationConstructiveCheckerAndMapWF producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults).2.2.2.2.2.2

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleStructural producer halign hlookups
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleStructuralIotaBaseAndTargetResults producer halign
    hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) :
    CheckerEnvInductive .safe result semanticResult Q := by
  exact (restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults producer
    halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry).1

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaKinds
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule,
      rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.registrationSemanticAndStructuralIotaBaseAndTargetResults producer halign hconstants history hsource
    hvalues hlookups ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence
    coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {fuel : FuelConfig}
    (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
    (source : AddInductive.Context)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hrun : AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams true fuel) = .ok staged)
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (hrestored : preprocessing.aux2nested.size ≠ 0 →
      Nonempty { evidence : RestoredRecordEvidence preprocessing staged
          (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
          (restoredEnvironmentRecords preprocessing staged types) //
        evidence.entries = entries preprocessing staged })
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStructuralSemantics_of_stage
    preprocessing staged stats infos source hpre hrun hlookups entries hrestored producer
    entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndChecker
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationHistory history producer hconstants hresultConstants hrecursors

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationHistory_of_sourceTypehood history producer hconstants hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationAlignmentHistory_of_sourceTypehood history producer hconstants
    hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationHistory history producer hconstants hresultConstants hrecursors

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationHistory_of_sourceTypehood history producer hconstants hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationAlignmentHistory_of_sourceTypehood history producer hconstants
    hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  metadata.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result)
      (staged : Kernel.Environment) (stats : AddInductive.InductiveStats)
      (root : AddInductive.Context) (constructors : Kernel.Environment)
      (elimLevel : Level) (infos : Array AddInductive.RecInfo) (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries allowPrimitive preprocessing staged }) := by
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hlookups,
      hbranch, hrestored⟩ :=
    addDecl.sourceRecursorRuleStagesAndRestoredRecordEvidence_of_restorationStages
      hmap hresult coverage entries records_eq
  exact ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hprefix, hlookups, hrestored⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordIotaBaseAndTargetResultsEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have h :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) : True := by
  have h := addDecl.sourceRecursorRuleStagesAndRestoredRecordEvidence_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq
  have _metadata : SafeInductiveRestorationMetadata env lparams nparams types true fuel result := h.1
  have _stages := h.2
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordIotaBaseAndTargetResultsEvidence_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have hStages :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have h := addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have hStages :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have h := addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_of_restorationStages (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural_of_restorationStages
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hm
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndChecker_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hSemanticIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hSemanticIota
  have _ := hm
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorFieldStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, hpre, hrun, hprefix, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _ := hpre
  have _ := hrun
  have _ := hprefix
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorFieldStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _ := hpre
  have _ := hrun
  have _ := hprefix
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.constructorFieldStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.constructorFieldStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecordStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source, isK,
      hpre, hrun, hscope, hprefix, hframe, hlevels, hcounts, hindexing, hdistinct, hsource,
      hbranch, hnames, hrecords⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hlevels
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsource
  have _ := hbranch
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecordStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source, isK,
      hpre, hrun, hscope, hprefix, hframe, hlevels, hcounts, hindexing, hdistinct, hsource,
      hbranch, hnames, hrecords⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hlevels
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsource
  have _ := hbranch
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecords_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK,
      hpre, hrun, hlevels, hnames, hrecords⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecords_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK,
      hpre, hrun, hlevels, hnames, hrecords⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleAt_of_restorationStages hmap hresult index hindex ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK,
      before, after, sourceRule, finalRule, info, hpre, hrun, hlevels, hnames, hbefore, hafter,
      hsource, hfinal, hctorName, hctorEq, hfieldsEq, hrhs, hlookup, hmetadata, hfields, hcount, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _sourceRule : RecursorRule := sourceRule
  have _finalRule : RecursorRule := finalRule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hsource
  have _ := hfinal
  have _ := hctorName
  have _ := hctorEq
  have _ := hfieldsEq
  have _ := hrhs
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  have _ := hcount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleAt_of_checkedPrimitive hmap hcheck hresult index hindex ctorIndex hctor
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK,
      before, after, sourceRule, finalRule, info, hpre, hrun, hlevels, hnames, hbefore, hafter,
      hsource, hfinal, hctorName, hctorEq, hfieldsEq, hrhs, hlookup, hmetadata, hfields, hcount, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _sourceRule : RecursorRule := sourceRule
  have _finalRule : RecursorRule := finalRule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hsource
  have _ := hfinal
  have _ := hctorName
  have _ := hctorEq
  have _ := hfieldsEq
  have _ := hrhs
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  have _ := hcount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.originalRecursorFinalHeader_of_restorationStages hmap hresult index hindex
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK, before, after,
      hpre, hrun, hlevels, hnames, hbefore, hafter, hheader, hall, htype⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hheader
  have _ := hall
  have _ := htype
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.originalRecursorFinalHeader_of_checkedPrimitive hmap hcheck hresult index hindex
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK, before, after,
      hpre, hrun, hlevels, hnames, hbefore, hafter, hheader, hall, htype⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hheader
  have _ := hall
  have _ := htype
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRuleStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hnodup, hframe, hcounts, hindexing, hdistinct, hsources,
      hbranch, hnames, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hnodup
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hbranch
  have _ := hnames
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRuleStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hnodup, hframe, hcounts, hindexing, hdistinct, hsources,
      hbranch, hnames, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hnodup
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hbranch
  have _ := hnames
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleLookup_of_restorationStages hmap hresult index hindex ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, recursor, rule, info,
      hpre, hrun, hlookup, hcount, hrule, hname, hctorLookup, hmetadata, hfields, hfieldCount, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _recursor : RecursorVal := recursor
  have _rule : RecursorRule := rule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hcount
  have _ := hrule
  have _ := hname
  have _ := hctorLookup
  have _ := hmetadata
  have _ := hfields
  have _ := hfieldCount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleLookup_of_checkedPrimitive hmap hcheck hresult index hindex ctorIndex hctor
  obtain ⟨preprocessing, staged, recursor, rule, info,
      hpre, hrun, hlookup, hcount, hrule, hname, hctorLookup, hmetadata, hfields, hfieldCount, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _recursor : RecursorVal := recursor
  have _rule : RecursorRule := rule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hcount
  have _ := hrule
  have _ := hname
  have _ := hctorLookup
  have _ := hmetadata
  have _ := hfields
  have _ := hfieldCount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.sourceRecursorHeader_of_restorationStages hmap hresult index hindex
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK, recursor,
      hpre, hrun, hlevels, hlookup, hheader⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _recursor : RecursorVal := recursor
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hlookup
  have _ := hheader
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.sourceRecursorHeader_of_checkedPrimitive hmap hcheck hresult index hindex
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK, recursor,
      hpre, hrun, hlevels, hlookup, hheader⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _recursor : RecursorVal := recursor
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hlookup
  have _ := hheader
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorLookups_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorLookups_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorLookup_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hdirect, hnested⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hdirect
  have _ := hnested
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorLookup_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hdirect, hnested⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hdirect
  have _ := hnested
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorFieldsLookup_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hfields⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorFieldsLookup_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hfields⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorArity_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hfields, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hfields
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorArity_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hfields, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hfields
  have _ := htotal
  trivial

example {ctx : AddInductive.Context} {safety : DefinitionSafety} {venv : VEnv}
    {types : List InductiveType} {numParams numNested : Nat} {isUnsafe : Bool}
    (hchecker : CheckerEnv safety ctx.env venv)
    (shape : Environment.PrimitiveInductiveDecl ctx.lparams numParams types isUnsafe) :
    (AddInductive.checkInductiveTypes numParams types.toArray (fun stats => do
      AddInductive.withEnv
        (← AddInductive.declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
          AddInductive.checkConstructors types.toArray stats isUnsafe
          AddInductive.declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) = some ctorEnv ∧
        ctorEnv.WF ∧ CheckerEnv safety env' ctorEnv := by
  exact AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerWithModel
    ctx numParams types numNested isUnsafe hchecker
    ((Environment.checkPrimitiveInductive.eq_true_iff ctx.env ctx.lparams numParams types isUnsafe).mpr shape)

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (venv : VEnv) : True := by
  obtain ⟨decl, hkind, hheaders, hdeclWF, htranslation, hscope⟩ :=
    addDecl.checkedPrimitiveFrontendAndModel hmap hcheck hresult venv
  have _decl : VInductDecl := decl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hlookups, hchecker⟩ :=
    addDecl.checkedPrimitiveModelAndRecursorStages hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hlookups
  have _ := hchecker
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
      hlookups, hbranch, hfinal⟩ :=
    addDecl.checkedPrimitiveModelAndGeneratedRuleIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hfinal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hrestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredRuleIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hrestored
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (venv : VEnv) : True := by
  have _combined :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredRuleEvidence hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hrecursor hentry ruleResult
      hrecursors venv
  obtain ⟨modelDeclCombined, hkindCombined, hheadersCombined, hdeclWFCombined,
      htranslationCombined, hregistrationCombined,
      ⟨preprocessingCombined, stagedCombined, statsCombined, rootCombined,
        constructorsCombined, elimLevelCombined, infosCombined, sourceCombined,
        hpreCombined, hrunCombined, hscopeCombined, hprefixCombined, hlookupsCombined,
        hsemanticCombined⟩⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hresultConstants history hsource
      hvalues ruleResult hrecursor hentry hrecursors venv
  have _modelDeclCombined : VInductDecl := modelDeclCombined
  have _ := hkindCombined
  have _ := hheadersCombined
  have _ := hdeclWFCombined
  have _ := htranslationCombined
  have _ := hregistrationCombined
  have _preCombined : ElimNestedInductive.Result := preprocessingCombined
  have _stagedCombined : Kernel.Environment := stagedCombined
  have _statsCombined : AddInductive.InductiveStats := statsCombined
  have _rootCombined : AddInductive.Context := rootCombined
  have _constructorsCombined : Kernel.Environment := constructorsCombined
  have _elimLevelCombined : Level := elimLevelCombined
  have _infosCombined : Array AddInductive.RecInfo := infosCombined
  have _sourceCombined : AddInductive.Context := sourceCombined
  have _ := hpreCombined
  have _ := hrunCombined
  have _ := hscopeCombined
  have _ := hprefixCombined
  have _ := hlookupsCombined
  have _ := hsemanticCombined
  obtain ⟨modelDeclRestored, hkindRestored, hheadersRestored, hdeclWFRestored,
      htranslationRestored,
      ⟨preprocessingRestored, stagedRestored, statsRestored, rootRestored,
        constructorsRestored, elimLevelRestored, infosRestored, sourceRestored,
        hpreRestored, hrunRestored, hscopeRestored, hprefixRestored, hlookupsRestored,
        hsemanticRestored, hfinalRestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentSemantics hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult
      hrecursor hentry venv
  have _modelDeclRestored : VInductDecl := modelDeclRestored
  have _kindRestored := hkindRestored
  have _headersRestored := hheadersRestored
  have _declWFRestored := hdeclWFRestored
  have _translationRestored := htranslationRestored
  have _preRestored : ElimNestedInductive.Result := preprocessingRestored
  have _stagedRestored : Kernel.Environment := stagedRestored
  have _statsRestored : AddInductive.InductiveStats := statsRestored
  have _rootRestored : AddInductive.Context := rootRestored
  have _constructorsRestored : Kernel.Environment := constructorsRestored
  have _elimLevelRestored : Level := elimLevelRestored
  have _infosRestored : Array AddInductive.RecInfo := infosRestored
  have _sourceRestored : AddInductive.Context := sourceRestored
  have _ := hpreRestored
  have _ := hrunRestored
  have _ := hscopeRestored
  have _ := hprefixRestored
  have _ := hlookupsRestored
  have _ := hsemanticRestored
  have _ := hfinalRestored
  obtain ⟨modelDeclRestoredIota, hkindRestoredIota, hheadersRestoredIota,
      hdeclWFRestoredIota, htranslationRestoredIota,
      ⟨preprocessingRestoredIota, stagedRestoredIota, statsRestoredIota,
        rootRestoredIota, constructorsRestoredIota, elimLevelRestoredIota,
        infosRestoredIota, sourceRestoredIota, hpreRestoredIota,
        hrunRestoredIota, hscopeRestoredIota, hprefixRestoredIota,
        hlookupsRestoredIota, hsemanticRestoredIota, hfinalRestoredIota⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants
      hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDeclRestoredIota : VInductDecl := modelDeclRestoredIota
  have _ := hkindRestoredIota
  have _ := hheadersRestoredIota
  have _ := hdeclWFRestoredIota
  have _ := htranslationRestoredIota
  have _preRestoredIota : ElimNestedInductive.Result := preprocessingRestoredIota
  have _stagedRestoredIota : Kernel.Environment := stagedRestoredIota
  have _statsRestoredIota : AddInductive.InductiveStats := statsRestoredIota
  have _rootRestoredIota : AddInductive.Context := rootRestoredIota
  have _constructorsRestoredIota : Kernel.Environment := constructorsRestoredIota
  have _elimLevelRestoredIota : Level := elimLevelRestoredIota
  have _infosRestoredIota : Array AddInductive.RecInfo := infosRestoredIota
  have _sourceRestoredIota : AddInductive.Context := sourceRestoredIota
  have _ := hpreRestoredIota
  have _ := hrunRestoredIota
  have _ := hscopeRestoredIota
  have _ := hprefixRestoredIota
  have _ := hlookupsRestoredIota
  have _ := hsemanticRestoredIota
  have _ := hfinalRestoredIota
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
        hlookups, hbranch, hsemantic⟩⟩ :=
    addDecl.checkedPrimitiveModelAndAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hsemantic
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRegistration (venv := venv) hmap hcheck hresult
      producer hconstants hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, allowPrimitive,
      hscope, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveHistory_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := hscope
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, allowPrimitive,
      hscope, hregistration⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRegistration_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration,
      hhistory⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveHistory (venv := venv) hmap hcheck hresult
      producer hconstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, haligned, hmap', hhistory,
      hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndCheckerHistory (venv := venv) hmap hcheck hresult producer
      hconstants hresultConstants history hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration,
      haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood (venv := venv)
      hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hregistration⟩ :=
    addDecl.checkedPrimitiveRegistrationRealization hmap hcheck hresult producer hconstants
      hresultConstants hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationAndHistory hmap hcheck hresult producer
      hconstants hresultConstants history hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment hmap hcheck hresult
      producer hconstants hresultConstants history hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationAndHistory_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAlignmentAndRegistration_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory,
      haligned⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveAlignmentPackage_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hmetadata, hscope,
      hregistration, haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _metadata := hmetadata
  have _scope := hscope
  have _registration := hregistration
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨hscope, hregistration⟩ :=
    metadata.toFrontendScopeAndConstructiveRegistration producer hconstants hrecursors
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) : True := by
  obtain ⟨scope, hmodelResult, hmapResult, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment_of_sourceTypehood
      hmap hcheck hresult producer hconstants hresultConstants history hsource
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  obtain ⟨scope, hpreserves⟩ :=
    addDecl.checkedPrimitiveFrontendPreserves hmap hcheck hresult
  have _scope := scope
  have _preserves := hpreserves
  trivial

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (entry : RecursorEntry) (hentry : entry ∈ evidence.recursors)
    (rule : RecursorRule) (hrule : rule ∈ entry.info.rules) : True := by
  obtain ⟨constructor, minor, hiota⟩ :=
    evidence.recursorGeneratedRuleIotaKind ruleResults entry hentry rule hrule
  have targetResult := hiota.targetResult
  let targetResult' := targetResult
  obtain ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
      htranslated, htyped, hkind⟩ := targetResult
  have _constructor : Constructor := constructor
  have _minor : Expr := minor
  have _target : TypeChecker.MLCtx := target
  have _count : Nat := count
  have _arguments : List VExpr := arguments
  have _replacements : List Expr := replacements
  have _resultType : VExpr := resultType
  have _insertionLift : Lift := insertionLift
  have _rhsSemantic : VExpr := rhsSemantic
  have _translated := htranslated
  have _typed := htyped
  have _kind := hkind
  have _typedProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.hasType targetResult'
  have _sortProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.sortArity targetResult'
  have _translatedProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.translated targetResult'
  have _baseProjection := hiota.baseResult
  have _sharedProjection := hiota.baseAndTargetResults
  have _pairedBaseProjection := AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults.baseResult
    hiota.baseAndTargetResults
  have _pairedTargetProjection := AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults.targetResult
    hiota.baseAndTargetResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndCheckerHistoryIotaBaseAndTargetResults
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
    hsource hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} (producer : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ entry ∈ producer.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.orderedGeneratedRuleIotaBaseAndTargetResults_of_generatedRuleResults
    producer ruleResults
  trivial

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx?
      `Lean4Lean.Verify.InductiveNativeRestorationBridge
    | throwError "restored native record bridge module absent"
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "restored native record bridge introduces an axiom: {name}"
      if information.type.hasSorry then
        throwError "restored native record bridge has an admitted type: {name}"
      if let some value := information.value? (allowOpaque := true) then
        if value.hasSorry then
          throwError "restored native record bridge has an admitted value: {name}"
      for dependency in (← collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains dependency do
          throwError "unexpected restored native record bridge dependency {dependency} in {name}"
  logInfo "restored native record bridge: all owned types and proof values checked; only standard logic and the retained translation relation admission are allowed transitively"

end Lean4Lean.Tests.InductiveNativeBridge
