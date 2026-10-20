import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveNativeTrace
import Lean4Lean.Verify.InductiveRestorationMetadata

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

end Lean4Lean.Tests.InductiveNativeBridge
