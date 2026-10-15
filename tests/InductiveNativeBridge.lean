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

end Lean4Lean.Tests.InductiveNativeBridge
