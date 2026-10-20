import Lean4Lean.Verify.InductiveRuleBodyTranslation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRuleBodyTranslationTest

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "rule body: dependency manifest changed for {name}: {repr actual}"

private def audit : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let structural := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  exactAxioms ``IHModelStep.acceptsGeneratedValue structural
  exactAxioms ``IHModelStep.acceptsGeneratedRecursiveValue structural
  exactAxioms ``RecursorMinorOpening.applyArguments structural
  exactAxioms ``RecursorMinorOpening.applyNativeArguments structural
  exactAxioms ``RecursorMinorOpening.applyNativePeeledArguments structural
  exactAxioms ``RecursorMinorOpening.applyNativePeeledFieldAndIHArguments structural
  exactAxioms ``NativeTelescopeArguments.weakFV structural
  let fieldStructural := structural ++ [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  exactAxioms ``CtorFieldModelEndpoint.nativeFieldArguments fieldStructural
  exactAxioms ``IHModelStep.generatedNativeArgument structural
  let canonicalStructural := fieldStructural ++ [``Expr.eqv_eq, ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq]
  exactAxioms ``IHModelStep.generatedCanonicalRecursiveValue canonicalStructural
  exactAxioms ``GeneratedIHNativeSuffix.ofNativeForallTail (logical ++ [``sorryAx])
  exactAxioms ``IHModelStep.generatedNativeArgumentAtTarget structural
  exactAxioms ``GeneratedIHNativeSuffix.nativeArguments structural
  exactAxioms ``GeneratedIHNativeSuffix.nativeArgumentsAtTarget structural
  exactAxioms ``GeneratedIHNativeSuffix.applyNativePeeledFieldAndIHArguments structural
  exactAxioms ``MinorModelStep.nativeFieldArguments fieldStructural
  exactAxioms ``MinorModelStep.peeledDomainSource fieldStructural
  exactAxioms ``GeneratedIHNativeSuffix.ofCanonicalForallTail canonicalStructural
  exactAxioms ``MinorModelStep.generatedNativeIHArguments canonicalStructural
  exactAxioms ``MinorModelStep.generatedNativeFieldAndIHArguments canonicalStructural
  exactAxioms ``MinorModelStep.consumeGeneratedFieldAndIHArguments structural
  exactAxioms ``MinorModelStep.generatedConstructorRhsBody canonicalStructural
  exactAxioms ``MinorModelStep.abstractConstructorRhsBody fieldStructural
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhs fieldStructural
  exactAxioms ``RecursorRuleRhsReceipt.applyIota (logical ++ [``sorryAx])
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhsIota fieldStructural
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRuleBodyTranslation
    | throwError "rule body: module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "rule body: owned axiom {name}"
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then throwError "rule body: direct admission {name}"
      count := count + 1
  unless count == 97 do throwError "rule body: expected ninety-seven owned declarations, got {count}"
  logInfo m!"rule body: generated IH openings, canonical recursive suffix, field/IH receipts, peeled minor source and constructor RHS body/lambda/rule/iota/result bridges audited ({count} declarations)"

run_meta
  audit

#print axioms IHModelStep.acceptsGeneratedValue
#print axioms IHModelStep.acceptsGeneratedRecursiveValue
#print axioms RecursorMinorOpening.applyArguments
#print axioms RecursorMinorOpening.applyNativeArguments
#print axioms RecursorMinorOpening.applyNativePeeledArguments
#print axioms RecursorMinorOpening.applyNativePeeledFieldAndIHArguments
#print axioms NativeTelescopeArguments.weakFV
#print axioms CtorFieldModelEndpoint.nativeFieldArguments
#print axioms IHModelStep.generatedNativeArgument
#print axioms IHModelStep.generatedCanonicalRecursiveValue
#print axioms GeneratedIHNativeSuffix.ofNativeForallTail
#print axioms IHModelStep.generatedNativeArgumentAtTarget
#print axioms GeneratedIHNativeSuffix.nativeArguments
#print axioms GeneratedIHNativeSuffix.nativeArgumentsAtTarget
#print axioms GeneratedIHNativeSuffix.applyNativePeeledFieldAndIHArguments
#print axioms MinorModelStep.nativeFieldArguments
#print axioms GeneratedIHNativeSuffix.ofCanonicalForallTail
#print axioms MinorModelStep.generatedNativeIHArguments
#print axioms MinorModelStep.generatedNativeFieldAndIHArguments
#print axioms MinorModelStep.consumeGeneratedFieldAndIHArguments
#print axioms MinorModelStep.generatedConstructorRhsBody
#print axioms MinorModelStep.abstractConstructorRhsBody
#print axioms MinorModelStep.abstractConstructorRuleRhs
#print axioms RecursorRuleRhsReceipt.applyIota
#print axioms MinorModelStep.abstractConstructorRuleRhsIota

end InductiveRuleBodyTranslationTest
