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
  exactAxioms ``LocalRecursorRuleRhsScope.receipts logical
  exactAxioms ``LocalRecursorRuleRhsScope.atReceipt logical
  exactAxioms ``LocalRecursorRuleRhsScope.impReceipts logical
  exactAxioms ``LocalRecursorRuleRhsScope.impScopedReceipts logical
  exactAxioms ``LocalRecursorRuleRhsScope.ruleSemantics [``propext, ``sorryAx, ``Classical.choice, ``Quot.sound]
  exactAxioms ``RecursorRuleRhsScope.receipts logical
  exactAxioms ``RecursorRuleRhsScope.atReceipt logical
  exactAxioms ``RecursorRuleRhsScope.impReceipts logical
  exactAxioms ``RecursorRuleRhsScope.impScopedReceipts logical
  exactAxioms ``RecursorRuleRhsScope.impGeneratedConstructorRuleRhs
    [``propext, ``sorryAx, ``Classical.choice, ``Quot.sound]
  exactAxioms ``LocalRecursorRuleRhsScope.impGeneratedConstructorRuleRhs
    [``propext, ``sorryAx, ``Classical.choice, ``Quot.sound]
  exactAxioms ``ElimNestedInductive.TypedParameterArguments.resultKind structural
  exactAxioms ``VEnv.SortArity.weak' [``propext, ``Quot.sound]
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
  exactAxioms ``RecursorRuleRhsReceipt.applyIotaKind structural
  exactAxioms ``RecursorRuleRhsReceipt.applyIotaWeakFV structural
  exactAxioms ``RecursorRuleRhsReceipt.applyIotaWeakFVKind structural
  exactAxioms ``RecursorRuleRhsReceipt.applyIotaKindWeakFVKind structural
  exactAxioms ``RecursorRuleRhsCountReceipt.applyIotaKindWeakFVKind structural
  exactAxioms ``RecursorRuleRhsFVarReceipt.applyIotaKindWeakFVKind structural
  exactAxioms ``RecursorRuleRhsScopeReceipt.applyIotaKindWeakFVKind structural
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhsIota fieldStructural
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhsIotaKind fieldStructural
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhsIotaWeakFV fieldStructural
  exactAxioms ``MinorModelStep.abstractConstructorRuleRhsIotaWeakFVKind fieldStructural
  exactAxioms ``MinorModelStep.abstractScopedConstructorRuleRhsIotaWeakFVKind fieldStructural
  exactAxioms ``MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKind canonicalStructural
  exactAxioms ``MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBody canonicalStructural
  exactAxioms ``MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSource canonicalStructural
  exactAxioms ``MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied canonicalStructural
  exactAxioms ``MinorModelStep.generatedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied canonicalStructural
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
  unless count == 127 do throwError "rule body: expected one hundred twenty-seven owned declarations, got {count}"
  logInfo m!"indexed local generated constructor-RHS result consumer with explicit body/source/applied witnesses, all-rule and local dual-receipt adapters, indexed local rule-semantics receipt/result consumer, all-rule scoped-and-ordinary receipt consumer adapter, indexed local scoped-and-ordinary receipt consumer adapter, indexed local scoped-to-ordinary receipt consumer adapter, indexed local scoped-to-ordinary receipt lookup, all-rule scoped receipt consumer adapter, indexed scoped-to-ordinary receipt lookup, all-rule scoped-to-ordinary receipt projection, direct scoped/fvar/count result transport, generated scoped constructor RHS weak-FV/kind producer-consumer with retained body, source-RHS, and applied-semantic witnesses, ordinary recursor-rule result consumer, composed base/lifted iota/kind transport, scoped-to-final rule receipts, scoped constructor RHS weak-FV/kind consumer, generated IH openings, canonical recursive suffix, field/IH receipts, peeled minor source and constructor RHS body/lambda/rule/iota/result/kind/weak-FV/consumer bridges audited ({count} declarations)"

run_meta
  audit

#print axioms IHModelStep.acceptsGeneratedValue
#print axioms LocalRecursorRuleRhsScope.receipts
#print axioms LocalRecursorRuleRhsScope.atReceipt
#print axioms LocalRecursorRuleRhsScope.impReceipts
#print axioms LocalRecursorRuleRhsScope.impScopedReceipts
#print axioms LocalRecursorRuleRhsScope.ruleSemantics
#print axioms RecursorRuleRhsScope.receipts
#print axioms RecursorRuleRhsScope.atReceipt
#print axioms RecursorRuleRhsScope.impReceipts
#print axioms RecursorRuleRhsScope.impScopedReceipts
#print axioms RecursorRuleRhsScope.impGeneratedConstructorRuleRhs
#print axioms LocalRecursorRuleRhsScope.impGeneratedConstructorRuleRhs
#print axioms IHModelStep.acceptsGeneratedRecursiveValue
#print axioms RecursorMinorOpening.applyArguments
#print axioms RecursorMinorOpening.applyNativeArguments
#print axioms RecursorMinorOpening.applyNativePeeledArguments
#print axioms RecursorMinorOpening.applyNativePeeledFieldAndIHArguments
#print axioms NativeTelescopeArguments.weakFV
#print axioms ElimNestedInductive.TypedParameterArguments.resultKind
#print axioms VEnv.SortArity.weak'
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
#print axioms RecursorRuleRhsReceipt.applyIotaKind
#print axioms RecursorRuleRhsReceipt.applyIotaWeakFV
#print axioms RecursorRuleRhsReceipt.applyIotaWeakFVKind
#print axioms RecursorRuleRhsReceipt.applyIotaKindWeakFVKind
#print axioms RecursorRuleRhsCountReceipt.applyIotaKindWeakFVKind
#print axioms RecursorRuleRhsFVarReceipt.applyIotaKindWeakFVKind
#print axioms RecursorRuleRhsScopeReceipt.applyIotaKindWeakFVKind
#print axioms MinorModelStep.abstractConstructorRuleRhsIota
#print axioms MinorModelStep.abstractConstructorRuleRhsIotaKind
#print axioms MinorModelStep.abstractConstructorRuleRhsIotaWeakFV
#print axioms MinorModelStep.abstractConstructorRuleRhsIotaWeakFVKind
#print axioms MinorModelStep.abstractScopedConstructorRuleRhsIotaWeakFVKind
#print axioms MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKind
#print axioms MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBody
#print axioms MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSource
#print axioms MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied
#print axioms MinorModelStep.generatedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied

end InductiveRuleBodyTranslationTest
