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
  unless count == 5 do throwError "rule body: expected five owned declarations, got {count}"
  logInfo m!"rule body: generated IH openings and typed minor application bridge audited ({count} declarations)"

run_meta
  audit

#print axioms IHModelStep.acceptsGeneratedValue
#print axioms IHModelStep.acceptsGeneratedRecursiveValue
#print axioms RecursorMinorOpening.applyArguments
#print axioms RecursorMinorOpening.applyNativeArguments
#print axioms RecursorMinorOpening.applyNativePeeledArguments

end InductiveRuleBodyTranslationTest
