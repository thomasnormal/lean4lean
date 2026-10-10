import Lean4Lean.Verify.InductiveHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.TypeChecker
open private Lean.Kernel.Environment.add from Lean.Environment

namespace CheckerEnvironmentTest

private def nativeAlias : DefinitionVal := {
  name := `SortAlias, levelParams := [], type := .sort (.succ .zero),
  value := .sort .zero, hints := .abbrev, safety := .safe }

private def semanticAlias : VDefVal := {
  name := nativeAlias.name, uvars := 0, type := .sort (.succ .zero), value := .sort .zero }

private def emptyNative := Kernel.Environment.empty `CheckerEnvironmentTest
private def seededNative := emptyNative.add (.defnInfo nativeAlias)
private def aliasHeaderEnv :=
  (VEnv.empty.addConst semanticAlias.name semanticAlias.toVConstant).getD VEnv.empty
private def seededSemantic := aliasHeaderEnv.addDefEq semanticAlias.toDefEq

private theorem seededTrEnv (safety : DefinitionSafety) :
    TrEnv safety seededNative seededSemantic := by
  change TrEnv' safety (emptyNative.constants.insert nativeAlias.name (.defnInfo nativeAlias))
    false seededSemantic
  apply TrEnv'.defn (ci := nativeAlias) (ci' := semanticAlias) (env := VEnv.empty)
    (env' := aliasHeaderEnv)
  · exact ⟨⟨⟨DefinitionSafety.le_safe, rfl, .sort rfl⟩, rfl⟩, .sort rfl⟩
  · change ({} : ConstMap).find? nativeAlias.name = none
    simp [SMap.find?]
  · exact .sort trivial
  · rfl
  · exact .empty

private def family : InductiveType := {
  name := `StagedFamily, type := .sort (.succ .zero), ctors := [] }
private def header : VInductiveType := {
  name := family.name, uvars := 0, type := .sort (.succ .zero), ctors := [] }
private def familyInfo : InductiveVal := {
  name := family.name, levelParams := [], type := family.type, numParams := 0,
  numIndices := 0, all := [family.name], ctors := [], numNested := 0,
  isRec := false, isUnsafe := false, isReflexive := false }
private def stagedNative := seededNative.add (.inductInfo familyInfo)
private def stagedSemantic :=
  (seededSemantic.addConst header.name header.toVConstant).getD seededSemantic

private theorem stagedChecker (safety : DefinitionSafety) :
    CheckerEnv safety stagedNative stagedSemantic := by
  apply (seededTrEnv safety).checkerEnv.addConst (ci := .inductInfo familyInfo)
    (ci' := header.toVConstant)
  · change (SMap.insert ({} : ConstMap) nativeAlias.name (.defnInfo nativeAlias)).find?
      familyInfo.name = none
    rw [SMap.WF.empty.find?_insert]
    simp [nativeAlias, familyInfo, family, SMap.find?]
  · exact ⟨DefinitionSafety.le_safe, rfl, .sort rfl⟩
  · rfl
  · exact ⟨_, .sort trivial⟩
  · rfl

private theorem stagedAliasValue (safety : DefinitionSafety) :
    TrExpr stagedSemantic [] [] nativeAlias.value (.const nativeAlias.name []) := by
  apply (stagedChecker safety).of_value (ci := .defnInfo nativeAlias)
    (name := nativeAlias.name) ?_ DefinitionSafety.le_safe rfl rfl
  change stagedNative.constants.find?' nativeAlias.name = some (.defnInfo nativeAlias)
  rw [(stagedChecker safety).map_wf.find?'_eq_find?]
  change (seededNative.constants.insert familyInfo.name (.inductInfo familyInfo)).find?
    nativeAlias.name = some (.defnInfo nativeAlias)
  rw [(seededTrEnv safety).map_wf.find?_insert]
  have hne : (familyInfo.name == nativeAlias.name) = false := by decide
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  change (SMap.insert ({} : ConstMap) nativeAlias.name (.defnInfo nativeAlias)).find?
    nativeAlias.name = some (.defnInfo nativeAlias)
  rw [SMap.WF.empty.find?_insert]
  simp

private def context (native : Kernel.Environment) (isUnsafe : Bool) : AddInductive.Context := {
  env := native, lparams := [], safety := if isUnsafe then .unsafe else .safe,
  allowPrimitive := false }

private def checkedStage (types : Array InductiveType) (isUnsafe : Bool) :
    AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes 0 types fun stats =>
    AddInductive.declareInductiveTypes stats 0 types 0 isUnsafe

example (isUnsafe : Bool) :
    (checkedStage #[family] isUnsafe (context seededNative isUnsafe)).WF fun result =>
      ∃ final, seededSemantic.addInductHeaders [header] = some final ∧
        CheckerEnv (if isUnsafe then .unsafe else .safe) result final := by
  apply AddInductive.checkInductiveTypes.refinesHeadersChecker
    (context seededNative isUnsafe) 0 #[family] 0 isUnsafe
    (seededTrEnv _).checkerEnv DefinitionSafety.le_rfl
  · exact .cons ⟨rfl, rfl, .sort rfl⟩ .nil
  · intro candidate hmem
    simp only [List.mem_singleton] at hmem
    subst candidate
    exact ⟨_, .sort trivial⟩

example (safety : DefinitionSafety) :
    (checkedStage #[] false { context seededNative false with safety }).WF fun result =>
      ∃ final, seededSemantic.addInductHeaders [] = some final ∧
        CheckerEnv safety result final :=
  AddInductive.checkInductiveTypes.refinesHeadersChecker _ 0 #[] 0 false
    (seededTrEnv safety).checkerEnv DefinitionSafety.le_safe .nil (by simp)

example (isUnsafe : Bool) :
    (checkedStage #[family, { family with name := `SecondFamily }] isUnsafe
      (context seededNative isUnsafe)).WF fun result =>
      ∃ final, seededSemantic.addInductHeaders
        [header, { header with name := `SecondFamily }] = some final ∧
          CheckerEnv (if isUnsafe then .unsafe else .safe) result final := by
  apply AddInductive.checkInductiveTypes.refinesHeadersChecker
    (context seededNative isUnsafe) 0 _ 0 isUnsafe
    (seededTrEnv _).checkerEnv DefinitionSafety.le_rfl
  · exact .cons ⟨rfl, rfl, .sort rfl⟩ (.cons ⟨rfl, rfl, .sort rfl⟩ .nil)
  · intro candidate hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact ⟨_, .sort trivial⟩

private theorem stagedFamilyTyping :
    stagedSemantic.HasType 0 [] (.const family.name []) header.type :=
  .const (ci := header.toVConstant) rfl (by simp) rfl

example : TrExprS stagedSemantic [] [] (.const family.name []) (.const family.name []) :=
  .const (ci := header.toVConstant) rfl rfl rfl

private def audit (theoremName : Name) (expected : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  unless axioms.size == expected.length && axioms.all expected.contains do
    throwError "{theoremName}: unexpected dependencies: {repr axioms}"
  logInfo m!"{theoremName}: axioms = {repr axioms}"

run_meta
  let logical := [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  let maps := logical ++ [``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.findAux_isSome]
  for theoremName in [``TrEnv.checkerEnv, ``CheckerEnv.map_wf, ``CheckerEnv.find?,
      ``CheckerEnv.find?_uniq, ``CheckerEnv.find?_iff, ``CheckerEnv.of_value,
      ``CheckerEnv.addConst, ``AddInductive.declareInductiveTypes.refinesChecker,
      ``AddInductive.checkInductiveTypes.refinesHeadersChecker,
      ``stagedChecker, ``stagedAliasValue] do
    audit theoremName maps
  for theoremName in [``CheckerEnv.empty, ``seededTrEnv] do
    audit theoremName logical
  audit ``stagedFamilyTyping [``propext, ``Quot.sound]
  let mut count := 0
  for (seeded, native) in [(false, emptyNative), (true, seededNative)] do
    for isUnsafe in [false, true] do
      for types in [#[], #[family], #[family, { family with name := `SecondFamily }]] do
        let .ok result := checkedStage types isUnsafe (context native isUnsafe)
          | throwError "header staging rejected a valid fixture"
        for type in types do
          let some (.inductInfo info) := result.find? type.name | throwError "missing staged header"
          unless info.type == type.type && info.isUnsafe == isUnsafe do
            throwError "wrong staged header"
          let .ok checked := M.run result (if isUnsafe then .unsafe else .safe) {} [] {}
            (checkType (.const type.name []))
            | throwError "cannot check staged family"
          unless checked == .sort (.succ .zero) do
            throwError "cannot check staged family: {repr checked}"
          if isUnsafe && (M.run result .safe {} [] {} (checkType (.const type.name []))).isOk then
            throwError "safe checker admitted an unsafe staged family"
        if seeded then
          let .ok reduced := M.run result (if isUnsafe then .unsafe else .safe) {} [] {}
            (whnf (.const nativeAlias.name []))
            | throwError "seeded delta reduction failed"
          unless reduced == .sort .zero do throwError "lost seeded delta reduction: {repr reduced}"
        if !types.isEmpty && (checkedStage types isUnsafe (context result isUnsafe)).isOk then
          throwError "accepted repeated header staging"
        count := count + 1
  logInfo m!"{count} empty/single/mutual, safe/unsafe and delta-preservation staging controls"

end CheckerEnvironmentTest
