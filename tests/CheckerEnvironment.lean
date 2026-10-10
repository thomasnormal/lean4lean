import Lean4Lean.Verify.ConstructorHeaders
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

private def boolType : InductiveType := {
  name := ``Bool, type := .sort (.succ .zero),
  ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] }

private def natType (binderName : Name) (binderInfo : BinderInfo) : InductiveType := {
  name := ``Nat, type := .sort (.succ .zero),
  ctors := [⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩] }

private def primitiveStage (types : List InductiveType) : AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes 0 types.toArray fun stats => do
    AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0 types.toArray 0 false) do
      AddInductive.checkConstructors types.toArray stats false
      AddInductive.declareConstructors stats types.toArray false

private def primitiveContext (native : Kernel.Environment) : AddInductive.Context :=
  { context native false with allowPrimitive := true }

private theorem acceptedPrimitiveChecker {native : Kernel.Environment} {semantic : VEnv}
    {safety : DefinitionSafety} {types : List InductiveType}
    (hchecker : CheckerEnv safety native semantic)
    (shape : Lean4Lean.Environment.PrimitiveInductiveDecl [] 0 types false) :
    (primitiveStage types (primitiveContext native)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ semantic ≤ final ∧
        final.defeqs = semantic.defeqs := by
  have recognized := (Lean4Lean.Environment.checkPrimitiveInductive.eq_true_iff
    native [] 0 types false).mpr shape
  refine (AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorChecker
    (primitiveContext native) 0 types 0 false hchecker recognized).mono ?_
  rintro result ⟨decl, headers, constructors, _, addedHeaders, _, _, addedCtors, hfinal⟩
  exact ⟨constructors, hfinal,
    (VEnv.addInductHeaders.le addedHeaders).trans (VEnv.addConstructorHeaders.le addedCtors),
    (VEnv.addConstructorHeaders.defeqs_eq addedCtors).trans (VEnv.addInductHeaders.defeqs_eq addedHeaders)⟩

example : (primitiveStage [boolType] (primitiveContext emptyNative)).WF fun result =>
    ∃ final, CheckerEnv .safe result final ∧ VEnv.empty ≤ final ∧
      final.defeqs = VEnv.empty.defeqs :=
  acceptedPrimitiveChecker (CheckerEnv.empty _) .bool

example (binderName : Name) (binderInfo : BinderInfo) (safety : DefinitionSafety) :
    (primitiveStage [natType binderName binderInfo] (primitiveContext seededNative)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ seededSemantic ≤ final ∧
        final.defeqs = seededSemantic.defeqs :=
  acceptedPrimitiveChecker (seededTrEnv safety).checkerEnv (.nat binderName binderInfo)

private theorem seededAliasLookup :
    seededNative.constants.find? nativeAlias.name = some (.defnInfo nativeAlias) := by
  change (SMap.insert ({} : ConstMap) nativeAlias.name (.defnInfo nativeAlias)).find?
    nativeAlias.name = some (.defnInfo nativeAlias)
  rw [SMap.WF.empty.find?_insert]
  simp

private theorem rejectsNewDefinitionFrame : ¬NativeValueFrame emptyNative seededNative := by
  intro frame
  have hlookup := frame.values seededAliasLookup
    (show (ConstantInfo.defnInfo nativeAlias).value? = some nativeAlias.value from rfl)
  change ({} : ConstMap).find? nativeAlias.name = some (.defnInfo nativeAlias) at hlookup
  simp [SMap.find?] at hlookup

private theorem rejectsRemovedDefinitionFrame : ¬NativeValueFrame seededNative emptyNative := by
  intro frame
  have hlookup := frame.lookups seededAliasLookup
  change ({} : ConstMap).find? nativeAlias.name = some (.defnInfo nativeAlias) at hlookup
  simp [SMap.find?] at hlookup

private theorem retainedAliasValue {types : List InductiveType} (safety : DefinitionSafety)
    (shape : Lean4Lean.Environment.PrimitiveInductiveDecl [] 0 types false) :
    (primitiveStage types (primitiveContext seededNative)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧
        TrExpr final [] [] nativeAlias.value (.const nativeAlias.name []) := by
  intro result accepted
  obtain ⟨final, hchecker, _, _⟩ :=
    acceptedPrimitiveChecker (seededTrEnv safety).checkerEnv shape result accepted
  have hframe := AddInductive.checkInductiveTypes.preservesHeaderConstructorValues
    (primitiveContext seededNative) 0 types.toArray 0 false
    (seededTrEnv safety).map_wf result accepted
  have hlookup : result.find? nativeAlias.name = some (.defnInfo nativeAlias) := by
    change result.constants.find?' nativeAlias.name = some (.defnInfo nativeAlias)
    rw [hframe.map_wf.find?'_eq_find?]
    exact hframe.lookups seededAliasLookup
  exact ⟨final, hchecker, hchecker.of_value hlookup DefinitionSafety.le_safe rfl rfl⟩

private def familyCtor : Constructor := ⟨`StagedFamily.mk, .const family.name []⟩
private def familyCtorHeader : VConstVal := {
  name := familyCtor.name, uvars := 0, type := .const family.name [] }
private def familyStats : AddInductive.InductiveStats := {
  levels := [], resultLevel := .succ .zero, nindices := #[0],
  indConsts := #[.const family.name []], params := #[], isNotZero := true }

private theorem ordinaryConstructorChecker :
    (AddInductive.declareConstructors familyStats #[{ family with ctors := [familyCtor] }] false
      (context stagedNative false)).WF fun result =>
        ∃ final, stagedSemantic.addConstructorHeaders [familyCtorHeader] = some final ∧
          CheckerEnv .safe result final := by
  apply AddInductive.declareConstructors.refinesChecker (context stagedNative false) familyStats
    #[{ family with ctors := [familyCtor] }] false (vtypes := [{ header with ctors := [familyCtorHeader] }])
    (stagedChecker .safe) DefinitionSafety.le_safe
  · exact .cons (.cons ⟨rfl, rfl, TrExprS.const (ci := header.toVConstant) rfl rfl rfl⟩ .nil) .nil
  · intro ctor hmem
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hmem
    subst ctor
    exact ⟨_, stagedFamilyTyping⟩

private def ordinaryMutual : Array InductiveType := #[
  { name := `Left, type := .sort (.succ .zero), ctors := [⟨`Left.unit, .const `Left []⟩,
      ⟨`Left.swap, .forallE `right (.const `Right []) (.const `Left []) .default⟩] },
  { name := `Right, type := .sort (.succ .zero), ctors := [
      ⟨`Right.wrap, .forallE `left (.const `Left []) (.const `Right []) .default⟩] }]

private def checkedConstructorStage (types : Array InductiveType) (isUnsafe : Bool) :
    AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes 0 types fun stats => do
    AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0 types 0 isUnsafe) do
      AddInductive.checkConstructors types stats isUnsafe
      AddInductive.declareConstructors stats types isUnsafe

example (isUnsafe : Bool) :
    (checkedConstructorStage ordinaryMutual isUnsafe (context seededNative isUnsafe)).WF
      (NativeValueFrame seededNative) :=
  AddInductive.checkInductiveTypes.preservesHeaderConstructorValues
    (context seededNative isUnsafe) 0 ordinaryMutual 0 isUnsafe (seededTrEnv .safe).map_wf

example (safety : DefinitionSafety) :
    (primitiveStage [boolType] (primitiveContext seededNative)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧
        TrExpr final [] [] nativeAlias.value (.const nativeAlias.name []) :=
  retainedAliasValue safety .bool

run_meta
  let simple := [``propext, ``Quot.sound]
  let logical := simple ++ [``Classical.choice, ``sorryAx]
  let native := simple ++ [``Classical.choice, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.findAux_isSome]
  let semantic := native ++ [``sorryAx]
  let primitive := semantic ++ [``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel,
    ``Lean.Syntax.structEq_eq]
  for theoremName in [``NativeValueFrame.refl, ``NativeValueFrame.trans, ``NativeValueFrame.foldlM] do
    audit theoremName simple
  audit ``CheckerEnv.of_valueFrame logical
  for theoremName in [``NativeValueFrame.addConst,
      ``AddInductive.declareInductiveTypes.preservesValues,
      ``AddInductive.declareConstructors.preservesValues,
      ``AddInductive.checkInductiveTypes.preservesHeaderConstructorValues] do
    audit theoremName native
  for theoremName in [``AddInductive.declareConstructors.refinesChecker, ``ordinaryConstructorChecker] do
    audit theoremName semantic
  for theoremName in [
      ``AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorChecker,
      ``acceptedPrimitiveChecker, ``retainedAliasValue] do
    audit theoremName primitive
  for theoremName in [``seededAliasLookup, ``rejectsNewDefinitionFrame, ``rejectsRemovedDefinitionFrame] do
    audit theoremName [``propext, ``Quot.sound, ``Classical.choice,
      ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert]
  let mut count := 0
  for (seeded, native) in [(false, emptyNative), (true, seededNative)] do
    let types := [boolType] ++ ([Name.anonymous, `value, `nested.binder].flatMap fun binderName =>
      [BinderInfo.default, .implicit, .strictImplicit, .instImplicit].map (natType binderName))
    for type in types do
      let .ok result := primitiveStage [type] (primitiveContext native)
        | throwError "primitive staging failed"
      for ctor in type.ctors do
        let some (.ctorInfo info) := result.find? ctor.name | throwError "missing primitive constructor"
        unless info.type == ctor.type && info.induct == type.name && !info.isUnsafe do
          throwError "wrong primitive constructor signature"
        let .ok inferred := M.run result .safe {} [] {} (inferType (.const ctor.name []))
          | throwError "cannot infer a staged constructor type"
        unless inferred == ctor.type do throwError "wrong inferred constructor type"
      if seeded then
        let some (.defnInfo info) := result.find? nativeAlias.name | throwError "lost seed definition"
        unless info == nativeAlias do throwError "changed seed definition"
        let .ok reduced := M.run result .safe {} [] {} (whnf (.const nativeAlias.name []))
          | throwError "lost seeded delta reduction"
        unless reduced == .sort .zero do throwError "wrong seeded delta reduction"
      if (primitiveStage [type] (primitiveContext result)).isOk then
        throwError "accepted repeated primitive staging"
      if (primitiveStage [type] { primitiveContext native with allowPrimitive := false }).isOk then
        throwError "accepted unauthorized primitive staging"
      count := count + 1
  logInfo m!"{count} primitive constructor/value-preservation controls with duplicate/authorization rejections"
  let mut ordinaryCount := 0
  for (seeded, native) in [(false, emptyNative), (true, seededNative)] do
    for isUnsafe in [false, true] do
      for types in [#[], #[{ family with ctors := [familyCtor] }], ordinaryMutual] do
        let .ok result := checkedConstructorStage types isUnsafe (context native isUnsafe)
          | throwError "ordinary constructor staging failed"
        for type in types do
          for ctor in type.ctors do
            let .ok inferred := M.run result (if isUnsafe then .unsafe else .safe) {} [] {}
              (inferType (.const ctor.name [])) | throwError "cannot infer a staged ordinary constructor"
            unless inferred == ctor.type do throwError "wrong inferred ordinary constructor type"
            if isUnsafe && (M.run result .safe {} [] {} (checkType (.const ctor.name []))).isOk then
              throwError "safe view admitted an unsafe constructor"
        if seeded then
          let .ok reduced := M.run result (if isUnsafe then .unsafe else .safe) {} [] {}
            (whnf (.const nativeAlias.name [])) | throwError "ordinary staging lost seeded delta reduction"
          unless reduced == .sort .zero do throwError "ordinary staging changed seeded delta reduction"
        if !types.isEmpty && (checkedConstructorStage types isUnsafe (context result isUnsafe)).isOk then
          throwError "ordinary staging admitted duplicate names"
        ordinaryCount := ordinaryCount + 1
  logInfo m!"{ordinaryCount} ordinary empty/single/mutual constructor staging controls"

end CheckerEnvironmentTest
