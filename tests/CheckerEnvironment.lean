import Lean4Lean.Verify.RestrictedContext
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

private theorem emptyPrimitiveSafety : NativePrimitiveSafety emptyNative :=
  NativePrimitiveSafety.of_native SMap.WF.empty
    (VEnvs.WF.empty `CheckerEnvironmentTest).safePrimitives

private theorem seededPrimitiveSafety : NativePrimitiveSafety seededNative := by
  apply emptyPrimitiveSafety.addConst (ci := .defnInfo nativeAlias)
  · change ({} : ConstMap).find? nativeAlias.name = none
    simp [SMap.find?]
  · intro _
    exact ⟨rfl, rfl⟩

private theorem emptyPrimitives : VEnv.empty.HasPrimitives :=
  (VEnvs.WF.empty `CheckerEnvironmentTest).hasPrimitives (safety := .safe)

private theorem seededPrimitives : seededSemantic.HasPrimitives := by
  have aliasPrimitives : aliasHeaderEnv.HasPrimitives :=
    emptyPrimitives.addConst (show VEnv.empty.addConst semanticAlias.name
      semanticAlias.toVConstant = some aliasHeaderEnv from rfl) (by decide)
  exact aliasPrimitives.addDefEq

private theorem acceptedPrimitiveInterfaces {native : Kernel.Environment} {semantic : VEnv}
    {safety : DefinitionSafety} {types : List InductiveType}
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (shape : Lean4Lean.Environment.PrimitiveInductiveDecl [] 0 types false) :
    (primitiveStage types (primitiveContext native)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result := by
  have recognized := (Lean4Lean.Environment.checkPrimitiveInductive.eq_true_iff
    native [] 0 types false).mpr shape
  refine (AddInductive.checkInductiveTypes.refinesPrimitiveInterfaces
    (primitiveContext native) 0 types 0 false hchecker hp hsafe recognized).mono ?_
  rintro result ⟨decl, headers, constructors, _, _, _, _, _, hfinal, hprimitives, hsafe'⟩
  exact ⟨constructors, hfinal, hprimitives, hsafe'⟩

example : (primitiveStage [boolType] (primitiveContext emptyNative)).WF fun result =>
    ∃ final, CheckerEnv .safe result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result :=
  acceptedPrimitiveInterfaces (CheckerEnv.empty _) emptyPrimitives emptyPrimitiveSafety .bool

example (binderName : Name) (binderInfo : BinderInfo) (safety : DefinitionSafety) :
    (primitiveStage [natType binderName binderInfo] (primitiveContext seededNative)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result :=
  acceptedPrimitiveInterfaces (seededTrEnv safety).checkerEnv seededPrimitives seededPrimitiveSafety
    (.nat binderName binderInfo)

private def pairStage (natFirst : Bool) : AddInductive.M Kernel.Environment := do
  let first := if natFirst then natType `value .default else boolType
  let second := if natFirst then boolType else natType `value .default
  AddInductive.withEnv (← primitiveStage [first]) (primitiveStage [second])

private theorem withEnv_bind {ctx : AddInductive.Context}
    {action next : AddInductive.M Kernel.Environment} {intermediate post : Kernel.Environment → Prop}
    (hfirst : (action ctx).WF intermediate)
    (hnext : ∀ middle, intermediate middle → (next { ctx with env := middle }).WF post) :
    ((do AddInductive.withEnv (← action) next) ctx).WF post :=
  hfirst.bind hnext

private theorem pairInterfaces (natFirst : Bool) {native : Kernel.Environment} {semantic : VEnv}
    {safety : DefinitionSafety} (hchecker : CheckerEnv safety native semantic)
    (hp : semantic.HasPrimitives) (hsafe : NativePrimitiveSafety native) :
    (pairStage natFirst (primitiveContext native)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result := by
  cases natFirst
  · refine withEnv_bind (action := primitiveStage [boolType])
      (next := primitiveStage [natType `value .default])
      (acceptedPrimitiveInterfaces hchecker hp hsafe .bool) ?_
    rintro middle ⟨semantic, hchecker, hp, hsafe⟩
    exact acceptedPrimitiveInterfaces hchecker hp hsafe (.nat `value .default)
  · refine withEnv_bind (action := primitiveStage [natType `value .default])
      (next := primitiveStage [boolType])
      (acceptedPrimitiveInterfaces hchecker hp hsafe (.nat `value .default)) ?_
    rintro middle ⟨semantic, hchecker, hp, hsafe⟩
    exact acceptedPrimitiveInterfaces hchecker hp hsafe .bool

example (natFirst : Bool) (safety : DefinitionSafety) :
    (pairStage natFirst (primitiveContext seededNative)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result :=
  pairInterfaces natFirst (seededTrEnv safety).checkerEnv seededPrimitives seededPrimitiveSafety

private def boolHeaderOnly := (VEnv.empty.addInductHeaders boolInductDecl.types).getD VEnv.empty
private def natHeaderOnly := (VEnv.empty.addInductHeaders natInductDecl.types).getD VEnv.empty

private theorem boolHeaderOnly_notPrimitives : ¬boolHeaderOnly.HasPrimitiveLiterals := by
  intro hliterals
  obtain ⟨⟨constant, hlookup⟩, _⟩ := hliterals.bool ⟨_, rfl⟩
  change none = some constant at hlookup
  contradiction

private theorem natHeaderOnly_notPrimitives : ¬natHeaderOnly.HasPrimitiveLiterals := by
  intro hliterals
  obtain ⟨⟨constant, hlookup⟩, _⟩ := hliterals.nat ⟨_, rfl⟩
  change none = some constant at hlookup
  contradiction

example : ¬boolHeaderOnly.HasPrimitives := fun hp => boolHeaderOnly_notPrimitives hp.literals
example : ¬natHeaderOnly.HasPrimitives := fun hp => natHeaderOnly_notPrimitives hp.literals

example (isUnsafe : Bool) :
    (checkedConstructorStage ordinaryMutual isUnsafe (context seededNative isUnsafe)).WF NativePrimitiveSafety :=
  AddInductive.checkInductiveTypes.preservesHeaderConstructorPrimitiveSafety
    (context seededNative isUnsafe) 0 ordinaryMutual 0 isUnsafe seededPrimitiveSafety (.inl rfl)

run_meta
  let simple := [``propext, ``Quot.sound]
  let lookup := simple ++ [``Classical.choice, ``Lean.PersistentHashMap.findAux_isSome]
  let native := lookup ++ [``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let primitive := native ++ [``sorryAx, ``Lean.Expr.eqv_eq,
    ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  audit ``VEnv.HasPrimitives.literals [``propext]
  for theoremName in [``VEnv.addInductHeaders.constants_eq,
      ``VEnv.addConstructorHeaders.constants_eq, ``VInductDecl.stagedConstants_eq,
      ``VEnv.HasPrimitives.mono_of_literals, ``boolInductDecl.hasPrimitives, ``natInductDecl.hasPrimitives,
      ``boolHeaderOnly_notPrimitives, ``natHeaderOnly_notPrimitives] do
    audit theoremName simple
  for theoremName in [``NativePrimitiveSafety.of_native, ``NativePrimitiveSafety.find?] do
    audit theoremName lookup
  for theoremName in [``NativePrimitiveSafety.addConst,
      ``AddInductive.declareInductiveTypes.preservesPrimitiveSafety,
      ``AddInductive.declareConstructors.preservesPrimitiveSafety,
      ``AddInductive.checkInductiveTypes.preservesHeaderConstructorPrimitiveSafety] do
    audit theoremName native
  audit ``Lean4Lean.Environment.PrimitiveInductiveDecl.safeMonomorphic []
  audit ``withEnv_bind [``propext, ``Quot.sound, ``Classical.choice]
  for theoremName in [
      ``AddInductive.checkInductiveTypes.refinesPrimitiveInterfaces,
      ``acceptedPrimitiveInterfaces, ``pairInterfaces] do
    audit theoremName primitive
  for theoremName in [``emptyPrimitiveSafety, ``emptyPrimitives, ``seededPrimitives] do
    audit theoremName (lookup ++ [``sorryAx])
  audit ``seededPrimitiveSafety (native ++ [``sorryAx])
  let mut pairs := 0
  for native in [emptyNative, seededNative] do
    for natFirst in [false, true] do
      let .ok result := pairStage natFirst (primitiveContext native) | throwError "primitive pair staging failed"
      for name in [``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ] do
        let some info := result.find? name | throwError "missing primitive interface member"
        unless info.safety == .safe && info.levelParams.isEmpty do
          throwError "primitive interface member is unsafe or polymorphic"
      for value in [0, 1, 37] do
        let .ok inferred := M.run result .safe {} [] {} (checkType (.lit (.natVal value)))
          | throwError "cannot type check a Nat literal after primitive staging"
        unless inferred == .const ``Nat [] do throwError "wrong Nat literal type"
      let .ok succType := M.run result .safe {} [] {} (checkType (.const ``Nat.succ []))
        | throwError "cannot type check the retained Nat constructor"
      unless succType == (natType `value .default).ctors[1]!.type do throwError "wrong retained Nat interface"
      let .ok falseType := M.run result .safe {} [] {} (checkType (.const ``Bool.false []))
        | throwError "cannot type check the retained Bool constructor"
      unless falseType == .const ``Bool [] do throwError "wrong retained Bool interface"
      pairs := pairs + 1
  logInfo m!"{pairs} Bool/Nat order-composition and primitive-literal interface controls"

private theorem acceptedOrdinaryInterfaces {native : Kernel.Environment} {semantic : VEnv}
    {safety : DefinitionSafety} (isUnsafe : Bool)
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe
      (context native isUnsafe)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧
        NativePrimitiveSafety result ∧ NativePrimitiveFrame native result := by
  refine (AddInductive.checkInductiveTypes.refinesOrdinaryInterfaces
    (context native isUnsafe) 0 #[{ family with ctors := [familyCtor] }] 0 isUnsafe
    (headers := [header]) (vtypes := [{ header with ctors := [familyCtorHeader] }])
    hchecker hp hsafe rfl hsafety (.cons ⟨rfl, rfl, .sort rfl⟩ .nil) ?_ ?_ ?_).mono ?_
  · intro candidate hmem
    simp only [List.mem_singleton] at hmem
    subst candidate
    exact ⟨_, .sort trivial⟩
  · intro headerEnv hadd
    have hlookup := VEnv.addInductHeaders.constants hadd (header := header) (by simp)
    exact .cons (.cons ⟨rfl, rfl, TrExprS.const (ci := header.toVConstant) hlookup rfl rfl⟩ .nil) .nil
  · intro headerEnv hadd candidate hmem
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hmem
    subst candidate
    have hlookup := VEnv.addInductHeaders.constants hadd (header := header) (by simp)
    exact ⟨_, .const (ci := header.toVConstant) hlookup (by simp) rfl⟩
  · rintro result ⟨headerEnv, final, _, _, hfinal, hp', hsafe', hframe⟩
    exact ⟨final, hfinal, hp', hsafe', hframe⟩

example (isUnsafe : Bool) :
    (checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe
      (context seededNative isUnsafe)).WF fun result =>
      ∃ final, CheckerEnv (if isUnsafe then .unsafe else .safe) result final ∧
        final.HasPrimitives ∧ NativePrimitiveSafety result ∧ NativePrimitiveFrame seededNative result :=
  acceptedOrdinaryInterfaces isUnsafe (seededTrEnv _).checkerEnv seededPrimitives
    seededPrimitiveSafety DefinitionSafety.le_rfl

private def pairThenOrdinary (natFirst isUnsafe : Bool) : AddInductive.M Kernel.Environment :=
  fun ctx => do
    let native ← pairStage natFirst (primitiveContext ctx.env)
    checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe (context native isUnsafe)

private theorem pairThenOrdinaryInterfaces (natFirst isUnsafe : Bool)
    {native : Kernel.Environment} {semantic : VEnv} {safety : DefinitionSafety}
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe) :
    (pairThenOrdinary natFirst isUnsafe (context native isUnsafe)).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧ NativePrimitiveSafety result := by
  refine Except.WF.bind (x := pairStage natFirst (primitiveContext native))
    (f := fun middle => checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe
      (context middle isUnsafe)) (pairInterfaces natFirst hchecker hp hsafe) ?_
  rintro middle ⟨model, hmiddle, hp', hsafe'⟩
  exact (acceptedOrdinaryInterfaces isUnsafe hmiddle hp' hsafe' hsafety).mono
    fun _ ⟨final, hfinal, hp'', hsafe'', _⟩ => ⟨final, hfinal, hp'', hsafe''⟩

example (natFirst isUnsafe : Bool) :
    (pairThenOrdinary natFirst isUnsafe (context seededNative isUnsafe)).WF fun result =>
      ∃ final, CheckerEnv (if isUnsafe then .unsafe else .safe) result final ∧
        final.HasPrimitives ∧ NativePrimitiveSafety result :=
  pairThenOrdinaryInterfaces natFirst isUnsafe (seededTrEnv _).checkerEnv seededPrimitives
    seededPrimitiveSafety DefinitionSafety.le_rfl

private theorem restrictedOrdinaryInterfaces (isUnsafe : Bool)
    {native : Kernel.Environment} {semantic : VEnv} {safety : DefinitionSafety}
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe
      (context native isUnsafe)).WF fun result =>
      ∃ final, Nonempty (RestrictedContext safety result final) :=
  (acceptedOrdinaryInterfaces isUnsafe hchecker hp hsafe hsafety).mono fun _ =>
    fun ⟨final, hfinal, hp', hsafe', _⟩ =>
      ⟨final, ⟨RestrictedContext.ofOrdinary hfinal hp' hsafe' []⟩⟩

example (isUnsafe : Bool) :
    (checkedConstructorStage #[{ family with ctors := [familyCtor] }] isUnsafe
      (context seededNative isUnsafe)).WF fun result =>
      ∃ final, Nonempty (RestrictedContext (if isUnsafe then .unsafe else .safe) result final) :=
  restrictedOrdinaryInterfaces isUnsafe (seededTrEnv _).checkerEnv seededPrimitives
    seededPrimitiveSafety DefinitionSafety.le_rfl

private theorem pairThenRestrictedInterfaces (natFirst isUnsafe : Bool)
    {native : Kernel.Environment} {semantic : VEnv} {safety : DefinitionSafety}
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe) :
    (pairThenOrdinary natFirst isUnsafe (context native isUnsafe)).WF fun result =>
      ∃ final, Nonempty (RestrictedContext safety result final) :=
  (pairThenOrdinaryInterfaces natFirst isUnsafe hchecker hp hsafe hsafety).mono fun _ =>
    fun ⟨final, hfinal, hp', hsafe'⟩ =>
      ⟨final, ⟨RestrictedContext.ofOrdinary hfinal hp' hsafe' []⟩⟩

example (natFirst isUnsafe : Bool) :
    (pairThenOrdinary natFirst isUnsafe (context seededNative isUnsafe)).WF fun result =>
      ∃ final, Nonempty (RestrictedContext (if isUnsafe then .unsafe else .safe) result final) :=
  pairThenRestrictedInterfaces natFirst isUnsafe (seededTrEnv _).checkerEnv seededPrimitives
    seededPrimitiveSafety DefinitionSafety.le_rfl

private def boolHeaderNative := emptyNative.add (.inductInfo { familyInfo with name := ``Bool })

private theorem boolHeaderPrimitiveSafety : NativePrimitiveSafety boolHeaderNative := by
  apply emptyPrimitiveSafety.addConst (ci := .inductInfo { familyInfo with name := ``Bool })
  · change ({} : ConstMap).find? ``Bool = none
    simp [SMap.find?]
  · intro _
    exact ⟨rfl, rfl⟩

private theorem rejectsPrimitiveInsertionFrame : ¬NativePrimitiveFrame emptyNative boolHeaderNative := by
  intro frame
  have hprim : Kernel.Environment.primitives.contains ``Bool := by
    apply Std.TreeSet.mem_iff_contains.mp
    simp [Kernel.Environment.primitives, NameSet.ofList]
  have hconstant := frame.constants hprim
  change (({} : ConstMap).insert ``Bool (.inductInfo { familyInfo with name := ``Bool })).find? ``Bool =
    ({} : ConstMap).find? ``Bool at hconstant
  rw [SMap.WF.empty.find?_insert] at hconstant
  simp [SMap.find?] at hconstant

private theorem rejectsPrimitiveRemovalFrame : ¬NativePrimitiveFrame boolHeaderNative emptyNative := by
  intro frame
  have hprim : Kernel.Environment.primitives.contains ``Bool := by
    apply Std.TreeSet.mem_iff_contains.mp
    simp [Kernel.Environment.primitives, NameSet.ofList]
  have hconstant := frame.constants hprim
  change ({} : ConstMap).find? ``Bool =
    (({} : ConstMap).insert ``Bool (.inductInfo { familyInfo with name := ``Bool })).find? ``Bool at hconstant
  rw [SMap.WF.empty.find?_insert] at hconstant
  simp [SMap.find?] at hconstant

private theorem aliasPrimitiveFrame : NativePrimitiveFrame emptyNative seededNative := by
  apply NativePrimitiveFrame.addConst (ci := .defnInfo nativeAlias) SMap.WF.empty
  · change ({} : ConstMap).find? nativeAlias.name = none
    simp [SMap.find?]
  · apply Bool.eq_false_iff.mpr
    intro hcontains
    have hmem := Std.TreeSet.mem_iff_contains.mpr hcontains
    simp [Kernel.Environment.primitives, NameSet.ofList, ConstantInfo.name,
      ConstantInfo.toConstantVal, nativeAlias] at hmem

private def polymorphicFamily : InductiveType := {
  name := `PolymorphicFamily, type := .sort (.succ (.param `u)),
  ctors := [⟨`PolymorphicFamily.mk, .const `PolymorphicFamily [.param `u]⟩] }

private def polymorphicHeader : VInductiveType := {
  name := polymorphicFamily.name, uvars := 1, type := .sort (.succ (.param 0)),
  ctors := [{ name := `PolymorphicFamily.mk, uvars := 1, type := .const `PolymorphicFamily [.param 0] }] }

private theorem acceptedPolymorphicInterfaces {native : Kernel.Environment} {semantic : VEnv}
    {safety : DefinitionSafety} (isUnsafe : Bool)
    (hchecker : CheckerEnv safety native semantic) (hp : semantic.HasPrimitives)
    (hsafe : NativePrimitiveSafety native)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkedConstructorStage #[polymorphicFamily] isUnsafe
      { context native isUnsafe with lparams := [`u] }).WF fun result =>
      ∃ final, CheckerEnv safety result final ∧ final.HasPrimitives ∧
        NativePrimitiveSafety result ∧ NativePrimitiveFrame native result := by
  refine (AddInductive.checkInductiveTypes.refinesOrdinaryInterfaces
    { context native isUnsafe with lparams := [`u] } 0 #[polymorphicFamily] 0 isUnsafe
    (headers := [polymorphicHeader]) (vtypes := [polymorphicHeader]) hchecker hp hsafe rfl hsafety
    (.cons ⟨rfl, rfl, .sort rfl⟩ .nil) ?_ ?_ ?_).mono ?_
  · intro candidate hmem
    simp only [List.mem_singleton] at hmem
    subst candidate
    exact ⟨_, .sort (by decide)⟩
  · intro headerEnv hadd
    have hlookup := VEnv.addInductHeaders.constants hadd (header := polymorphicHeader) (by simp)
    exact .cons (.cons ⟨rfl, rfl, TrExprS.const (ci := polymorphicHeader.toVConstant) hlookup rfl rfl⟩ .nil) .nil
  · intro headerEnv hadd candidate hmem
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, polymorphicHeader,
      List.mem_singleton] at hmem
    subst candidate
    have hlookup := VEnv.addInductHeaders.constants hadd (header := polymorphicHeader) (by simp)
    exact ⟨_, .const (ci := polymorphicHeader.toVConstant) hlookup
      (by simp [VLevel.WF]) rfl⟩
  · rintro result ⟨headerEnv, final, _, _, hfinal, hp', hsafe', hframe⟩
    exact ⟨final, hfinal, hp', hsafe', hframe⟩

example (isUnsafe : Bool) :
    (checkedConstructorStage #[polymorphicFamily] isUnsafe
      { context seededNative isUnsafe with lparams := [`u] }).WF fun result =>
      ∃ final, CheckerEnv (if isUnsafe then .unsafe else .safe) result final ∧
        final.HasPrimitives ∧ NativePrimitiveSafety result ∧ NativePrimitiveFrame seededNative result :=
  acceptedPolymorphicInterfaces isUnsafe (seededTrEnv _).checkerEnv seededPrimitives
    seededPrimitiveSafety DefinitionSafety.le_rfl

private def sameConstant : Option ConstantInfo → Option ConstantInfo → Bool
  | none, none => true
  | some (.axiomInfo first), some (.axiomInfo second) => first == second
  | some (.defnInfo first), some (.defnInfo second) => first == second
  | some (.thmInfo first), some (.thmInfo second) => first == second
  | some (.opaqueInfo first), some (.opaqueInfo second) => first == second
  | some (.quotInfo first), some (.quotInfo second) =>
    first.toConstantVal == second.toConstantVal && match first.kind, second.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | some (.inductInfo first), some (.inductInfo second) =>
    first.toConstantVal == second.toConstantVal && first.numParams == second.numParams &&
      first.numIndices == second.numIndices && first.all == second.all && first.ctors == second.ctors &&
      first.numNested == second.numNested && first.isRec == second.isRec &&
      first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive
  | some (.ctorInfo first), some (.ctorInfo second) => first == second
  | some (.recInfo first), some (.recInfo second) => first == second
  | _, _ => false

run_meta
  let logical := [``propext, ``Quot.sound, ``Classical.choice]
  let native := logical ++ [``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.findAux_isSome]
  let semantic := native ++ [``sorryAx]
  let primitive := semantic ++ [``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel,
    ``Lean.Syntax.structEq_eq]
  for theoremName in [``NativePrimitiveFrame.refl, ``NativePrimitiveFrame.trans,
      ``NativePrimitiveFrame.foldlM, ``NativePrimitiveSafety.of_frame,
      ``VEnv.HasPrimitives.mono_of_primitiveConstants] do
    audit theoremName logical
  audit ``NativePrimitiveFrame.find? (logical ++ [``Lean.PersistentHashMap.findAux_isSome])
  for theoremName in [``NativePrimitiveFrame.addConst, ``aliasPrimitiveFrame,
      ``AddInductive.declareInductiveTypes.preservesPrimitives,
      ``AddInductive.declareConstructors.preservesPrimitives,
      ``AddInductive.checkInductiveTypes.preservesHeaderConstructorPrimitives] do
    audit theoremName native
  for theoremName in [``Aligned.constants_eq_of_lookup, ``CheckerEnv.hasPrimitives_of_frame,
      ``AddInductive.declareInductiveTypes.refinesOrdinaryInterfaces,
      ``AddInductive.declareConstructors.refinesOrdinaryInterfaces,
      ``AddInductive.checkInductiveTypes.refinesOrdinaryInterfaces,
      ``acceptedOrdinaryInterfaces, ``acceptedPolymorphicInterfaces, ``boolHeaderPrimitiveSafety] do
    audit theoremName semantic
  audit ``pairThenOrdinaryInterfaces primitive
  for theoremName in [``rejectsPrimitiveInsertionFrame, ``rejectsPrimitiveRemovalFrame] do
    audit theoremName (logical ++
      [``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert])
  let mut count := 0
  let mut forbidden := 0
  for (seeded, initial) in [(false, emptyNative), (true, seededNative)] do
    for natFirst in [false, true] do
      let .ok native := pairStage natFirst (primitiveContext initial) | throwError "cannot seed primitive interfaces"
      for isUnsafe in [false, true] do
        for types in [#[], #[{ family with ctors := [familyCtor] }], ordinaryMutual] do
          let .ok result := checkedConstructorStage types isUnsafe (context native isUnsafe)
            | throwError "ordinary staging after primitives failed"
          for name in Kernel.Environment.primitives.toList do
            unless sameConstant (result.find? name) (native.find? name) do
              throwError "ordinary staging changed a reserved primitive lookup"
          let .ok inferred := M.run result .safe {} [] {} (checkType (.lit (.natVal 37)))
            | throwError "ordinary staging broke Nat literal type checking"
          unless inferred == .const ``Nat [] do throwError "wrong Nat literal type after ordinary staging"
          if seeded then
            let .ok reduced := M.run result .safe {} [] {} (whnf (.const nativeAlias.name []))
              | throwError "ordinary staging broke retained safe delta reduction"
            unless reduced == .sort .zero do throwError "ordinary staging changed retained safe delta reduction"
          count := count + 1
        let .ok result := checkedConstructorStage #[polymorphicFamily] isUnsafe
          { context native isUnsafe with lparams := [`u] }
          | throwError "polymorphic ordinary staging after primitives failed"
        for name in Kernel.Environment.primitives.toList do
          unless sameConstant (result.find? name) (native.find? name) do
            throwError "polymorphic ordinary staging changed a reserved primitive lookup"
        let .ok inferred := M.run result (if isUnsafe then .unsafe else .safe) {} [`u] {}
          (checkType (.const `PolymorphicFamily.mk [.param `u]))
          | throwError "cannot type check a polymorphic ordinary constructor"
        unless inferred == .const `PolymorphicFamily [.param `u] do
          throwError "wrong polymorphic ordinary constructor type"
        let .ok literalType := M.run result .safe {} [] {} (checkType (.lit (.natVal 37)))
          | throwError "polymorphic ordinary staging broke Nat literal type checking"
        unless literalType == .const ``Nat [] do throwError "wrong Nat literal type after polymorphic staging"
        if seeded then
          let .ok reduced := M.run result .safe {} [] {} (whnf (.const nativeAlias.name []))
            | throwError "polymorphic ordinary staging broke retained safe delta reduction"
          unless reduced == .sort .zero do throwError "polymorphic ordinary staging changed retained safe delta reduction"
        count := count + 1
  let native := (← getEnv).toKernelEnv
  for isUnsafe in [false, true] do
    let .ok result := checkedConstructorStage ordinaryMutual isUnsafe (context native isUnsafe)
      | throwError "ordinary staging in the imported primitive environment failed"
    for name in Kernel.Environment.primitives.toList do
      unless sameConstant (result.find? name) (native.find? name) do
        throwError "ordinary staging changed an imported primitive record"
    let addition := .app (.app (.const ``Nat.add []) (.lit (.natVal 2))) (.lit (.natVal 3))
    let .ok reduced := M.run result .safe {} [] {} (whnf addition)
      | throwError "ordinary staging broke imported primitive addition"
    unless reduced == .lit (.natVal 5) do throwError "ordinary staging changed imported primitive addition"
    count := count + 1
  for name in Kernel.Environment.primitives.toList do
    for isUnsafe in [false, true] do
      for lparams in [[], [`u]] do
        for types in [#[{ family with name }], #[{ family with ctors := [⟨name, familyCtor.type⟩] }]] do
          if (checkedConstructorStage types isUnsafe { context emptyNative isUnsafe with lparams }).isOk then
            throwError "ordinary staging admitted a reserved primitive name"
          forbidden := forbidden + 1
  logInfo m!"{count} ordinary-after-primitive preservation controls; {forbidden} reserved-name rejections"

run_meta
  audit ``Lean4Lean.TypeChecker.Inner.checkLevel.checker [``propext, ``Quot.sound,
    ``Classical.choice, ``Lean.Level.hasParam_eq]
  audit ``Lean4Lean.TypeChecker.Inner.envGet.lookup [``propext, ``Quot.sound, ``Classical.choice]
  audit ``Lean4Lean.TypeChecker.Inner.inferConstant.checker [``propext, ``Quot.sound,
    ``Classical.choice, ``sorryAx, ``Lean.Level.hasParam_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.Expr.replace_eq,
    ``Lean.Expr.hasLevelParam_eq, ``Lean.Level.hasMVar_eq, ``Lean.Level.instLawfulBEqLevel]
  audit ``Lean4Lean.TypeChecker.Inner.infer_sort.checker [``propext, ``Quot.sound,
    ``Classical.choice, ``sorryAx]
  audit ``RestrictedContext.ofOrdinary [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  audit ``RestrictedContext.inferSort [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  audit ``RestrictedContext.inferConstant [``propext, ``Quot.sound, ``Classical.choice,
    ``sorryAx, ``Lean.Level.hasParam_eq, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.Expr.replace_eq, ``Lean.Expr.hasLevelParam_eq, ``Lean.Level.hasMVar_eq,
    ``Lean.Level.instLawfulBEqLevel]
  audit ``RestrictedContext.appExpr [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  audit ``RestrictedContext.forallExpr [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  audit ``restrictedOrdinaryInterfaces [``propext, ``Quot.sound, ``Classical.choice,
    ``sorryAx, ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  audit ``pairThenRestrictedInterfaces [``propext, ``Quot.sound, ``Classical.choice,
    ``sorryAx, ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]

end CheckerEnvironmentTest
