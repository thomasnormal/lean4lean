import Lean4Lean.Verify.ConstructorHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

namespace PrimitiveInductiveStagingTest

private def boolType : InductiveType := {
  name := ``Bool, type := .sort (.succ .zero),
  ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] }

private def natType (binderName : Name) (binderInfo : BinderInfo) : InductiveType := {
  name := ``Nat, type := .sort (.succ .zero),
  ctors := [⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩] }

private def marker : AxiomVal := {
  name := `ExistingMarker, levelParams := [], type := .sort .zero, isUnsafe := false }

private def markerValue : VConstVal := { name := marker.name, uvars := 0, type := .sort .zero }

private def emptyNative := Kernel.Environment.empty `PrimitiveInductiveStagingTest
private def seededNative := emptyNative.add (.axiomInfo marker)
private def seededSemantic :=
  (VEnv.empty.addConst markerValue.name markerValue.toVConstant).getD VEnv.empty

private theorem seededAligned (safety : DefinitionSafety) :
  Aligned safety seededNative.constants seededSemantic :=
  Aligned.const .empty (by simp [SMap.find?])
    ⟨DefinitionSafety.le_safe, rfl, .sort rfl⟩ rfl rfl

private theorem seededWF : seededSemantic.WF :=
  ⟨[.axiom markerValue], .decl (.axiom ⟨_, .sort trivial⟩ rfl) .empty⟩

private def context (native : Kernel.Environment) : Context := {
  env := native, lparams := [], safety := .safe, allowPrimitive := true,
  fuel := { recDepth := 16, inductiveFuel := 4 } }

private def checkedStage (types : List InductiveType) : M Kernel.Environment :=
  checkInductiveTypes 0 types.toArray fun stats => do
    withEnv (← declareInductiveTypes stats 0 types.toArray 0 false) do
      checkConstructors types.toArray stats false
      declareConstructors stats types.toArray false

private theorem acceptedStaging {native : Kernel.Environment} {semantic : VEnv}
    {types : List InductiveType} {safety : DefinitionSafety}
    (aligned : Aligned safety native.constants semantic) (wellformed : semantic.WF)
    (primitive : Environment.PrimitiveInductiveDecl [] 0 types false) :
    (checkedStage types (context native)).WF fun result =>
      ∃ final, final.WF ∧ Aligned safety result.constants final ∧
        semantic ≤ final ∧ final.defeqs = semantic.defeqs := by
  have recognized := (Environment.checkPrimitiveInductive.eq_true_iff native [] 0 types false).mpr primitive
  refine (checkInductiveTypes.refinesPrimitiveHeaderConstructorWF
    (context native) 0 types 0 false aligned wellformed recognized).mono ?_
  rintro result ⟨decl, headers, constructors, _, addedHeaders, _, _, addedCtors, ctorWF, ctorAligned⟩
  exact ⟨constructors, ctorWF, ctorAligned,
    (VEnv.addInductHeaders.le addedHeaders).trans (VEnv.addConstructorHeaders.le addedCtors),
    (VEnv.addConstructorHeaders.defeqs_eq addedCtors).trans (VEnv.addInductHeaders.defeqs_eq addedHeaders)⟩

example : (checkedStage [boolType] (context emptyNative)).WF fun result =>
    ∃ final, final.WF ∧ Aligned .safe result.constants final ∧
      VEnv.empty ≤ final ∧ final.defeqs = VEnv.empty.defeqs :=
  acceptedStaging Aligned.empty ⟨[], .empty⟩ .bool

example (binderName : Name) (binderInfo : BinderInfo) (safety : DefinitionSafety) :
    (checkedStage [natType binderName binderInfo] (context seededNative)).WF fun result =>
      ∃ final, final.WF ∧ Aligned safety result.constants final ∧
        seededSemantic ≤ final ∧ final.defeqs = seededSemantic.defeqs :=
  acceptedStaging (seededAligned safety) seededWF (.nat binderName binderInfo)

example (headerEnv : VEnv)
    (added : seededSemantic.addInductHeaders natInductDecl.types = some headerEnv) :
    ∀ ctor ∈ natInductDecl.types.flatMap (fun type => type.ctors), ctor.toVConstant.WF headerEnv :=
  natInductDecl.constructorWF added

private def checkAccepted (native : Kernel.Environment) (type : InductiveType) : MetaM Unit := do
  let ctx := context native
  let .ok true := Environment.checkPrimitiveInductive native [] 0 [type] false
    | throwError "primitive fixture was not recognized"
  let .ok result := checkedStage [type] ctx | throwError "recognized primitive staging failed"
  let some (.inductInfo header) := result.find? type.name | throwError "missing primitive header"
  unless header.type == type.type && header.levelParams.isEmpty && header.numParams == 0 &&
      header.numIndices == 0 && !header.isUnsafe do
    throwError "incorrect primitive header"
  for ctor in type.ctors do
    let some (.ctorInfo info) := result.find? ctor.name | throwError "missing primitive constructor"
    unless info.type == ctor.type && info.induct == type.name && !info.isUnsafe do
      throwError "incorrect primitive constructor"
  if result.contains (type.name ++ `rec) then throwError "staging installed a recursor"
  if native.contains marker.name then
    let some (.axiomInfo info) := result.find? marker.name | throwError "old declaration disappeared"
    unless info.name == marker.name && info.type == marker.type && info.levelParams.isEmpty &&
        !info.isUnsafe do throwError "old declaration changed"
  else if result.contains marker.name then
    throwError "staging invented an old declaration"
  if (checkedStage [type] { ctx with env := result }).isOk then
    throwError "staging accepted duplicate primitive names"
  if (checkedStage [type] { ctx with allowPrimitive := false }).isOk then
    throwError "staging bypassed primitive authorization"
  if (checkedStage [type] { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }).isOk then
    throwError "staging accepted zero structural fuel"
  for occupied in type.name :: type.ctors.map (fun ctor => ctor.name) do
    let collision := native.add (.axiomInfo { marker with name := occupied })
    let .ok true := Environment.checkPrimitiveInductive collision [] 0 [type] false
      | throwError "recognition unexpectedly rejected an occupied name"
    let .error (.alreadyDeclared _ rejected) := checkedStage [type] (context collision)
      | throwError "staging accepted or misreported an occupied name"
    unless rejected == occupied do throwError "staging reported the wrong occupied name"

run_meta
  let expected := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let theoremName := ``checkInductiveTypes.refinesPrimitiveHeaderConstructorWF
  let axioms ← collectAxioms theoremName
  unless axioms.size == expected.length && axioms.all expected.contains do
    throwError "primitive staging has unexpected dependencies: {repr axioms}"
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let mut count : Nat := 0
  for native in [emptyNative, seededNative] do
    checkAccepted native boolType
    count := count + 1
    for binderName in [Name.anonymous, `value, `nested.binder] do
      for binderInfo in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
        checkAccepted native (natType binderName binderInfo)
        count := count + 1
  logInfo m!"{count} primitive staging fixtures with duplicate/auth/fuel and individual name-collision controls"

end PrimitiveInductiveStagingTest
