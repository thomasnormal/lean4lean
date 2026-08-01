import Lean4Lean.Verify.Environment
import Lean.Util.CollectAxioms

namespace RebasedEnvironmentFuelTest
open Lean hiding Environment Exception
open Lean4Lean

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (declaration : Declaration)
    (notInductive : ∀ levelParams numParams types isUnsafe,
      declaration ≠ .inductDecl levelParams numParams types isUnsafe) (fuel : FuelConfig) :
    (Lean4Lean.addDecl environment declaration true fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDecl.WF_noninductive wellFormed declaration notInductive fuel

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (value : TheoremVal) (fuel : FuelConfig) :
    (Lean4Lean.addTheorem environment value true fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧ ∃ translated : VConstVal, ∀ safety,
        (models.venv safety).AddConst safety (.thmInfo value)
          translated.toVConstant (models'.venv safety) :=
  addTheorem.WF wellFormed value fuel

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (value : DefinitionVal) (fuel : FuelConfig) :
    (Lean4Lean.addDefinition environment value true fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        (∀ safety, models.venv safety ≤ models'.venv safety) ∧
        (value.safety ≠ .unsafe → ∃ translated : VDefVal, ∀ safety,
          (models.venv safety).AddDef safety (.defnInfo value) translated
            (models'.venv safety)) :=
  addDefinition.WF wellFormed value fuel

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (values : List DefinitionVal) (fuel : FuelConfig) :
    (Lean4Lean.addMutual environment values true fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addMutual.WF wellFormed values fuel

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (declarations : List Declaration)
    (notInductive : ∀ declaration ∈ declarations, ∀ levelParams numParams types isUnsafe,
      declaration ≠ .inductDecl levelParams numParams types isUnsafe) (fuel : FuelConfig) :
    (declarations.foldlM (fun current declaration => Lean4Lean.addDecl current declaration true fuel)
      environment).WF fun result =>
        ∃ models' : VEnvs, models'.WF result ∧
          ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDecl.foldlM_WF_noninductive wellFormed declarations notInductive fuel

example (mainModule : Name) (declarations : List Declaration)
    (notInductive : ∀ declaration ∈ declarations, ∀ levelParams numParams types isUnsafe,
      declaration ≠ .inductDecl levelParams numParams types isUnsafe) (fuel : FuelConfig) :
    (declarations.foldlM (fun current declaration => Lean4Lean.addDecl current declaration true fuel)
      (Kernel.Environment.empty mainModule)).WF fun result => ∃ models : VEnvs, models.WF result :=
  addDecl.fromEmpty_noninductive mainModule declarations notInductive fuel

private def runtimeControls : MetaM Unit := do
  let prefixDeclarations : List Declaration := [
    .axiomDecl {
      name := `FuelProposition, levelParams := [],
      type := .sort .zero, isUnsafe := false },
    .axiomDecl {
      name := `fuelProof, levelParams := [],
      type := .const `FuelProposition [], isUnsafe := false },
    .axiomDecl {
      name := `FuelOther, levelParams := [],
      type := .sort .zero, isUnsafe := false }]
  let suffixDeclarations : List Declaration := [
    .defnDecl {
      name := `fuelDefinition, levelParams := [],
      type := .const `FuelProposition [], value := .const `fuelProof [],
      hints := .abbrev, safety := .safe },
    .thmDecl {
      name := `fuelTheorem, levelParams := [],
      type := .const `FuelProposition [], value := .const `fuelProof [] },
    .opaqueDecl {
      name := `fuelOpaque, levelParams := [],
      type := .const `FuelProposition [], value := .const `fuelProof [], isUnsafe := false },
    .mutualDefnDecl [{
      name := `fuelMutual, levelParams := [],
      type := .const `FuelProposition [], value := .const `fuelProof [],
      hints := .opaque, safety := .unsafe }]]
  let fuels : List FuelConfig := [{}, { recDepth := 32, whnf := 128, whnfEager := 128 },
    { recDepth := 128, whnf := 512, whnfEager := 512 }]
  for fuel in fuels do
    let empty := Kernel.Environment.empty `RebasedFuelTest
    let .ok initial := prefixDeclarations.foldlM (fun current declaration =>
        Lean4Lean.addDecl current declaration true fuel) empty
      | throwError "rebased axiom prefix rejected"
    let .ok final := suffixDeclarations.foldlM (fun current declaration =>
        Lean4Lean.addDecl current declaration true fuel) initial
      | throwError "rebased definition/theorem/opaque/mutual suffix rejected"
    for name in [`FuelProposition, `fuelProof, `FuelOther] do
      let some before := initial.find? name | throwError "rebased prefix constant absent"
      let some after := final.find? name | throwError "rebased frontend dropped an old constant"
      unless before.type == after.type &&
          before.value? (allowOpaque := true) == after.value? (allowOpaque := true) do
        throwError "rebased frontend changed an old type/value"
    for name in [`fuelDefinition, `fuelTheorem, `fuelOpaque, `fuelMutual] do
      unless (final.find? name).isSome do throwError "rebased frontend dropped a new constant"
    let incorrect : Declaration := .thmDecl {
      name := `fuelIncorrect, levelParams := [],
      type := .const `FuelOther [], value := .const `fuelProof [] }
    unless !(Lean4Lean.addDecl initial incorrect true fuel).isOk do
      throwError "rebased frontend accepts a proof of an unrelated proposition"
    unless !(Lean4Lean.addDecl final suffixDeclarations.head! true fuel).isOk do
      throwError "rebased frontend accepts a duplicate name"
    unless !(Lean4Lean.addDecl initial .quotDecl true fuel).isOk do
      throwError "rebased frontend bootstraps quotients without Eq"
  logInfo "three actual checked pipelines preserve old constants and reject wrong proofs, duplicate names and quotient bootstrap without Eq"

run_meta
  let allowed ← collectAxioms ``Lean4Lean.TypeChecker.checkType.WF
  for theoremName in #[``addAxiom.WF, ``addDefinition.WF, ``addTheorem.WF,
      ``addOpaque.WF, ``addMutual.WF, ``addDecl.WF_noninductive,
      ``addDecl.foldlM_WF_noninductive, ``addDecl.fromEmpty_noninductive,
      ``VEnvs.WF.empty, ``addDefinition.WF_nonprimitive, ``checkConstantValBody.WF,
      ``checkConstantValCore.WF, ``checkConstantVal.WF, ``checkBodyCore.WF,
      ``checkBody.WF, ``checkTheorem.WF, ``checkDefinitionBody.WF,
      ``checkDefinition.WF, ``checkOpaque.WF, ``Primitive.checkDef.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "rebased environment theorem is an axiom: {theoremName}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "rebased environment proof absent: {theoremName}"
    if proof.hasSorry then
      throwError "rebased environment direct admission: {theoremName}"
    if proof.getUsedConstants.contains ``addDecl.WF then
      throwError "non-inductive proof relies on the admitted inductive frontend: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "dependency outside the upstream checker baseline: {dependency} in {theoremName}"
    logInfo m!"{theoremName}: {repr dependencies}"
  runtimeControls

end RebasedEnvironmentFuelTest
