import Lean4Lean.Verify.Environment
import Lean.Util.CollectAxioms

namespace RebasedRestrictedFrontendTest
open Lean hiding Environment Exception
open Lean4Lean

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (declaration : Declaration) (fuel : FuelConfig) :
    (Lean4Lean.addDeclVerified environment declaration fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDeclVerified.WF wellFormed declaration fuel

example (environment : Kernel.Environment) (levelParams : List Name) (numParams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig) :
    Lean4Lean.addDeclVerified environment
      (.inductDecl levelParams numParams types isUnsafe) fuel =
        .error (.other "inductive declarations are not supported by the verified checker") :=
  rfl

private def runtimeControls : MetaM Unit := do
  let prefixDeclarations : List Declaration := [
    .axiomDecl {
      name := `RestrictedProposition, levelParams := [],
      type := .sort .zero, isUnsafe := false },
    .axiomDecl {
      name := `restrictedProof, levelParams := [],
      type := .const `RestrictedProposition [], isUnsafe := false },
    .axiomDecl {
      name := `RestrictedOther, levelParams := [],
      type := .sort .zero, isUnsafe := false }]
  let definition : DefinitionVal := {
    name := `restrictedDefinition, levelParams := [],
    type := .const `RestrictedProposition [], value := .const `restrictedProof [],
    hints := .abbrev, safety := .safe }
  let suffixDeclarations : List Declaration := [
    .defnDecl definition,
    .thmDecl {
      name := `restrictedTheorem, levelParams := [],
      type := .const `RestrictedProposition [], value := .const `restrictedProof [] },
    .opaqueDecl {
      name := `restrictedOpaque, levelParams := [],
      type := .const `RestrictedProposition [], value := .const `restrictedProof [],
      isUnsafe := false }]
  let fuels : List FuelConfig := [{}, { recDepth := 32, whnf := 128, whnfEager := 128 },
    { recDepth := 128, whnf := 512, whnfEager := 512 }]
  for fuel in fuels do
    let empty := Kernel.Environment.empty `RebasedRestrictedTest
    let .ok initial := prefixDeclarations.foldlM (fun current declaration =>
        Lean4Lean.addDeclVerified current declaration fuel) empty
      | throwError "rebased restricted axiom prefix rejected"
    let .ok final := suffixDeclarations.foldlM (fun current declaration =>
        Lean4Lean.addDeclVerified current declaration fuel) initial
      | throwError "rebased restricted definition/theorem/opaque suffix rejected"
    for name in [`RestrictedProposition, `restrictedProof, `RestrictedOther] do
      let some before := initial.find? name | throwError "restricted prefix constant absent"
      let some after := final.find? name | throwError "restricted frontend dropped an old constant"
      unless before.type == after.type &&
          before.value? (allowOpaque := true) == after.value? (allowOpaque := true) do
        throwError "restricted frontend changed an old type/value"
    for name in [`restrictedDefinition, `restrictedTheorem, `restrictedOpaque] do
      unless (final.find? name).isSome do
        throwError "restricted frontend dropped a new constant"
    let incorrect : Declaration := .thmDecl {
      name := `restrictedIncorrect, levelParams := [],
      type := .const `RestrictedOther [], value := .const `restrictedProof [] }
    unless !(Lean4Lean.addDeclVerified initial incorrect fuel).isOk do
      throwError "restricted frontend accepts an unrelated proof"
    unless !(Lean4Lean.addDeclVerified final (.defnDecl definition) fuel).isOk do
      throwError "restricted frontend accepts a duplicate name"
    unless !(Lean4Lean.addDeclVerified initial (.inductDecl [] 0 [] false) fuel).isOk do
      throwError "restricted frontend accepts inductive declarations"
  logInfo "restricted frontend preserves its prefix across three fuels and rejects wrong proofs, duplicates and inductives"

run_meta
  let theoremName := ``addDeclVerified.WF
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "restricted frontend theorem is an axiom"
  let some proof := information.value? (allowOpaque := true)
    | throwError "restricted frontend proof absent"
  if proof.hasSorry then
    throwError "restricted frontend direct admission"
  if proof.getUsedConstants.contains ``addDecl.WF then
    throwError "restricted frontend depends on the admitted inductive frontend"
  let allowed ← collectAxioms ``Lean4Lean.TypeChecker.checkType.WF
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless allowed.contains dependency do
      throwError "restricted frontend dependency outside the checker baseline: {dependency}"
  logInfo m!"{theoremName}: {repr dependencies}"
  runtimeControls

end RebasedRestrictedFrontendTest
