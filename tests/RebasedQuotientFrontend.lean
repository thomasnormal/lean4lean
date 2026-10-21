import Lean4Lean.Verify.Environment
import Lean.Util.CollectAxioms

namespace RebasedQuotientFrontendTest
open Lean hiding Environment Exception
open Lean4Lean
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions
  Lean.Kernel.Environment.irBaseExts from Lean.Environment

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (fuel : FuelConfig) :
    (Lean4Lean.addQuotVerified environment fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addQuotVerified.WF wellFormed fuel

private def withConstants (environment : Kernel.Environment) (constants : ConstMap)
    (quotInit : Bool) : Kernel.Environment :=
  Lean.Kernel.Environment.mk constants quotInit environment.diagnostics environment.const2ModIdx
    (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment)
    environment.header

private def replaceConstant (environment : Kernel.Environment) (constant : ConstantInfo) :
    Kernel.Environment :=
  let constants := { environment.constants with
    map₁ := environment.constants.map₁.erase constant.name
    map₂ := environment.constants.map₂.erase constant.name }
  withConstants environment (constants.insert constant.name constant) environment.quotInit

private def runtimeControls : MetaM Unit := do
  let native := (← getEnv).toKernelEnv
  let quotientNames := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  let constants := quotientNames.foldl (fun constants name => { constants with
    map₁ := constants.map₁.erase name, map₂ := constants.map₂.erase name }) native.constants
  let fresh := withConstants native constants false
  let some (.inductInfo equality) := fresh.find? ``Eq
    | throwError "native Eq declaration absent"
  let some (.ctorInfo reflexivity) := fresh.find? ``Eq.refl
    | throwError "native Eq.refl constructor absent"
  let .ok standard := Lean4Lean.addDecl fresh .quotDecl
    | throwError "upstream quotient bootstrap rejected"
  for fuel in [{}, { recDepth := 32, whnf := 128, whnfEager := 128 },
      { recDepth := 128, whnf := 512, whnfEager := 512 }] do
    let .ok added := Lean4Lean.addDeclVerified fresh .quotDecl fuel
      | throwError "verified quotient bootstrap rejected"
    unless added.quotInit do throwError "verified quotient bootstrap did not mark initialization"
    for name in quotientNames do
      let some (.quotInfo actual) := added.find? name
        | throwError "verified quotient constant absent"
      let some (.quotInfo expected) := standard.find? name
        | throwError "upstream quotient constant absent"
      let sameKind := match actual.kind, expected.kind with
        | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
        | _, _ => false
      unless actual.levelParams == expected.levelParams && sameKind do
        throwError "verified quotient changes its universe parameters or kind"
      let .ok true := TypeChecker.M.run added (lparams := actual.levelParams) (fuel := fuel)
          (x := TypeChecker.isDefEq actual.type expected.type)
        | throwError "verified quotient header differs from the actual upstream header"
    for name in [``Eq, ``Eq.refl, ``Nat] do
      let some before := fresh.find? name | throwError "quotient prefix constant absent"
      let some after := added.find? name | throwError "quotient frontend dropped a prefix constant"
      unless before.type == after.type &&
          before.value? (allowOpaque := true) == after.value? (allowOpaque := true) do
        throwError "quotient frontend changed a prefix type/value"
  let noFuel : FuelConfig := { recDepth := 0, whnf := 0, whnfEager := 0 }
  unless !(Lean4Lean.addDeclVerified fresh .quotDecl noFuel).isOk do
    throwError "verified quotient bootstrap ignores exhausted callback fuel"
  unless (Lean4Lean.addDeclVerified standard .quotDecl noFuel).isOk do
    throwError "initialized quotient frontend is not idempotent with exhausted fuel"
  for replacement in [
      ConstantInfo.inductInfo { equality with isUnsafe := true },
      .inductInfo { equality with levelParams := [] },
      .inductInfo { equality with type := .sort .zero },
      .inductInfo { equality with ctors := [] },
      .ctorInfo { reflexivity with isUnsafe := true },
      .ctorInfo { reflexivity with levelParams := [] },
      .ctorInfo { reflexivity with type := .sort .zero },
      .axiomInfo { reflexivity.toConstantVal with isUnsafe := false }] do
    let invalid := replaceConstant fresh replacement
    unless !(Lean4Lean.checkEqType invalid).isOk do
      throwError "quotient guard accepts invalid {replacement.name}: unsafe={replacement.isUnsafe}, universe parameters={replacement.levelParams}"
    unless !(Lean4Lean.addDeclVerified invalid .quotDecl).isOk do
      throwError "verified quotient bootstrap accepts an invalid Eq or Eq.refl declaration"
  for name in quotientNames do
    let some source := native.find? name | throwError "native quotient source absent"
    let collision := replaceConstant fresh (.axiomInfo {
      source.toConstantVal with isUnsafe := false })
    unless !(Lean4Lean.addDecl collision .quotDecl).isOk do
      throwError "upstream quotient frontend overwrites an existing constant"
    unless !(Lean4Lean.addDeclVerified collision .quotDecl).isOk do
      throwError "verified quotient frontend overwrites an existing constant"
  logInfo "native-prelude quotient controls pass: three fuels, compatible headers, prefix preservation, exhausted-fuel rejection, idempotence, Eq/reflexivity guards and four fresh-name checks"

run_meta
  let allowed ← collectAxioms ``Lean4Lean.TypeChecker.checkType.WF
  for theoremName in #[``checkEqType.WF, ``addQuot.WF, ``addQuotVerified.WF,
      ``addDefinition.WF_unsafe, ``addDeclVerified.WF, ``TypeChecker.Inner.isDelta_is_some,
      ``TypeChecker.Inner.unfoldDefinitionCore.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "frontend theorem is an axiom"
    let some proof := information.value? (allowOpaque := true)
      | throwError "frontend proof absent"
    if proof.hasSorry then throwError "frontend direct admission"
    if proof.getUsedConstants.contains ``addDecl.WF then
      throwError "frontend theorem relies on the admitted inductive frontend"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "dependency outside the existing checker baseline: {dependency}"
    logInfo m!"{theoremName}: {repr dependencies}"
  runtimeControls

end RebasedQuotientFrontendTest
