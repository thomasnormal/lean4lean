import Lean4Lean.Verify.Environment
import Lean.Util.CollectAxioms

namespace NonInductiveDeclarationFrontendTest
open Lean hiding Environment Exception
open Lean4Lean

example {environment : Kernel.Environment} {models : VEnvs} (wellFormed : models.WF environment)
    (declaration : Declaration)
    (notInductive : ∀ lparams nparams types isUnsafe,
      declaration ≠ .inductDecl lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl environment declaration true {}).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDecl.WF_noninductive wellFormed declaration notInductive

example {environment : Kernel.Environment} {models : VEnvs} (wellFormed : models.WF environment) :
    (Lean4Lean.addDecl environment .quotDecl).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDecl.WF_noninductive wellFormed .quotDecl (by intros; simp)

example {environment : Kernel.Environment} {models : VEnvs} (wellFormed : models.WF environment)
    (declarations : List Declaration)
    (notInductive : ∀ declaration ∈ declarations, ∀ lparams nparams types isUnsafe,
      declaration ≠ .inductDecl lparams nparams types isUnsafe) (fuel : FuelConfig) :
    (declarations.foldlM (fun current declaration => Lean4Lean.addDecl current declaration true fuel)
      environment).WF fun result =>
        ∃ models' : VEnvs, models'.WF result ∧
          ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDecl.foldlM_WF_noninductive wellFormed declarations notInductive fuel

example (mainModule : Name) (declarations : List Declaration)
    (notInductive : ∀ declaration ∈ declarations, ∀ lparams nparams types isUnsafe,
      declaration ≠ .inductDecl lparams nparams types isUnsafe) (fuel : FuelConfig) :
    (declarations.foldlM (fun current declaration => Lean4Lean.addDecl current declaration true fuel)
      (Kernel.Environment.empty mainModule)).WF fun result => ∃ models : VEnvs, models.WF result :=
  addDecl.fromEmpty_noninductive mainModule declarations notInductive fuel

private def nativeControls : MetaM Unit := do
  let base : List Declaration := [
    .axiomDecl {
      name := `FrontendProposition, levelParams := [],
      type := .sort .zero, isUnsafe := false },
    .axiomDecl {
      name := `frontendProof, levelParams := [],
      type := .const `FrontendProposition [], isUnsafe := false },
    .axiomDecl {
      name := `FrontendOther, levelParams := [],
      type := .sort .zero, isUnsafe := false }]
  let ordinary : List Declaration := [
    .defnDecl {
      name := `frontendDefinition, levelParams := [],
      type := .const `FrontendProposition [], value := .const `frontendProof [],
      hints := .abbrev, safety := .safe },
    .thmDecl {
      name := `frontendTheorem, levelParams := [],
      type := .const `FrontendProposition [], value := .const `frontendProof [] },
    .opaqueDecl {
      name := `frontendOpaque, levelParams := [],
      type := .const `FrontendProposition [], value := .const `frontendProof [], isUnsafe := false },
    .mutualDefnDecl [{
      name := `frontendMutual, levelParams := [],
      type := .const `FrontendProposition [], value := .const `frontendProof [],
      hints := .opaque, safety := .unsafe }]]
  let fuels : List FuelConfig := [{}, { recDepth := 32, whnf := 128, whnfEager := 128 },
    { recDepth := 128, whnf := 512, whnfEager := 512 }]
  for fuel in fuels do
    let empty := Kernel.Environment.empty `NonInductiveFrontendTest
    let .ok initial := base.foldlM (fun current declaration =>
        Lean4Lean.addDecl current declaration true fuel) empty
      | throwError "actual non-inductive axiom prefix rejected"
    let .ok final := ordinary.foldlM (fun current declaration =>
        Lean4Lean.addDecl current declaration true fuel) initial
      | throwError "actual non-inductive definition/theorem/opaque/mutual suffix rejected"
    for name in [`FrontendProposition, `frontendProof, `FrontendOther] do
      let some before := initial.find? name | throwError "frontend prefix constant absent"
      let some after := final.find? name | throwError "actual frontend dropped an old constant"
      unless before.type == after.type && before.value? == after.value? do
        throwError "actual frontend changed an old type/value"
    for name in [`frontendDefinition, `frontendTheorem, `frontendOpaque, `frontendMutual] do
      unless (final.find? name).isSome do throwError "actual frontend dropped a new constant"
    let incorrect : Declaration := .thmDecl {
      name := `frontendIncorrect, levelParams := [],
      type := .const `FrontendOther [], value := .const `frontendProof [] }
    unless !(Lean4Lean.addDecl initial incorrect true fuel).isOk do
      throwError "actual frontend accepted a proof at an unrelated proposition"
    unless !(Lean4Lean.addDecl final ordinary.head! true fuel).isOk do
      throwError "actual frontend accepted a duplicate declaration name"
    unless !(Lean4Lean.addDecl initial .quotDecl true fuel).isOk do
      throwError "actual frontend bootstrapped quotients without the required Eq inductive"
    unless !(Lean4Lean.addDecl empty .quotDecl true fuel).isOk do
      throwError "actual frontend bootstrapped quotients from the empty environment"
  let native := (← getEnv).toKernelEnv
  unless native.quotInit do throwError "native initialized quotient control absent"
  let .ok unchanged := Lean4Lean.addDecl native .quotDecl true { recDepth := 0 }
    | throwError "initialized actual quotient frontend rejected at zero callback depth"
  unless unchanged.quotInit do throwError "initialized actual quotient frontend lost its gate"
  for name in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    let some before := native.find? name | throwError "native quotient object absent"
    let some after := unchanged.find? name | throwError "initialized quotient object disappeared"
    unless before.type == after.type && before.value? == after.value? do
      throwError "initialized actual quotient frontend changed an object"
  logInfo m!"three actual checked non-inductive pipelines cover axioms, safe definitions, theorems, opaques and unsafe mutual definitions, old lookup/type/value preservation, wrong-proof and duplicate-name rejection, empty/nonempty quotient bootstrap rejection; native initialized quotient identity succeeds at zero callback depth outside the current TrEnv bootstrap fragment"

run_meta
  let theoremName := ``addDecl.WF_noninductive
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "regular declaration theorem is an axiom"
  let some proof := information.value? | throwError "regular declaration theorem proof missing"
  if proof.hasSorry then throwError "regular declaration theorem has an admission"
  let baseline ← collectAxioms ``addDeclVerified.WF
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless baseline.contains dependency do
      throwError "regular declaration theorem has unexpected dependency: {dependency}"
  for theoremName in #[``checkEqType.WF, ``addQuot.WF,
      ``addDecl.foldlM_WF_noninductive, ``addDecl.fromEmpty_noninductive] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "non-inductive frontend axiom: {theoremName}"
    let some proof := information.value? | throwError "non-inductive frontend proof absent: {theoremName}"
    if proof.hasSorry then throwError "non-inductive frontend direct admission: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected non-inductive frontend dependency: {dependency} in {theoremName}"
    logInfo m!"{theoremName}: {repr dependencies}"
  logInfo m!"actual non-inductive declaration frontend, quotient worker and folds have no direct admission; inherited dependencies = {repr dependencies}; quotient bootstrap rejection follows from the existing TrEnv inductive exclusion"
  nativeControls

end NonInductiveDeclarationFrontendTest
