import Lean4Lean.Verify.PrimitiveInductiveRecursors
import Lean.Util.CollectAxioms

namespace PrimitiveInductiveReceiptTest
open Lean hiding Environment Exception
open Lean4Lean

example (environment : Kernel.Environment) (model : VEnv)
    (levels : List Name) (parameters : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    (Environment.checkPrimitiveInductive environment levels parameters types isUnsafe).WF
      (fun primitive => primitive = true →
        ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
          decl.HeadersWF model ∧
          ∀ model', model.addInductHeaders decl.types = some model' →
            TrInductDecl model model' levels parameters types decl) :=
  Environment.checkPrimitiveInductive.toVDecl_WF environment model levels parameters types isUnsafe

example (environment : Kernel.Environment) (model : VEnv)
    (levels : List Name) (parameters : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    (Environment.checkPrimitiveInductive environment levels parameters types isUnsafe).WF
      (fun primitive => primitive = true →
        ∃ decl, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
          decl.HeadersWF model ∧ decl.WF model ∧
          ∀ model', model.addInductHeaders decl.types = some model' →
            TrInductDecl model model' levels parameters types decl) :=
  Environment.checkPrimitiveInductive.toVDecl_WF_model
    environment model levels parameters types isUnsafe

run_meta
  let theoremName := ``Environment.checkPrimitiveInductive.toVDecl_WF
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "primitive frontend receipt is an axiom"
  let some proof := information.value? (allowOpaque := true) | throwError "primitive frontend receipt proof missing"
  if proof.hasSorry then throwError "primitive frontend receipt has an admission"
  let baseline ← collectAxioms ``Environment.checkPrimitiveInductive.toVDecl
  let axioms ← collectAxioms theoremName
  for axiomName in axioms do
    unless baseline.contains axiomName do
      throwError "primitive frontend receipt has unexpected dependency: {axiomName}"
  logInfo m!"primitive checker success is theorem-backed through VDecl/header translation; dependencies = {repr axioms}"

run_meta
  let theoremName := ``Environment.checkPrimitiveInductive.toVDecl_WF_model
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "primitive model receipt is an axiom"
  let some proof := information.value? (allowOpaque := true) | throwError "primitive model receipt proof missing"
  if proof.hasSorry then throwError "primitive model receipt has an admission"

end PrimitiveInductiveReceiptTest

namespace PrimitiveInductivePreprocessingTest
open Lean hiding Environment Exception
open Lean4Lean

example (environment : Kernel.Environment) (fuel : FuelConfig) :
    NonNestedInductivePreprocessing environment [] 0 [canonicalBoolType] fuel :=
  canonicalBoolNonNested environment fuel

example (environment : Kernel.Environment) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) :
    NonNestedInductivePreprocessing environment [] 0
      [canonicalNatType binderName binderInfo] fuel :=
  canonicalNatNonNested environment fuel binderName binderInfo

example (environment : Kernel.Environment) (fuel : FuelConfig) (check : Bool)
    (hmap : environment.constants.WF) :
    (addDecl environment (.inductDecl [] 0 [canonicalBoolType] false) check fuel).WF fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope environment [] 0 [canonicalBoolType] allowPrimitive fuel result :=
  addDecl.safeCanonicalBool environment check fuel hmap

example (environment : Kernel.Environment) (fuel : FuelConfig) (check : Bool)
    (binderName : Name) (binderInfo : BinderInfo) (hmap : environment.constants.WF) :
    (addDecl environment (.inductDecl [] 0 [canonicalNatType binderName binderInfo] false) check fuel).WF fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope environment [] 0 [canonicalNatType binderName binderInfo]
          allowPrimitive fuel result :=
  addDecl.safeCanonicalNat environment check fuel binderName binderInfo hmap

run_meta
  for theoremName in [``canonicalBoolPreprocess, ``canonicalBoolNonNested,
      ``canonicalNatPreprocess, ``canonicalNatNonNested,
      ``addDecl.safeCanonicalBool, ``addDecl.safeCanonicalNat] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "canonical primitive receipt is not theorem-backed: {theoremName}"
    let some proof := information.value? (allowOpaque := true) |
      throwError "canonical primitive receipt proof missing: {theoremName}"
    if proof.hasSorry then
      throwError "canonical primitive receipt has an admission: {theoremName}"
  logInfo "canonical Bool/Nat preprocessing and frontend-scope receipts are theorem-backed"

end PrimitiveInductivePreprocessingTest

namespace PrimitiveInductiveRegistrationTest
open Lean hiding Environment Exception
open Lean4Lean

private def emptyNative := Kernel.Environment.empty `PrimitiveInductiveRegistrationTest
private def canonicalContext (fuel : FuelConfig) : AddInductive.Context :=
  inductiveScopeContext emptyNative [] true fuel

private theorem emptyChecker (fuel : FuelConfig) :
    CheckerEnv .safe (canonicalContext fuel).env VEnv.empty := by
  refine { aligned := .empty, wf := ⟨[], .empty⟩, safeValues := ?_ }
  intro name ci value hfind
  change SMap.find? ({ stage₁ := false } : ConstMap) name = some ci at hfind
  rw [SMap.find?_emptyStage] at hfind
  contradiction

private theorem emptyMapWF : emptyNative.constants.WF := by
  change SMap.WF ({ stage₁ := false } : ConstMap)
  exact SMap.WF.emptyStage false

example (check : Bool) (fuel : FuelConfig) :
    (addDecl emptyNative (.inductDecl [] 0 [canonicalBoolType] false) check fuel).WF (fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope emptyNative [] 0 [canonicalBoolType] allowPrimitive fuel result) ∧
    (AddInductive.checkInductiveTypes 0 [canonicalBoolType].toArray (fun stats => do
      AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0
        [canonicalBoolType].toArray 0 false) do
        AddInductive.checkConstructors [canonicalBoolType].toArray stats false
        AddInductive.declareConstructors stats [canonicalBoolType].toArray false)
      (canonicalContext fuel)).WF (fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF VEnv.empty ∧ decl.WF VEnv.empty ∧
        VEnv.empty.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl VEnv.empty headerEnv [] 0 [canonicalBoolType] decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧ ctorEnv.WF ∧ VDecl.WF VEnv.empty (.induct decl) ctorEnv ∧
        CheckerEnv .safe env' ctorEnv) :=
  addDecl.safeCanonicalBoolRegistration emptyNative check fuel emptyMapWF VEnv.empty
    (emptyChecker fuel)

example (check : Bool) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) :
    (addDecl emptyNative
      (.inductDecl [] 0 [canonicalNatType binderName binderInfo] false) check fuel).WF
      (fun result => ∃ allowPrimitive,
        NonNestedInductiveScope emptyNative [] 0 [canonicalNatType binderName binderInfo]
          allowPrimitive fuel result) ∧
    (AddInductive.checkInductiveTypes 0
      [canonicalNatType binderName binderInfo].toArray (fun stats => do
        AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0
          [canonicalNatType binderName binderInfo].toArray 0 false) do
          AddInductive.checkConstructors [canonicalNatType binderName binderInfo].toArray stats false
          AddInductive.declareConstructors stats [canonicalNatType binderName binderInfo].toArray false)
      (canonicalContext fuel)).WF (fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF VEnv.empty ∧ decl.WF VEnv.empty ∧
        VEnv.empty.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl VEnv.empty headerEnv [] 0
          [canonicalNatType binderName binderInfo] decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧ ctorEnv.WF ∧ VDecl.WF VEnv.empty (.induct decl) ctorEnv ∧
        CheckerEnv .safe env' ctorEnv) :=
  addDecl.safeCanonicalNatRegistration emptyNative check fuel binderName binderInfo emptyMapWF
    VEnv.empty (emptyChecker fuel)

run_meta
  for theoremName in [``addDecl.safeCanonicalBoolRegistration,
      ``addDecl.safeCanonicalNatRegistration] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "canonical registration package is not theorem-backed: {theoremName}"
    let some proof := information.value? (allowOpaque := true) |
      throwError "canonical registration package proof missing: {theoremName}"
    if proof.hasSorry then
      throwError "canonical registration package has an admission: {theoremName}"
  logInfo "canonical Bool/Nat frontend and VDecl registration packages are theorem-backed"

end PrimitiveInductiveRegistrationTest

namespace PrimitiveInductiveRecursorTest
open Lean hiding Environment Exception
open Lean4Lean

#check addDecl.safeCanonicalBoolRecursors
#check addDecl.safeCanonicalNatRecursors

run_meta
  let environment := Kernel.Environment.empty `PrimitiveInductiveRecursorTest
  let fuel : FuelConfig := { recDepth := 16, inductiveFuel := 4 }
  let checkResult (label : String) (type : InductiveType) (recName : Name)
      (ctorCount : Nat) : MetaM Unit := do
    let .ok result := addDecl environment (.inductDecl [] 0 [type] false) true fuel
      | throwError "{label} frontend did not succeed"
    let some (.recInfo recursor) := result.find? recName
      | throwError "{label} recursor was not registered"
    unless recursor.name == recName && recursor.all == [type.name] &&
        recursor.rules.length == ctorCount do
      throwError "{label} recursor metadata was incorrect"
    for rule in recursor.rules do
      unless type.ctors.any (·.name == rule.ctor) do
        throwError "{label} recursor contains an unknown constructor rule"
  checkResult "Bool" canonicalBoolType ``Bool.rec 2
  for binderName in [Name.anonymous, `value, `nested.binder] do
    for binderInfo in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
      checkResult "Nat" (canonicalNatType binderName binderInfo) ``Nat.rec 2
  logInfo "canonical Bool/Nat recursor registration succeeded for all Nat binder fixtures"

run_meta
  for theoremName in [``addDecl.safeCanonicalBoolRecursors,
      ``addDecl.safeCanonicalNatRecursors] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "canonical recursor receipt is not theorem-backed: {theoremName}"
    let some proof := information.value? (allowOpaque := true) |
      throwError "canonical recursor receipt proof missing: {theoremName}"
    if proof.hasSorry then
      throwError "canonical recursor receipt has an admission: {theoremName}"
  logInfo "canonical Bool/Nat recursor receipts are theorem-backed"

end PrimitiveInductiveRecursorTest

namespace PrimitiveInductivePreprocessingRuntimeTest
open Lean hiding Environment Exception
open Lean4Lean

run_meta
  let environment := Kernel.Environment.empty `PrimitiveInductivePreprocessingRuntimeTest
  let fuel : FuelConfig := { recDepth := 16, inductiveFuel := 4 }
  let checkResult (label : String) (types : List InductiveType) : MetaM Unit := do
    let .ok preprocessing := inductivePreprocessing environment [] 0 types fuel
      | throwError "{label} preprocessing did not succeed"
    unless preprocessing.aux2nested.size == 0 do
      throwError "{label} preprocessing retained auxiliary nested declarations"
  checkResult "Bool" [canonicalBoolType]
  for binderName in [Name.anonymous, `value, `nested.binder] do
    for binderInfo in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
      checkResult "Nat" [canonicalNatType binderName binderInfo]
  logInfo "runtime preprocessing receipts succeeded for Bool and all Nat binder-name/info fixtures"

end PrimitiveInductivePreprocessingRuntimeTest
