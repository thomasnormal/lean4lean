import Lean4Lean.Verify.PrimitiveInductivePreprocessing
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
