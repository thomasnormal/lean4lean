import Lean4Lean.Verify.PrimitiveInductiveModel
import Lean.Util.CollectAxioms

namespace PrimitiveInductiveModelTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive

#check canonicalAnnotationModel.constants
#check canonicalAnnotationModel.definitions
#check canonicalBoolHeaderModel.added
#check canonicalBoolModel.added
#check canonicalBoolModel.constants
#check canonicalBoolModel.definitions
#check canonicalBoolModel.headers
#check canonicalEliminationLevelMapping

example : CanonicalAnnotationConstants canonicalAnnotationModel :=
  canonicalAnnotationModel.constants

example : CanonicalAnnotationDefinitions canonicalAnnotationModel :=
  canonicalAnnotationModel.definitions

example : boolInductDecl.HeadersWF canonicalBoolHeaderModel := by
  exact boolInductDecl.headersWF.mono
    (VEnv.addInductHeaders.le canonicalBoolHeaderModel.added)

example : boolInductDecl.HeadersWF canonicalBoolModel := by
  exact (boolInductDecl.headersWF.mono
    (VEnv.addInductHeaders.le canonicalBoolHeaderModel.added)).mono
      (VEnv.addConstructorHeaders.le canonicalBoolModel.added)

example : CanonicalAnnotationConstants canonicalBoolModel :=
  canonicalBoolModel.constants

example : CanonicalAnnotationDefinitions canonicalBoolModel :=
  canonicalBoolModel.definitions

example (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) (level : Level)
    (lparams : reader.lparams = [])
    (result : getElimLevel stats types reader = .ok level) :
    (getRecLevelParams level reader.lparams).Nodup ∧
      VLevel.ofLevel (getRecLevelParams level reader.lparams) level =
        some (if level.isParam then .param 0 else .zero) :=
  canonicalEliminationLevelMapping lparams result

example :
    (canonicalBoolModel : VEnv).constants ``Bool =
        some ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) ∧
      (canonicalBoolModel : VEnv).constants ``Bool.false =
        some ({ uvars := 0, type := .const ``Bool [] } : VConstant) ∧
      (canonicalBoolModel : VEnv).constants ``Bool.true =
        some ({ uvars := 0, type := .const ``Bool [] } : VConstant) :=
  canonicalBoolModel.headers

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical model receipt is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical model receipt proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical model receipt has an admission: {name}"

run_meta
  for theoremName in [``canonicalAnnotationModel.constants,
      ``canonicalAnnotationModel.definitions, ``canonicalBoolHeaderModel.added,
      ``canonicalBoolModel.added, ``canonicalBoolModel.constants,
      ``canonicalBoolModel.definitions, ``canonicalBoolModel.headers,
      ``canonicalEliminationLevelMapping] do
    auditTheorem theoremName
  let headerModel : VEnv := canonicalBoolHeaderModel
  let constructorModel : VEnv := canonicalBoolModel
  unless (headerModel.constants ``Bool).isSome do
    throwError "canonical Bool header model omitted Bool"
  unless (constructorModel.constants ``Bool.false).isSome ∧
      (constructorModel.constants ``Bool.true).isSome do
    throwError "canonical Bool constructor model omitted a constructor"
  logInfo "canonical annotation/model receipts verified"

end PrimitiveInductiveModelTest
