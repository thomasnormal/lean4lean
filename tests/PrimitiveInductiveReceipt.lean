import Lean4Lean.Verify.Inductive
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

run_meta
  let theoremName := ``Environment.checkPrimitiveInductive.toVDecl_WF
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then throwError "primitive frontend receipt is an axiom"
  let some proof := information.value? | throwError "primitive frontend receipt proof missing"
  if proof.hasSorry then throwError "primitive frontend receipt has an admission"
  let baseline ← collectAxioms ``Environment.checkPrimitiveInductive.toVDecl
  let axioms ← collectAxioms theoremName
  for axiomName in axioms do
    unless baseline.contains axiomName do
      throwError "primitive frontend receipt has unexpected dependency: {axiomName}"
  logInfo m!"primitive checker success is theorem-backed through VDecl/header translation; dependencies = {repr axioms}"

end PrimitiveInductiveReceiptTest
