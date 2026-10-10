import Lean4Lean.Verify.InductiveConstructorDomainReceipts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker

theorem getType_fvar_eq_inferFVar (reader : Context) (identifier : FVarId)
    (declaration : LocalDecl) (lookup : reader.lctx.find? identifier = some declaration) :
    getType (.fvar identifier) reader =
      TypeChecker.Inner.inferFVar
        { env := reader.env, lctx := reader.lctx, safety := reader.safety,
          lparams := reader.lparams, fuel := reader.fuel } identifier := by
  change Except.ok (reader.lctx.get! identifier |>.type) = _
  simp [TypeChecker.Inner.inferFVar, LocalContext.get!, lookup]
  rfl

end Lean4Lean.AddInductive
