import Lean4Lean.Verify.ConstructorDomainLookup
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive Lean4Lean.TypeChecker
open private Lean.Kernel.Environment.add from Lean.Environment

namespace ConstructorDomainLookupTest

private def native := Kernel.Environment.empty `ConstructorDomainLookupTest
private def identifier : FVarId := ⟨`bridge⟩
private def localType : Expr := q(Prop)
private def reader : Lean4Lean.AddInductive.Context := {
  env := native,
  lctx := LocalContext.mkLocalDecl ({} : LocalContext) identifier `argument localType .default,
  lparams := [], safety := .safe, allowPrimitive := false }

private def audit (name : Name) (expected : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == expected.length && axioms.all expected.contains do
    throwError "{name}: unexpected dependencies: {repr axioms}"
  logInfo m!"{name}: axioms = {repr axioms}"

run_meta
  audit ``Lean4Lean.AddInductive.getType_fvar_eq_inferFVar
    [``propext, ``Quot.sound, ``Classical.choice]
  let context : TypeChecker.Context := {
    env := native, lctx := reader.lctx, safety := reader.safety,
    lparams := reader.lparams, fuel := reader.fuel }
  let .ok nativeType := getType (.fvar identifier) reader
    | throwError "native getType lookup failed"
  let .ok inferredType := TypeChecker.Inner.inferFVar context identifier
    | throwError "native inferFVar lookup failed"
  unless nativeType == inferredType && nativeType == localType do
    throwError "native getType/inferFVar bridge returned the wrong type"
  logInfo "one constructor-domain getType/inferFVar bridge control"

end ConstructorDomainLookupTest
