import Lean4Lean.Verify.Inductive
import Lean4Lean.Inductive.Add
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveHeadersTest

private def headers : List VInductiveType := boolInductDecl.types ++ natInductDecl.types

private def stagedEnv : VEnv := (VEnv.empty.addInductHeaders headers).getD VEnv.empty

example : VEnv.empty.addInductHeaders headers = some stagedEnv := rfl

example : stagedEnv.Ordered := by
  apply VEnv.addInductHeaders.ordered VEnv.Ordered.empty ?_ (show
    VEnv.empty.addInductHeaders headers = some stagedEnv from rfl)
  intro header hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact (boolInductDecl.headersWF header hmem).2
  · exact (natInductDecl.headersWF header hmem).2

example : stagedEnv.constants ``Bool = some { uvars := 0, type := .sort (.succ .zero) } := rfl
example : stagedEnv.constants ``Nat = some { uvars := 0, type := .sort (.succ .zero) } := rfl

example : [``Bool.false, ``Bool.true, ``Nat.zero, ``Nat.succ].any
    (fun name => (stagedEnv.constants name).isSome) = false := by decide

example : (VEnv.empty.addInductHeaders (headers ++ headers)).isSome = false := by decide
example : (stagedEnv.addInductHeaders boolInductDecl.types).isSome = false := by decide
example : (stagedEnv.addInductHeaders natInductDecl.types).isSome = false := by decide
example : VEnv.empty.addInductHeaders [] = some VEnv.empty := rfl

example (env env' : VEnv) (decl : VInductDecl) (hheaders : decl.HeadersWF env)
    (hordered : env.Ordered) (hadd : env.addInductHeaders decl.types = some env') :
    env'.Ordered :=
  VEnv.addInductHeaders.ordered hordered (fun header hmem => (hheaders header hmem).2) hadd

example (env env' : VEnv) (hadd : env.addInductHeaders headers = some env') :
    env'.defeqs = env.defeqs := VEnv.addInductHeaders.defeqs_eq hadd

private def polymorphicHeader : VInductiveType := {
  name := `Parametric
  uvars := 1
  type := .sort (.param 0)
  ctors := []
}

example : polymorphicHeader.toVConstant.WF VEnv.empty := ⟨_, .sort (by decide)⟩

example : ((VEnv.empty.addInductHeaders [polymorphicHeader]).getD VEnv.empty).Ordered := by
  apply VEnv.addInductHeaders.ordered VEnv.Ordered.empty ?_ (show
    VEnv.empty.addInductHeaders [polymorphicHeader] = some
      ((VEnv.empty.addInductHeaders [polymorphicHeader]).getD VEnv.empty) from rfl)
  intro header hmem
  simp only [List.mem_singleton] at hmem
  subst header
  exact ⟨_, .sort (by decide)⟩

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{theoremName}: unexpected axiom {axiomName}"

private def checkExecutableHeader (imported : Kernel.Environment) (typeName : Name) : MetaM Unit := do
  let some (.inductInfo info) := imported.find? typeName | throwError "missing {typeName}"
  let ctors ← info.ctors.mapM fun name => do
    let some (.ctorInfo ctor) := imported.find? name | throwError "missing {name}"
    pure ({ name := ctor.name, type := ctor.type } : Constructor)
  let type : InductiveType := { name := info.name, type := info.type, ctors }
  let stats : AddInductive.InductiveStats := {
    levels := [], resultLevel := .succ .zero, nindices := #[0],
    indConsts := #[.const typeName []], params := #[], isNotZero := true }
  let ctx : AddInductive.Context := {
    env := Kernel.Environment.empty `InductiveHeadersTest,
    lparams := [], safety := .safe, allowPrimitive := true }
  let action := AddInductive.declareInductiveTypes stats 0 #[type] 0 false
  let .ok result := action ctx | throwError "failed to stage {typeName}"
  let some (.inductInfo registered) := result.find? typeName | throwError "missing staged header"
  unless registered.levelParams.isEmpty && registered.numParams == 0 && registered.numIndices == 0 &&
      registered.type == type.type && registered.ctors == info.ctors && registered.all == [typeName] &&
      !registered.isUnsafe do
    throwError "incorrect staged metadata for {typeName}"
  for name in info.ctors do
    if result.contains name then throwError "header staging installed constructor {name}"
  if (action { ctx with env := imported }).isOk then throwError "accepted duplicate {typeName}"
  if (action { ctx with allowPrimitive := false }).isOk then
    throwError "accepted {typeName} without primitive authorization"

run_meta
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [``VEnv.addInductHeaders.le, ``VEnv.addInductHeaders.constants,
      ``VEnv.addInductHeaders.defeqs_eq, ``VEnv.addInductHeaders.ordered,
      ``VInductDecl.HeadersWF.mono, ``boolInductDecl.headersWF, ``natInductDecl.headersWF] do
    audit theoremName standard
  audit ``Environment.PrimitiveInductiveDecl.toVDecl (standard ++ [``sorryAx])
  let translation := standard ++ [``sorryAx, ``Lean.Expr.eqv_eq,
    ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  audit ``Environment.checkPrimitiveInductive.toVDecl translation
  let imported := (← Lean.getEnv).toKernelEnv
  for typeName in [``Bool, ``Nat] do
    checkExecutableHeader imported typeName

end InductiveHeadersTest
