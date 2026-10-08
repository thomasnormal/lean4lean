import Lean4Lean.Verify.InductiveNestedScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive

namespace InductiveNestedScopeTest

inductive NestedTree (element : Type universeLevel) where
  | node : element → List (NestedTree element) → NestedTree element

def NestedTree.leaf (value : element) : NestedTree element := .node value []

example (value : element) : NestedTree.leaf value = .node value [] := rfl

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.lctx.toList.map LocalDecl.toExpr = result.params.toList.reverse :=
  (ElimNestedInductive.run.paramsValid_run' fuel numParams types env state).mono
    fun _ hvalid => hvalid.2.context.decls

example (result : Result) (numParams : Nat) (type : Expr)
    (hvalid : ParamValidity numParams result.lctx result.params)
    (htype : type.looseBVarRange' ≤ numParams) :
    (result.openAux type).hasLooseBVars = false :=
  result.openAux_scopeFlag numParams type hvalid htype

private def minimalType : InductiveType :=
  let name := `NestedScopeDatatype
  let sortType := Expr.sort (.succ .zero)
  let family := mkApp (.const name []) (.bvar 0)
  let domain := mkApp (.const ``List [.zero]) family
  let header := Expr.forallE `A sortType sortType .implicit
  let ctorType := Expr.forallE `A sortType
    (.forallE `field domain (mkApp (.const name []) (.bvar 1)) .default) .implicit
  { name, type := header, ctors := [{ name := name ++ `mk, type := ctorType }] }

private def checkStages (env : Lean.Environment) : MetaM Unit := do
  let indType := minimalType
  unless (env.addDeclCore 0 (.inductDecl [] 1 [indType] false) none).isOk do
    throwError "minimal nested source failed native validation"
  let fuel : FuelConfig := {}
  let .ok result := StateT.run' (ElimNestedInductive.run fuel.inductiveFuel 1 [indType]
      env.toKernelEnv) { lvls := [], newTypes := #[indType] }
    | throwError "minimal nested source failed preprocessing"
  unless result.aux2nested.size == 1 do
    throwError "minimal source did not generate one nested auxiliary"
  let .ok added := AddInductive.run 1 result.types result.aux2nested.size
      { env := env.toKernelEnv, allowPrimitive := false, lparams := [], safety := .safe, fuel }
    | throwError "minimal nested source failed the staged inductive checker"
  let params := result.params
  unless params == result.lctx.getFVars do
    throwError "retained parameters differ from their chronological context"
  result.aux2nested.forM fun _ auxiliary => do
    unless auxiliary.hasLooseBVars do
      throwError "auxiliary fixture no longer isolates an abstract parameter"
    let raw := TypeChecker.M.run added (safety := .safe) (lctx := result.lctx)
        (lparams := []) (fuel := fuel) do
      TypeChecker.checkType auxiliary
    match raw with
    | .error (.other message) =>
      unless message == "type checker does not support loose bound variables, replace them with free variables before invoking it" do
        throwError "unexpected raw-auxiliary diagnostic: {message}"
    | _ => throwError "raw auxiliary did not reproduce the scope rejection"
    let opened := result.openAux auxiliary
    unless !opened.hasLooseBVars do
      throwError "opening the actual parameters left loose bound variables"
    unless (TypeChecker.M.run added (safety := .safe) (lctx := result.lctx)
        (lparams := []) (fuel := fuel) do
        TypeChecker.checkType opened).isOk do
      throwError "opened auxiliary failed type checking"
    let outOfRange := TypeChecker.M.run added (safety := .safe) (lctx := result.lctx)
        (lparams := []) (fuel := fuel) do
      TypeChecker.checkType (result.openAux (.bvar result.nparams))
    match outOfRange with
    | .error (.other message) =>
      unless message == "type checker does not support loose bound variables, replace them with free variables before invoking it" do
        throwError "unexpected out-of-range auxiliary diagnostic: {message}"
    | _ => throwError "opening erased the out-of-range scope rejection"
  unless (Lean4Lean.addDecl env.toKernelEnv (.inductDecl [] 1 [indType] false)).isOk do
    throwError "valid minimal nested source failed the frontend"

private def parameterBinders (numParams : Nat) (level : Level) (body : Expr) : Expr :=
  (List.range numParams).foldr (fun index result =>
    .forallE (Name.mkNum `parameter index) (.sort (.succ level)) result .implicit) body

private def nestedDomain (shape : Nat) (level : Level) (family : Expr) : Expr :=
  match shape with
  | 0 => mkApp (.const ``List [level]) family
  | 1 => mkApp (.const ``Option [level]) family
  | _ => mkApp (.const ``List [level]) (mkApp (.const ``Option [level]) family)

private def fixture (numParams shape : Nat) (level : Level) : InductiveType :=
  let name := `NestedScopeMatrix
  let family offset := mkAppN (.const name (if level == .zero then [] else [level]))
    ((List.range numParams).map fun index => Expr.bvar (numParams - 1 - index + offset)).toArray
  let domain := nestedDomain shape level (family 0)
  let ctorType := parameterBinders numParams level
    (.forallE `field domain (family 1) .default)
  { name, type := parameterBinders numParams level (.sort (.succ level)),
    ctors := [{ name := name ++ `mk, type := ctorType }] }

private def dependentFixture (shape : Nat) (level : Level) : InductiveType :=
  let name := `NestedScopeDependent
  let family offset := mkAppN (.const name (if level == .zero then [] else [level]))
    #[.bvar (1 + offset), .bvar offset]
  let binders body := Expr.forallE `A (.sort (.succ level))
    (.forallE `value (.bvar 0) body .implicit) .implicit
  let domain := nestedDomain shape level (family 0)
  let ctorType := binders (.forallE `field domain (family 1) .default)
  { name, type := binders (.sort (.succ level)),
    ctors := [{ name := name ++ `mk, type := ctorType }] }

private def checkParameterScopes (env : Kernel.Environment) (indType : InductiveType)
    (numParams : Nat) (lparams : List Name) : MetaM Unit := do
  let .ok result := StateT.run' (ElimNestedInductive.run ({} : FuelConfig).inductiveFuel
      numParams [indType] env) { lvls := lparams.map .param, newTypes := #[indType] }
    | throwError "matrix fixture failed preprocessing"
  unless result.params.size == numParams && result.params == result.lctx.getFVars do
    throwError "preprocessing did not retain the chronological parameter array"
  result.aux2nested.forM fun _ auxiliary => do
    unless auxiliary.looseBVarRange' ≤ numParams && !(result.openAux auxiliary).hasLooseBVars do
      throwError "opening the retained parameters did not discharge auxiliary scope"
  unless (result.openAux (.bvar numParams)).hasLooseBVars do
    throwError "out-of-range auxiliary variable was incorrectly erased"

private def checkFrontendAgreement (env : Lean.Environment) (indType : InductiveType)
    (numParams : Nat) (lparams : List Name) (isUnsafe check : Bool) : MetaM Unit := do
  let decl := Declaration.inductDecl lparams numParams [indType] isUnsafe
  let .ok native := env.addDeclCore 0 decl none
    | throwError "nested matrix fixture failed native validation"
  let .ok checked := Lean4Lean.addDecl env.toKernelEnv decl check
    | throwError "native-accepted nested fixture failed lean4lean validation"
  for name in indType.name :: indType.ctors.map (·.name) do
    let some expected := native.find? name
      | throwError "native environment is missing a declaration"
    let some actual := checked.find? name
      | throwError "lean4lean environment is missing a declaration"
    unless expected.type == actual.type do
      throwError "restored nested declaration differs from native: {name}"

private def checkFixture (env : Lean.Environment) (indType : InductiveType)
    (numParams : Nat) (lparams : List Name) : MetaM Unit := do
  checkParameterScopes env.toKernelEnv indType numParams lparams
  for isUnsafe in [false, true] do
    for check in [false, true] do
      checkFrontendAgreement env indType numParams lparams isUnsafe check

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta do
  for theoremName in [``ElimNestedInductive.run.loop.frameWithParams,
      ``ParamContext.params_noLooseBVars] do
    audit theoremName []
  let contextInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  for theoremName in [``ElimNestedInductive.run.paramsValid,
      ``ElimNestedInductive.run.paramsValid_run'] do
    audit theoremName contextInterfaces
  let openingInterfaces := [``Expr.instantiate_eq, ``Expr.instantiateRev_eq]
  for theoremName in [``openParams_noLooseBVars, ``Result.openAux_noLooseBVars] do
    audit theoremName openingInterfaces
  audit ``Result.openAux_scopeFlag (``Expr.looseBVarRange_eq :: openingInterfaces)
  audit ``ElimNestedInductive.run.openAux_scope (contextInterfaces ++ openingInterfaces)
  let env ← Lean.getEnv
  checkStages env
  for level in [Level.zero, .param `u] do
    let lparams := if level == .zero then [] else [`u]
    for shape in [0, 1, 2] do
      for numParams in [0, 1, 2, 3, 4] do
        checkFixture env (fixture numParams shape level) numParams lparams
      checkFixture env (dependentFixture shape level) 2 lparams
  logInfo "checked eight proof audits, the isolated raw/opened boundary, 36 retained-context scope checks, and 144 native/frontend agreements"

end InductiveNestedScopeTest
