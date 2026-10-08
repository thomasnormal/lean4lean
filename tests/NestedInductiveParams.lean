import Lean4Lean.Verify.InductiveParams
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace NestedInductiveParamsTest

example (type : Expr) (numParams : Nat)
    (next mismatch : LocalContext → Expr → Array Expr → M α) :
    withParams type numParams (fun lctx remainder params =>
      if params.size == numParams then next lctx remainder params else mismatch lctx remainder params)
      = withParams type numParams next :=
  withParams.assert_size type numParams next mismatch

example [Inhabited α] (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) :
    withParams type numParams (fun lctx remainder params => do
      assert! params.size == numParams
      next lctx remainder params) = withParams type numParams next :=
  withParams.assert_size type numParams next _

example (ctor : Constructor) (numParams : Nat) (params : Array Expr) :
    withParams ctor.type numParams (fun lctx ctorType ctorParams => do
      assert! ctorParams.size == numParams
      return { ctor with
        type := lctx.mkForall ctorParams (← replaceAllNested lctx params ctorParams ctorType) }) =
    withParams ctor.type numParams (fun lctx ctorType ctorParams => do
      return { ctor with
        type := lctx.mkForall ctorParams (← replaceAllNested lctx params ctorParams ctorType) }) :=
  withParams.assert_size ctor.type numParams _ _

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Kernel.Environment) (state : State)
    (hsize : params.size = numParams) :
    (ElimNestedInductive.run.loop numParams lctx params index fuel env state).WF fun result =>
      result.1.nparams = numParams :=
  ElimNestedInductive.run.loop.paramCount numParams lctx params index fuel env state hsize

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.nparams = numParams :=
  ElimNestedInductive.run.paramCount fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.nparams = numParams :=
  ElimNestedInductive.run.paramCount_run' fuel numParams types env state

example (fuel numParams : Nat) (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams [] env state).WF fun result =>
      result.1.nparams = numParams :=
  ElimNestedInductive.run.paramCount fuel numParams [] env state

example (numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run 0 numParams types env state).WF fun result =>
      result.1.nparams = numParams :=
  ElimNestedInductive.run.paramCount 0 numParams types env state

private def parameterBinders (numParams : Nat) (body : Expr) : Expr :=
  (List.range numParams).foldr (fun index remainder =>
    .forallE (.num `parameter index) (.sort (.succ .zero)) remainder .implicit) body

private def familyApp (name : Name) (numParams offset : Nat) : Expr :=
  mkAppN (.const name []) ((List.range numParams).map fun index =>
    Expr.bvar (numParams - 1 - index + offset)).toArray

private def datatype (numParams : Nat) (nested : Bool) : InductiveType :=
  let name := if nested then `NestedParameterTree else `PlainParameterTree
  let domain := if nested then mkApp (.const ``List [.zero]) (familyApp name numParams 0)
    else if numParams = 0 then .const ``Nat [] else .bvar (numParams - 1)
  let type := parameterBinders numParams (.sort (.succ .zero))
  let ctorType := parameterBinders numParams
    (.forallE `field domain (familyApp name numParams 1) .default)
  { name, type, ctors := [{ name := name ++ `node, type := ctorType }] }

private def checkResultContext (env : Kernel.Environment) (state : State)
    (numParams : Nat) (types : List InductiveType) (result : Result) : MetaM Unit := do
  let header :: _ := types | throwError "successful preprocessing without a source header"
  let .ok ((lctx, _, params), _) :=
    withParams header.type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state | throwError "successful preprocessing without an extracted parameter context"
  let actual := result.lctx.decls.toList.filterMap id
  let expected := lctx.decls.toList.filterMap id
  let fields := fun (decl : LocalDecl) =>
    (decl.index, decl.toExpr, decl.userName, decl.type, decl.binderInfo, decl.kind,
      decl.isLet (allowNondep := true))
  unless actual.length == params.size && expected.length == params.size &&
      actual.map fields == expected.map fields do
    throwError "preprocessing changed the original extracted parameter declarations"

private def checkPreprocessing (env : Kernel.Environment) (state : State)
    (fuel numParams : Nat) (types : List InductiveType) (expected : Except String Nat)
    (addedAux : Nat := 0) : MetaM Unit := do
  match ElimNestedInductive.run fuel numParams types env state, expected with
  | .ok (result, final), .ok numTypes =>
    unless result.nparams == numParams && result.lctx.numIndices == numParams &&
        result.types.length == numTypes && final.newTypes.size == numTypes &&
        final.nestedAux.size == state.nestedAux.size + addedAux do
      throwError "incorrect nested preprocessing parameter count or auxiliary growth"
    checkResultContext env state numParams types result
    for type in result.types do
      unless numParams ≤ AddInductive.declareConstructors.arity 0 type.type do
        throwError "preprocessed header lost its parameter prefix"
      for ctor in type.ctors do
        unless numParams ≤ AddInductive.declareConstructors.arity 0 ctor.type do
          throwError "preprocessed constructor lost its parameter prefix"
  | .error (.other message), .error expectedMessage =>
    unless message == expectedMessage do
      throwError "unexpected nested preprocessing diagnostic: {message}"
  | _, _ => throwError "unexpected nested preprocessing outcome"

private def checkFixtures (env : Kernel.Environment) (seeded : Bool) : MetaM Unit := do
  let initial : State := if seeded then
    { ngen := { namePrefix := `NestedParamsSeed, idx := 13 }, lvls := [],
      nestedAux := #[(.const ``Nat [], `StoredAux)], nextIdx := 7, newTypes := #[] }
    else { lvls := [], newTypes := #[] }
  for numParams in [0, 1, 2] do
    let plain := datatype numParams false
    let nested := datatype numParams true
    let state := { initial with newTypes := #[plain] }
    checkPreprocessing env state 2 numParams [plain] (.ok 1)
    checkPreprocessing env state 1 numParams [plain]
      (.error "deep recursion: ElimNestedInductive.run.loop")
    checkPreprocessing env state 0 numParams [plain]
      (.error "deep recursion: ElimNestedInductive.run.loop")
    checkPreprocessing env { initial with newTypes := #[nested] } 3 numParams [nested] (.ok 2) 1
    checkPreprocessing env { initial with newTypes := #[nested] } 2 numParams [nested]
      (.error "deep recursion: ElimNestedInductive.run.loop")
    checkPreprocessing env initial 1 numParams [plain] (.ok 0)
    let extra := { plain with name := `ExtraParameterTree, ctors := [] }
    checkPreprocessing env { state with newTypes := state.newTypes.push extra }
      3 numParams [plain] (.ok 2)
    checkPreprocessing env initial 4 numParams []
      (.error "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.")
  for numParams in [1, 2] do
    let source := datatype numParams false
    let missingCtorType :=
      parameterBinders (numParams - 1) (familyApp source.name (numParams - 1) 0)
    let missingCtor : Constructor := { name := source.name ++ `missing, type := missingCtorType }
    let missing := { source with ctors := [missingCtor] }
    checkPreprocessing env { initial with newTypes := #[missing] } 3 numParams [missing]
      (.error "invalid inductive datatype declaration, incorrect number of parameters")
    let hiddenCtorType := Expr.mdata {}
      (parameterBinders numParams (familyApp source.name numParams 0))
    let hiddenCtor : Constructor := { name := source.name ++ `hidden, type := hiddenCtorType }
    let hidden := { source with ctors := [hiddenCtor] }
    checkPreprocessing env { initial with newTypes := #[hidden] } 3 numParams [hidden]
      (.error "invalid inductive datatype declaration, incorrect number of parameters")

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound, ``Expr.instantiate1_eq].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``withParams.assert_size, ``ElimNestedInductive.run.loop.paramCount,
      ``ElimNestedInductive.run.paramCount, ``ElimNestedInductive.run.paramCount_run'] do
    audit theoremName
  let env := (← Lean.getEnv).toKernelEnv
  checkFixtures env false
  checkFixtures env true

end NestedInductiveParamsTest
