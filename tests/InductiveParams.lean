import Lean4Lean.Verify.InductiveParams
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamsTest

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment)
    (state : State) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamPrefix numParams type remainder params →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.prefix type numParams next env state post hnext

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamPrefix numParams type result.1.2.1 result.1.2.2 :=
  withParams.getPrefix type numParams env state

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.2.2.size = numParams ∧
        ∀ param ∈ result.1.2.2, param.isFVar = true :=
  (withParams.getPrefix type numParams env state).mono fun _ hprefix => ⟨hprefix.1, hprefix.2.2⟩

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment) (state : State) :
    (withParams type numParams next env state).WF fun _ =>
      numParams ≤ AddInductive.declareConstructors.arity 0 type :=
  withParams.paramArity type numParams next env state

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment) (state : State)
    (hsmall : AddInductive.declareConstructors.arity 0 type < numParams) :
    withParams type numParams next env state = .error
      (.other "invalid inductive datatype declaration, incorrect number of parameters") :=
  withParams.reject_of_arity_lt type numParams next env state hsmall

example (name : Name) (levels : List Level)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment) (state : State) :
    withParams (.const name levels) 1 next env state = .error
      (.other "invalid inductive datatype declaration, incorrect number of parameters") :=
  withParams.reject_of_arity_lt (.const name levels) 1 next env state
    (by simp [AddInductive.declareConstructors.arity])

example (fuel numParams : Nat) (type : InductiveType) (types : List InductiveType)
    (env : Kernel.Environment) (state : State)
    (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    ElimNestedInductive.run fuel numParams (type :: types) env state = .error
      (.other "invalid inductive datatype declaration, incorrect number of parameters") :=
  ElimNestedInductive.run.reject_of_paramArity fuel numParams type types env state hsmall

example (env : Kernel.Environment) (lparams : List Name) (numParams : Nat)
    (type : InductiveType) (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    Lean4Lean.Environment.addInductive env lparams numParams (type :: types) isUnsafe allowPrimitive
      fuel = .error (.other "invalid inductive datatype declaration, incorrect number of parameters") :=
  Lean4Lean.Environment.addInductive.reject_of_paramArity env lparams numParams type types isUnsafe
    allowPrimitive fuel hsmall

example (env : Kernel.Environment) (lparams : List Name) (numParams : Nat)
    (type : InductiveType) (types : List InductiveType) (isUnsafe check : Bool) (fuel : FuelConfig) :
    (Lean4Lean.addDecl env (.inductDecl lparams numParams (type :: types) isUnsafe) check fuel).WF
      fun _ => numParams ≤ AddInductive.declareConstructors.arity 0 type.type :=
  Lean4Lean.addDecl.inductiveParamArity env lparams numParams type types isUnsafe check fuel

example (env result : Kernel.Environment) (lparams : List Name) (numParams : Nat)
    (type : InductiveType) (types : List InductiveType) (isUnsafe check : Bool) (fuel : FuelConfig)
    (hsmall : AddInductive.declareConstructors.arity 0 type.type < numParams) :
    Lean4Lean.addDecl env (.inductDecl lparams numParams (type :: types) isUnsafe) check fuel ≠
      .ok result :=
  Lean4Lean.addDecl.reject_inductive_of_paramArity env result lparams numParams type types isUnsafe
    check fuel hsmall

private def checkPrefix (env : Kernel.Environment) (state : State) (type : Expr)
    (numParams : Nat) (accepted : Bool) (remainderArity : Nat := 0) : MetaM Unit := do
  let result := withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
    env state
  unless result.isOk == accepted do throwError "incorrect syntactic parameter-prefix outcome"
  match result with
  | .error (.other message) =>
    unless message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "incorrect parameter-prefix diagnostic"
  | .error _ => throwError "unexpected parameter-prefix error"
  | .ok ((lctx, remainder, params), final) =>
    unless params.size == numParams && params.all Expr.isFVar && lctx.numIndices == numParams &&
        AddInductive.declareConstructors.arity 0 remainder == remainderArity &&
        AddInductive.declareConstructors.arity 0 type == numParams + remainderArity do
      throwError "incorrect parameter-prefix statistics"
    let expected := (List.range numParams).map fun index =>
      Expr.fvar ⟨.num state.ngen.namePrefix (state.ngen.idx + index)⟩
    unless params.toList == expected && final.ngen.namePrefix == state.ngen.namePrefix &&
        final.ngen.idx == state.ngen.idx + numParams && final.lvls == state.lvls &&
        final.nestedAux == state.nestedAux && final.nextIdx == state.nextIdx &&
        final.newTypes.map (·.name) == state.newTypes.map (·.name) do
      throwError "parameter prefix changed unrelated state or fresh-name order"

private def checkFrontendRejection (env : Kernel.Environment) (type : Expr)
    (numParams : Nat) (isUnsafe check : Bool) (fuel : FuelConfig) : MetaM Unit := do
  let declaration := Declaration.inductDecl [] numParams
    [{ name := `ParameterGuard, type, ctors := [] }] isUnsafe
  match Lean4Lean.addDecl env declaration check fuel with
  | .error (.other message) =>
    unless message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected full-frontend prefix rejection: {message}"
  | _ => throwError "full frontend bypassed the parameter-prefix guard"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound, ``Expr.instantiate1_eq].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``withParams.prefix, ``withParams.getPrefix, ``withParams.paramArity,
      ``withParams.reject_of_arity_lt, ``ElimNestedInductive.run.reject_of_paramArity,
      ``Lean4Lean.Environment.addInductive.reject_of_paramArity,
      ``Lean4Lean.addDecl.inductiveParamArity, ``Lean4Lean.addDecl.reject_inductive_of_paramArity] do
    audit theoremName
  let env := (← Lean.getEnv).toKernelEnv
  let sortType := Expr.sort (.succ .zero)
  let two := Expr.forallE `parameter sortType
    (.forallE `value (.bvar 0) sortType .strictImplicit) .implicit
  let hidden := Expr.forallE `parameter sortType (.const `HiddenTail []) .default
  let beta := Expr.app (.lam `unused sortType two .default) (.const ``Nat [])
  let letType := Expr.letE `family (.sort (.succ (.succ .zero))) two (.bvar 0) false
  let states : List State := [
    { lvls := [], newTypes := #[] },
    { ngen := { namePrefix := `SeededParams, idx := 11 }, lvls := [.param `u],
      nestedAux := #[(.const ``Nat [], `StoredAux)], nextIdx := 7,
      newTypes := #[{ name := `ExistingHeader, type := sortType, ctors := [] }] }]
  for state in states do
    checkPrefix env state sortType 0 true
    checkPrefix env state sortType 1 false
    checkPrefix env state two 0 true 2
    checkPrefix env state two 1 true 1
    checkPrefix env state two 2 true
    checkPrefix env state two 3 false
    checkPrefix env state hidden 1 true
    checkPrefix env state hidden 2 false
    for wrapped in [Expr.const `HiddenParameter [], .mdata {} two, beta, letType] do
      checkPrefix env state wrapped 0 true
      checkPrefix env state wrapped 1 false
  for isUnsafe in [false, true] do
    for check in [false, true] do
      for fuel in [({} : FuelConfig), { inductiveFuel := 0 }] do
        checkFrontendRejection env (.const ``Nat []) 1 isUnsafe check fuel
        checkFrontendRejection env hidden 2 isUnsafe check fuel

end InductiveParamsTest
