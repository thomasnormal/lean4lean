import Lean4Lean.Verify.InductiveNestedGuard
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive
namespace InductiveNestedGuardTest

inductive IndexedFamily (element : Type) : Nat → Type where
  | nil : IndexedFamily element 0

example (type : Expr) (env : Kernel.Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned => returned.2 = state :=
  isNestedInductiveApp?.frame type env state

example (type : Expr) (env : Kernel.Environment) (state : State) :
    (isNestedInductiveApp? type env state).WF fun returned =>
      returned.2 = state ∧ ∀ info, returned.1 = some info →
        (mkAppRange type.getAppFn 0 info.numParams type.getAppArgs).looseBVarRange' = 0 :=
  isNestedInductiveApp?.prefixScope type env state

private def parameterType (numParams : Nat) : Expr :=
  (List.range numParams).foldr (fun index result =>
    .forallE (Name.mkNum `parameter index) (.sort (.succ .zero)) result .implicit)
    (.sort (.succ .zero))

private def scopedArgs (family : Expr) : List Expr :=
  let sortType := Expr.sort (.succ .zero)
  let payload := Expr.fvar ⟨`UnrelatedFreeVariable⟩
  [.app family sortType, .app family (.const ``Nat []), .app family payload,
    .app family (.mvar ⟨`UnrelatedMetavariable⟩), .app family (.lit (.natVal 3)),
    .app family (.app payload payload),
    .lam `bound sortType (.app family (.bvar 0)) .default,
    .forallE `bound sortType (.app family (.bvar 0)) .implicit,
    .letE `bound sortType payload (.app family (.bvar 0)) false,
    .mdata {} (.app family payload), .proj `UncheckedProjection 0 (.app family payload),
    .lam `outer sortType
      (.forallE `inner (.bvar 0) (.app family (.bvar 1)) .default) .default]

private def sameState (expected actual : State) : Bool :=
  expected.ngen.namePrefix == actual.ngen.namePrefix && expected.ngen.idx == actual.ngen.idx &&
    expected.lvls == actual.lvls && expected.nextIdx == actual.nextIdx &&
    expected.nestedAux == actual.nestedAux &&
    expected.newTypes.map (·.name) == actual.newTypes.map (·.name)

private def checkCase (env : Kernel.Environment) (state : State) (container : Name)
    (numContainerParams : Nat) (sourceParams : Array Expr) (target : Result)
    (arg expectedArg : Expr) : MetaM Unit := do
  let args := (List.replicate numContainerParams arg).toArray
  let type := mkAppN (.const container []) args
  let .ok (selected, after) := isNestedInductiveApp? type env state
    | throwError "clean nested guard unexpectedly rejects"
  unless sameState state after do throwError "nested guard modifies its preprocessing state"
  match selected with
  | none =>
    unless numContainerParams == 0 do throwError "nonempty nested prefix was not recognized"
  | some info =>
    unless info.numParams == numContainerParams && !arg.hasLooseBVars do
      throwError "nested guard changed parameter count or accepted a loose parameter"
    let paramPrefix := mkAppRange type.getAppFn 0 info.numParams type.getAppArgs
    unless paramPrefix.looseBVarRange' == 0 && !paramPrefix.hasLooseBVars do
      throwError "nested guard failed its scoped-prefix contract"
    let .ok (rebound, finalState) := replaceParams target.params paramPrefix sourceParams env after
      | throwError "guarded prefix rebinding failed"
    let expected := mkAppN (.const container [])
      (List.replicate numContainerParams expectedArg).toArray
    unless rebound == expected && sameState state finalState do
      throwError "guarded rebinding changed syntax or preprocessing state"
    unless !(target.openAux (rebound.abstract target.params)).hasLooseBVars do
      throwError "guarded rebinding/final abstraction did not discharge auxiliary scope"

private def checkLooseParams (env : Kernel.Environment) (state : State) (container : Name)
    (numParams : Nat) (family : Expr) : MetaM Unit := do
  if numParams == 0 then return
  for index in [0, numParams / 2, numParams - 1] do
    let args := (List.replicate numParams family).toArray.set! index (.app family (.bvar 0))
    match isNestedInductiveApp? (mkAppN (.const container []) args) env state with
    | .error (.other message) =>
      unless message == s!"invalid nested inductive datatype '{container}', nested inductive datatypes parameters cannot contain local variables." do
        throwError "loose nested parameter changed its diagnostic"
    | _ => throwError "nested guard did not reject a loose parameter at index {index}"

private def checkNone (env : Kernel.Environment) (state : State) (type : Expr) : MetaM Unit := do
  let .ok (none, after) := isNestedInductiveApp? type env state
    | throwError "non-nested/unsupported guard input changed behavior"
  unless sameState state after do throwError "none-result guard modifies preprocessing state"

private def checkContext (env : Kernel.Environment) (container : Name) (numContainerParams : Nat)
    (numParams : Nat) (generator : NameGenerator) : MetaM Unit := do
  let header := parameterType numParams
  let familyType : InductiveType := { name := `GuardNewFamily, type := header, ctors := [] }
  let state : State := {
    ngen := generator, lvls := [], nextIdx := 7, newTypes := #[familyType],
    nestedAux := #[(.const ``Nat [], `StoredAux)] }
  let .ok ((_, _, sourceParams), _) := withParams header numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state
    | throwError "guard fixture source parameter extraction failed"
  let .ok target := StateT.run' (ElimNestedInductive.run ({} : FuelConfig).inductiveFuel
      numParams [familyType] env) {
        ngen := { namePrefix := `GuardTarget, idx := generator.idx + 100 },
        lvls := [], newTypes := #[familyType] }
    | throwError "guard fixture target preprocessing failed"
  let family := mkAppN (.const familyType.name []) sourceParams
  let targetFamily := mkAppN (.const familyType.name []) target.params
  for (arg, expected) in (scopedArgs family).zip (scopedArgs targetFamily) do
    checkCase env state container numContainerParams sourceParams target arg expected
  checkLooseParams env state container numContainerParams family
  let partialArgs := (List.replicate (numContainerParams - 1) (.app family (.bvar 0))).toArray
  checkNone env state (mkAppN (.const container []) partialArgs)

private def checkBoundaries (env : Kernel.Environment) : MetaM Unit := do
  let familyType : InductiveType := { name := `GuardNewFamily, type := .sort (.succ .zero), ctors := [] }
  let state : State := { lvls := [], newTypes := #[familyType] }
  let family := Expr.const familyType.name []
  for type in [Expr.const ``List [.zero], .app (.fvar ⟨`UnknownHead⟩) family,
      .app (.const `UnknownContainer []) family] do
    checkNone env state type
  checkNone env { state with newTypes := #[] } (mkApp (.const ``List [.zero]) (.app family (.bvar 0)))
  checkNone env state (mkApp (.const ``List [.zero]) (.bvar 0))
  checkNone env state (mkApp (.const (Name.mkNum `GuardContainer 0) []) family)
  let indexed := mkAppN (.const ``IndexedFamily []) #[family, .bvar 0]
  let .ok (some info, after) := isNestedInductiveApp? indexed env state
    | throwError "loose index was incorrectly treated as a loose parameter"
  unless info.numParams == 1 && indexed.hasLooseBVars && sameState state after &&
      !(mkAppRange indexed.getAppFn 0 info.numParams indexed.getAppArgs).hasLooseBVars do
    throwError "guard scope must apply only to the parameter prefix, not the entire application"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta do
  for theoremName in [``isNestedInductiveApp?.scope, ``isNestedInductiveApp?.frame] do
    audit theoremName []
  audit ``NestedAppScope.argRange [``Expr.looseBVarRange_eq]
  let rangeInterfaces := [``Expr.looseBVarRange_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  for theoremName in [``NestedAppScope.prefixRange, ``isNestedInductiveApp?.prefixScope,
      ``isNestedInductiveApp?.prefixScopeFlag] do
    audit theoremName rangeInterfaces
  audit ``isNestedInductiveApp?.checkedRebinding
    (rangeInterfaces ++ [``Expr.abstract_eq, ``Expr.instantiate_eq, ``Expr.instantiateRev_eq])
  let mut env ← Lean.getEnv
  for numContainerParams in [0, 1, 2, 3, 31, 32, 33, 65] do
    let container := Name.mkNum `GuardContainer numContainerParams
    let indType : InductiveType := { name := container, type := parameterType numContainerParams, ctors := [] }
    let .ok added := env.addDeclCore 0 (.inductDecl [] numContainerParams [indType] false) none
      | throwError "native validation rejected the closed guard-container declaration"
    env := added
    for generator in [NameGenerator.mk `_nested_fresh 0, { namePrefix := `GuardSource, idx := 17 }] do
      for numParams in [0, 1, 2, 33] do
        checkContext env.toKernelEnv container numContainerParams numParams generator
  checkBoundaries env.toKernelEnv
  logInfo "checked seven proof audits, 768 guard/rebinding cases (672 accepts/96 none), 168 loose-parameter rejections, 64 arity-boundary none cases, and seven classification/index boundaries"

end InductiveNestedGuardTest
