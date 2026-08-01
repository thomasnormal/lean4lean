import Lean4Lean.Verify.Environment
import Lean.Util.CollectAxioms

namespace RebasedPrimitiveGuardsTest
open Lean hiding Environment Exception
open Lean4Lean
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions
  Lean.Kernel.Environment.irBaseExts from Lean.Environment

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (value : DefinitionVal)
    (primitiveName : Kernel.Environment.primitives.contains value.name = true)
    (fuel : FuelConfig) :
    (checkDefinition environment value).WF
      (.mk' wellFormed .safe value.levelParams fuel) {} fun _ _ =>
        ∃ translated : VDefVal, value.safety = .safe ∧ value.levelParams = [] ∧
          Primitive.PrimitiveResult (models.venv .safe) value translated ∧
          translated.WF (models.venv .safe) ∧ environment.find? value.name = none :=
  (checkDefinition.WF_primitive wellFormed value primitiveName fuel).mono
    fun _ _ _ ⟨translated, result, _, _, _, _, bodyWellFormed, fresh⟩ =>
      ⟨translated, result.safe, result.no_level_params, result, bodyWellFormed, fresh⟩

example {environment : Kernel.Environment} {models : VEnvs}
    (wellFormed : models.WF environment) (value : DefinitionVal)
    (nonUnsafe : value.safety ≠ .unsafe)
    (primitiveName : Kernel.Environment.primitives.contains value.name = true)
    (fuel : FuelConfig) :
    (Lean4Lean.addDefinition environment value true fuel).WF fun result =>
      ∃ models' : VEnvs, models'.WF result ∧
        ∀ safety, models.venv safety ≤ models'.venv safety :=
  addDefinition.WF_primitive wellFormed value nonUnsafe primitiveName fuel

private def withoutConstant (environment : Kernel.Environment) (name : Name) :
    Kernel.Environment :=
  let constants := { environment.constants with
    map₁ := environment.constants.map₁.erase name
    map₂ := environment.constants.map₂.erase name }
  Lean.Kernel.Environment.mk constants environment.quotInit environment.diagnostics environment.const2ModIdx
    (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment)
    environment.header

private def tagCodomain : Expr → Expr
  | .forallE name domain body information =>
    .forallE name domain (tagCodomain body) information
  | expression => .mdata {} expression

private def primitiveControls : MetaM Unit := do
  let native := (← getEnv).toKernelEnv
  let some (.defnInfo addition) := native.find? ``Nat.add
    | throwError "native Nat.add definition absent"
  let emptySlot := withoutConstant native addition.name
  unless (emptySlot.find? addition.name).isNone do
    throwError "primitive fixture did not remove the old definition"
  let .forallE name domain body information := addition.type
    | throwError "native Nat.add header is not a function"
  let taggedType := Expr.forallE name (.mdata {} domain) body information
  unless !(taggedType == Primitive.eraseMData addition.type) do
    throwError "metadata fixture does not differ from the canonical header"
  for header in [addition.type, taggedType] do
    let declaration := { addition with type := header }
    let .ok added := Lean4Lean.addDefinition emptySlot declaration true {}
      | throwError "actual primitive frontend rejects a valid Nat.add header"
    let some (.defnInfo stored) := added.find? addition.name
      | throwError "actual primitive frontend does not install Nat.add"
    unless stored.type == header && stored.value == addition.value do
      throwError "actual primitive frontend changes the source declaration"
    for preservedName in [``Nat, ``Nat.zero, ``Nat.succ, ``Bool] do
      let some before := emptySlot.find? preservedName
        | throwError "primitive prefix control absent"
      let some after := added.find? preservedName
        | throwError "primitive frontend drops a prefix constant"
      unless before.type == after.type &&
          before.value? (allowOpaque := true) == after.value? (allowOpaque := true) do
        throwError "primitive frontend changes a prefix type/value"
  for invalid in [{ addition with safety := .partial },
      { addition with safety := .unsafe }, { addition with levelParams := [`extra] },
      { addition with type := tagCodomain addition.type },
      { addition with value := q(fun left (_ : Nat) => left) }] do
    unless !(Lean4Lean.addDefinition emptySlot invalid true {}).isOk do
      throwError "actual primitive frontend accepts an invalid header or recurrence"
  let wrongBody := { addition with value := q(Bool.true) }
  match Lean4Lean.addDefinition emptySlot wrongBody true {} with
  | .error (.declTypeMismatch _ _ _) => pure ()
  | .error error => throwError "unexpected body-check diagnostic: {error.toMessageData (← getOptions)}"
  | .ok _ => throwError "actual primitive frontend accepts an ill-typed body"
  unless !(Lean4Lean.addDefinition emptySlot addition true { recDepth := 0 }).isOk do
    throwError "actual primitive frontend unexpectedly succeeds at zero callback fuel"
  for primitiveName in [``Char.ofNat, ``String.ofList] do
    let some (.defnInfo definition) := native.find? primitiveName
      | throwError "native literal primitive definition absent: {primitiveName}"
    let fresh := withoutConstant native primitiveName
    let .forallE name domain body information := definition.type
      | throwError "native literal primitive header is not a function: {primitiveName}"
    let tagged := Expr.forallE name (.mdata {} domain) body information
    for header in [definition.type, tagged] do
      unless (Lean4Lean.addDefinition fresh { definition with type := header } true {}).isOk do
        throwError "actual literal primitive frontend rejects a valid header: {primitiveName}"
    for invalid in [{ definition with safety := .partial },
        { definition with levelParams := [`extra] },
        { definition with type := tagCodomain definition.type }] do
      unless !(Lean4Lean.addDefinition fresh invalid true {}).isOk do
        throwError "actual literal primitive frontend accepts an invalid header: {primitiveName}"
    if primitiveName == ``String.ofList then
      for missing in [``List.nil, ``List.cons] do
        unless !(Lean4Lean.addDefinition (withoutConstant fresh missing) definition true {}).isOk do
          throwError "actual String.ofList frontend ignores a missing constructor dependency: {missing}"
  logInfo "actual Nat.add/Char.ofNat/String.ofList checking accepts domain metadata, rejects misplaced metadata and safety/universe violations, checks String constructor dependencies, rejects a false recurrence, preserves source/prefix data and diagnoses the body before primitive probes"

private def arithmeticControls : MetaM Unit := do
  let native := (← getEnv).toKernelEnv
  let cases : List (Name × Nat) := [(``Nat.add, 48 + 18), (``Nat.sub, 48 - 18),
    (``Nat.mul, 48 * 18), (``Nat.pow, 48 ^ 18), (``Nat.gcd, Nat.gcd 48 18),
    (``Nat.mod, 48 % 18), (``Nat.div, 48 / 18), (``Nat.land, Nat.land 48 18),
    (``Nat.lor, Nat.lor 48 18), (``Nat.xor, Nat.xor 48 18),
    (``Nat.shiftLeft, Nat.shiftLeft 48 18), (``Nat.shiftRight, Nat.shiftRight 48 18)]
  let fuel : FuelConfig := { recDepth := 8, whnf := 8, whnfEager := 8 }
  for (name, expected) in cases do
    let expression := mkApp2 (.const name []) (mkNatLit 48) (mkNatLit 18)
    let .ok (some result) := (TypeChecker.RecM.run
        (TypeChecker.Inner.reduceNat expression)).run native (fuel := fuel)
      | throwError "direct native arithmetic reduction fails: {name}"
    unless result.rawNatLit? == some expected do
      throwError "direct native arithmetic result differs: {name}"
  for (name, left, right, expected) in [(``Nat.beq, 48, 18, false), (``Nat.beq, 18, 18, true),
      (``Nat.ble, 48, 18, false), (``Nat.ble, 18, 48, true), (``Nat.ble, 18, 18, true)] do
    let expression := mkApp2 (.const name []) (mkNatLit left) (mkNatLit right)
    let .ok (some result) := (TypeChecker.RecM.run
        (TypeChecker.Inner.reduceNat expression)).run native (fuel := fuel)
      | throwError "direct native arithmetic predicate fails: {name}"
    unless result == mkConst (if expected then ``Bool.true else ``Bool.false) do
      throwError "direct native arithmetic predicate differs: {name}"
  logInfo "all fourteen direct binary native arithmetic/predicate branches return the expected result without fallback unfolding"

run_meta
  let allowed ← collectAxioms ``Lean4Lean.TypeChecker.checkType.WF
  for theoremName in #[``checkDefinition.WF_primitive, ``addDefinition.WF_primitive,
      ``Primitive.checkCharOfNat.WF, ``Primitive.checkStringOfList.WF,
      ``TypeChecker.Inner.reduceNat.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "primitive theorem is an axiom: {theoremName}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "primitive theorem proof absent: {theoremName}"
    if proof.hasSorry then throwError "primitive theorem has a direct admission: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "primitive dependency outside the checker baseline: {dependency} in {theoremName}"
    logInfo m!"{theoremName}: {repr dependencies}"
  primitiveControls
  arithmeticControls

end RebasedPrimitiveGuardsTest
