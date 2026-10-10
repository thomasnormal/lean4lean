import Lean4Lean.Verify.InductiveValueFrame
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveValueFrameTest

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF
      (NativeValueFrame ctx.env) :=
  declareRecursors.preservesValues stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF (NativeValueFrame ctx.env) :=
  AddInductive.run.preservesValues nparams types numNested ctx hwf

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (hvalues : ∀ info, allowed info → info.value? = none) : NativeValueFrame original result :=
  trace.preservesValues hwf hvalues

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {info : ConstantInfo}
    (record : RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :
    info.value? = none := record.value?_eq_none

example (preprocessing : ElimNestedInductive.Result) (staged original : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hwf : original.constants.WF) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel original).WF
      fun result => NativeValueFrame original result.2 :=
  (restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel original).mono
    fun _ trace => trace.preservesValues hwf (fun _ record => record.value?_eq_none)

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hwf : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF
      (NativeValueFrame env) :=
  Lean4Lean.Environment.addInductive.safePreservesValues env lparams nparams types allowPrimitive fuel hwf

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hwf : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF
      (NativeValueFrame env) :=
  Lean4Lean.addDecl.safeInductivePreservesValues env lparams nparams types check fuel hwf

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hwf : env.constants.WF)
    (accepted : Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {name : Name} {info : ConstantInfo} {value : Expr}
    (lookup : result.constants.find? name = some info) (hvalue : info.value? = some value) :
    env.constants.find? name = some info :=
  (Lean4Lean.addDecl.safeInductivePreservesValues env lparams nparams types check fuel hwf
    result accepted).values lookup hvalue

private def retainedValue : DefinitionVal := {
  name := `InductiveRetainedValue, levelParams := [], type := .sort (.succ .zero),
  value := .sort .zero, hints := .abbrev, safety := .safe }

private def datatype (name : Name) (ctors : List Constructor) : InductiveType := {
  name, type := .sort (.succ .zero), ctors }

private def mutualTypes : List InductiveType := [
  datatype `ValueLeft [⟨`ValueLeft.unit, .const `ValueLeft []⟩,
    ⟨`ValueLeft.swap, .forallE `right (.const `ValueRight []) (.const `ValueLeft []) .default⟩],
  datatype `ValueRight [
    ⟨`ValueRight.wrap, .forallE `left (.const `ValueLeft []) (.const `ValueRight []) .default⟩]]

private def closeParams (count : Nat) (body : Expr) : Expr :=
  (List.range count).foldr (fun _ result => .forallE `A (.sort (.succ .zero)) result .default) body

private def family (name : Name) (count shift : Nat) : Expr :=
  mkAppN (.const name []) ((List.range count).toArray.map fun index => .bvar (count - 1 - index + shift))

private def nestedType (name : Name) (count : Nat) : InductiveType := {
  name, type := closeParams count (.sort (.succ .zero)), ctors := [{
    name := name ++ `mk
    type := closeParams count (.forallE `children
      (.app (.const ``List [.zero]) (family name count 0)) (family name count 1) .default) }] }

private def sameConstant : Option ConstantInfo → Option ConstantInfo → Bool
  | none, none => true
  | some (.axiomInfo first), some (.axiomInfo second) => first == second
  | some (.defnInfo first), some (.defnInfo second) => first == second
  | some (.thmInfo first), some (.thmInfo second) => first == second
  | some (.opaqueInfo first), some (.opaqueInfo second) => first == second
  | some (.quotInfo first), some (.quotInfo second) =>
    first.toConstantVal == second.toConstantVal && match first.kind, second.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | some (.inductInfo first), some (.inductInfo second) =>
    first.toConstantVal == second.toConstantVal && first.numParams == second.numParams &&
      first.numIndices == second.numIndices && first.all == second.all && first.ctors == second.ctors &&
      first.numNested == second.numNested && first.isRec == second.isRec &&
      first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive
  | some (.ctorInfo first), some (.ctorInfo second) => first == second
  | some (.recInfo first), some (.recInfo second) => first == second
  | _, _ => false

private def checkFrame (original result : Kernel.Environment) : MetaM Unit := do
  for (name, info) in original.constants.toList do
    unless sameConstant (some info) (result.find? name) do
      throwError "inductive registration changed old record {name}"
  for (name, info) in result.constants.toList do
    if info.value?.isSome then
      unless sameConstant (original.find? name) (some info) do
        throwError "inductive registration introduced a value record {name}"
  unless sameConstant (result.find? retainedValue.name) (some (.defnInfo retainedValue)) do
    throwError "inductive registration lost the seeded safe definition"
  let .ok reduced := Lean4Lean.TypeChecker.M.run result .safe {} [] {}
      (Lean4Lean.TypeChecker.whnf (.const retainedValue.name []))
    | throwError "retained delta reduction failed"
  unless reduced == retainedValue.value do throwError "retained delta reduction changed"

private def checkFrontend (env : Kernel.Environment) (nparams : Nat) (types : List InductiveType)
    (nested : Bool) : MetaM Unit := do
  unless ((← Lean.getEnv).addDeclCore 0 (.inductDecl [] nparams types false) none).isOk do
    throwError "value-frame fixture fails native kernel validation"
  let .ok preprocessing := inductivePreprocessing env [] nparams types {}
    | throwError "value-frame preprocessing failed"
  unless (preprocessing.aux2nested.size > 0) == nested do
    throwError "value-frame fixture reached the wrong restoration branch"
  let .ok allowPrimitive := Lean4Lean.Environment.checkPrimitiveInductive env [] nparams types false
    | throwError "value-frame primitive dispatch failed"
  for safety in [DefinitionSafety.safe, .unsafe] do
    let ctx := { inductiveScopeContext env [] allowPrimitive {} with safety }
    let .ok staged := AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size ctx
      | throwError "value-frame staged run failed"
    checkFrame env staged
    if nested && safety == .safe then
      let .ok (_, restored) := restoreInductiveEnvironment preprocessing staged types [] allowPrimitive {} env
        | throwError "value-frame explicit restoration failed"
      checkFrame env restored
  for check in [false, true] do
    let .ok result := Lean4Lean.addDecl env (.inductDecl [] nparams types false) check
      | throwError "value-frame public dispatch failed with check={check}"
    checkFrame env result
  let .ok result := Lean4Lean.Environment.addInductive env [] nparams types false allowPrimitive
    | throwError "value-frame public frontend failed"
  checkFrame env result

private def audit (theoremName : Name) (maps := true) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if maps then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``declareRecursors.preservesValues, ``AddInductive.run.preservesValues,
      ``FreshRegistrationTrace.preservesValues,
      ``Lean4Lean.Environment.addInductive.safePreservesValues,
      ``Lean4Lean.addDecl.safeInductivePreservesValues] do
    audit theoremName
  audit ``RestoredInductiveRecord.value?_eq_none false
  let imported := (← Lean.getEnv).toKernelEnv
  let .ok env := Lean4Lean.addDecl imported (.defnDecl retainedValue) true
    | throwError "cannot install the retained safe definition"
  checkFrame env env
  checkFrontend env 0 [datatype `ValueEmpty []] false
  checkFrontend env 0 [datatype `ValueEnum [⟨`ValueEnum.mk, .const `ValueEnum []⟩]] false
  checkFrontend env 0 [datatype `ValueRecursive [⟨`ValueRecursive.zero, .const `ValueRecursive []⟩,
    ⟨`ValueRecursive.next, .forallE `previous (.const `ValueRecursive [])
      (.const `ValueRecursive []) .default⟩]] false
  checkFrontend env 0 mutualTypes false
  for count in [0, 1, 2] do
    checkFrontend env count [nestedType `ValueNested count] true
  checkFrontend env 0 [nestedType `ValueNested 0, datatype `ValueNestedEmpty []] true
  for check in [false, true] do
    if (Lean4Lean.addDecl env (.inductDecl [] 0 [datatype `ValueCollision [
        ⟨retainedValue.name, .const `ValueCollision []⟩]] false) check).isOk then
      throwError "value-frame frontend accepted a colliding value-bearing constructor name"
    if (Lean4Lean.addDecl env (.inductDecl [] 0 [nestedType `ValueNested 0] false) check
        { inductiveFuel := 0 }).isOk then
      throwError "value-frame frontend accepted zero preprocessing fuel"
  let collision := { retainedValue with name := `ValueRecursorCollision.rec }
  let .ok collisionEnv := Lean4Lean.addDecl env (.defnDecl collision) true
    | throwError "cannot seed the recursor collision"
  for check in [false, true] do
    if (Lean4Lean.addDecl collisionEnv (.inductDecl [] 0 [datatype `ValueRecursorCollision [
        ⟨`ValueRecursorCollision.mk, .const `ValueRecursorCollision []⟩]] false) check).isOk then
      throwError "value-frame frontend accepted a colliding value-bearing recursor name"
  logInfo "8 direct/nested fixtures retain every old record and exactly the old values, including safe delta reduction; both run safeties, both dispatch flags and collision/fuel failures passed"

end InductiveValueFrameTest
