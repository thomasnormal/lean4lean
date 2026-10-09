import Lean4Lean.Verify.InductiveFrontendRestoration
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveFrontendRestorationTest

example {allowed : ConstantInfo → Prop} {original current result : Kernel.Environment}
    (first : FreshRegistrationTrace allowed original current)
    (second : FreshRegistrationTrace allowed current result) : FreshRegistrationTrace allowed original result :=
  first.trans second

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF) :
    result.constants.WF ∧ (∀ name info, original.find? name = some info → result.find? name = some info) :=
  trace.preserves hwf

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (hlookup : result.find? name = some info) :
    original.find? name = some info ∨ allowed info := trace.lookup hwf name info hlookup

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (habsent : original.find? name = none)
    (hlookup : result.find? name = some info) : allowed info := trace.newLookup hwf name info habsent hlookup

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (recName : Name) (env : Kernel.Environment) :
    (restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive recName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveRecursor.trace preprocessing staged allIndNames recNameMap allowPrimitive recName env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (ctorName : Name) (env : Kernel.Environment) :
    (restoreInductiveConstructor preprocessing staged allowPrimitive ctorName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveConstructor.trace preprocessing staged allIndNames recNameMap allowPrimitive ctorName env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) (env : Kernel.Environment) :
    (restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveDatatype.trace preprocessing staged allIndNames recNameMap allowPrimitive indType env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (env : Kernel.Environment) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2) env result.2 :=
  restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel env

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result) :
    result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) := scope.preserves

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.Environment.addInductive.safeFrontend env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  Lean4Lean.Environment.addInductive.safePreserves env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.addDecl.safeInductiveFrontend env lparams nparams types check fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  Lean4Lean.addDecl.safeInductivePreserves env lparams nparams types check fuel hmap

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (count : Nat) (body : Expr) : Expr :=
  (List.range count).foldr (fun _ result => .forallE `A sortType result .default) body

private def family (name : Name) (count shift : Nat) : Expr :=
  mkAppN (.const name []) ((List.range count).toArray.map fun index => .bvar (count - 1 - index + shift))

private def nestedType (name : Name) (count fields : Nat) (nested := true) : InductiveType :=
  let domain : Expr := if nested then .app (.const ``List [.zero]) (family name count 0) else .const ``Nat []
  let ctorType := (List.range fields).foldr (fun index body =>
    .forallE `field (domain.liftLooseBVars 0 index) body .default) (family name count fields)
  { name, type := closeParams count sortType, ctors := [{ name := name ++ `mk, type := closeParams count ctorType }] }

private def compareHeader (first second : InductiveVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.all == second.all && first.ctors == second.ctors && first.numNested == second.numNested &&
      first.isRec == second.isRec && first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive do
    throwError "nested frontend changed restored header metadata"

private def compareConstructor (first second : ConstructorVal) : MetaM Unit := do
  unless first.induct == second.induct && first.cidx == second.cidx && first.numParams == second.numParams &&
      first.numFields == second.numFields && first.isUnsafe == second.isUnsafe do
    throwError "nested frontend changed restored constructor metadata"

private def compareRecursor (first second : RecursorVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.numMotives == second.numMotives && first.numMinors == second.numMinors && first.all == second.all &&
      first.k == second.k && first.isUnsafe == second.isUnsafe && first.rules.length == second.rules.length do
    throwError "nested frontend changed restored recursor metadata"
  for (left, right) in first.rules.zip second.rules do
    unless left.ctor == right.ctor && left.nfields == right.nfields && left.rhs == right.rhs do
      throwError "nested frontend changed restored recursor rule"

private def compareConstant (expected actual : ConstantInfo) : MetaM Unit := do
  unless expected.name == actual.name && expected.type == actual.type &&
      expected.levelParams == actual.levelParams do throwError "nested frontend changed exact restored record"
  match expected, actual with
  | .inductInfo first, .inductInfo second => compareHeader first second
  | .ctorInfo first, .ctorInfo second => compareConstructor first second
  | .recInfo first, .recInfo second => compareRecursor first second
  | _, _ => throwError "nested frontend changed restored record kind"

private def checkLookup (env : Kernel.Environment) (info : ConstantInfo) : MetaM Unit := do
  let some actual := env.find? info.name | throwError "missing restored record {info.name}"
  compareConstant info actual

private def checkOld (original result : Kernel.Environment) : MetaM Unit := do
  for name in [``Nat, ``Nat.rec, ``List, ``List.rec, ``Bool, ``Bool.rec] do
    if let some before := original.find? name then
      let some after := result.find? name | throwError "nested frontend dropped old lookup {name}"
      compareConstant before after

private def checkRestoredRecords (original staged result : Kernel.Environment)
    (preprocessing : ElimNestedInductive.Result) (types : List InductiveType) : MetaM Unit := do
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  let allIndNames := types.map (·.name)
  for indType in types do
    let some (.inductInfo info) := staged.find? indType.name | throwError "missing staged nested header"
    checkLookup result (.inductInfo { info with all := allIndNames })
    for ctorName in info.ctors do
      let some (.ctorInfo ctor) := staged.find? ctorName | throwError "missing staged nested constructor"
      checkLookup result (.ctorInfo { ctor with type := preprocessing.restoreNested staged ctor.type })
  for name in types.map (mkRecName ∘ (·.name)) ++ recNames do
    let some (.recInfo info) := staged.find? name | throwError "missing staged nested recursor"
    checkLookup result (.recInfo (restoredRecursorVal preprocessing staged allIndNames recNameMap name info))
  for indType in preprocessing.types.drop types.length do
    unless (result.find? indType.name).isNone do throwError "staged auxiliary header leaked into public result"
    for ctor in indType.ctors do
      unless (result.find? ctor.name).isNone do throwError "staged auxiliary constructor leaked into public result"
  checkOld original result

private def checkFrontend (env : Kernel.Environment) (nparams : Nat) (types : List InductiveType)
    (nested : Bool) (lparams : List Name := []) : MetaM Unit := do
  unless ((← Lean.getEnv).addDeclCore 0 (.inductDecl lparams nparams types false) none).isOk do
    throwError "restoration fixture fails native kernel validation"
  let preprocessing ← match inductivePreprocessing env lparams nparams types {} with
    | .ok result => pure result
    | .error exception => throwError "restoration preprocessing failed for {types.map (·.name)}: {exception.toMessageData {}}"
  unless (preprocessing.aux2nested.size > 0) == nested do throwError "fixture has wrong restoration branch"
  let .ok allowPrimitive := Lean4Lean.Environment.checkPrimitiveInductive env lparams nparams types false
    | throwError "restoration primitive dispatch failed"
  let .ok staged := AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams allowPrimitive {}) | throwError "restoration staged run failed"
  let expected ← if nested then do
    let .ok (_, restored) := restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive {} env
      | throwError "explicit restoration failed"
    pure restored
  else pure staged
  for check in [false, true] do
    let .ok added := Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check
      | throwError "public restoration failed with check={check}"
    if nested then
      checkRestoredRecords env staged added preprocessing types
      checkRestoredRecords env staged expected preprocessing types
    else
      for indType in types do
        for name in indType.name :: mkRecName indType.name :: indType.ctors.map (·.name) do
          let some record := expected.find? name | throwError "missing direct staged record"
          checkLookup added record
      checkOld env added
  let .ok publicResult := Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive
    | throwError "public safe restoration failed"
  if nested then checkRestoredRecords env staged publicResult preprocessing types
  else checkOld env publicResult

private def fixtures (env : Kernel.Environment) : MetaM Unit := do
  for count in [0, 1, 2] do
    for fields in [1, 2, 5] do
      checkFrontend env count [nestedType `RestoredNested count fields] true
    checkFrontend env count [nestedType `RestoredPlain count 2 false] false
  checkFrontend env 0 [nestedType `RestoredNested 0 1, {
    name := `RestoredEmpty, type := sortType, ctors := [] }] true
  let name := `RestoredIndexed
  let indexed : InductiveType := {
    name
    type := .forallE `index (.const ``Nat []) sortType .default
    ctors := [{
      name := name ++ `mk
      type := .forallE `index (.const ``Nat [])
        (.forallE `field (.app (.const ``List [.zero]) (.app (.const name []) (.const ``Nat.zero [])))
          (.app (.const name []) (.bvar 1)) .default) .default }] }
  checkFrontend env 0 [indexed] true
  let poly : InductiveType := {
    name := `RestoredPoly
    type := .forallE `A (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default
    ctors := [{
      name := `RestoredPoly.mk
      type := .forallE `A (.sort (.succ (.param `u)))
        (.forallE `field (.app (.const ``List [.param `u]) (.app (.const `RestoredPoly [.param `u]) (.bvar 0)))
          (.app (.const `RestoredPoly [.param `u]) (.bvar 1)) .default) .default }] }
  checkFrontend env 1 [poly] true [`u]
  logInfo "15 frontend fixtures passed direct/nested branches, both check flags, exact restored headers/constructors/recursors/rules, auxiliary non-leakage and old lookups"

private def failures (env : Kernel.Environment) : MetaM Unit := do
  let types := [nestedType `RestoredNested 0 1]
  let .ok preprocessing := inductivePreprocessing env [] 0 types {} | throwError "missing failure preparation"
  let .ok staged := AddInductive.run 0 preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env [] false {}) | throwError "missing staged failure preparation"
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  let .ok (_, result) := restoreInductiveEnvironment preprocessing staged types [] false {} env
    | throwError "missing successful restoration preparation"
  if (restoreInductiveEnvironment preprocessing staged types [] false {} result).isOk then
    throwError "restoration accepted a colliding installed header"
  for name in `RestoredNested.rec :: recNames do
    let .ok (_, next) := restoreInductiveRecursor preprocessing staged [`RestoredNested] recNameMap false name env
      | throwError "individual restored recursor failed"
    if (restoreInductiveRecursor preprocessing staged [`RestoredNested] recNameMap false name next).isOk then
      throwError "restoration accepted a colliding main/auxiliary recursor"
  let .ok (_, next) := restoreInductiveConstructor preprocessing staged false `RestoredNested.mk env
    | throwError "individual restored constructor failed"
  if (restoreInductiveConstructor preprocessing staged false `RestoredNested.mk next).isOk then
    throwError "restoration accepted a colliding constructor"
  for check in [false, true] do
    if (Lean4Lean.addDecl env (.inductDecl [] 0 types false) check { inductiveFuel := 0 }).isOk then
      throwError "nested frontend accepted zero preprocessing fuel"
    let poisoned := { types.head! with type := .fvar ⟨`RestorationPoison⟩ }
    let .error (.declHasFVars _ _ _) := Lean4Lean.addDecl env (.inductDecl [] 0 [poisoned] false) check
      | throwError "nested frontend bypassed original-source guard"
  let .error .deepRecursion := restoreInductiveEnvironment preprocessing staged types [] false
      { recDepth := 0 } env | throwError "restoration lost final auxiliary-check fuel failure"
  logInfo "restoration collision controls and public preflight/preprocessing/final auxiliary-check failures passed"

private def audit (theoremName : Name) (maps := false) (full := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if maps then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome] else []
  let allowed := allowed ++ if full then [
    ``Lean.PersistentArray.toList'_push,
    ``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``AddInductive.restorationAddFresh true
  audit ``FreshRegistrationTrace.trans
  audit ``FreshRegistrationTrace.preserves true
  audit ``FreshRegistrationTrace.lookup true
  audit ``FreshRegistrationTrace.newLookup true
  audit ``restoreInductiveRecursor.trace true
  audit ``restoreInductiveConstructor.trace true
  audit ``restoreInductiveDatatype.trace true
  audit ``restoreInductiveEnvironment.trace true
  audit ``SafeInductiveFrontendScope.preserves true
  audit ``Lean4Lean.Environment.addInductive.safeFrontend true true
  audit ``Lean4Lean.Environment.addInductive.safePreserves true true
  audit ``Lean4Lean.addDecl.safeInductiveFrontend true true
  audit ``Lean4Lean.addDecl.safeInductivePreserves true true
  let env := (← Lean.getEnv).toKernelEnv
  fixtures env
  failures env

end InductiveFrontendRestorationTest
