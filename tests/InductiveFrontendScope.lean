import Lean4Lean.Verify.InductiveFrontendScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveFrontendScopeTest

example {env : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {fuel : FuelConfig} {preprocessing : ElimNestedInductive.Result}
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hnoaux : preprocessing.aux2nested.size = 0) :
    NonNestedInductivePreprocessing env lparams nparams types fuel :=
  NonNestedInductivePreprocessing.of_result hpre hnoaux

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      InductiveSourcesNoMVarNoFVar types ∧
      ∃ preprocessing, inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        (preprocessing.aux2nested.size = 0 →
          ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
            stats.SafeRunScope nparams preprocessing.types.toArray 0
              (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result) :=
  Lean4Lean.Environment.addInductive.safeStages env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.Environment.addInductive.safeNonNested env lparams nparams types allowPrimitive fuel hmap hnonNested

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) (preprocessing : ElimNestedInductive.Result)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hnoaux : preprocessing.aux2nested.size = 0) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.Environment.addInductive.safeNonNestedResult env lparams nparams types allowPrimitive fuel
    hmap preprocessing hpre hnoaux

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (hscope : NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result) :
    result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  hscope.preserves

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (hscope : NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (stats : InductiveStats) (root : Context)
      (constructors : Kernel.Environment) (infos : Array RecInfo) (source : Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      preprocessing.aux2nested.size = 0 ∧
      stats.SafeRunScope nparams preprocessing.types.toArray 0
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result ∧
      ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source result := hscope.localRules

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF)
    (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.addDecl.safeNonNestedInductive env lparams nparams types check fuel hmap hnonNested

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF)
    (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  Lean4Lean.addDecl.safeNonNestedPreserves env lparams nparams types check fuel hmap hnonNested

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (count : Nat) (body : Expr) : Expr :=
  (List.range count).foldr (fun _ result => .forallE `A sortType result .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor := []) : InductiveType :=
  { name, type := closeParams nparams sortType, ctors }

structure Receipt where
  stats : InductiveStats
  root : Context
  constructors : Kernel.Environment
  elimLevel : Level
  infos : Array RecInfo
  source : Context
  env : Kernel.Environment

private def captureRun (nparams : Nat) (types : Array InductiveType) : M Receipt := do
  Kernel.Environment.checkDuplicatedUnivParams (← readThe Context).lparams
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      let root ← readThe Context
      let constructors ← declareConstructors stats types false
      withEnv constructors do
        let elimLevel ← getElimLevel stats types
        mkRecInfos stats types elimLevel fun infos => do
          let source ← readThe Context
          let isK ← isKTarget stats types
          let env ← declareRecursors stats types elimLevel infos source.lparams source.lctx isK false
          return { stats, root, constructors, elimLevel, infos, source, env }

private def checkReader (original ctx : Context) : MetaM Unit := do
  unless ctx.safety == .safe && ctx.ngen.namePrefix == original.ngen.namePrefix &&
      ctx.ngen.idx >= original.ngen.idx &&
      ctx.lctx.numIndices == original.lctx.numIndices + ctx.ngen.idx - original.ngen.idx &&
      (ctx.lctx.find? ⟨ctx.ngen.curr⟩).isNone do
    throwError "frontend reader lost scope or reservation: safety={repr ctx.safety}, locals={ctx.lctx.numIndices}, generator={ctx.ngen.idx}"
  for decl in original.lctx do
    let some found := ctx.lctx.find? decl.fvarId | throwError "frontend reader dropped an old local"
    unless found.index == decl.index && found.type == decl.type &&
        found.value? (allowNondep := true) == decl.value? (allowNondep := true) do
      throwError "frontend reader changed an old local"
  for decl in ctx.lctx do
    let some found := ctx.lctx.find? decl.fvarId | throwError "frontend reader lost a declared local"
    unless found.index == decl.index && found.toExpr == decl.toExpr do
      throwError "frontend reader map/list disagreement"
    if let .num namePrefix index := decl.fvarId.name then
      if namePrefix == ctx.ngen.namePrefix && index >= ctx.ngen.idx then
        throwError "frontend reader has an unreserved generated name"

private def checkRule (receipt : Receipt) (types : Array InductiveType) (parent index : Nat)
    (ctor : Constructor) (rule : RecursorRule) : MetaM Unit := do
  let capture := mkRecInfos.loopCtorArgs receipt.stats ctor.type fun _ fields selected => do
    return (fields, selected, ← readThe Context)
  let .ok (fields, selected, current) := capture receipt.source | throwError "frontend field replay failed"
  checkReader receipt.source current
  unless fields.toList.eraseDups.length == fields.size && selected.toList.eraseDups.length == selected.size &&
      selected.toList.isSublist fields.toList do throwError "frontend RHS fields lost distinctness/order"
  for field in fields do
    let some decl := current.lctx.find? field.fvarId! | throwError "frontend RHS field is undeclared"
    unless decl.toExpr == field && (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "frontend RHS field lost its declaration shape"
  let motives := receipt.infos.map (·.motive)
  let minors := receipt.infos.flatMap (·.minors)
  let minor := receipt.infos[parent]!.minors[index]!
  let replay := mkRecRules.loopU types receipt.stats motives minors
    (getRecLevels receipt.elimLevel receipt.stats.levels) selected 0 #[] fun values =>
    pure (({
      ctor := ctor.name
      nfields := fields.size
      rhs := recursorRuleRhs receipt.stats motives minors fields values current.lctx minor } : RecursorRule), values.size)
  let .ok (expected, count) := replay current | throwError "frontend RHS value replay failed"
  unless rule.ctor == expected.ctor && rule.nfields == expected.nfields &&
      rule.rhs == expected.rhs && count == selected.size do
    throwError "frontend recursor lost its exact local-minor distinct RHS recipe"

private def compareInductive (first second : InductiveVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.all == second.all && first.ctors == second.ctors && first.numNested == second.numNested &&
      first.isRec == second.isRec && first.isUnsafe == second.isUnsafe do
    throwError "frontend changed staged inductive metadata"

private def compareConstructor (first second : ConstructorVal) : MetaM Unit := do
  unless first.induct == second.induct && first.cidx == second.cidx && first.numParams == second.numParams &&
      first.numFields == second.numFields && first.isUnsafe == second.isUnsafe do
    throwError "frontend changed staged constructor metadata"

private def compareRecursor (first second : RecursorVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.numMotives == second.numMotives && first.numMinors == second.numMinors && first.all == second.all &&
      first.k == second.k && first.isUnsafe == second.isUnsafe && first.rules.length == second.rules.length do
    throwError "frontend changed staged recursor metadata"
  for (left, right) in first.rules.zip second.rules do
    unless left.ctor == right.ctor && left.nfields == right.nfields && left.rhs == right.rhs do
      throwError "frontend changed a staged recursor rule"

private def compareConstant (expected actual : ConstantInfo) : MetaM Unit := do
  unless expected.name == actual.name && expected.type == actual.type &&
      expected.levelParams == actual.levelParams do throwError "frontend changed a staged constant"
  match expected, actual with
  | .inductInfo first, .inductInfo second => compareInductive first second
  | .ctorInfo first, .ctorInfo second => compareConstructor first second
  | .recInfo first, .recInfo second => compareRecursor first second
  | _, _ => throwError "frontend changed a staged constant kind"

private def compareBatch (expected actual : Kernel.Environment) (types : List InductiveType) : MetaM Unit := do
  for indType in types do
    for name in indType.name :: mkRecName indType.name :: indType.ctors.map (·.name) do
      let some first := expected.find? name | throwError "missing staged constant {name}"
      let some second := actual.find? name | throwError "missing frontend constant {name}"
      compareConstant first second

private def checkReceipt (original : Context) (receipt : Receipt) (types : Array InductiveType) : MetaM Unit := do
  checkReader original receipt.root
  checkReader receipt.root receipt.source
  unless receipt.infos.size == types.size do throwError "frontend recursor counts lost parent alignment"
  for parent in [:types.size] do
    let indType := types[parent]!
    unless receipt.infos[parent]!.minors.size == indType.ctors.length do
      throwError "frontend recursor counts lost minor alignment"
    let some (.inductInfo _) := receipt.root.env.find? indType.name | throwError "missing original header root"
    for ctor in indType.ctors do
      unless (receipt.root.env.find? ctor.name).isNone do throwError "constructor leaked into positivity root"
      let some (.ctorInfo _) := receipt.constructors.find? ctor.name | throwError "missing constructor stage"
      let some (.ctorInfo _) := receipt.source.env.find? ctor.name | throwError "missing actual source reader"
    let some (.recInfo info) := receipt.env.find? (mkRecName indType.name) | throwError "missing frontend recursor"
    unless info.rules.length == indType.ctors.length do throwError "frontend recursor rules lost alignment"
    let .ok (rules, nextOffset) := mkRecRules types receipt.elimLevel receipt.stats parent
        (receipt.infos.map (·.motive)) (receipt.infos.flatMap (·.minors))
        (recursorMinorOffset types parent) receipt.source | throwError "frontend source rule generation failed"
    unless nextOffset == recursorMinorOffset types (parent + 1) && rules.length == info.rules.length do
      throwError "frontend source rule generation lost exact prefix offsets"
    for (generated, stored) in rules.zip info.rules do
      unless generated.ctor == stored.ctor && generated.nfields == stored.nfields && generated.rhs == stored.rhs do
        throwError "frontend source rule generation changed a stored RHS"
    for index in [:indType.ctors.length] do
      checkRule receipt types parent index indType.ctors[index]! info.rules[index]!

private def checkFrontend (env : Kernel.Environment) (nparams : Nat) (types : List InductiveType)
    (lparams : List Name := []) (fuel : FuelConfig := {}) : MetaM Unit := do
  let .ok preprocessing := inductivePreprocessing env lparams nparams types fuel
    | throwError "frontend preprocessing failed for {types.map (·.name)}, nparams={nparams}, lparams={lparams}"
  unless preprocessing.aux2nested.size == 0 do throwError "non-nested frontend fixture has auxiliaries"
  let .ok allowPrimitive := Lean4Lean.Environment.checkPrimitiveInductive env lparams nparams types false
    | throwError "frontend primitive dispatch failed"
  let ctx := inductiveScopeContext env lparams allowPrimitive fuel
  let .ok receipt := captureRun nparams preprocessing.types.toArray ctx
    | throwError "frontend capture failed for {types.map (·.name)}, ctors={types.flatMap (·.ctors) |>.map (·.name)}, lparams={lparams}"
  checkReceipt ctx receipt preprocessing.types.toArray
  let .ok staged := AddInductive.run nparams preprocessing.types 0 ctx | throwError "frontend staged run failed"
  compareBatch receipt.env staged preprocessing.types
  let .ok frontend := Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel
    | throwError "safe public frontend failed"
  compareBatch staged frontend preprocessing.types
  for check in [false, true] do
    let .ok added := Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel
      | throwError "safe declaration frontend failed with check={check}"
    compareBatch frontend added preprocessing.types
    for name in [``Nat, ``Nat.rec, ``List, ``List.rec] do
      if let some before := env.find? name then
        let some after := added.find? name | throwError "frontend dropped old lookup {name}"
        compareConstant before after

private def fixtures (env : Kernel.Environment) : MetaM Unit := do
  let node := Expr.const `FrontendNode []
  let other := Expr.const `FrontendOther []
  let param := Expr.const `FrontendParam []
  let base : Constructor := { name := `FrontendNode.base, type := node }
  let step : Constructor := { name := `FrontendNode.step, type := .forallE `field node node .default }
  let higher : Constructor := {
    name := `FrontendNode.higher
    type := .forallE `field (.forallE `index (.const ``Nat []) node .default) node .implicit }
  let many : Constructor := {
    name := `FrontendNode.many
    type := (List.range 33).foldr (fun _ body => .forallE `field node body .implicit) node }
  let paramStep : Constructor := {
    name := `FrontendParam.step
    type := closeParams 1 (.forallE `field (.app param (.bvar 0)) (.app param (.bvar 1)) .default) }
  let indexed : InductiveType := {
    name := `FrontendIndexed
    type := closeParams 1 (.forallE `index (.const ``Nat []) sortType .default)
    ctors := [{
      name := `FrontendIndexed.base
      type := closeParams 1 (.forallE `index (.const ``Nat [])
        (.mkAppList (.const `FrontendIndexed []) [.bvar 1, .bvar 0]) .default) }] }
  checkFrontend env 0 [header `FrontendNode 0]
  checkFrontend env 0 [header `FrontendNode 0 [base, step, higher]]
  checkFrontend env 0 [header `FrontendNode 0 [base, many]]
  checkFrontend env 1 [header `FrontendParam 1 [paramStep]]
  checkFrontend env 1 [indexed]
  let otherCtor : Constructor := {
    name := `FrontendNode.other
    type := .forallE `field other node .default }
  checkFrontend env 0 [header `FrontendNode 0 [base, otherCtor], header `FrontendEmpty 0,
    header `FrontendOther 0 [{ name := `FrontendOther.base, type := other }]]
  checkFrontend env 0 [header `FrontendNode 0 [{
    name := `FrontendNode.base
    type := .const `FrontendNode [.param `u] }]] [`u]
  let poly := Expr.const `FrontendPoly [.param `u]
  checkFrontend env 1 [{
    name := `FrontendPoly
    type := .forallE `A (.sort (.param `u)) (.sort (.param `u)) .default
    ctors := [{
      name := `FrontendPoly.mk
      type := .forallE `A (.sort (.param `u)) (.forallE `field (.bvar 0)
        (.app poly (.bvar 1)) .default) .default }] }] [`u]
  checkFrontend (Kernel.Environment.empty `FrontendPrimitive) 0 [header ``Bool 0 [
    { name := ``Bool.false, type := .const ``Bool [] }, { name := ``Bool.true, type := .const ``Bool [] }]]
  checkFrontend (Kernel.Environment.empty `FrontendPrimitive) 0 [header ``Nat 0 [
    { name := ``Nat.zero, type := .const ``Nat [] },
    { name := ``Nat.succ, type := .forallE `value (.const ``Nat []) (.const ``Nat []) .default }]]
  logInfo "10 public no-auxiliary fixtures passed exact preprocessing, primitive dispatch, both check flags, staged records/readers and distinct RHS replays"

private def failures (env : Kernel.Environment) : MetaM Unit := do
  let node := Expr.const `FrontendNode []
  let base : Constructor := { name := `FrontendNode.base, type := node }
  let plain := [header `FrontendNode 0 [base]]
  for check in [false, true] do
    let .error (.other fuelMessage) := Lean4Lean.addDecl env (.inductDecl [] 0 plain false) check { inductiveFuel := 0 }
      | throwError "frontend lost fuel rejection"
    unless fuelMessage == "deep recursion: ElimNestedInductive.run.loop" do
      throwError "frontend changed preprocessing fuel diagnostic"
    if (Lean4Lean.addDecl env (.inductDecl [] 0 [] false) check).isOk then
      throwError "public frontend accepted an empty batch"
    for (nparams, types) in [(1, plain), (0, [header `FrontendNode 0 [base, base]]),
        (0, [header ``Nat 0]), (0, [header `FrontendNode 0 [{ name := `FrontendNode.rec, type := node }]])] do
      if (Lean4Lean.addDecl env (.inductDecl [] nparams types false) check).isOk then
        throwError "frontend accepted malformed/colliding fixture"
    let .error (.declHasFVars _ name original) := Lean4Lean.addDecl env
        (.inductDecl [] 0 [{ name := `FrontendPoison, type := .fvar ⟨`poison⟩, ctors := [] }] false) check
      | throwError "frontend lost original-source guard"
    unless name == `FrontendPoison && original == .fvar ⟨`poison⟩ do throwError "frontend changed source diagnostic"
    if (Lean4Lean.addDecl env (.inductDecl [`u, `u] 0 plain false) check).isOk then
      throwError "frontend accepted duplicate universe parameters"
  let nested : InductiveType := { name := `FrontendNested, type := sortType, ctors := [{
    name := `FrontendNested.mk
    type := .forallE `field (.app (.const ``List [.zero]) (.const `FrontendNested []))
      (.const `FrontendNested []) .default }] }
  let .ok preprocessing := inductivePreprocessing env [] 0 [nested] {}
    | throwError "nested boundary preprocessing failed"
  unless preprocessing.aux2nested.size > 0 do throwError "nested fixture no longer excludes no-auxiliary premise"
  for check in [false, true] do
    unless (Lean4Lean.addDecl env (.inductDecl [] 0 [nested] false) check).isOk do
      throwError "nested control unexpectedly failed outside structural frontend certificate"
  logInfo "16 frontend failures retained empty/source/fuel/arity/freshness/universe boundaries; successful nested control remains outside no-auxiliary certificate"

private def audit (theoremName : Name) (full := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if full then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentArray.toList'_push,
    ``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``NonNestedInductivePreprocessing.of_result
  audit ``NonNestedInductiveScope.preserves
  audit ``NonNestedInductiveScope.localRules
  audit ``Lean4Lean.Environment.addInductive.safeStages true
  audit ``Lean4Lean.Environment.addInductive.safeNonNested true
  audit ``Lean4Lean.Environment.addInductive.safeNonNestedResult true
  audit ``Lean4Lean.addDecl.safeNonNestedInductive true
  audit ``Lean4Lean.addDecl.safeNonNestedPreserves true
  let env := (← Lean.getEnv).toKernelEnv
  fixtures env
  failures env

end InductiveFrontendScopeTest
