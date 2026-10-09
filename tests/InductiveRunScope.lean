import Lean4Lean.Verify.InductiveRunScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveRunScopeTest

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M ResultType)
    (collect : InductiveStats → M CaptureType) (resume : CaptureType → Except Kernel.Exception ResultType)
    (ctx : Context) (hnext : ∀ stats current, next stats current = (collect stats current).bind resume) :
    checkInductiveTypes nparams types next ctx = (checkInductiveTypes nparams types collect ctx).bind resume :=
  checkInductiveTypes.morphism nparams types next collect resume ctx hnext

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (collect : Array RecInfo → M CaptureType)
    (resume : CaptureType → Except Kernel.Exception ResultType) (ctx : Context)
    (hnext : ∀ infos current, next infos current = (collect infos current).bind resume) :
    mkRecInfos stats types elimLevel next ctx = (mkRecInfos stats types elimLevel collect ctx).bind resume :=
  mkRecInfos.morphism stats types elimLevel next collect resume ctx hnext

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → RecursorInfoCounts types infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedCounts stats types elimLevel next ctx post hwf hreserved hnext

example (nparams : Nat) (types : List InductiveType) (numNested : Nat) (ctx : Context)
    (hsafety : ctx.safety = .safe) (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (AddInductive.run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunScope nparams types.toArray numNested ctx root constructors env :=
  AddInductive.run.safeScope nparams types numNested ctx hsafety hmap hwf hreserved

example {stats : InductiveStats} {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    stats.SafeRunMinorOffsets nparams types numNested original root constructors env := hscope.minorOffsets

example {stats : InductiveStats} {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhsDistinct stats types infos source env := hscope.localRules

example {stats : InductiveStats} {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ original with env := constructors } : Context).RecursorScopeFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhsDistinct stats types infos source env := hscope.originalSource

example {stats : InductiveStats} {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    root.lctx.WF ∧ ContextReserved root.lctx root.ngen := ⟨hscope.rootScope.wf, hscope.rootScope.reserved⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat) (ctx : Context)
    (hsafety : ctx.safety = .safe) (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (env : Kernel.Environment)
    (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    env.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → env.find? name = some info) := by
  obtain ⟨stats, root, constructors, hscope⟩ :=
    AddInductive.run.safeScope nparams types numNested ctx hsafety hmap hwf hreserved env hresult
  exact ⟨hscope.resultWF, hscope.toSafeRunRegistration.preservesOriginal⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat) (ctx : Context)
    (hsafety : ctx.safety = .safe) (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (AddInductive.run nparams types numNested ctx).WF fun env => env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment)
        (infos : Array RecInfo) (source : Context),
        stats.SafeRunScope nparams types.toArray numNested ctx root constructors env ∧
        ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
        RecursorInfoCounts types.toArray infos ∧ LocalRecursorRuleRhsDistinct stats types.toArray infos source env :=
  AddInductive.run.safeRhsDistinct nparams types numNested ctx hsafety hmap hwf hreserved

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ current => .forallE `parameter sortType current .default) body

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

private def captureRun (nparams : Nat) (types : Array InductiveType) (numNested : Nat := 0) : M Receipt := do
  Kernel.Environment.checkDuplicatedUnivParams (← readThe Context).lparams
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types numNested false) do
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

private def checkReader (original current : Context) : MetaM Unit := do
  unless current.ngen.namePrefix == original.ngen.namePrefix && current.ngen.idx >= original.ngen.idx &&
      current.lctx.numIndices == original.lctx.numIndices + current.ngen.idx - original.ngen.idx &&
      (current.lctx.find? ⟨current.ngen.curr⟩).isNone do
    throwError "complete safe run lost structural context advancement or freshness"
  for decl in original.lctx do
    let some found := current.lctx.find? decl.fvarId | throwError "complete safe run dropped an old local declaration"
    unless found.index == decl.index && found.type == decl.type && found.userName == decl.userName &&
        found.value? (allowNondep := true) == decl.value? (allowNondep := true) do
      throwError "complete safe run changed an old local declaration"
  for decl in current.lctx do
    let some found := current.lctx.find? decl.fvarId | throwError "retained reader has no native declaration lookup"
    unless found.index == decl.index && found.toExpr == decl.toExpr do throwError "retained reader list/map disagreement"
    if let .num namePrefix index := decl.fvarId.name then
      if namePrefix == current.ngen.namePrefix && index >= current.ngen.idx then
        throwError "retained reader lost generator reservation"

private def checkRecipe (receipt : Receipt) (types : Array InductiveType) (parent : Nat)
    (index : Nat) (ctor : Constructor) (rule : RecursorRule) : MetaM Unit := do
  let stage := mkRecInfos.loopCtorArgs receipt.stats ctor.type fun _ fields selected => do
    return (fields, selected, ← readThe Context)
  let .ok (fields, selected, current) := stage receipt.source | throwError "stored scoped-rule replay failed"
  checkReader receipt.source current
  unless fields.toList.eraseDups.length == fields.size && selected.toList.eraseDups.length == selected.size &&
      selected.toList.isSublist fields.toList do throwError "stored rule lost distinct ordered field identities"
  for field in fields do
    let some decl := current.lctx.find? field.fvarId! | throwError "stored-rule field is undeclared"
    unless decl.toExpr == field && (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "stored-rule field has incorrect native declaration shape"
  let motives := receipt.infos.map (·.motive)
  let minors := receipt.infos.flatMap (·.minors)
  let minor := receipt.infos[parent]!.minors[index]!
  let replay := mkRecRules.loopU types receipt.stats motives minors
    (getRecLevels receipt.elimLevel receipt.stats.levels) selected 0 #[] fun values =>
    pure (({
      ctor := ctor.name
      nfields := fields.size
      rhs := recursorRuleRhs receipt.stats motives minors fields values current.lctx minor } : RecursorRule), values.size)
  let .ok (expected, count) := replay current | throwError "stored-rule recursive-value replay failed"
  unless rule.ctor == expected.ctor && rule.nfields == expected.nfields && rule.rhs == expected.rhs &&
      count == selected.size do throwError "stored rule lost its coupled distinct RHS recipe"

private def checkRecursorRecord (actual expected : RecursorVal) : MetaM Unit := do
  unless actual.type == expected.type && actual.levelParams == expected.levelParams &&
      actual.numParams == expected.numParams && actual.numIndices == expected.numIndices &&
      actual.numMotives == expected.numMotives && actual.numMinors == expected.numMinors &&
      actual.k == expected.k && actual.isUnsafe == expected.isUnsafe &&
      actual.rules.length == expected.rules.length do
    throwError "capture and direct run disagree on recursor metadata"

private def checkRecords (original : Context) (types : Array InductiveType) (receipt : Receipt)
    (direct : Kernel.Environment) : MetaM Unit := do
  checkReader original receipt.root
  checkReader { receipt.root with env := receipt.constructors } receipt.source
  unless receipt.infos.size == types.size do throwError "complete safe run lost recursor counts"
  for parent in [:types.size] do
    let type := types[parent]!
    unless (receipt.root.env.find? type.name).isSome && (receipt.constructors.find? type.name).isSome do
      throwError "complete safe run lost its original header/positivity root"
    let some (.recInfo recursor) := receipt.env.find? (mkRecName type.name) | throwError "missing installed scoped recursor"
    let some (.recInfo actual) := direct.find? recursor.name | throwError "direct run lost instrumented recursor"
    checkRecursorRecord actual recursor
    let .ok (generated, nextIndex) := mkRecRules types receipt.elimLevel receipt.stats parent
        (receipt.infos.map (·.motive)) (receipt.infos.flatMap (·.minors))
        (recursorMinorOffset types parent) receipt.source | throwError "actual source rule generation failed"
    unless nextIndex == recursorMinorOffset types (parent + 1) && generated.length == recursor.rules.length do
      throwError "actual source rule generation lost exact minor offsets"
    for (ctor, index) in type.ctors.zipIdx do
      unless (receipt.root.env.find? ctor.name).isNone && (receipt.constructors.find? ctor.name).isSome do
        throwError "complete safe run replaced its positivity root by the constructor environment"
      let some rule := recursor.rules[index]? | throwError "missing stored scoped rule"
      let some actualRule := actual.rules[index]? | throwError "missing direct scoped rule"
      unless actualRule.ctor == rule.ctor && actualRule.nfields == rule.nfields && actualRule.rhs == rule.rhs do
        throwError "direct and captured safe runs disagree on stored rules"
      checkRecipe receipt types parent index ctor rule

private def checkRun (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat := 0) : MetaM Unit := do
  let .ok receipt := captureRun nparams types numNested ctx | throwError "complete scoped capture failed"
  let .ok direct := AddInductive.run nparams types.toList numNested ctx | throwError "complete scoped direct run failed"
  checkRecords ctx types receipt direct
  for name in [``Nat, ``Nat.rec, ``List, ``List.rec] do
    let some before := ctx.env.find? name | throwError "missing original scope environment fixture"
    let some after := direct.find? name | throwError "complete safe run dropped an original constant"
    unless before.type == after.type && before.levelParams == after.levelParams do
      throwError "complete safe run changed an original constant"

private def fixtures (ctx : Context) : MetaM Unit := do
  let node := Expr.const `ScopedRunNode []
  let other := Expr.const `ScopedRunOther []
  let param := Expr.const `ScopedRunParam []
  let base : Constructor := { name := `ScopedRunNode.base, type := node }
  let recursive : Constructor := { name := `ScopedRunNode.step, type := .forallE `field node node .default }
  let higher : Constructor := {
    name := `ScopedRunNode.higher
    type := .forallE `field (.forallE `index (.const ``Nat []) node .default) node .implicit }
  let many : Constructor := {
    name := `ScopedRunNode.many
    type := (List.range 33).foldr (fun _ body => .forallE `field node body .implicit) node }
  let mutualCtor : Constructor := { name := `ScopedRunNode.mutual, type := .forallE `field other node .default }
  let paramBase : Constructor := { name := `ScopedRunParam.base, type := closeParams 1 (.app param (.bvar 0)) }
  let paramStep : Constructor := {
    name := `ScopedRunParam.step
    type := closeParams 1 (.forallE `field (.app param (.bvar 0)) (.app param (.bvar 1)) .default) }
  let indexedHead := Expr.const `ScopedRunIndexed []
  let indexedType : InductiveType := {
    name := `ScopedRunIndexed
    type := closeParams 1 (.forallE `index (.const ``Nat []) sortType .default)
    ctors := [{
      name := `ScopedRunIndexed.base
      type := closeParams 1
        (.forallE `index (.const ``Nat []) (.mkAppList indexedHead [.bvar 1, .bvar 0]) .default) }] }
  let seeded := { ctx with
    ngen := { namePrefix := `RunScopeSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `RunScopeSeed 16⟩ `old sortType .default
      |>.mkLetDecl ⟨`RunScopeOldLet⟩ `old (.const ``Nat []) (.const ``Nat.zero []) }
  for current in [ctx, seeded] do
    checkRun current 0 #[]
    checkRun current 0 #[header `ScopedRunNode 0]
    checkRun current 0 #[header `ScopedRunNode 0 [base, recursive, higher]]
    checkRun current 0 #[header `ScopedRunNode 0 [base, many]]
    checkRun current 1 #[header `ScopedRunParam 1 [paramBase, paramStep]]
    checkRun current 0 #[header `ScopedRunNode 0 [base, mutualCtor], header `ScopedRunEmpty 0,
      header `ScopedRunOther 0 [{ name := `ScopedRunOther.base, type := other }]]
    checkRun current 1 #[indexedType]
  checkRun ctx 0 #[header `ScopedRunNode 0 [base, recursive]] 2
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } 0 #[]
  logInfo "16 complete safe runs passed coupled roots, constructors, source readers, distinct fields, and exact RHS replays"

private def failures (ctx : Context) : MetaM Unit := do
  let node := Expr.const `ScopedRunNode []
  let base : Constructor := { name := `ScopedRunNode.base, type := node }
  let types := #[header `ScopedRunNode 0 [base]]
  let .error .deepRecursion := AddInductive.run 0 types.toList 0
      { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } | throwError "complete safe run lost fuel rejection"
  let .error (.other _) := AddInductive.run 1 types.toList 0 ctx | throwError "complete safe run lost parameter rejection"
  let duplicate := #[header `ScopedRunNode 0 [base, base]]
  if (AddInductive.run 0 duplicate.toList 0 ctx).isOk then throwError "complete safe run accepted duplicate constructors"
  let imported := #[header `Nat 0]
  if (AddInductive.run 0 imported.toList 0 ctx).isOk then throwError "complete safe run accepted a header collision"
  let recCollision : Constructor := { name := `ScopedRunNode.rec, type := node }
  let late := #[header `ScopedRunNode 0 [recCollision]]
  if (AddInductive.run 0 late.toList 0 ctx).isOk then throwError "complete safe run accepted a late recursor collision"
  logInfo "five early/late complete-run failures retained fuel, parameter, and freshness boundaries"

private def morphismFixtures (ctx : Context) : MetaM Unit := do
  let empty : Array InductiveType := #[]
  let head := #[header `MorphismHeader 1]
  for (nparams, types) in [(0, empty), (1, head), (2, head)] do
    let collect := checkInductiveTypes nparams types fun stats => do return (stats, ← readThe Context)
    let direct := checkInductiveTypes nparams types fun _ => (throw (.other "header morphism sentinel") : M Unit)
    let captured : Except Kernel.Exception Unit := (collect ctx).bind fun _ => .error (.other "header morphism sentinel")
    match direct ctx, captured with
    | .error (.other first), .error (.other second) =>
      unless first == second do throwError "header morphism changed failure diagnostics"
    | _, _ => throwError "header morphism failed to propagate captured continuation/rejection"
  let node := Expr.const `MorphismNode []
  let types := #[header `MorphismNode 0 [{ name := `MorphismNode.base, type := node }]]
  let .ok receipt := captureRun 0 types 0 ctx | throwError "missing recursor morphism preparation"
  for current in [receipt.source, { receipt.source with fuel := { receipt.source.fuel with inductiveFuel := 0 } }] do
    let collect := mkRecInfos receipt.stats types receipt.elimLevel fun infos => do return (infos, ← readThe Context)
    let direct := mkRecInfos receipt.stats types receipt.elimLevel
      fun _ => (throw (.other "recursor morphism sentinel") : M Unit)
    let captured : Except Kernel.Exception Unit := (collect current).bind fun _ => .error (.other "recursor morphism sentinel")
    match direct current, captured with
    | .error (.other first), .error (.other second) =>
      unless first == second do throwError "recursor morphism changed continuation diagnostics"
    | .error .deepRecursion, .error .deepRecursion => pure ()
    | _, _ => throwError "recursor morphism changed continuation/fuel rejection"
  logInfo "five continuation morphism fixtures preserved callback and prefix failures"

private def audit (theoremName : Name) (structural := false) (registration := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if structural then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push] else []
  let allowed := allowed ++ if registration then [
    ``Lean.PersistentHashMap.findAux_isSome, ``Expr.eqv_eq, ``Expr.instantiate1_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``checkInductiveTypes.morphism
  audit ``checkInductiveTypes.scopedStats true
  audit ``mkRecInfos.morphism
  audit ``mkRecInfos.scopedCounts true
  audit ``checkInductiveTypes.safeScopedConstructorRegistration true true
  audit ``InductiveStats.SafeRunScope.minorOffsets
  audit ``InductiveStats.SafeRunScope.localRules
  audit ``InductiveStats.SafeRunScope.originalSource
  audit ``AddInductive.run.safeScope true true
  audit ``AddInductive.run.safeRhsDistinct true true
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  failures ctx
  morphismFixtures ctx

end InductiveRunScopeTest
