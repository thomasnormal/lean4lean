import Lean4Lean.Verify.RecursorMetadata
import Lean4Lean.Verify.InductiveRegistration
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace RecursorRegistrationTest

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx).WF
      fun env => env.constants.WF ∧
        ∀ name info, ctx.env.find? name = some info → env.find? name = some info :=
  declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx = .ok env) :
    env.constants.WF :=
  (declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx
    hwf env hresult).1

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (name : Name) (info : ConstantInfo)
    (hold : ctx.env.find? name = some info)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx = .ok env) :
    env.find? name = some info :=
  (declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx
    hwf env hresult).2 name info hold

example (stats : InductiveStats) (types : Array InductiveType) (nparams numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested original root constructors)
    (elimLevel : Level) (recInfos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe
      { root with env := constructors } = .ok env) :
    env.constants.WF ∧
      (∀ name info, original.env.find? name = some info → env.find? name = some info) ∧
      stats.HeaderMetadata nparams types numNested false original.lparams env ∧
      stats.ConstructorMetadata original.lparams types false env := by
  obtain ⟨hfinal, hkeep⟩ := declareRecursors.preserves stats types elimLevel recInfos lparams
    lctx isK isUnsafe { root with env := constructors } hregistration.resultWF env hresult
  refine ⟨hfinal, fun name info hold => hkeep name info (hregistration.preservesOriginal name info hold),
    ?_, ?_⟩
  · intro parent hparent
    exact hkeep _ _ (hregistration.resultHeaderMetadata parent hparent)
  · intro parent hparent index ctor hctor
    obtain ⟨hfind, harity⟩ := hregistration.constructorMetadata parent hparent index ctor hctor
    exact ⟨hkeep _ _ hfind, harity⟩

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env :=
  declareRecursors.metadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment)
    (hresult : declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx = .ok env)
    (index : Nat) (hindex : index < types.size) :
    ∃ rules minorIndex nextIndex,
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (rules, nextIndex) ∧
      env.find? (mkRecName types[index]!.name) = some (.recInfo
        (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules)) :=
  (declareRecursors.metadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf
    env hresult).2.2 index hindex

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ (info : RecursorVal) (minorIndex nextIndex : Nat),
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (info.rules, nextIndex) :=
  hmetadata.sourceRules

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment) (nparams : Nat)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hparams : stats.ParamsCount nparams types.size) (hmotives : infos.size = types.size)
    (hminors : (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length) :
    stats.DeclaredRecursorCounts nparams types env :=
  hmetadata.declaredCounts hparams hmotives hminors

example (stats : InductiveStats) (types : Array InductiveType) (nparams numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested original root constructors)
    (elimLevel : Level) (infos : Array RecInfo) (lctx : LocalContext) (isK isUnsafe : Bool)
    (hresult : declareRecursors stats types elimLevel infos original.lparams lctx isK isUnsafe
      { root with env := constructors } = .ok env)
    (hmotives : infos.size = types.size)
    (hminors : (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length) :
    stats.DeclaredRecursorCounts nparams types env := by
  have hmetadata := (declareRecursors.metadata stats types elimLevel infos original.lparams
    lctx isK isUnsafe { root with env := constructors } hregistration.resultWF env hresult).2.2
  exact hmetadata.declaredCounts hregistration.traces.2.1 hmotives hminors

example (stats : InductiveStats) (env : Kernel.Environment) :
    stats.DeclaredRecursorCounts 17 #[] env := by
  simp [InductiveStats.DeclaredRecursorCounts]

private def statsFor (types : Array InductiveType) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, params := #[], isNotZero := true,
  indConsts := types.map fun type => .const type.name [], nindices := types.map fun _ => 0 }

private def typeFor (name : Name) (ctors : List Name) : InductiveType := {
  name, type := .sort (.succ .zero),
  ctors := ctors.map fun ctor => { name := ctor, type := .const name [] } }

private def infoFor (name : Name) (minorNames : Array Name) : RecInfo := {
  motive := .fvar ⟨name ++ `motive⟩, major := .fvar ⟨name ++ `major⟩, indices := #[],
  minors := minorNames.map fun minor => .fvar ⟨minor⟩ }

private def localsFor (infos : Array RecInfo) : LocalContext := Id.run do
  let mut lctx : LocalContext := {}
  for info in infos do
    for binder in #[info.motive, info.major] ++ info.minors do
      lctx := lctx.mkLocalDecl binder.fvarId! binder.fvarId!.name (.const ``Nat [])
  return lctx

private def checkPreserved (original env : Kernel.Environment) (name : Name) : MetaM Unit := do
  let some old := original.find? name | throwError "missing old-entry fixture {name}"
  let some retained := env.find? name | throwError "recursor registration dropped {name}"
  unless old.name == retained.name && old.type == retained.type &&
      old.levelParams == retained.levelParams && old.isUnsafe == retained.isUnsafe do
    throwError "recursor registration changed {name}"

private def rulesMatch (before after : List RecursorRule) : Bool :=
  before.length == after.length && (before.zip after).all fun pair =>
    pair.1.ctor == pair.2.ctor && pair.1.nfields == pair.2.nfields && pair.1.rhs == pair.2.rhs

private def checkExact (ctx : Context) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (env : Kernel.Environment) (index minorIndex : Nat) : MetaM Nat := do
  let .ok (rules, nextIndex) := mkRecRules types elimLevel stats index
      (infos.map (·.motive)) (infos.flatMap (·.minors)) minorIndex ctx
    | throwError "rule-generation receipt did not replay"
  let expected := declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules
  let some (.recInfo actual) := env.find? expected.name | throwError "missing exact recursor record"
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.all == expected.all &&
      actual.numParams == expected.numParams && actual.numIndices == expected.numIndices &&
      actual.numMotives == expected.numMotives && actual.numMinors == expected.numMinors &&
      actual.k == expected.k && actual.isUnsafe == expected.isUnsafe && rulesMatch actual.rules rules do
    throwError "installed recursor differs from the complete metadata specification"
  unless nextIndex == minorIndex + types[index]!.ctors.length do
    throwError "incorrect replayed minor-index advancement"
  return nextIndex

private def checkRecursor (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (lparams : List Name) (elimLevel : Level) (lctx : LocalContext) (env : Kernel.Environment)
    (index offset : Nat) (isK isUnsafe : Bool) : MetaM Unit := do
  let type := types[index]!
  let some (.recInfo info) := env.find? (mkRecName type.name)
    | throwError "missing recursor {type.name}"
  let minors := infos.flatMap (·.minors)
  unless info.levelParams == getRecLevelParams elimLevel lparams &&
      !info.type.hasFVar &&
      info.numParams == 0 && info.numIndices == 0 && info.numMotives == infos.size &&
      info.numMinors == minors.size && info.all == (types.map (·.name)).toList &&
      info.k == isK && info.isUnsafe == isUnsafe && info.rules.length == type.ctors.length do
    throwError "incorrect recursor metadata for {type.name}"
  for ruleIndex in [:type.ctors.length] do
    let rule := info.rules[ruleIndex]!
    let expected := lctx.mkLambda (infos.map (·.motive)) <|
      lctx.mkLambda minors minors[offset + ruleIndex]!
    unless rule.ctor == type.ctors[ruleIndex]!.name && rule.nfields == 0 &&
        rule.rhs == expected && !rule.rhs.hasFVar do
      throwError "incorrect threaded minor index for {type.name}, rule {ruleIndex}"
  discard <| checkExact ctx (statsFor types) types elimLevel infos lparams lctx isK isUnsafe env index offset

private def checkSuccess (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (lparams : List Name) (elimLevel : Level) (isK isUnsafe : Bool) : MetaM Unit := do
  let lctx := localsFor infos
  let .ok env := declareRecursors (statsFor types) types elimLevel infos lparams lctx isK isUnsafe
      { ctx with lctx }
    | throwError "low-level recursor registration unexpectedly failed"
  let mut offset := 0
  for index in [:types.size] do
    checkRecursor { ctx with lctx } types infos lparams elimLevel lctx env index offset isK isUnsafe
    offset := offset + types[index]!.ctors.length
  for name in [``Nat, ``Nat.zero, ``Nat.succ, ``Nat.rec, ``List, ``List.rec] do
    checkPreserved ctx.env env name
  unless env.quotInit == ctx.env.quotInit do throwError "recursor registration changed quotient state"

private def checkCollision (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (expected : Name) : MetaM Unit := do
  let lctx := localsFor infos
  let .error (.alreadyDeclared _ name) :=
    declareRecursors (statsFor types) types .zero infos [] lctx false false { ctx with lctx }
    | throwError "expected recursor freshness rejection"
  unless name == expected do throwError "incorrect recursor collision name {name}"

private def checkedStage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Level × Array RecInfo × LocalContext × Bool × Bool × Context × Kernel.Environment) :=
  checkInductiveTypes nparams types fun stats => do
    let isUnsafe := (← readThe Context).safety != .safe
    withEnv (← declareInductiveTypes stats nparams types 0 isUnsafe) do
      checkConstructors types stats isUnsafe
      withEnv (← declareConstructors stats types isUnsafe) do
        let elimLevel ← getElimLevel stats types
        mkRecInfos stats types elimLevel fun infos => do
          let lctx ← getLCtx
          let isK ← isKTarget stats types
          let source ← readThe Context
          let env ← declareRecursors stats types elimLevel infos source.lparams lctx isK isUnsafe
          return (stats, elimLevel, infos, lctx, isK, isUnsafe, source, env)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter (.sort (.succ .zero)) body .default) body

private def checkedHeader (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams (.sort (.succ .zero)), ctors }

private def checkChecked (ctx : Context) (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  let .ok (stats, elimLevel, infos, lctx, isK, isUnsafe, source, env) := checkedStage nparams types ctx
    | throwError "checked recursor fixture unexpectedly failed"
  let expectedParams := if types.isEmpty then 0 else nparams
  unless stats.params.size == expectedParams && infos.size == types.size &&
      (infos.flatMap (·.minors)).size == (types.toList.flatMap (·.ctors)).length do
    throwError "checked fixture does not supply the count-alignment premises"
  let mut minorIndex := 0
  for index in [:types.size] do
    unless infos[index]!.indices.size == stats.nindices[index]! do
      throwError "checked fixture does not align recursor and datatype indices"
    minorIndex ← checkExact source stats types elimLevel infos source.lparams lctx isK isUnsafe env index minorIndex
  for name in [``Nat, ``Nat.rec, ``List, ``List.rec] do checkPreserved source.env env name

private def audit (theoremName : Name) (mapInterfaces := true) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if mapInterfaces then [
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``declareRecursors.preserves
  audit ``declareRecursors.metadata
  audit ``InductiveStats.RecursorMetadata.sourceRules false
  audit ``InductiveStats.RecursorMetadata.declaredCounts false
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let first := typeFor `RecursorPreservedFirst [`RecursorPreservedFirst.left, `RecursorPreservedFirst.right]
  let empty := typeFor `RecursorPreservedEmpty []
  let last := typeFor `RecursorPreservedLast [`RecursorPreservedLast.last]
  let types := #[first, empty, last]
  let firstInfo := infoFor first.name #[`minorLeft, `minorRight]
  let emptyInfo := infoFor empty.name #[]
  let lastInfo := infoFor last.name #[`minorLast]
  let infos := #[firstInfo, emptyInfo, lastInfo]
  for allowPrimitive in [false, true] do
    for isK in [false, true] do
      for isUnsafe in [false, true] do
        let current := { ctx with allowPrimitive, safety := if isUnsafe then .unsafe else .safe }
        checkSuccess current #[] #[] [] .zero isK isUnsafe
        checkSuccess current #[empty] #[emptyInfo] [] .zero isK isUnsafe
        checkSuccess current types infos [`v] (.param `u) isK isUnsafe
  checkSuccess { ctx with safety := .unsafe } types infos [] .zero false false
  checkCollision ctx #[typeFor ``Nat []] #[emptyInfo] ``Nat.rec
  checkCollision ctx #[empty, typeFor ``Nat []] #[emptyInfo, lastInfo] ``Nat.rec
  checkCollision ctx #[empty, empty] #[emptyInfo, lastInfo] (mkRecName empty.name)
  let lctx := localsFor infos
  let .error .deepRecursion := declareRecursors (statsFor types) types .zero infos [] lctx false false
      { ctx with lctx, fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "rule-generation failure must propagate before registration"
  checkSuccess { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    #[empty] #[emptyInfo] [] .zero false false
  logInfo "26 successful recursor traversals, three freshness rejections, and one rule-generation failure passed"
  let natType := Expr.const ``Nat []
  let zero := Expr.const `CheckedMetaZero []
  let one := Expr.const `CheckedMetaOne []
  let other := Expr.const `CheckedMetaOther []
  let two := Expr.const `CheckedMetaTwo []
  let base : Constructor := { name := `CheckedMetaZero.base, type := zero }
  let recursive : Constructor := {
    name := `CheckedMetaZero.tail, type := .forallE `tail zero zero .default }
  let higher : Constructor := {
    name := `CheckedMetaZero.higher
    type := .forallE `function (.forallE `index natType zero .default) zero .implicit }
  let parameterOnly : Constructor := {
    name := `CheckedMetaOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterField : Constructor := {
    name := `CheckedMetaOne.value
    type := closeParams 1 (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let parameterRecursive : Constructor := {
    name := `CheckedMetaOne.tail
    type := closeParams 1 (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `CheckedMetaOne.mutual
    type := closeParams 1 (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherBase : Constructor := {
    name := `CheckedMetaOther.base, type := closeParams 1 (.app other (.bvar 0)) }
  let twoBase : Constructor := {
    name := `CheckedMetaTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let mutualTypes := #[checkedHeader `CheckedMetaOne 1 [parameterOnly, mutualCtor],
    checkedHeader `CheckedMetaOther 1 [otherBase]]
  checkChecked ctx 0 #[]
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 []]
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 [base, recursive, higher]]
  checkChecked ctx 1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterField, parameterRecursive]]
  checkChecked ctx 2 #[checkedHeader `CheckedMetaTwo 2 [twoBase]]
  checkChecked ctx 1 mutualTypes
  let indexed := Expr.const `CheckedMetaIndexed []
  checkChecked ctx 1 #[{
    name := `CheckedMetaIndexed
    type := closeParams 1 (.forallE `index natType (.sort (.succ .zero)) .default)
    ctors := [{
      name := `CheckedMetaIndexed.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }]
  checkChecked { ctx with
    ngen := { namePrefix := `MetadataSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing natType }
    1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterRecursive]]
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `CheckedMetaPoly [polyLevel]
  checkChecked { ctx with lparams := [`u] } 1 #[{
    name := `CheckedMetaPoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `CheckedMetaPoly.base
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }]
  let negative : Constructor := {
    name := `CheckedMetaZero.negative
    type := .forallE `function (.forallE `value zero natType .default) zero .default }
  checkChecked { ctx with safety := .unsafe } 0 #[checkedHeader `CheckedMetaZero 0 [negative]]
  checkChecked { ctx with allowPrimitive := true } 1 mutualTypes
  checkChecked { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
    1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterRecursive]]
  logInfo "12 checked recursor fixtures passed exact records, rule receipts, index/parameter/motive/minor counts"

end RecursorRegistrationTest
