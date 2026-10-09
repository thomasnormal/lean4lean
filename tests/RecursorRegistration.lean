import Lean4Lean.Verify.RecursorRegistration
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

private def checkRecursor (types : Array InductiveType) (infos : Array RecInfo)
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

private def checkSuccess (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (lparams : List Name) (elimLevel : Level) (isK isUnsafe : Bool) : MetaM Unit := do
  let lctx := localsFor infos
  let .ok env := declareRecursors (statsFor types) types elimLevel infos lparams lctx isK isUnsafe
      { ctx with lctx }
    | throwError "low-level recursor registration unexpectedly failed"
  let mut offset := 0
  for index in [:types.size] do
    checkRecursor types infos lparams elimLevel lctx env index offset isK isUnsafe
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

private def audit : MetaM Unit := do
  let theoremName := ``declareRecursors.preserves
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit
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

end RecursorRegistrationTest
