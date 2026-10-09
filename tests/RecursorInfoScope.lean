import Lean4Lean.Verify.RecursorInfoScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.loopArgs1_scope Lean4Lean.AddInductive.loopInd1_scope
  Lean4Lean.AddInductive.loopU_scope Lean4Lean.AddInductive.loopCtors_scope
  Lean4Lean.AddInductive.loopInd2_scope from Lean4Lean.Verify.RecursorInfoScope

namespace RecursorInfoScopeTest

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scope stats types elimLevel next ctx post hwf hreserved hnext

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF
      fun result => ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 :=
  mkRecInfos.getScopeCounts stats types elimLevel ctx hwf hreserved

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (infos : Array RecInfo) (current : Context)
    (hresult : mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx =
      .ok (infos, current)) : current.lctx.WF ∧ ContextReserved current.lctx current.ngen := by
  obtain ⟨hframe, _⟩ := mkRecInfos.getScopeCounts stats types elimLevel ctx hwf hreserved _ hresult
  exact ⟨hframe.wf, hframe.reserved⟩

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (infos : Array RecInfo) (current : Context)
    (hresult : mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx =
      .ok (infos, current)) (fvar : FVarId) (decl : LocalDecl)
    (hlookup : ctx.lctx.find? fvar = some decl) : current.lctx.find? fvar = some decl :=
  (mkRecInfos.getScopeCounts stats types elimLevel ctx hwf hreserved _ hresult).1.oldLookup hwf hlookup

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 :=
  mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (env : Kernel.Environment) (infos : Array RecInfo) (source : Context)
    (hresult : mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx =
      .ok (env, infos, source)) : LocalRecursorRuleRhsScope stats types infos source env :=
  (mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv _ hresult).2.2.2.2.2

private def infoStage (stats : InductiveStats) (types : Array InductiveType) :
    M (Array RecInfo × Context) :=
  mkRecInfos stats types (.succ .zero) fun infos => do return (infos, ← readThe Context)

private def prepared (stats : InductiveStats) (types : Array InductiveType) : M Context := do
  let ctx ← readThe Context
  let headers ← declareInductiveTypes stats stats.params.size types 0 false
  let constructors ← declareConstructors stats types false { ctx with env := headers }
  return { ctx with env := constructors }

private def checkContext (original current : Context) : MetaM Unit := do
  unless current.ngen.namePrefix == original.ngen.namePrefix && current.ngen.idx >= original.ngen.idx &&
      current.lctx.numIndices == original.lctx.numIndices + (current.ngen.idx - original.ngen.idx) &&
      (current.lctx.find? ⟨current.ngen.curr⟩).isNone do
    throwError "incorrect source reader advancement or next-name freshness"
  for decl in current.lctx do
    let some found := current.lctx.find? decl.fvarId | throwError "source declaration has no native lookup"
    unless found.index == decl.index && found.type == decl.type && found.toExpr == decl.toExpr do
      throwError "source declaration list/map disagreement"
  for decl in original.lctx do
    let some found := current.lctx.find? decl.fvarId | throwError "old source declaration disappeared"
    unless found.index == decl.index && found.type == decl.type &&
        found.value? (allowNondep := true) == decl.value? (allowNondep := true) do
      throwError "old source lookup changed"

private def checkInfo (source : Context) (type : InductiveType) (info : RecInfo) (indices : Nat) : MetaM Unit := do
  unless info.indices.size == indices && info.minors.size == type.ctors.length do
    throwError "incorrect index/minor count"
  for field in info.indices ++ #[info.major, info.motive] ++ info.minors do
    unless field.isFVar do throwError "recursor-info binder is not a free-variable atom"
    let some decl := source.lctx.find? field.fvarId! | throwError "recursor-info binder is absent from source reader"
    unless decl.toExpr == field && (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "incorrect recursor-info declaration shape"

private def checkFixture (ctx : Context) (stats : InductiveStats) (types : Array InductiveType) : MetaM Unit := do
  let .ok root := prepared stats types ctx | throwError "fixture registration failed"
  let .ok (infos, source) := infoStage stats types root | throwError "recursor-info generation failed"
  checkContext root source
  unless infos.size == types.size do throwError "incorrect source recursor-info count"
  for index in [:types.size] do
    checkInfo source types[index]! infos[index]! stats.nindices[index]!
  let .ok (env, registeredInfos, registeredSource) :=
      mkRecInfos.scopeRegistration stats types (.succ .zero) ctx.lparams false false root
    | throwError "source scope registration failed"
  checkContext root registeredSource
  unless registeredSource.ngen.idx == source.ngen.idx && registeredSource.ngen.namePrefix == source.ngen.namePrefix &&
      registeredSource.lctx.numIndices == source.lctx.numIndices &&
      registeredInfos.size == infos.size do throwError "registration changed retained source witnesses"
  for index in [:types.size] do
    let some (.recInfo recursor) := env.find? (mkRecName types[index]!.name) | throwError "missing registered recursor"
    unless recursor.rules.length == types[index]!.ctors.length &&
        recursor.numMinors == (infos.flatMap (·.minors)).size do throwError "incorrect scoped recursor counts"

private def statsFor (types : Array InductiveType) (indices : Array Nat) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, params := #[], isNotZero := true,
  indConsts := types.map fun type => .const type.name [], nindices := indices }

private def typeFor (name : Name) (ctors : List Constructor := []) : InductiveType := {
  name, type := .sort (.succ .zero), ctors }

private def checkFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  checkFixture ctx (statsFor #[] #[]) #[]
  let empty := #[typeFor `ScopeInfoEmpty]
  checkFixture ctx (statsFor empty #[0]) empty
  let root := Expr.const `ScopeInfoSimple []
  let simple := #[typeFor `ScopeInfoSimple [{ name := `ScopeInfoSimple.mk, type := root }]]
  checkFixture ctx (statsFor simple #[0]) simple
  let recursive := #[typeFor `ScopeInfoRec [
    { name := `ScopeInfoRec.zero, type := .const `ScopeInfoRec [] },
    { name := `ScopeInfoRec.step, type := .forallE `field (.const `ScopeInfoRec []) (.const `ScopeInfoRec []) .implicit }]]
  checkFixture ctx (statsFor recursive #[0]) recursive
  let higher := #[typeFor `ScopeInfoHigher [{
    name := `ScopeInfoHigher.mk
    type := .forallE `field (.forallE `argument natType (.const `ScopeInfoHigher []) .default)
      (.const `ScopeInfoHigher []) .default }]]
  checkFixture ctx (statsFor higher #[0]) higher
  let indexed : Array InductiveType := #[{
    name := `ScopeInfoIndexed
    type := .forallE `index natType (.sort (.succ .zero)) .implicit
    ctors := [{
      name := `ScopeInfoIndexed.mk
      type := .forallE `index natType (.app (.const `ScopeInfoIndexed []) (.bvar 0)) .default }] }]
  checkFixture ctx (statsFor indexed #[1]) indexed
  let mutualTypes := #[typeFor `ScopeInfoLeft [{
      name := `ScopeInfoLeft.mk
      type := .forallE `right (.const `ScopeInfoRight []) (.const `ScopeInfoLeft []) .default }],
    typeFor `ScopeInfoMiddle, typeFor `ScopeInfoRight [{ name := `ScopeInfoRight.mk, type := .const `ScopeInfoRight [] }]]
  checkFixture ctx (statsFor mutualTypes #[0, 0, 0]) mutualTypes
  let old : FVarId := ⟨.num `InfoSeed 2⟩
  let seeded := { ctx with
    ngen := { namePrefix := `InfoSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl old `parameter (.sort (.succ .zero)) .default }
  let parameterized : Array InductiveType := #[{
    name := `ScopeInfoParam
    type := .forallE `parameter (.sort (.succ .zero)) (.sort (.succ .zero)) .default
    ctors := [{
      name := `ScopeInfoParam.mk
      type := .forallE `parameter (.sort (.succ .zero))
        (.forallE `field (.bvar 0) (.app (.const `ScopeInfoParam []) (.bvar 1)) .default) .default }] }]
  checkFixture seeded { (statsFor parameterized #[0]) with params := #[.fvar old] } parameterized
  let manyType := (List.range 33).foldr
    (fun _ body => .forallE `field (.const `ScopeInfoMany []) body .implicit) (.const `ScopeInfoMany [])
  let many := #[typeFor `ScopeInfoMany [{ name := `ScopeInfoMany.mk, type := manyType }]]
  checkFixture ctx (statsFor many #[0]) many
  logInfo "nine recursor-info source fixtures and registrations passed native declarations, old lookups, counts, and freshness"

private def checkFailures (ctx : Context) : MetaM Unit := do
  let types := #[typeFor `ScopeInfoFuel]
  let stats := statsFor types #[0]
  let .ok root := prepared stats types ctx | throwError "fuel fixture setup failed"
  let .error .deepRecursion := infoStage stats types
      { root with fuel := { root.fuel with inductiveFuel := 0 } } | throwError "source zero-fuel failure was lost"
  let partialType := Expr.forallE `field (.const ``Nat [])
    (.forallE `field (.const ``Nat []) (.const `ScopeInfoPartial []) .default) .default
  let partialTypes := #[typeFor `ScopeInfoPartial [{ name := `ScopeInfoPartial.mk, type := partialType }]]
  let partialStats := statsFor partialTypes #[0]
  let .ok partialRoot := prepared partialStats partialTypes ctx | throwError "partial-fuel setup failed"
  let .error .deepRecursion := infoStage partialStats partialTypes
      { partialRoot with fuel := { partialRoot.fuel with inductiveFuel := 2 } }
    | throwError "source partially allocated traversal must fail"
  let bad : Array InductiveType := #[{ name := `ScopeInfoBad, type := .fvar ⟨`UndeclaredHeader⟩, ctors := [] }]
  let .ok (_, untyped) := infoStage (statsFor bad #[0]) bad ctx | throwError "untyped-header control failed"
  unless (untyped.lctx.find? ⟨`UndeclaredHeader⟩).isNone do
    throwError "structural source validity must not establish source header typing"
  logInfo "two source fuel failures and an unchecked untyped-header boundary passed"

private def audit (theoremName : Name) (registration := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let allowed := allowed ++ if registration then [``Lean.PersistentHashMap.findAux_isSome] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``Lean4Lean.AddInductive.loopArgs1_scope, ``Lean4Lean.AddInductive.loopInd1_scope,
      ``Lean4Lean.AddInductive.loopU_scope, ``Lean4Lean.AddInductive.loopCtors_scope,
      ``Lean4Lean.AddInductive.loopInd2_scope, ``mkRecInfos.scope, ``mkRecInfos.getScopeCounts] do
    audit theoremName
  audit ``mkRecInfos.registeredScope true
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  checkFixtures ctx
  checkFailures ctx

end RecursorInfoScopeTest
