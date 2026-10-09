import Lean4Lean.Verify.RecursorInfoIndices
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace RecursorInfoIndicesTest

abbrev IndexTypeAlias := Nat → Type

example (stats : InductiveStats) (type : Expr) (index : Nat) (indices : Array Expr) (fuel : Nat)
    (next : Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ terminal finalIndex finalIndices current,
      RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices current →
      ctx.RecursorScopeFrame current → (next finalIndices current).WF post) :
    (mkRecInfos.loopArgs1 stats type index indices fuel next ctx).WF post :=
  mkRecInfos.loopArgs1.scopedTrace stats type index indices fuel next ctx post hwf hreserved hnext

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    ∀ name domain body bi, terminal ≠ .forallE name domain body bi := trace.terminal

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    indices.size ≤ finalIndices.size := trace.indexSize

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx) :
    index ≤ finalIndex ∧ finalIndex ≤ max index stats.params.size := trace.parameterRange

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hparams : stats.ParamsAreFVars) :
    index + indices.size + declareConstructors.arity 0 type ≤ finalIndex + finalIndices.size := trace.rawArity hparams

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) : ctx.RecursorScopeFrame finalCtx :=
  trace.scope hwf hreserved

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hdeclared : RecursorFieldsDeclared ctx.lctx indices) : RecursorFieldsDeclared finalCtx.lctx finalIndices :=
  trace.declared hdeclared

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current next : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (frame : current.RecursorScopeFrame next) : RecursorInfoIndexSource stats types elimLevel parent original info next :=
  source.mono frame

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) (minors : Array Expr) :
    RecursorInfoIndexSource stats types elimLevel parent original { info with minors } current := source.withMinors minors

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) :
    RecursorFieldsDeclared current.lctx ((info.indices.push info.major).push info.motive) := source.declared

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) :
    ∃ decl, current.lctx.find? info.major.fvarId! = some decl ∧ decl.toExpr = info.major ∧
      decl.type = recursorMajorDomain stats parent info.indices := source.majorLookup

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) (hparams : stats.ParamsAreFVars) :
    declareConstructors.arity 0 types[parent]!.type ≤ stats.params.size + info.indices.size := source.rawArity hparams

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : RecursorInfoIndexSources stats types elimLevel original infos current) (hparams : stats.ParamsAreFVars) :
    ∀ parent, parent < types.size →
      declareConstructors.arity 0 types[parent]!.type ≤ stats.params.size + infos[parent]!.indices.size :=
  sources.rawArities hparams

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedIndexSources stats types elimLevel next ctx post hwf hreserved hnext

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 :=
  mkRecInfos.getIndexSources stats types elimLevel ctx hwf hreserved

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (lparams : List Name)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 :=
  mkRecInfos.registeredIndexSources stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv

example (stats : InductiveStats) (ctx : Context) (indices : Array Expr) (index : Nat) :
    RecursorIndexTrace stats (.sort .zero) index indices ctx (.sort .zero) index indices ctx :=
  .stop (by intro name domain body bi heq; cases heq)

example (stats : InductiveStats) (ctx : Context) :
    mkRecInfos.loopArgs1 stats (.sort .zero) 0 #[] 1 (fun indices => do return (indices, ← readThe Context)) ctx =
      .ok (#[], ctx) := rfl

example (stats : InductiveStats) (type : Expr) (index : Nat) (indices : Array Expr)
    (next : Array Expr → M α) (ctx : Context) :
    mkRecInfos.loopArgs1 stats type index indices 0 next ctx = .error .deepRecursion := rfl

example (stats : InductiveStats) (elimLevel : Level) (ctx : Context) :
    mkRecInfos stats #[] elimLevel (fun infos => do return (infos, ← readThe Context)) ctx = .ok (#[], ctx) := by
  simp [mkRecInfos, mkRecInfos.loopInd1.eq_def, mkRecInfos.loopInd2.eq_def]
  rfl

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hwrong : finalIndex < index) : False := by have hbound := trace.parameterRange.1; omega

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (hwrong : finalIndices.size < indices.size) : False := by have hbound := trace.indexSize; omega

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (name : Name) (domain body : Expr) (bi : BinderInfo) (hwrong : terminal = .forallE name domain body bi) : False :=
  trace.terminal name domain body bi hwrong

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : RecursorInfoIndexSources stats types elimLevel original infos current)
    (hwrong : infos.size ≠ types.size) : False := hwrong sources.1

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hmissing : current.lctx.find? info.major.fvarId! = none) : False := by
  obtain ⟨decl, hlookup, _⟩ := source.majorLookup
  rw [hmissing] at hlookup
  cases hlookup

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current) (decl : LocalDecl)
    (hlookup : current.lctx.find? info.major.fvarId! = some decl)
    (hwrong : decl.type ≠ recursorMajorDomain stats parent info.indices) : False := by
  obtain ⟨actual, hactual, _, htype⟩ := source.majorLookup
  have heq := Option.some.inj (hactual.symm.trans hlookup)
  exact hwrong (heq ▸ htype)

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let ctx ← readThe Context
    let headers ← declareInductiveTypes stats nparams types 0 false
    let root := { ctx with env := headers }
    checkConstructors types stats false root
    let constructors ← declareConstructors stats types false root
    let source := { root with env := constructors }
    let (infos, current) ← mkRecInfos stats types (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) source
    return (stats, source, infos, current)

private def checkInfo (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (info : RecInfo) (source : Context) : MetaM Unit := do
  unless info.indices.size == stats.nindices[parent]! &&
      declareConstructors.arity 0 types[parent]!.type ≤ stats.params.size + info.indices.size do
    throwError "checked header/index counts or raw-arity bound disagree"
  let some major := source.lctx.find? info.major.fvarId! | throwError "major declaration missing"
  unless major.toExpr == info.major && major.type == recursorMajorDomain stats parent info.indices do
    throwError "major declaration lost literal datatype application"
  let some motive := source.lctx.find? info.motive.fvarId! | throwError "motive declaration missing"
  unless motive.toExpr == info.motive && motive.userName == recursorMotiveName types parent &&
      motive.type == recursorMotiveDomain (.succ .zero) info.indices info.major source do
    throwError "motive declaration lost literal source binders"
  for field in (info.indices.push info.major).push info.motive do
    let some decl := source.lctx.find? field.fvarId! | throwError "generated binder missing"
    unless decl.toExpr == field && (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "generated binder lost its declaration shape"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) (strictRaw := false) : MetaM Unit := do
  let .ok (stats, root, infos, source) := stage nparams types ctx | throwError "checked index-source stage failed"
  unless stats.nindices == expected && infos.size == types.size do throwError "fixture has wrong checked header counts"
  for parent in [:types.size] do
    checkInfo stats types parent infos[parent]! source
  if strictRaw then
    unless declareConstructors.arity 0 types[0]!.type < stats.params.size + infos[0]!.indices.size do
      throwError "alias fixture must expose a strictly larger normalized binder count"
  let .ok (_, registeredInfos, registeredSource) :=
    mkRecInfos.scopeRegistration stats types (.succ .zero) ctx.lparams false false root
    | throwError "index-source registration failed"
  for parent in [:types.size] do
    checkInfo stats types parent registeredInfos[parent]! registeredSource
    unless registeredInfos[parent]!.indices == infos[parent]!.indices &&
        registeredInfos[parent]!.major == infos[parent]!.major && registeredInfos[parent]!.motive == infos[parent]!.motive do
      throwError "registration changed the same successful header source witnesses"

private def header (name : Name) (indices : Nat) : InductiveType :=
  { name, type := (List.range indices).foldr
      (fun _ body => .forallE `index (.const ``Nat []) body .implicit) (.sort (.succ .zero)), ctors := [] }

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `IndexSourceEmpty 0] #[0]
  checkFixture ctx 0 #[header `IndexSourceOne 1] #[1]
  checkFixture ctx 0 #[header `IndexSourceMany 33] #[33]
  checkFixture ctx 0 #[header `IndexSourceLeft 0, header `IndexSourceMiddle 2, header `IndexSourceRight 1] #[0, 2, 1]
  checkFixture ctx 0 #[{ name := `IndexSourceAlias, type := .const ``IndexTypeAlias [], ctors := [] }] #[1] true
  checkFixture ctx 1 #[{
    name := `IndexSourceParamAlias
    type := .forallE `parameter (.sort (.succ .zero)) (.const ``IndexTypeAlias []) .default
    ctors := [] }] #[1] true
  checkFixture ctx 1 #[{
    name := `IndexSourceDependent
    type := .forallE `parameter (.sort (.succ .zero))
      (.forallE `index (.bvar 0) (.sort (.succ .zero)) .default) .default
    ctors := [] }] #[1]
  checkFixture ctx 0 #[{
    name := `IndexSourceRecursive
    type := .sort (.succ .zero)
    ctors := [
      { name := `IndexSourceRecursive.zero, type := .const `IndexSourceRecursive [] },
      { name := `IndexSourceRecursive.step,
        type := .forallE `field (.const `IndexSourceRecursive []) (.const `IndexSourceRecursive []) .default }] }] #[0]
  let seeded := { ctx with
    ngen := { namePrefix := `IndexSourceSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `IndexSourceSeed 2⟩ `old (.const ``Nat []) .default }
  checkFixture seeded 0 #[header `IndexSourceSeeded 2] #[2]
  checkFixture { ctx with lparams := [`u] } 1 #[{
    name := `IndexSourcePoly
    type := .forallE `parameter (.sort (.param `u)) (.sort (.param `u)) .default
    ctors := [] }] #[0]
  logInfo "ten checked index-source fixtures and registrations passed header counts, raw bounds and major/motive declarations; two aliases expose strict raw/normalized gaps"

private def boundaries (ctx : Context) : MetaM Unit := do
  let stats := { (default : InductiveStats) with params := #[.fvar ⟨`MissingParameter⟩] }
  let .ok (#[], source) := mkRecInfos.loopArgs1 stats (.sort .zero) 0 #[] 1
      (fun indices => do return (indices, ← readThe Context)) ctx | throwError "partial parameter boundary changed"
  unless source.ngen.idx == ctx.ngen.idx do throwError "terminal helper allocates no parameters or indices"
  let .error .deepRecursion := mkRecInfos.loopArgs1 stats (.sort .zero) 0 #[] 0 pure ctx
    | throwError "zero-fuel boundary changed"
  let types := #[header `IndexSourceFuel 3]
  let .error .deepRecursion := stage 0 types { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    | throwError "partially consumed checked header must fail"
  let .ok (checkedStats, root, _, _) := stage 0 types ctx | throwError "partial recursor setup failed"
  let .error .deepRecursion := mkRecInfos checkedStats types (.succ .zero) pure
      { root with fuel := { root.fuel with inductiveFuel := 2 } } | throwError "partially consumed recursor indices must fail"
  let inconsistentStats := { checkedStats with nindices := #[99] }
  let .ok inconsistentInfos := mkRecInfos inconsistentStats types (.succ .zero) pure root
    | throwError "unchecked index-count boundary changed"
  unless inconsistentInfos[0]!.indices.size == 3 && inconsistentStats.nindices[0]! == 99 do
    throwError "bare recursor-info generation must not certify unchecked stored index counts"
  let unchecked : Array InductiveType := #[{
    name := `IndexSourceUnchecked
    type := .fvar ⟨`UndeclaredIndexHeader⟩
    ctors := [] }]
  let uncheckedStats := { (default : InductiveStats) with
    indConsts := #[.const `IndexSourceUnchecked []]
    nindices := #[0] }
  let .ok (_, untyped) := mkRecInfos uncheckedStats unchecked (.succ .zero)
      (fun infos => do return (infos, ← readThe Context)) ctx | throwError "untyped-header boundary changed"
  unless (untyped.lctx.find? ⟨`UndeclaredIndexHeader⟩).isNone do
    throwError "index-source receipts must not establish unchecked header typing"
  logInfo "partial-parameter terminal, zero fuel, partial header/recursor traversals and unchecked header/index-count boundaries passed"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let scope := [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let registration := scope ++ [``Lean.PersistentHashMap.findAux_isSome]
  audit ``mkRecInfos.loopArgs1.scopedTrace scope
  audit ``RecursorIndexTrace.terminal
  audit ``RecursorIndexTrace.indexSize
  audit ``RecursorIndexTrace.parameterRange
  audit ``RecursorIndexTrace.rawArity [``Expr.instantiate1_eq]
  audit ``RecursorIndexTrace.scope scope
  audit ``RecursorIndexTrace.declared scope
  audit ``RecursorInfoIndexSource.mono
  audit ``RecursorInfoIndexSource.withMinors
  audit ``RecursorInfoIndexSource.declared scope
  audit ``RecursorInfoIndexSource.majorLookup scope
  audit ``RecursorInfoIndexSource.rawArity [``Expr.instantiate1_eq]
  audit ``RecursorInfoIndexSources.rawArities [``Expr.instantiate1_eq]
  audit ``mkRecInfos.scopedIndexSources scope
  audit ``mkRecInfos.getIndexSources scope
  audit ``mkRecInfos.registeredIndexSources registration
  let ctx : Context := { env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  boundaries ctx

end RecursorInfoIndicesTest
