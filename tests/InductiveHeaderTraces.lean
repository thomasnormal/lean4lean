import Lean4Lean.Verify.InductiveHeaderTraces
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveHeaderTracesTest

abbrev IndexAlias := Nat → Type
abbrev ParameterAlias := (carrier : Type) → carrier → Type
abbrev CarrierAlias := Nat

example (nparams fuel : Nat) (stats : InductiveStats) (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ terminal finalStats finalIndices current,
      CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices current →
      ctx.RecursorScopeFrame current → (next terminal finalStats finalIndices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next ctx).WF post :=
  checkInductiveTypes.loopInd.loop.scopedTrace nparams fuel stats type index nindices next ctx post hwf hreserved hnext

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    ∀ name domain body bi, terminal ≠ .forallE name domain body bi := trace.terminal

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    index ≤ nparams ∧ nindices ≤ finalIndices := trace.countBounds

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    finalStats.nindices = stats.nindices ∧ finalStats.indConsts = stats.indConsts ∧ finalStats.levels = stats.levels :=
  trace.headerFields

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hparams : stats.params.size = if stats.indConsts.isEmpty then index else nparams) :
    finalStats.params.size = nparams := trace.paramsCount hparams

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hfirst : ¬ stats.indConsts.isEmpty = true) : finalStats.params = stats.params := trace.paramsUnchanged hfirst

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx) :
    stats.params.toList.Sublist finalStats.params.toList := trace.paramsSublist

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) : ctx.RecursorScopeFrame finalCtx :=
  trace.scope hwf hreserved

example {nparams parent count : Nat} {types : Array InductiveType} {original current next : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current)
    (frame : current.RecursorScopeFrame next) : CheckedHeaderSource nparams types parent original params count next :=
  source.mono frame

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current) :
    original.env.checkNoMVarNoFVar types[parent]!.name types[parent]!.type = .ok () := source.guarded

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current) :
    params.size = nparams := source.paramsCount

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current) :
    original.RecursorScopeFrame current := source.scope

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M α) (ctx : Context)
    (post : α → Prop) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, CheckedHeaderSources nparams types ctx stats current →
      ctx.RecursorScopeFrame current → (next stats current).WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.scopedHeaderTraces nparams types next ctx post hwf hreserved hnext

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx).WF
      fun result => CheckedHeaderSources nparams types ctx result.1 result.2 ∧
        ctx.RecursorScopeFrame result.2 ∧ result.1.ParamsCount nparams types.size ∧
        result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup :=
  checkInductiveTypes.getHeaderTraces nparams types ctx hwf hreserved

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (stats : InductiveStats) (current : Context)
    (hresult : checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx =
      .ok (stats, current)) (parent : Nat) (hparent : parent < types.size) :
    CheckedHeaderSource nparams types parent ctx stats.params stats.nindices[parent]! current :=
  (checkInductiveTypes.getHeaderTraces nparams types ctx hwf hreserved _ hresult).1.2 parent hparent

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hwrong : nparams < index) : False := by have hbound := trace.countBounds.1; omega

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (hwrong : finalIndices < nindices) : False := by have hbound := trace.countBounds.2; omega

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (name : Name) (domain body : Expr) (bi : BinderInfo) (hwrong : terminal = .forallE name domain body bi) : False :=
  trace.terminal name domain body bi hwrong

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current)
    (hwrong : params.size ≠ nparams) : False := hwrong source.paramsCount

example {nparams : Nat} {types : Array InductiveType} {original current : Context} {stats : InductiveStats}
    (sources : CheckedHeaderSources nparams types original stats current)
    (hwrong : stats.nindices.size ≠ types.size) : False := hwrong sources.1.1

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context}
    {params : Array Expr} (source : CheckedHeaderSource nparams types parent original params count current)
    (hwrong : original.env.checkNoMVarNoFVar types[parent]!.name types[parent]!.type ≠ .ok ()) : False :=
  hwrong source.guarded

private def sortType : Expr := .sort (.succ .zero)

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `index (.const ``Nat []) body .implicit) sortType

private def header (name : Name) (type : Expr := sortType) : InductiveType := { name, type, ctors := [] }

private def stage (nparams : Nat) (types : Array InductiveType) : M (InductiveStats × Context) :=
  checkInductiveTypes nparams types fun stats => do return (stats, ← readThe Context)

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (counts : Array Nat) (strictRaw := false) : MetaM Unit := do
  let .ok (stats, source) := stage nparams types ctx | throwError "checked-header trace fixture failed"
  let params := if types.isEmpty then 0 else nparams
  unless stats.nindices == counts && stats.params.size == params && stats.indConsts.size == types.size do
    throwError "checked-header trace lost its returned binder counts"
  let allocated := params + counts.foldl (· + ·) 0
  unless source.ngen.idx == ctx.ngen.idx + allocated && source.lctx.numIndices == ctx.lctx.numIndices + allocated do
    throwError "checked-header trace allocation readers changed"
  for decl in ctx.lctx do
    let some retained := source.lctx.find? decl.fvarId | throwError "checked-header trace dropped an old local"
    unless retained.toExpr == decl.toExpr && retained.type == decl.type do
      throwError "checked-header trace changed an old local"
  for param in stats.params do
    unless param.isFVar && (source.lctx.find? param.fvarId!).isSome do
      throwError "checked-header trace lost its shared parameter"
  if strictRaw then
    unless declareConstructors.arity 0 types[0]!.type < params + counts[0]! do
      throwError "normalized header must expose a strict raw-arity gap"

private def fixtures (ctx : Context) : MetaM Unit := do
  let dependent := Expr.forallE `carrier sortType (.forallE `index (.bvar 0) sortType .strictImplicit) .default
  let three := Expr.forallE `carrier sortType (.forallE `first (.bvar 0)
    (.forallE `second (.bvar 1) sortType .implicit) .default) .instImplicit
  checkFixture ctx 0 #[] #[]
  checkFixture ctx 0 #[header `TraceZero] #[0]
  checkFixture ctx 0 #[header `TraceFirst (indexed 1), header `TraceSecond (indexed 2)] #[1, 2]
  checkFixture ctx 1 #[header `TraceFirst dependent, header `TraceSecond dependent] #[1, 1]
  checkFixture ctx 2 #[header `TraceFirst three, header `TraceSecond three] #[1, 1]
  checkFixture ctx 0 #[header `TraceAlias (.const ``IndexAlias [])] #[1] true
  checkFixture ctx 1 #[header `TraceAlias (.const ``ParameterAlias []), header `TraceSecond dependent] #[1, 1] true
  checkFixture ctx 0 #[header `TraceAnnotated (.mdata {} (indexed 2))] #[2] true
  let beta := Expr.app (.lam `carrier sortType (.forallE `index (.bvar 0) sortType .default) .default) (.const ``Nat [])
  checkFixture ctx 0 #[header `TraceBeta beta] #[1] true
  let letType := Expr.letE `carrier sortType (.const ``Nat []) (.forallE `index (.bvar 0) sortType .default) false
  checkFixture ctx 0 #[header `TraceLet letType] #[1] true
  let tailAlias := Expr.forallE `carrier sortType (.const ``IndexAlias []) .implicit
  checkFixture ctx 1 #[header `TraceFirst tailAlias, header `TraceSecond tailAlias] #[1, 1] true
  let originalDomain := Expr.forallE `parameter (.const ``Nat []) (indexed 1) .default
  let aliasDomain := Expr.forallE `renamed (.const ``CarrierAlias []) (indexed 2) .strictImplicit
  checkFixture ctx 1 #[header `TraceFirst originalDomain, header `TraceSecond aliasDomain] #[1, 2]
  checkFixture { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } } 1 #[header `TraceExactFuel dependent] #[1]
  checkFixture { ctx with lparams := [`u] } 1 #[header `TracePoly
    (.forallE `carrier (.sort (.param `u)) (.sort (.param `u)) .default)] #[0]
  let seeded := { ctx with
    ngen := { namePrefix := `HeaderTraceSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `HeaderTraceSeed 16⟩ `old (.const ``Bool []) .implicit }
  checkFixture seeded 1 #[header `TraceFirst dependent, header `TraceSecond three] #[1, 2]
  logInfo "fifteen checked-header trace fixtures passed stored counts, allocation readers and shared parameters; six expose raw/normalized gaps"

private def expectFailure (result : Except Kernel.Exception α) (label : String) : MetaM Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throwError "{label} unexpectedly succeeded"

private def failures (ctx : Context) : MetaM Unit := do
  let param := Expr.forallE `carrier sortType sortType .default
  let wrong := Expr.forallE `carrier (.const ``Nat []) sortType .default
  expectFailure (stage 0 #[header `TraceFree (.fvar ⟨`MissingHeader⟩)] ctx) "source free variable"
  expectFailure (stage 0 #[header `TraceMeta (.mvar ⟨`MissingHeader⟩)] ctx) "source metavariable"
  expectFailure (stage 0 #[header `TraceNotType (.const ``Nat.zero [])] ctx) "non-sort terminal"
  expectFailure (stage 0 #[header `TraceUnknown (.const `MissingHeader [])] ctx) "unknown constant"
  expectFailure (stage 2 #[header `TraceShort param] ctx) "unconsumed parameters"
  expectFailure (stage 1 #[header `TraceFirst param, header `TraceSecond wrong] ctx) "mutual parameter domain mismatch"
  expectFailure (stage 0 #[header `TraceFirst, header `TraceSecond (.sort (.succ (.succ .zero)))] ctx) "mutual universe mismatch"
  let .error .deepRecursion := stage 0 #[header `TraceFuel] { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "zero-fuel diagnostic changed"
  let .error .deepRecursion := stage 0 #[header `TraceFuel (indexed 2)]
      { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } } | throwError "partial traversal fuel diagnostic changed"
  let .error (.other sentinel) := checkInductiveTypes 0 #[header `TraceSentinel]
      (fun _ => (throw (.other "header trace sentinel") : M Unit)) ctx | throwError "continuation failure swallowed"
  unless sentinel == "header trace sentinel" do throwError "continuation diagnostic changed"
  logInfo "ten source/type/parameter/universe/fuel/continuation failures retain checked-header boundaries"

private def boundaries (ctx : Context) : MetaM Unit := do
  let stats : InductiveStats := default
  let next := fun terminal (stats : InductiveStats) count => (pure (terminal, stats.params.size, count) : M _)
  let .ok (_, 0, 99) := checkInductiveTypes.loopInd.loop 1 stats sortType 1 99 1 next ctx
    | throwError "unchecked helper must not certify the initial parameter vector or index count"
  let .ok (terminal, 0, 0) := checkInductiveTypes.loopInd.loop 0 stats (.const ``Nat.zero []) 0 0 1 next ctx
    | throwError "unchecked terminal helper must not establish terminal-sort validity"
  unless terminal == .const ``Nat.zero [] do throwError "unchecked helper changed its terminal expression"
  let .error (.other mismatch) := checkInductiveTypes.loopInd.loop 1 stats sortType 0 0 1 next ctx
    | throwError "checked traversal must reject unconsumed parameters even before the enclosing sort check"
  unless mismatch == "number of parameters mismatch in inductive datatype declaration" do
    throwError "terminal parameter mismatch diagnostic changed"
  logInfo "three helper boundaries separate initial statistic validity, terminal-sort checking and complete parameter consumption"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let scope := [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  audit ``checkInductiveTypes.loopInd.loop.scopedTrace scope
  audit ``CheckedHeaderTrace.terminal
  audit ``CheckedHeaderTrace.countBounds
  audit ``CheckedHeaderTrace.headerFields
  audit ``CheckedHeaderTrace.paramsCount
  audit ``CheckedHeaderTrace.paramsUnchanged
  audit ``CheckedHeaderTrace.paramsSublist
  audit ``CheckedHeaderTrace.scope scope
  audit ``CheckedHeaderSource.mono
  audit ``CheckedHeaderSource.guarded
  audit ``CheckedHeaderSource.paramsCount
  audit ``CheckedHeaderSource.scope scope
  audit ``checkInductiveTypes.scopedHeaderTraces scope
  audit ``checkInductiveTypes.getHeaderTraces scope
  let ctx : Context := { env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  failures ctx
  boundaries ctx

end InductiveHeaderTracesTest
