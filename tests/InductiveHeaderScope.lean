import Lean4Lean.Verify.InductiveHeaderScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.checkedHeader_loop_scope Lean4Lean.AddInductive.checkedHeader_loopInd_scope
  from Lean4Lean.Verify.InductiveHeaderScope

namespace InductiveHeaderScopeTest

abbrev NormalizedHeader := Type → Nat → Type

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M ResultType)
    (ctx : Context) (post : ResultType → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats current, ctx.RecursorScopeFrame current → (next stats current).WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.scope nparams types next ctx post hwf hreserved hnext

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx).WF
      fun result => ctx.RecursorScopeFrame result.2 ∧ result.1.HeaderSizes types.size ∧
        result.1.ParamsCount nparams types.size ∧ result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup :=
  checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (stats : InductiveStats) (current : Context)
    (hresult : checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx =
      .ok (stats, current)) : current.lctx.WF ∧ ContextReserved current.lctx current.ngen := by
  have hframe := (checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved _ hresult).1
  exact ⟨hframe.wf, hframe.reserved⟩

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (stats : InductiveStats) (current : Context)
    (hresult : checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx =
      .ok (stats, current)) : ctx.lctx.toList.Sublist current.lctx.toList :=
  (checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved _ hresult).1.declarations

example (nparams : Nat) (types : Array InductiveType) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (stats : InductiveStats) (current : Context)
    (hresult : checkInductiveTypes nparams types (fun stats => do return (stats, ← readThe Context)) ctx =
      .ok (stats, current)) (fvar : FVarId) (decl : LocalDecl)
    (hlookup : ctx.lctx.find? fvar = some decl) : current.lctx.find? fvar = some decl :=
  (checkInductiveTypes.getScopeStats nparams types ctx hwf hreserved _ hresult).1.oldLookup hwf hlookup

example {original current : Context} (hframe : original.RecursorScopeFrame current)
    (env : Kernel.Environment) :
    ({ original with env } : Context).RecursorScopeFrame { current with env } := hframe.withEnv env

example (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (nparams : Nat) :
    (checkInductiveTypes nparams #[] (fun stats => do return (stats, ← readThe Context)) ctx).WF
      fun result => ctx.RecursorScopeFrame result.2 ∧ result.1.HeaderSizes 0 ∧
        result.1.ParamsCount nparams 0 ∧ result.1.ParamsAreFVars ∧ result.1.params.toList.Nodup :=
  checkInductiveTypes.getScopeStats nparams #[] ctx hwf hreserved

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Context → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ stats root env,
      ({ ctx with env := root.env } : Context).RecursorScopeFrame root →
      (next stats root { root with env }).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested isUnsafe) do
        checkConstructors types stats isUnsafe
        let root ← readThe Context
        withEnv (← declareConstructors stats types isUnsafe) do
          next stats root) ctx).WF post :=
  checkInductiveTypes.constructorRootScope nparams types numNested isUnsafe next ctx post hwf hreserved hnext

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (ctx : Context)
    (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats types false) do
          return (stats, root, (← readThe Context).env)) ctx).WF fun result =>
      result.1.SafeConstructorRegistration nparams types numNested ctx result.2.1 result.2.2 ∧
      ({ ctx with env := result.2.1.env } : Context).RecursorScopeFrame result.2.1 :=
  checkInductiveTypes.getScopedConstructorRegistration nparams types numNested ctx hmap hwf hreserved

private def sortType : Expr := .sort (.succ .zero)

private def header (name : Name) (type : Expr := sortType) : InductiveType := { name, type, ctors := [] }

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `binder (.const ``Nat []) body .implicit) sortType

private def dependent : Expr :=
  .forallE `binder sortType (.forallE `binder (.bvar 0) sortType .strictImplicit) .default

private def stage (nparams : Nat) (types : Array InductiveType) : M (InductiveStats × Context) :=
  checkInductiveTypes nparams types fun stats => do return (stats, ← readThe Context)

private def fuelValues (fuel : FuelConfig) : List Nat :=
  [fuel.whnf, fuel.whnfEager, fuel.lazyDelta, fuel.etaExpand, fuel.recDepth, fuel.inductiveFuel]

private def checkOldLookups (original current : Context) : MetaM Unit := do
  for decl in original.lctx do
    let some retained := current.lctx.find? decl.fvarId | throwError "checked header dropped an old declaration"
    unless retained.index == decl.index && retained.userName == decl.userName &&
        retained.type == decl.type && retained.value? (allowNondep := true) == decl.value? (allowNondep := true) &&
        retained.kind == decl.kind && retained.binderInfo == decl.binderInfo do
      throwError "checked header changed an old declaration"

private def checkReader (original current : Context) (allocated : Nat) : MetaM Unit := do
  unless current.lparams == original.lparams && current.safety == original.safety &&
      current.allowPrimitive == original.allowPrimitive && fuelValues current.fuel == fuelValues original.fuel &&
      current.env.quotInit == original.env.quotInit do
    throwError "checked header changed immutable reader fields"
  unless current.ngen.namePrefix == original.ngen.namePrefix &&
      current.ngen.idx == original.ngen.idx + allocated &&
      current.lctx.numIndices == original.lctx.numIndices + allocated do
    throwError "checked header allocation count or generator advancement changed"
  let mut entries : Array LocalDecl := #[]
  for decl in current.lctx do entries := entries.push decl
  let decls := entries.toList
  unless decls.map LocalDecl.index == List.range current.lctx.numIndices do
    throwError "checked header produced noncontiguous declaration indices"
  let ids := decls.map (·.fvarId)
  unless ids.eraseDups.length == ids.length do throwError "checked header produced duplicate declarations"
  for decl in decls do
    let some present := current.lctx.find? decl.fvarId | throwError "checked declaration is absent from native lookup"
    unless present.toExpr == decl.toExpr && present.index == decl.index do
      throwError "checked declaration native lookup disagrees with its list entry"
    if let .num namePrefix index := decl.fvarId.name then
      if namePrefix == current.ngen.namePrefix && index >= current.ngen.idx then
        throwError "checked context lost generator reservation"
  checkOldLookups original current

private def checkStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (indices : Array Nat) : MetaM Unit := do
  let .ok (stats, current) := stage nparams types ctx | throwError "checked-header scope fixture failed"
  let params := if types.isEmpty then 0 else nparams
  unless stats.nindices == indices && stats.indConsts.size == types.size && stats.params.size == params do
    throwError "checked-header scope lost its statistics counts"
  checkReader ctx current (params + indices.foldl (· + ·) 0)
  for param in stats.params do
    unless param.isFVar && (current.lctx.find? param.fvarId!).isSome do
      throwError "checked-header scope lost a shared parameter"
  for type in types do
    unless (current.env.find? type.name).isNone do throwError "checked headers prematurely installed a datatype"

private def fixtures (ctx : Context) : MetaM Unit := do
  let param := Expr.forallE `binder sortType sortType .instImplicit
  let three := Expr.forallE `binder sortType (.forallE `binder (.bvar 0)
    (.forallE `binder (.bvar 1) sortType .strictImplicit) .implicit) .default
  let seeded := { ctx with
    ngen := { namePrefix := `HeaderScopeSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `HeaderScopeSeed 16⟩ `old (.const ``Bool []) .implicit
      |>.mkLetDecl ⟨`HeaderScopeLet⟩ `old (.const ``Nat []) (.const ``Nat.zero []) }
  for safety in [DefinitionSafety.safe, .unsafe] do
    for original in [ctx, seeded] do
      let current := { original with safety }
      checkStage current 0 #[] #[]
      checkStage current 0 #[header `ScopeFirst] #[0]
      checkStage current 0 #[header `ScopeFirst, header `ScopeSecond, header `ScopeThird] #[0, 0, 0]
      checkStage current 1 #[header `ScopeFirst param, header `ScopeSecond param] #[0, 0]
      checkStage current 0 #[header `ScopeFirst (indexed 1), header `ScopeSecond (indexed 2)] #[1, 2]
      checkStage current 1 #[header `ScopeFirst dependent, header `ScopeSecond dependent] #[1, 1]
      checkStage current 2 #[header `ScopeFirst dependent, header `ScopeSecond dependent] #[0, 0]
      checkStage current 3 #[header `ScopeFirst three, header `ScopeSecond three] #[0, 0]
  checkStage ctx 1 #[header `ScopeNormalized (.const ``NormalizedHeader [])] #[1]
  checkStage seeded 0 #[header `ScopeWide (indexed 33)] #[33]
  checkStage { seeded with lparams := [`u] } 0 #[header `ScopePoly (.sort (.param `u))] #[0]
  checkStage { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } 0 #[] #[]
  logInfo "36 checked-header fixtures passed structural contexts, shared parameters, native lookups, and freshness"

private def constructorStage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Kernel.Environment) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      let root ← readThe Context
      withEnv (← declareConstructors stats types false) do
        return (stats, root, (← readThe Context).env)

private def checkConstructorRoot (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (indices : Array Nat) : MetaM Unit := do
  let .ok (stats, root, env) := constructorStage nparams types ctx
    | throwError "scoped constructor-registration prefix failed"
  let params := if types.isEmpty then 0 else nparams
  unless stats.params.size == params && stats.nindices == indices do
    throwError "scoped constructor root lost its coupled statistics"
  checkReader ctx root (params + indices.foldl (· + ·) 0)
  for type in types do
    unless (root.env.find? type.name).isSome && (env.find? type.name).isSome do
      throwError "scoped constructor root lost its actual header environment"
    for ctor in type.ctors do
      unless (root.env.find? ctor.name).isNone && (env.find? ctor.name).isSome do
        throwError "scoped constructor root conflated header and constructor environments"
    unless (env.find? (mkRecName type.name)).isNone do throwError "constructor prefix prematurely installed a recursor"

private def constructorRoots (ctx : Context) : MetaM Unit := do
  let node := Expr.const `HeaderScopedNode []
  let nodeType := { (header `HeaderScopedNode) with ctors := [
    { name := `HeaderScopedNode.base, type := node },
    { name := `HeaderScopedNode.step, type := .forallE `field node node .default }] }
  let indexedHead := Expr.const `HeaderScopedIndexed []
  let indexedType := { (header `HeaderScopedIndexed
      (.forallE `binder sortType (indexed 1) .default)) with ctors := [{
    name := `HeaderScopedIndexed.base
    type := .forallE `binder sortType (.forallE `binder (.const ``Nat [])
      (.mkAppList indexedHead [.bvar 1, .bvar 0]) .implicit) .default }] }
  let seeded := { ctx with
    ngen := { namePrefix := `ConstructorRootSeed, idx := 23 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `ConstructorRootSeed 22⟩ `old (.const ``Bool []) .default }
  for current in [ctx, seeded] do
    checkConstructorRoot current 0 #[] #[]
    checkConstructorRoot current 0 #[nodeType] #[0]
    checkConstructorRoot current 1 #[indexedType] #[1]
  logInfo "six constructor prefixes passed actual positivity roots, scoped statistics, and environment boundaries"

private def failures (ctx : Context) : MetaM Unit := do
  let param := Expr.forallE `binder sortType sortType .default
  let .error .deepRecursion := stage 0 #[header `ScopeFuel] { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "checked header lost zero-fuel rejection"
  let .error .deepRecursion := stage 1 #[header `ScopeFuel (Expr.forallE `binder sortType (indexed 1) .default)]
      { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    | throwError "checked header lost partial-allocation fuel rejection"
  let .error (.other shortage) := stage 2 #[header `ScopeShort param] ctx
    | throwError "checked header lost parameter-shortage rejection"
  unless shortage == "number of parameters mismatch in inductive datatype declaration" do
    throwError "checked-header shortage diagnostic changed"
  let wrong := Expr.forallE `binder (.const ``Nat []) sortType .default
  let .error (.other mismatch) := stage 1 #[header `ScopeFirst param, header `ScopeSecond wrong] ctx
    | throwError "checked header lost mutual parameter rejection"
  unless mismatch == "parameters of all inductive datatypes must match" do
    throwError "checked-header mutual parameter diagnostic changed"
  let .error (.other levelMismatch) := stage 0 #[header `ScopeFirst, header `ScopeSecond (.sort (.succ (.succ .zero)))] ctx
    | throwError "checked header lost mutual universe rejection"
  unless levelMismatch == "mutually inductive types must live in the same universe" do
    throwError "checked-header mutual universe diagnostic changed"
  let .error (.other sentinel) := checkInductiveTypes 0 #[header `ScopeSentinel]
      (fun _ => (throw (.other "header scope sentinel") : M Unit)) ctx
    | throwError "checked header swallowed continuation failure"
  unless sentinel == "header scope sentinel" do throwError "checked-header continuation diagnostic changed"
  logInfo "six checked-header fuel, parameter, universe, and continuation failures preserved diagnostics"

private def unreserved (ctx : Context) : MetaM Unit := do
  let old : FVarId := ⟨ctx.ngen.curr⟩
  let collision := { ctx with lctx := ctx.lctx.mkLocalDecl old `old (.const ``Bool []) .default }
  let .ok (_, current) := stage 0 #[header `ScopeUnreserved (indexed 1)] collision
    | throwError "unchecked reservation control unexpectedly rejected"
  let some before := collision.lctx.find? old | throwError "reservation control has no original declaration"
  let some after := current.lctx.find? old | throwError "reservation control has no final declaration"
  unless before.type == .const ``Bool [] && after.type == .const ``Nat [] do
    throwError "unreserved checked-header helper must expose native overwrite"
  logInfo "missing-reservation helper control demonstrates why root freshness is explicit"

private def audit (theoremName : Name) (interfaces := false) (registration := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if interfaces then [
    ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push] else []
  let allowed := allowed ++ if registration then [
    ``Lean.PersistentHashMap.findAux_isSome, ``Expr.eqv_eq, ``Expr.instantiate1_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``Context.RecursorScopeFrame.withEnv
  audit ``Lean4Lean.AddInductive.checkedHeader_loop_scope true
  audit ``Lean4Lean.AddInductive.checkedHeader_loopInd_scope true
  audit ``checkInductiveTypes.scope true
  audit ``checkInductiveTypes.getScopeStats true
  audit ``checkInductiveTypes.constructorRootScope true
  audit ``checkInductiveTypes.getScopedConstructorRegistration true true
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  constructorRoots ctx
  failures ctx
  unreserved ctx

end InductiveHeaderScopeTest
