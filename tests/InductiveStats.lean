import Lean4Lean.Verify.InductiveStats
import Lean4Lean.Verify.InductiveHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveStatsTest

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) :
    (checkInductiveTypes nparams types pure ctx).WF fun stats =>
      stats.ParamsCount nparams types.size :=
  checkInductiveTypes.getParamsCount nparams types ctx

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (hnonempty : types.size ≠ 0) :
    (checkInductiveTypes nparams types pure ctx).WF fun stats => stats.params.size = nparams :=
  checkInductiveTypes.getParamsCount_of_nonempty nparams types ctx hnonempty

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (hnonempty : types.size ≠ 0) (stats : InductiveStats)
    (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats) :
    stats.params.size = nparams :=
  checkInductiveTypes.getParamsCount_of_nonempty nparams types ctx hnonempty stats hcheck

example (ctx : Context) (nparams : Nat) :
    (checkInductiveTypes nparams #[] pure ctx).WF fun stats => stats.params.size = 0 :=
  (checkInductiveTypes.getParamsCount nparams #[] ctx).mono fun _ hcount =>
    by simpa only [InductiveStats.ParamsCount, Array.size_empty, ite_true] using hcount

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.ParamsCount nparams types.size → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.paramsCount nparams types next ctx post hnext

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes types.size →
      stats.ParamsCount nparams types.size → stats.ParamsAreFVars →
      stats.params.toList.Nodup → ctx.HeaderFrame ctx' → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsCountDistinct nparams types next ctx post hnext

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) :
    (checkInductiveTypes nparams types pure ctx).WF fun stats => stats.params.toList.Nodup :=
  checkInductiveTypes.getParamsNodup nparams types ctx

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats) :
    stats.params.toList.Nodup :=
  checkInductiveTypes.getParamsNodup nparams types ctx stats hcheck

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.params.toList.Nodup → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.paramsNodup nparams types next ctx post hnext

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes types.size → stats.ParamsAreFVars →
      stats.params.toList.Nodup → ctx'.env = ctx.env → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsDistinct nparams types next ctx post
    fun stats ctx' hsizes hfvars hnodup hframe => hnext stats ctx' hsizes hfvars hnodup hframe.env

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) :
    (checkInductiveTypes nparams types pure ctx).WF fun stats =>
      stats.nindices.size = types.size ∧ stats.indConsts.size = types.size :=
  checkInductiveTypes.getHeaderSizes nparams types ctx

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats) :
    stats.nindices.size = types.size :=
  (checkInductiveTypes.getHeaderSizes nparams types ctx stats hcheck).1

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats) :
    stats.indConsts.size = types.size :=
  (checkInductiveTypes.getHeaderSizes nparams types ctx stats hcheck).2

example (ctx : Context) (nparams : Nat) :
    (checkInductiveTypes nparams #[] pure ctx).WF fun stats =>
      stats.nindices.size = 0 ∧ stats.indConsts.size = 0 :=
  checkInductiveTypes.getHeaderSizes nparams #[] ctx

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.nindices.size = types.size →
      stats.indConsts.size = types.size → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.headerSizes nparams types next ctx post fun stats ctx' hsizes =>
    hnext stats ctx' hsizes.1 hsizes.2

example (ctx : Context) : ctx.HeaderFrame ctx := .refl ctx

example (ctx : Context) (lctx : LocalContext) (ngen : NameGenerator) :
    ctx.HeaderFrame { ctx with lctx, ngen } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example (original middle current : Context) (hfirst : original.HeaderFrame middle)
    (hsecond : middle.HeaderFrame current) : original.HeaderFrame current :=
  hfirst.trans hsecond

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← read)) ctx).WF
      fun result => result.2.env = ctx.env ∧ result.2.lparams = ctx.lparams :=
  (checkInductiveTypes.getFrameHeaderSizes nparams types ctx).mono fun _ hresult =>
    ⟨hresult.2.env, hresult.2.lparams⟩

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) :
    (checkInductiveTypes nparams types (fun stats => do return (stats, ← read)) ctx).WF
      fun result => result.2.safety = ctx.safety ∧
        result.2.allowPrimitive = ctx.allowPrimitive ∧ result.2.fuel = ctx.fuel :=
  (checkInductiveTypes.getFrameHeaderSizes nparams types ctx).mono fun _ hresult =>
    ⟨hresult.2.safety, hresult.2.allowPrimitive, hresult.2.fuel⟩

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', ctx'.env = ctx.env → ctx'.lparams = ctx.lparams →
      (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.frame nparams types next ctx post fun stats ctx' hframe =>
    hnext stats ctx' hframe.env hframe.lparams

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.nindices.size = types.size →
      ctx'.env = ctx.env → ctx'.lparams = ctx.lparams → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizes nparams types next ctx post fun stats ctx' hsizes hframe =>
    hnext stats ctx' hsizes.1 hframe.env hframe.lparams

private def sortType : Expr := .sort (.succ .zero)

private def datatype (name : Name) (type : Expr := sortType) : InductiveType := {
  name, type, ctors := [] }

private def parameterType (domain : Expr := sortType) : Expr :=
  .forallE `A domain sortType .default

private def indexedType (indices : Nat) : Expr :=
  indices.fold (fun _ _ type => .forallE `index (.const ``Nat []) type .default) sortType

private def dependentType : Expr :=
  .forallE `A sortType (.forallE `value (.bvar 0) sortType .default) .default

private def fuelValues (fuel : FuelConfig) : Array Nat :=
  #[fuel.whnf, fuel.whnfEager, fuel.lazyDelta, fuel.etaExpand, fuel.recDepth, fuel.inductiveFuel]

private def checkFrame (ctx observed : Context) (scopes : Nat) (types : Array InductiveType) :
    MetaM Unit := do
  let natHeader (env : Kernel.Environment) :=
    (env.find? ``Nat).map fun info => (info.name, info.levelParams, info.type)
  unless observed.lparams == ctx.lparams && observed.safety == ctx.safety &&
      observed.allowPrimitive == ctx.allowPrimitive && fuelValues observed.fuel == fuelValues ctx.fuel &&
      natHeader observed.env == natHeader ctx.env do
    throwError "changed fixed header-context fields"
  for type in types do
    unless observed.env.contains type.name == ctx.env.contains type.name do
      throwError "registered an unchecked datatype header"
  let expectedNames := scopes.fold (fun _ _ ngen => ngen.next) ctx.ngen
  unless observed.ngen.curr == expectedNames.curr &&
      observed.lctx.numIndices == ctx.lctx.numIndices + scopes do
    throwError "unexpected local-context or fresh-name behavior"

private def checkStats (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (indices : Array Nat) : MetaM Unit := do
  let .ok (stats, observed) :=
      checkInductiveTypes nparams types (fun stats => do return (stats, ← read)) ctx
    | throwError "rejected statistics fixture with {types.size} types and {nparams} parameters"
  unless stats.nindices == indices && stats.nindices.size == types.size &&
      stats.indConsts.size == types.size &&
      stats.params.size == (if types.isEmpty then 0 else nparams) &&
      stats.params.all Expr.isFVar &&
      stats.params.toList.eraseDups.length == stats.params.size &&
      stats.levels == ctx.lparams.map Level.param &&
      stats.indConsts == types.map (fun type => Expr.const type.name stats.levels) do
    throwError "incorrect inductive statistics"
  for index in [:types.size] do
    unless declareConstructors.arity 0 types[index]!.type ≤ nparams + stats.nindices[index]! do
      throwError "checked header counts are below raw source arity"
  let expectedParams := (List.range nparams).map fun index =>
    Expr.fvar ⟨.num ctx.ngen.namePrefix (ctx.ngen.idx + index)⟩
  unless stats.params.toList == expectedParams do
    throwError "incorrect parameter introduction names or ordering"
  let scopes := if types.isEmpty then 0 else nparams + indices.foldl (· + ·) 0
  checkFrame ctx observed scopes types

private def rejectStats (ctx : Context) (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  if (checkInductiveTypes nparams types pure ctx).isOk then
    throwError "accepted invalid statistics fixture"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``Context.HeaderFrame.refl
  audit ``Context.HeaderFrame.trans
  audit ``checkInductiveTypes.frameHeaderSizesParamsCountDistinct
  audit ``checkInductiveTypes.paramsCount
  audit ``checkInductiveTypes.getParamsCount
  audit ``checkInductiveTypes.getParamsCount_of_nonempty
  audit ``checkInductiveTypes.frameHeaderSizesParamsDistinct
  audit ``checkInductiveTypes.paramsNodup
  audit ``checkInductiveTypes.getParamsNodup
  audit ``checkInductiveTypes.frameHeaderSizes
  audit ``checkInductiveTypes.frame
  audit ``checkInductiveTypes.getFrameHeaderSizes
  audit ``checkInductiveTypes.headerSizes
  audit ``checkInductiveTypes.getHeaderSizes
  let imported := (← Lean.getEnv).toKernelEnv
  let ctx : Context := { env := imported, lparams := [], safety := .safe, allowPrimitive := false }
  for safety in [DefinitionSafety.safe, .unsafe] do
    let ctx := { ctx with safety }
    checkStats ctx 0 #[] #[]
    checkStats ctx 0 #[datatype `First] #[0]
    checkStats ctx 0 #[datatype `First, datatype `Second, datatype `Third] #[0, 0, 0]
    checkStats ctx 1 #[datatype `First parameterType, datatype `Second parameterType] #[0, 0]
    checkStats ctx 0 #[datatype `First (indexedType 1), datatype `Second (indexedType 2)] #[1, 2]
    checkStats ctx 1 #[datatype `First dependentType, datatype `Second dependentType] #[1, 1]
    checkStats ctx 2 #[datatype `First dependentType, datatype `Second dependentType] #[0, 0]
    let threeParams := Expr.forallE `A sortType (.forallE `value (.bvar 0)
      (.forallE `other (.bvar 1) sortType .strictImplicit) .implicit) .default
    checkStats ctx 3 #[datatype `First threeParams, datatype `Second threeParams] #[0, 0]
  let polyCtx := { ctx with lparams := [`u] }
  checkStats polyCtx 0 #[] #[]
  checkStats polyCtx 0 #[datatype `Poly (.sort (.param `u))] #[0]
  let seededCtx : Context := { polyCtx with
    lctx := polyCtx.lctx.mkLocalDecl ⟨`existing⟩ `existing sortType,
    ngen := { namePrefix := `_frame_fixture, idx := 37 }, allowPrimitive := true,
    fuel := {
      whnf := 73, whnfEager := 211, lazyDelta := 89
      etaExpand := 43, recDepth := 71, inductiveFuel := 9 } }
  checkStats seededCtx 0 #[] #[]
  let polyDependent : Expr := .forallE `A (.sort (.param `u))
    (.forallE `value (.bvar 0) (.sort (.param `u)) .default) .default
  checkStats seededCtx 1 #[datatype `FramedFirst polyDependent,
    datatype `FramedSecond polyDependent] #[1, 1]
  checkStats seededCtx 2 #[datatype `FramedFirst polyDependent,
    datatype `FramedSecond polyDependent] #[0, 0]
  rejectStats ctx 1 #[datatype `MissingParameter]
  rejectStats ctx 1 #[datatype `First parameterType,
    datatype `Second (parameterType (.sort .zero))]
  rejectStats ctx 0 #[datatype `First, datatype `Second (.sort .zero)]
  rejectStats ctx 0 #[datatype `UnknownUniverse (.sort (.param `u))]
  rejectStats ctx 0 #[datatype `InvalidType (.const `Missing [])]
  rejectStats { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } 0 #[datatype `NoFuel]

end InductiveStatsTest
