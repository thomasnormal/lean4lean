import Lean4Lean.Verify.InductiveStats
import Lean4Lean.Verify.InductiveHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveStatsTest

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

private def sortType : Expr := .sort (.succ .zero)

private def datatype (name : Name) (type : Expr := sortType) : InductiveType := {
  name, type, ctors := [] }

private def parameterType (domain : Expr := sortType) : Expr :=
  .forallE `A domain sortType .default

private def indexedType (indices : Nat) : Expr :=
  indices.fold (fun _ _ type => .forallE `index (.const ``Nat []) type .default) sortType

private def dependentType : Expr :=
  .forallE `A sortType (.forallE `value (.bvar 0) sortType .default) .default

private def checkStats (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (indices : Array Nat) : MetaM Unit := do
  let .ok stats := checkInductiveTypes nparams types pure ctx
    | throwError "rejected statistics fixture with {types.size} types and {nparams} parameters"
  unless stats.nindices == indices && stats.nindices.size == types.size &&
      stats.indConsts.size == types.size && stats.params.size == nparams &&
      stats.levels == ctx.lparams.map Level.param &&
      stats.indConsts == types.map (fun type => Expr.const type.name stats.levels) do
    throwError "incorrect inductive statistics"

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
  let polyCtx := { ctx with lparams := [`u] }
  checkStats polyCtx 0 #[] #[]
  checkStats polyCtx 0 #[datatype `Poly (.sort (.param `u))] #[0]
  rejectStats ctx 1 #[datatype `MissingParameter]
  rejectStats ctx 1 #[datatype `First parameterType,
    datatype `Second (parameterType (.sort .zero))]
  rejectStats ctx 0 #[datatype `First, datatype `Second (.sort .zero)]
  rejectStats ctx 0 #[datatype `UnknownUniverse (.sort (.param `u))]
  rejectStats ctx 0 #[datatype `InvalidType (.const `Missing [])]
  rejectStats { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } 0 #[datatype `NoFuel]

end InductiveStatsTest
