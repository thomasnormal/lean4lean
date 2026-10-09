import Lean4Lean.Verify.InductiveNormalizedHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveNormalizedHeadersTest

private def sortType : Expr := .sort (.succ .zero)

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `index (.const ``Nat []) body .implicit) sortType

private def header (name : Name) (type : Expr := sortType) : InductiveType := { name, type, ctors := [] }

private def explicitNormalization {type : Expr} (htype : SortTelescope type) :
    NormalizedSortTelescope type type := ⟨htype, fun ctx => htype.whnf ctx⟩

example {type : Expr} {normalized : Expr} (hshape : SortTelescope normalized)
    (hwhnf : ∀ ctx, ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF
      (fun result => result = normalized)) : NormalizedSortTelescope type normalized :=
  ⟨hshape, hwhnf⟩

example {nparams parent count : Nat} {types : Array InductiveType}
    {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    declareConstructors.arity 0 normalized = params.size + count :=
  source.telescopeCount_of_normalized hnormalized

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent count : Nat} {original current : Context} {info : RecInfo} {normalized : Expr}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized)
    (hcount : declareConstructors.arity 0 normalized = stats.params.size + count) :
    info.indices.size = count := source.telescopeIndexCount_of_normalized hnormalized hcount

example {nparams : Nat} {types : Array InductiveType} {stats : InductiveStats}
    {original checkedRoot recursorRoot current : Context} {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : NormalizedHeaderTelescope types) : RecursorIndexCounts stats types infos :=
  headers.normalizedTelescopeIndexCounts sources htypes

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedNormalizedAlignedIndices nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved hnext

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original checkedRoot ctx : Context) (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧ RecursorIndexCounts stats types result.1 :=
  mkRecInfos.getNormalizedAlignedIndices nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved

example {type normalized : Expr} (h : NormalizedSortTelescope type normalized)
    (ctx : Context) (result : Expr)
    (hresult : ((monadLift (TypeChecker.whnf type) : M Expr) ctx) = .ok result) : result = normalized :=
  h.2 ctx result hresult

example {type : Expr} (htype : SortTelescope type) :
    NormalizedSortTelescope type type := explicitNormalization htype

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context) :=
  checkInductiveTypes nparams types fun stats => do return (stats, ← readThe Context)

private def safeStage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          (← readThe Context).lparams false false
        return (stats, result)

private def checkNative (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, env, infos, source) := safeStage nparams types ctx
    | throwError "normalized-header native fixture failed"
  unless stats.nindices == expected && infos.size == types.size do
    throwError "normalized-header native fixture changed stored/generated counts"
  for parent in [:types.size] do
    unless infos[parent]!.indices.size == stats.nindices[parent]! do
      throwError "normalized-header native fixture lost count equality"
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "normalized-header native fixture lost recursor registration"
    unless recursor.numIndices == stats.nindices[parent]! do
      throwError "normalized-header native fixture lost registered count"
    for index in infos[parent]!.indices do
      unless (source.lctx.find? index.fvarId!).isSome do
        throwError "normalized-header native fixture lost generated index declaration"

private def fixtures (ctx : Context) : MetaM Unit := do
  let dependent := Expr.forallE `carrier sortType
    (.forallE `index (.bvar 0) sortType .strictImplicit) .default
  let annotated := .mdata {} (indexed 2)
  let letType := Expr.letE `carrier sortType (.const ``Nat [])
    (.forallE `index (.bvar 0) sortType .default) false
  let beta := Expr.app (.lam `carrier sortType
    (.forallE `index (.bvar 0) sortType .default) .default) (.const ``Nat [])
  checkNative ctx 0 #[] #[]
  checkNative ctx 0 #[header `NormalizedExplicit (indexed 3)] #[3]
  checkNative ctx 1 #[header `NormalizedDependent dependent] #[1]
  checkNative ctx 0 #[header `NormalizedAnnotated annotated] #[2]
  checkNative ctx 0 #[header `NormalizedLet letType] #[1]
  checkNative ctx 0 #[header `NormalizedBeta beta] #[1]
  checkNative ctx 0 #[header `NormalizedMixed (.mdata {} letType)] #[1]
  checkNative ctx 0 #[header `NormalizedMutual (indexed 1), header `NormalizedSecond annotated] #[1, 2]
  checkNative { ctx with lparams := [`u] } 1 #[header `NormalizedPoly
    (.forallE `carrier (.sort (.param `u)) (.sort (.param `u)) .default)] #[0]
  let seeded := { ctx with
    ngen := { namePrefix := `NormalizedHeaderSeed, idx := 19 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `NormalizedHeaderSeed 18⟩ `old (.const ``Bool []) .implicit }
  checkNative seeded 0 #[header `NormalizedSeeded annotated] #[2]
  logInfo "ten native normalized-header fixtures retained annotated/let/beta source actions and checked/generated/registered counts"

private def boundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `NormalizedBoundary (indexed 2)]
  let .ok (stats, _, _, source) := safeStage 0 types ctx
    | throwError "normalized boundary setup failed"
  let wrong := { stats with nindices := #[99] }
  let .ok inconsistent := mkRecInfos wrong types (.succ .zero) pure source
    | throwError "normalized boundary changed unchecked count behavior"
  unless inconsistent[0]!.indices.size == 2 && wrong.nindices[0]! == 99 do
    throwError "normalized boundary incorrectly certified unchecked statistics"
  let .error .deepRecursion := stage 0 #[header `NormalizedFuel (indexed 2)]
      { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    | throwError "normalized checked fuel boundary changed"
  logInfo "three normalized-header boundaries retain unchecked counts and partial checked fuel behavior"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  audit ``CheckedHeaderSource.telescopeCount_of_normalized binding
  audit ``RecursorInfoIndexSource.telescopeIndexCount_of_normalized binding
  audit ``CheckedHeaderSources.normalizedTelescopeIndexCounts binding
  audit ``mkRecInfos.scopedNormalizedAlignedIndices (binding ++ scope)
  audit ``mkRecInfos.getNormalizedAlignedIndices (binding ++ scope)
  let ctx : Context := { env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  boundaries ctx

end InductiveNormalizedHeadersTest
