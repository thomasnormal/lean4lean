import Lean4Lean.Verify.InductiveWrappedHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveWrappedSpinesTest

private def sortType : Expr := .sort (.succ .zero)

private def carrierBody : Expr := .forallE `index (.bvar 0) sortType .default

private def carrierResult : Expr := .forallE `index (.const ``Nat []) sortType .default

private def mixedLetBeta (data : MData) : Expr :=
  .letE `outer sortType (.const ``Nat [])
    (.mdata data (.app (.lam `inner sortType carrierBody .default) (.bvar 0))) false

private def mixedBetaLet (data : MData) : Expr :=
  .app (.lam `outer sortType
    (.mdata data (.letE `inner sortType (.bvar 0) carrierBody false)) .default) (.const ``Nat [])

private def mixedMetadataLetBeta (data : MData) : Expr := .mdata data (mixedLetBeta data)

private def mixedDoubleLetBeta (data : MData) : Expr :=
  .letE `unused (.const ``Nat []) (.lit (.natVal 0)) (mixedMetadataLetBeta data) true

private def exposedValue (data : MData) : Expr :=
  .app (.lam `unused (.const ``Nat []) (.mdata data carrierResult) .default) (.lit (.natVal 0))

private def exposedLet (data : MData) : Expr :=
  .letE `alias (.sort (.succ (.succ .zero))) (exposedValue data) (.bvar 0) false

private def mixedBetaDomainLet (data : MData) : Expr :=
  .app (.lam `outer sortType
    (.letE `identity (.forallE `argument (.bvar 0) (.bvar 1) .default)
      (.lam `argument (.bvar 0) (.bvar 0) .default)
      (.mdata data (.forallE `index (.bvar 1) sortType .default)) true) .default) (.const ``Nat [])

private theorem mixedLetBetaTrace (data : MData) :
    WrappedSortTelescope (mixedLetBeta data) carrierResult := by
  unfold mixedLetBeta
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope
    (.mdata data (.app (.lam `inner sortType carrierBody .default) (.const ``Nat []))) carrierResult
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope carrierResult carrierResult
  exact .telescope (.forallE `index (.const ``Nat []) .default (.sort (.succ .zero)))

private theorem mixedBetaLetTrace (data : MData) :
    WrappedSortTelescope (mixedBetaLet data) carrierResult := by
  unfold mixedBetaLet
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope
    (.mdata data (.letE `inner sortType (.const ``Nat []) carrierBody false)) carrierResult
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope carrierResult carrierResult
  exact .telescope (.forallE `index (.const ``Nat []) .default (.sort (.succ .zero)))

private theorem mixedMetadataLetBetaTrace (data : MData) :
    WrappedSortTelescope (mixedMetadataLetBeta data) carrierResult :=
  .mdata data (mixedLetBetaTrace data)

private theorem mixedDoubleLetBetaTrace (data : MData) :
    WrappedSortTelescope (mixedDoubleLetBeta data) carrierResult := by
  unfold mixedDoubleLetBeta
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope (mixedMetadataLetBeta data) carrierResult
  exact mixedMetadataLetBetaTrace data

private theorem exposedLetTrace (data : MData) :
    WrappedSortTelescope (exposedLet data) carrierResult := by
  unfold exposedLet
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope (exposedValue data) carrierResult
  unfold exposedValue
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope (.mdata data carrierResult) carrierResult
  apply WrappedSortTelescope.mdata
  exact .telescope (.forallE `index (.const ``Nat []) .default (.sort (.succ .zero)))

private theorem mixedBetaDomainLetTrace (data : MData) :
    WrappedSortTelescope (mixedBetaDomainLet data) carrierResult := by
  unfold mixedBetaDomainLet
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope
    (.letE `identity (.forallE `argument (.const ``Nat []) (.const ``Nat []) .default)
      (.lam `argument (.const ``Nat []) (.bvar 0) .default) (.mdata data carrierResult) true) carrierResult
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope (.mdata data carrierResult) carrierResult
  apply WrappedSortTelescope.mdata
  exact .telescope (.forallE `index (.const ``Nat []) .default (.sort (.succ .zero)))

private theorem mixedLetBetaNormalized (data : MData) :
    NormalizedSortTelescope (mixedLetBeta data) carrierResult := (mixedLetBetaTrace data).normalized

private theorem mixedBetaLetNormalized (data : MData) :
    NormalizedSortTelescope (mixedBetaLet data) carrierResult := (mixedBetaLetTrace data).normalized

example {source normalized : Expr} (trace : WrappedSortTelescope source normalized) :
    SortTelescope normalized := trace.shape

example {source normalized : Expr} (trace : WrappedSortTelescope source normalized) :
    NormalizedSortTelescope source normalized := trace.normalized

example {source normalized : Expr} (trace : WrappedSortTelescope source normalized)
    (depth : Nat) (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (hempty : state.whnfCoreCache = ∅) :
    ((TypeChecker.Methods.withFuel depth).whnfCore source false false ctx state).WF
      fun returned => returned.1 = normalized := trace.core depth ctx state hempty

example (data : MData) : declareConstructors.arity 0 (mixedLetBeta data) = 0 := rfl

example (data : MData) : declareConstructors.arity 0 (mixedBetaLet data) = 0 := rfl

example : declareConstructors.arity 0 carrierResult = 1 := rfl

example (data : MData) :
    ¬ SortTelescope (.mdata data (.letE `inner sortType (.bvar 0) carrierBody false)) := by
  intro hshape
  cases hshape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `MixedReceiptLet (mixedLetBeta data),
  header `MixedReceiptBeta (mixedBetaLet data),
  header `MixedReceiptDouble (mixedDoubleLetBeta data),
  header `MixedReceiptExposure (exposedLet data),
  header `MixedReceiptDomain (mixedBetaDomainLet data)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent hparent
  have hcases : parent = 0 ∨ parent = 1 ∨ parent = 2 ∨ parent = 3 ∨ parent = 4 := by
    have hbound : parent < 5 := by simpa [provedTypes] using hparent
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨carrierResult, mixedLetBetaTrace data⟩
  · exact ⟨carrierResult, mixedBetaLetTrace data⟩
  · exact ⟨carrierResult, mixedDoubleLetBetaTrace data⟩
  · exact ⟨carrierResult, exposedLetTrace data⟩
  · exact ⟨carrierResult, mixedBetaDomainLetTrace data⟩

private theorem provedRegisteredCounts (data : MData) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 0 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 0 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedIndexCounts 0 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 :=
  mkRecInfos.registeredWrappedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes hwf hreserved henv

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `index (.const ``Nat []) body .implicit) sortType

private def tagged : MData :=
  (({} : MData).insert `WrappedSpineTag (.ofNat 42)).insert `payload (.ofString "mixed")

private def wrap (kind : Nat) (type : Expr) : Expr :=
  match kind % 3 with
  | 0 => .mdata tagged type
  | 1 => .letE `unused (.const ``Nat []) (.lit (.natVal 0)) type true
  | _ => .app (.lam `unused (.const ``Nat []) type .default) (.lit (.natVal 0))

private def word (depth code : Nat) (type : Expr) : Expr :=
  (List.range depth).foldl (fun source index => wrap (code / 3 ^ index) source) type

private def chain (depth : Nat) (type : Expr) : Expr :=
  (List.range depth).foldl (fun source index => wrap index source) type

private def metadataChain (depth : Nat) (type : Expr) : Expr :=
  (List.range depth).foldl (fun source _ => .mdata tagged source) type

private def safeStage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          (← readThe Context).lparams false false
        return (stats, result)

private def checkWhnf (ctx : Context) (source normalized : Expr) : MetaM Unit := do
  let .ok result := ((monadLift (TypeChecker.whnf source) : M Expr) ctx)
    | throwError "mixed-spine normalization fixture failed"
  unless result == normalized do
    throwError "mixed-spine normalization fixture lost its canonical telescope"

private def checkRegistered (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, env, infos, source) := safeStage nparams types ctx
    | throwError "mixed-spine registration fixture failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "mixed-spine fixture changed checked parameter/index counts"
  for parent in [:types.size] do
    unless infos[parent]!.indices.size == expected[parent]! do
      throwError "mixed-spine fixture changed generated index counts"
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "mixed-spine fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "mixed-spine fixture changed registered count metadata"
    for index in infos[parent]!.indices do
      unless (source.lctx.find? index.fvarId!).isSome do
        throwError "mixed-spine fixture lost an allocated index declaration"

private def checkFixture (ctx : Context) (name : Name) (nparams : Nat)
    (source normalized : Expr) (nindices : Nat) : MetaM Unit := do
  checkWhnf ctx source normalized
  checkRegistered ctx nparams #[header name source] #[nindices]
  unless declareConstructors.arity 0 source == 0 &&
      declareConstructors.arity 0 normalized == nparams + nindices do
    throwError "mixed-spine fixture collapsed the raw/normalized arity boundary"

private def fixtures (ctx : Context) : MetaM Unit := do
  let telescope := indexed 2
  for depth in [2, 3] do
    for code in [:3 ^ depth] do
      checkFixture ctx (Name.mkNum (Name.mkNum `WrappedWord depth) code) 0
        (word depth code telescope) telescope 2
  for depth in [1, 2, 7, 16, 32, 65] do
    checkFixture ctx (Name.mkNum `WrappedChain depth) 0 (chain depth telescope) telescope 2
  for depth in [1, 32, 128] do
    checkFixture ctx (Name.mkNum `WrappedMetadata depth) 0 (metadataChain depth telescope) telescope 2
  checkFixture ctx `WrappedUsedLet 0 (mixedLetBeta tagged) carrierResult 1
  checkFixture ctx `WrappedUsedBeta 0 (mixedBetaLet tagged) carrierResult 1
  checkFixture ctx `WrappedUsedDouble 0 (mixedDoubleLetBeta tagged) carrierResult 1
  checkFixture ctx `WrappedExposure 0 (exposedLet tagged) carrierResult 1
  checkFixture ctx `WrappedDomain 0 (mixedBetaDomainLet tagged) carrierResult 1
  let dependent := Expr.forallE `carrier sortType
    (.forallE `index (.bvar 0) sortType .strictImplicit) .default
  checkFixture ctx `WrappedDependent 1 (chain 7 dependent) dependent 1
  checkRegistered ctx 0 (provedTypes tagged) #[1, 1, 1, 1, 1]

private def fuelBoundaries (ctx : Context) : MetaM Unit := do
  let telescope := indexed 2
  let .error .deepRecursion := ((monadLift (TypeChecker.whnf (chain 16 telescope)) : M Expr)
      { ctx with fuel := { ctx.fuel with recDepth := 0 } })
    | throwError "mixed-spine receipt incorrectly excludes depth-zero errors"
  for wrapped in [wrap 1 telescope, wrap 2 telescope, mixedLetBeta tagged, mixedBetaLet tagged] do
    let .error .deepRecursion := ((monadLift (TypeChecker.whnf wrapped) : M Expr)
        { ctx with fuel := { ctx.fuel with recDepth := 1 } })
      | throwError "mixed-spine receipt incorrectly excludes shallow-depth errors"
    let .error .deterministicTimeout := ((monadLift (TypeChecker.whnf wrapped) : M Expr)
        { ctx with fuel := { ctx.fuel with whnf := 0 } })
      | throwError "mixed-spine receipt incorrectly excludes exhausted-loop errors"
  checkWhnf { ctx with fuel := { ctx.fuel with recDepth := 1, whnf := 0 } }
    (metadataChain 128 telescope) telescope
  checkWhnf { ctx with fuel := { ctx.fuel with recDepth := 128, whnf := 1 } }
    (chain 65 telescope) telescope

private def uncheckedBoundary (ctx : Context) : MetaM Unit := do
  let types := provedTypes tagged
  let .ok (stats, _, _, reader) := safeStage 0 types ctx
    | throwError "mixed-spine unchecked boundary setup failed"
  let inconsistent := { stats with nindices := #[97, 98, 99, 100, 101] }
  let .ok infos := mkRecInfos inconsistent types (.succ .zero) pure reader
    | throwError "mixed-spine unchecked statistics stopped generating infos"
  unless infos.map (·.indices.size) == #[1, 1, 1, 1, 1] &&
      inconsistent.nindices == #[97, 98, 99, 100, 101] do
    throwError "mixed-spine receipt incorrectly certifies unchecked stored statistics"

private def cacheBoundary (ctx : Context) : MetaM Unit := do
  let source := mixedLetBeta tagged
  let cached := Expr.sort .zero
  let state : TypeChecker.State := { whnfCoreCache := (∅ : Std.HashMap Expr Expr).insert source cached }
  let reader : TypeChecker.Context := {
    env := ctx.env, safety := ctx.safety, lctx := ctx.lctx, lparams := ctx.lparams, fuel := ctx.fuel }
  let .ok (result, _) := (TypeChecker.Methods.withFuel 64).whnfCore source false false reader state
    | throwError "mixed-spine cache boundary no longer reads existing cache entries"
  unless result == cached && !(result == carrierResult) do
    throwError "mixed-spine core receipt incorrectly drops its empty-cache premise"
  checkWhnf ctx source carrierResult

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let wrappers := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  audit ``WrappedSortTelescope.shape
  audit ``WrappedSortTelescope.core wrappers
  audit ``WrappedSortTelescope.normalized wrappers
  for theoremName in [``mixedLetBetaTrace, ``mixedBetaLetTrace,
      ``mixedMetadataLetBetaTrace, ``mixedDoubleLetBetaTrace, ``exposedLetTrace,
      ``mixedBetaDomainLetTrace, ``provedHeaders] do
    audit theoremName binding
  for theoremName in [``mixedLetBetaNormalized, ``mixedBetaLetNormalized,
      ``WrappedHeaderTelescope.normalizedHeaders] do
    audit theoremName wrappers
  audit ``provedRegisteredCounts (wrappers ++ scope)
  audit ``CheckedHeaderSources.wrappedTelescopeIndexCounts wrappers
  audit ``mkRecInfos.registeredWrappedAlignedIndices
    (wrappers ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredWrappedIndexCounts (wrappers ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `WrappedSpineSeed, idx := 47 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `WrappedSpineSeed 46⟩ `old (.const ``Bool []) .implicit }
  let .ok (_, extendedEnv, _, _) := safeStage 0 #[header `WrappedReaderExtension sortType] ctx
    | throwError "mixed-spine environment-extension setup failed"
  for reader in [ctx, { ctx with lparams := [`u] }, seeded, { ctx with env := extendedEnv }] do
    fixtures reader
  fuelBoundaries ctx
  uncheckedBoundary ctx
  cacheBoundary ctx
  logInfo "208 mixed-spine registration prefixes and 207 successful WHNF observations cover all wrapper pairs/triples, deep chains, used substitutions, and four readers; nine fuel errors plus unchecked-count and cache boundaries remain explicit"

end InductiveWrappedSpinesTest
