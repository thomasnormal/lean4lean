import Lean4Lean.Verify.InductiveNormalizedWrappers
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveNormalizedWrappersTest

private def sortType : Expr := .sort (.succ .zero)

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `index (.const ``Nat []) body .implicit) sortType

private def annotate (type : Expr) : Expr := .mdata {} type

private def letWrapper (type : Expr) : Expr :=
  .letE `unused (.const ``Nat []) (.lit (.natVal 0)) type true

private def betaWrapper (type : Expr) : Expr :=
  .app (.lam `unused (.const ``Nat []) type .default) (.lit (.natVal 0))

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def carrierBody : Expr := .forallE `index (.bvar 0) sortType .default

private def carrierResult : Expr := .forallE `index (.const ``Nat []) sortType .default

private theorem carrierSubstitution : carrierBody.instantiate1 (.const ``Nat []) = carrierResult := by
  rw [Expr.instantiate1_eq]
  rfl

private theorem usedLetReceipt :
    NormalizedSortTelescope
      (.letE `carrier sortType (.const ``Nat []) carrierBody false) carrierResult := by
  have hshape : SortTelescope carrierBody := .forallE `index (.bvar 0) .default (.sort (.succ .zero))
  have hnormalized := SortTelescope.normalizedLet `carrier sortType (.const ``Nat []) carrierBody false
    (hshape.instantiate1 (.const ``Nat []))
  simpa only [carrierSubstitution] using hnormalized

private theorem usedBetaReceipt :
    NormalizedSortTelescope
      (.app (.lam `carrier sortType carrierBody .default) (.const ``Nat [])) carrierResult := by
  have hshape : SortTelescope carrierBody := .forallE `index (.bvar 0) .default (.sort (.succ .zero))
  have hnormalized := hshape.normalizedBeta `carrier sortType (.const ``Nat []) .default
  simpa only [carrierSubstitution] using hnormalized

private theorem annotatedReceipt :
    NormalizedSortTelescope (annotate (annotate (indexed 2))) (indexed 2) := by
  have hshape : SortTelescope (indexed 2) :=
    .forallE `index (.const ``Nat []) .implicit
      (.forallE `index (.const ``Nat []) .implicit (.sort (.succ .zero)))
  exact (hshape.normalized.mdata {}).mdata {}

private theorem annotatedHeaders :
    NormalizedHeaderTelescope #[header `ReceiptFamily (annotate (annotate (indexed 2)))] := by
  intro parent hparent
  have hzero : parent = 0 := by simpa using hparent
  subst parent
  exact ⟨indexed 2, annotatedReceipt⟩

private def provedTypes : Array InductiveType := #[
  header `ReceiptFamily (annotate (annotate (indexed 2))),
  header `ReceiptLet (annotate (.letE `carrier sortType (.const ``Nat []) carrierBody false)),
  header `ReceiptBeta (annotate (.app (.lam `carrier sortType carrierBody .default) (.const ``Nat [])))]

private theorem provedHeaders : NormalizedHeaderTelescope provedTypes := by
  intro parent hparent
  have hcases : parent = 0 ∨ parent = 1 ∨ parent = 2 := by
    have hbound : parent < 3 := by simpa [provedTypes] using hparent
    omega
  rcases hcases with rfl | rfl | rfl
  · exact ⟨indexed 2, annotatedReceipt⟩
  · exact ⟨carrierResult, usedLetReceipt.mdata {}⟩
  · exact ⟨carrierResult, usedBetaReceipt.mdata {}⟩

example (metadata : MData) :
    NormalizedSortTelescope (.mdata metadata sortType) sortType :=
  (SortTelescope.sort (.succ .zero)).normalized.mdata metadata

example (metadata : MData) (body : Expr) : ¬ SortTelescope (.mdata metadata body) := by
  intro htype
  cases htype

example (name : Name) (domain value body : Expr) (nondep : Bool) :
    ¬ SortTelescope (.letE name domain value body nondep) := by
  intro htype
  cases htype

example (function argument : Expr) : ¬ SortTelescope (.app function argument) := by
  intro htype
  cases htype

example (type : Expr) : declareConstructors.arity 0 (annotate type) = 0 := rfl

example (type : Expr) : declareConstructors.arity 0 (letWrapper type) = 0 := rfl

example (type : Expr) : declareConstructors.arity 0 (betaWrapper type) = 0 := rfl

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : NormalizedHeaderTelescope types) (hwf : ctx.lctx.WF)
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
  mkRecInfos.registeredNormalizedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes hwf hreserved henv

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (ctx : Context) (htypes : NormalizedHeaderTelescope types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedIndexCounts nparams types numNested elimLevel lparams
    isK ctx htypes hwf hreserved

private theorem provedRegisteredCounts (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 0 provedTypes (fun stats => do
      withEnv (← declareInductiveTypes stats 0 provedTypes 0 false) do
        checkConstructors provedTypes stats false
        withEnv (← declareConstructors stats provedTypes false) do
          let result ← mkRecInfos.scopeRegistration stats provedTypes (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 provedTypes result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedIndexCounts 0 provedTypes 0 (.succ .zero) [] false ctx
    provedHeaders hwf hreserved

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
    | throwError "wrapper normalization fixture failed"
  unless result == normalized do
    throwError "wrapper normalization fixture lost its canonical telescope"

private def checkRegistered (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, env, infos, source) := safeStage nparams types ctx
    | throwError "wrapper registration fixture failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "wrapper fixture changed checked parameter/index counts"
  for parent in [:types.size] do
    unless infos[parent]!.indices.size == expected[parent]! do
      throwError "wrapper fixture changed generated index counts"
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "wrapper fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "wrapper fixture changed registered metadata counts"
    for index in infos[parent]!.indices do
      unless (source.lctx.find? index.fvarId!).isSome do
        throwError "wrapper fixture lost an allocated index declaration"

private def checkFixture (ctx : Context) (name : Name) (nparams : Nat)
    (source normalized : Expr) (nindices : Nat) : MetaM Unit := do
  checkWhnf ctx source normalized
  checkRegistered ctx nparams #[header name source] #[nindices]
  unless declareConstructors.arity 0 source == 0 &&
      declareConstructors.arity 0 normalized == nparams + nindices do
    throwError "wrapper fixture collapsed the raw/normalized arity boundary"

private def fixtures (ctx : Context) : MetaM Unit := do
  let telescope := indexed 2
  let dependent := Expr.forallE `carrier sortType
    (.forallE `index (.bvar 0) sortType .strictImplicit) .default
  let wrappers : Array (Expr × Expr) := #[
    (annotate telescope, telescope),
    (annotate (annotate telescope), telescope),
    (letWrapper telescope, telescope),
    (betaWrapper telescope, telescope),
    (annotate (letWrapper telescope), telescope),
    (annotate (betaWrapper telescope), telescope),
    (letWrapper (annotate telescope), telescope),
    (betaWrapper (annotate telescope), telescope),
    (letWrapper (betaWrapper telescope), telescope),
    (betaWrapper (letWrapper telescope), telescope),
    (annotate (letWrapper (betaWrapper telescope)), telescope),
    (betaWrapper (annotate (letWrapper telescope)), telescope)]
  for index in [:wrappers.size] do
    checkFixture ctx (Name.mkNum `WrapperFamily index) 0 wrappers[index]!.1 wrappers[index]!.2 2
  checkFixture ctx `WrapperDependent 1 (annotate (letWrapper dependent)) dependent 1
  checkFixture ctx `WrapperSort 0 (betaWrapper (annotate sortType)) sortType 0
  checkFixture ctx `WrapperUsedLet 0
    (annotate (.letE `carrier sortType (.const ``Nat []) carrierBody false)) carrierResult 1
  checkFixture ctx `WrapperUsedBeta 0
    (annotate (.app (.lam `carrier sortType carrierBody .default) (.const ``Nat []))) carrierResult 1
  checkRegistered ctx 0 #[header `WrapperMutual (annotate (indexed 1)),
    header `WrapperOther (betaWrapper telescope)] #[1, 2]

private def boundaries (ctx : Context) : MetaM Unit := do
  let telescope := indexed 2
  let source := annotate (letWrapper (betaWrapper telescope))
  let .error .deepRecursion := ((monadLift (TypeChecker.whnf source) : M Expr)
      { ctx with fuel := { ctx.fuel with recDepth := 0 } })
    | throwError "wrapper receipt incorrectly excludes normalization depth errors"
  for wrapped in [letWrapper telescope, betaWrapper telescope] do
    let .error .deepRecursion := ((monadLift (TypeChecker.whnf wrapped) : M Expr)
        { ctx with fuel := { ctx.fuel with recDepth := 1 } })
      | throwError "wrapper receipt incorrectly excludes shallow recursion-depth errors"
    let .error .deterministicTimeout := ((monadLift (TypeChecker.whnf (annotate wrapped)) : M Expr)
        { ctx with fuel := { ctx.fuel with whnf := 0 } })
      | throwError "wrapper receipt incorrectly excludes exhausted WHNF-loop errors"
    checkWhnf { ctx with fuel := { ctx.fuel with recDepth := 2, whnf := 1 } } wrapped telescope
  let types := #[header `UncheckedWrapper source]
  let .ok (stats, _, _, reader) := safeStage 0 types ctx
    | throwError "unchecked wrapper boundary setup failed"
  let inconsistent := { stats with nindices := #[97] }
  let .ok infos := mkRecInfos inconsistent types (.succ .zero) pure reader
    | throwError "unchecked wrapper statistics stopped generating infos"
  unless infos[0]!.indices.size == 2 && inconsistent.nindices[0]! == 97 do
    throwError "wrapper receipt incorrectly certifies unchecked stored statistics"
  let innerWrapped := Expr.forallE `index (.const ``Nat []) (annotate sortType) .default
  checkWhnf ctx innerWrapped innerWrapped
  checkRegistered ctx 0 #[header `WrapperUnderBinder innerWrapped] #[1]

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  audit ``SortTelescope.normalized
  audit ``NormalizedSortTelescope.mdata
  audit ``SortTelescope.normalizedLet binding
  let beta := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  audit ``SortTelescope.normalizedBeta beta
  audit ``carrierSubstitution binding
  audit ``annotatedReceipt
  audit ``annotatedHeaders
  audit ``usedLetReceipt binding
  audit ``usedBetaReceipt beta
  audit ``provedHeaders beta
  audit ``provedRegisteredCounts (beta ++ scope)
  audit ``mkRecInfos.registeredNormalizedAlignedIndices
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``checkInductiveTypes.safeRegisteredNormalizedIndexCounts (binding ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `WrapperSeed, idx := 37 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `WrapperSeed 36⟩ `old (.const ``Bool []) .implicit }
  for reader in [ctx, { ctx with lparams := [`u] }, seeded] do
    fixtures reader
  boundaries ctx
  logInfo "51 wrapper registration prefixes and 51 WHNF observations preserved canonical outputs, raw-arity gaps, and registered counts; seven boundaries remain explicit"

end InductiveNormalizedWrappersTest
