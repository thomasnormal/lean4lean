import Lean4Lean.Verify.InductiveBinderBoundedClosure
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBoundedClosureTest

private def sortType : Expr := .sort (.succ .zero)

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr :=
  .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`BoundedClosureTag, .ofNat 43)] }

private def bindMany : Nat → Expr → Expr
  | 0, body => body
  | count + 1, body => .forallE `layer sortType (bindMany count body) .default

private theorem bindManyClosed {count depth : Nat} {body : Expr} :
    (bindMany count body).Closed depth ↔ body.Closed (depth + count) := by
  induction count generalizing depth with
  | zero => simp [bindMany]
  | succ count ih => simp [bindMany, Closed, sortType, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem bindManyFits {count : Nat} {body : Expr} :
    BVarRangeFits (bindMany count body) ↔ BVarRangeFits body := by
  induction count with
  | zero => rfl
  | succ count ih => simp [bindMany, BVarRangeFits, sortType, ih]

private theorem closedTallSourceCanExceedLeafBound :
    (bindMany (2^20) (.bvar (2^20 - 1))).Closed 0 ∧
      ¬ BVarRangeFits (bindMany (2^20) (.bvar (2^20 - 1))) := by
  rw [bindManyClosed, bindManyFits]
  simp [Closed, BVarRangeFits]

private theorem arbitraryDepthClosureDoesNotSupplyLeafBound :
    (Expr.bvar 1048575).Closed 1048576 ∧ ¬ BVarRangeFits (.bvar 1048575) := by
  simp [Closed, BVarRangeFits]

private theorem largestRepresentableBVarFits : BVarRangeFits (.bvar 1048574) := by
  simp [BVarRangeFits]

private theorem nextBVarDoesNotFit : ¬ BVarRangeFits (.bvar 1048575) := by
  simp [BVarRangeFits]

private theorem boundDoesNotEstablishClosure :
    BVarRangeFits (.bvar 1048574) ∧ ¬ (Expr.bvar 1048574).Closed 0 := by
  simp [BVarRangeFits, Closed]

private theorem boundDoesNotExcludeExpressionMeta (metavar : MVarId) :
    BVarRangeFits (.mvar metavar) ∧ ¬ (Expr.mvar metavar).Closed 0 := by
  simp [BVarRangeFits, Closed]

private theorem boundDoesNotExcludeUniverseMeta (metavar : LMVarId) :
    BVarRangeFits (.sort (.mvar metavar)) ∧ (Expr.sort (.mvar metavar)).Closed 0 ∧
      ¬ (Expr.sort (.mvar metavar)).FVarsIn (fun _ => False) := by
  simp [BVarRangeFits, Closed, FVarsIn, Level.hasMVar']

private theorem boundDoesNotExcludeFreeVariable (id : FVarId) :
    BVarRangeFits (.fvar id) ∧ (Expr.fvar id).Closed 0 ∧
      ¬ (Expr.fvar id).FVarsIn (fun _ => False) := by
  simp [BVarRangeFits, Closed, FVarsIn]

private theorem discardedDefaultDoesNotReflectBound :
    BVarRangeFits (peelTypeAnnotations (binary ``optParam [] (.const ``Nat []) (.bvar 1048575))) ∧
      ¬ BVarRangeFits (binary ``optParam [] (.const ``Nat []) (.bvar 1048575)) := by
  simp [peelTypeAnnotations, binary, BVarRangeFits]

private theorem boundSuppliesRangeAccuracy {value : Expr} (fits : BVarRangeFits value) :
    value.looseBVarRange = value.looseBVarRange' := fits.rangeAccurate

private theorem boundSuppliesZeroReflection {value : Expr} (fits : BVarRangeFits value)
    (zero : value.looseBVarRange = 0) : value.looseBVarRange' = 0 := fits.rangeZeroReflects zero

private theorem boundAndIntegrityCloseAtArbitraryDepth {value : Expr} {depth : Nat}
    {predicate : FVarId → Prop} (fits : BVarRangeFits value) (within : value.FVarsIn predicate)
    (range : value.looseBVarRange ≤ depth) : value.Closed depth :=
  within.closed_of_bvarRangeFits_atDepth fits range

private theorem guardedTypeCheckClosesWithBound {value inferred : Expr} {predicate : FVarId → Prop}
    {reader : TypeChecker.Context} {state nextState : TypeChecker.State}
    (within : value.FVarsIn predicate) (fits : BVarRangeFits value)
    (success : TypeChecker.checkType value reader state = .ok (inferred, nextState)) : value.Closed 0 :=
  TypeChecker.checkType_closed_of_bvarRangeFits within fits success

private theorem boundedClosureHasExactNativeCharacterization {value : Expr} {depth : Nat}
    (fits : BVarRangeFits value) :
    value.Closed depth ↔ value.looseBVarRange ≤ depth ∧ value.hasExprMVar = false :=
  fits.closed_iff_nativeRange

private theorem checkedSourceBoundSuppliesClosure {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (fits : BVarRangeFits types[parent]!.type) : types[parent]!.type.Closed 0 :=
  source.sourceClosed_of_bvarRangeFits fits

private theorem checkedHeadersBoundSuppliesSourceClosure {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checked : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (fits : HeaderSourceBVarRangeFits types) : HeaderSourceClosed types :=
  headers.sourceClosed_of_bvarRangeFits fits

private theorem checkedWrappedHeadersBoundSuppliesNormalizedClosure {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {original checked : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (fits : HeaderSourceBVarRangeFits types) :
    NormalizedHeaderClosed types := headers.wrappedClosed_of_bvarRangeFits wrapped fits

private theorem checkedNormalizedSourceBoundSuppliesClosure {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (fits : BVarRangeFits types[parent]!.type)
    (wrapper : WrappedSortTelescope types[parent]!.type wrapped)
    (normalization : NormalizedSortTelescope types[parent]!.type normalized) : normalized.Closed 0 :=
  source.normalizedClosed_of_bvarRangeFits fits wrapper normalization

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def dependent : Expr :=
  .forallE `carrier sortType
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0))
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)))
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1)))
          sortType .strictImplicit) .instImplicit) .default) .implicit

private theorem dependentFits : BVarRangeFits dependent := by
  simp [dependent, BVarRangeFits, sortType, unary, binary, equalityDomain, mkApp2, mkApp3]

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (unary ``semiOutParam [.succ .zero] (.bvar 0)) .default
      (.forallE `witness (unary ``outParam [.zero] (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))) .instImplicit
        (.forallE `optional
          (binary ``optParam [.zero] (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1))
            (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 2) (.bvar 1))) .strictImplicit
          (.sort (.succ .zero)))))

private def wrappedLet (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private def wrappedBeta (data : MData) : Expr :=
  .mdata data (.app (.lam `unused (.const ``Nat []) dependent .implicit) (.lit (.natVal 0)))

private theorem wrappedLetFits (data : MData) : BVarRangeFits (wrappedLet data) :=
  ⟨True.intro, True.intro, dependentFits⟩

private theorem wrappedBetaFits (data : MData) : BVarRangeFits (wrappedBeta data) :=
  ⟨⟨True.intro, dependentFits⟩, True.intro⟩

private theorem wrappedLetTrace (data : MData) : WrappedSortTelescope (wrappedLet data) dependent := by
  unfold wrappedLet
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private theorem wrappedBetaTrace (data : MData) : WrappedSortTelescope (wrappedBeta data) dependent := by
  unfold wrappedBeta
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.beta
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `BoundedClosureProvedLet (wrappedLet data), header `BoundedClosureProvedBeta (wrappedBeta data)]

private theorem provedSourceFits (data : MData) : HeaderSourceBVarRangeFits (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact wrappedLetFits data
  · exact wrappedBetaFits data

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem boundOnlySafeWrappedRegistration (data : MData) (ctx : Context)
    (hwf : ctx.lctx.WF) (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        RecursorBinderClosure result.1 (provedTypes data) checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredWrappedBinderClosure_of_bvarRangeFits 1 (provedTypes data) 0 (.succ .zero)
    [] false ctx (provedHeaders data) hwf reserved (provedSourceFits data)

private theorem boundOnlySourceReceipt {nparams : Nat} {types : Array InductiveType} {stats : InductiveStats}
    {original checked recursorRoot current : Context} {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (wrapped : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) (fits : HeaderSourceBVarRangeFits types) :
    RecursorBinderClosure stats types checked current infos :=
  headers.wrappedBinderClosure_of_bvarRangeFits sources wrapped support hwf fits

private theorem boundOnlyGetter (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (original checked ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderClosure stats types checked result.2 result.1 :=
  mkRecInfos.getWrappedBinderClosure_of_bvarRangeFits nparams stats types elimLevel original checked ctx
    headers wrapped hwf reserved support fits

private theorem boundOnlyCPS (α : Type) (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (original checked ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderClosure stats types checked current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedWrappedBinderClosure_of_bvarRangeFits nparams stats types elimLevel next original checked
    ctx post headers wrapped hwf reserved support fits hnext

private theorem boundOnlyRegistration (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (original checked ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checked)
    (wrapped : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderClosure stats types checked result.2.2 result.2.1 :=
  mkRecInfos.registeredWrappedBinderClosure_of_bvarRangeFits nparams stats types elimLevel lparams isK isUnsafe
    original checked ctx headers wrapped hwf reserved henv support fits

private def boundsHold : Expr → Bool
  | .bvar index => index + 1 ≤ 2^20 - 1
  | .app function argument => boundsHold function && boundsHold argument
  | .lam _ domain body _ | .forallE _ domain body _ => boundsHold domain && boundsHold body
  | .letE _ domain value body _ => boundsHold domain && boundsHold value && boundsHold body
  | .mdata _ value | .proj _ _ value => boundsHold value
  | _ => true

private def checkBounded (value : Expr) : MetaM Unit := do
  unless boundsHold value && value.looseBVarRange == value.looseBVarRange' do
    throwError "bounded-closure numeric leaf bound or native/structural range agreement failed"

private def checkClosed (value : Expr) : MetaM Unit := do
  checkBounded value
  unless !value.hasLooseBVars && !value.hasExprMVar do
    throwError "bounded-closure guarded/raw/peeled/stored expression is not closed"

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let generatorRoot ← readThe Context
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          generatorRoot.lparams false false
        return (stats, checked, generatorRoot, result)

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some declaration := ctx.lctx.getAt? (start + offset)
      | throwError "bounded-closure actual index points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkDeclaration (ctx : Context) (value : Expr) (domain : Expr)
    (position : Nat) : MetaM Unit := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "bounded-closure actual index lookup is missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations domain &&
      declaration.index == position do
    throwError "bounded-closure actual index stored-type/value/native-position anchor changed"
  checkClosed declaration.type

private def checkOpening (checkedCtx generatedCtx : Context) (nparams checkedStart generatedStart : Nat)
    (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    checkClosed left
    checkClosed right
    let .forallE _ leftRaw leftBody _ := left
      | throwError "bounded-closure checked opening ended before actual values"
    let .forallE _ rightRaw rightBody _ := right
      | throwError "bounded-closure generated opening ended before actual values"
    checkClosed leftRaw
    checkClosed rightRaw
    checkClosed (peelTypeAnnotations leftRaw)
    checkClosed (peelTypeAnnotations rightRaw)
    if position ≥ nparams then
      checkDeclaration checkedCtx leftValues[position]! leftRaw (checkedStart + position - nparams)
      checkDeclaration generatedCtx rightValues[position]! rightRaw (generatedStart + position - nparams)
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  checkClosed left
  checkClosed right
  unless left == sortType && right == sortType do
    throwError "bounded-closure actual checked/generated terminal changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  for type in types do
    checkClosed type.type
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "bounded-closure actual safe/header/recursor registration failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "bounded-closure actual count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "bounded-closure actual checked source normalization failed"
    checkClosed normalized
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "bounded-closure registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "bounded-closure registered recursor parameters/indices changed"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BoundedClosureSort sortType] #[0]
  for nparams in [0, 1, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BoundedClosureDependent nparams) dependent] #[4 - nparams]
    checkFixture ctx nparams #[header (Name.mkNum `BoundedClosureMutualFirst nparams) dependent,
      header (Name.mkNum `BoundedClosureMutualSecond nparams) dependent] #[4 - nparams, 4 - nparams]
  checkFixture ctx 1 #[header `BoundedClosureLet (wrappedLet tagged),
    header `BoundedClosureBeta (wrappedBeta tagged)] #[3, 3]
  let nat := Expr.const ``Nat []
  checkFixture ctx 0 #[
    header `BoundedClosureOut (.forallE `index (unary ``outParam [.succ .zero] nat) sortType .default),
    header `BoundedClosureAuto (.forallE `index
      (binary ``autoParam [.succ .zero] nat (.const ``Lean.Syntax.missing [])) sortType .default),
    header `BoundedClosureMetadata (.forallE `index (.mdata tagged
      (unary ``outParam [.succ .zero] nat)) sortType .default)] #[1, 1, 1]

private def rejectGuardCheck (reader : TypeChecker.Context) (source : Expr) : MetaM Unit := do
  let cache := ({} : InferCache).insert source sortType
  let state : TypeChecker.State := { inferTypeC := cache, inferTypeI := cache }
  for initial in [({} : TypeChecker.State), state] do
    for action in [TypeChecker.checkType, TypeChecker.inferType] do
      match action source reader initial with
      | .error (.other reason) =>
        unless reason.startsWith "type checker does not support loose bound variables" do
          throwError "bounded-closure loose-BVar check failed through the wrong guard"
      | _ => throwError "bounded-closure loose-BVar check incorrectly accepted a cached/uncached source"

private def rejectedLooseSources (ctx : Context) : MetaM Unit := do
  let reader : TypeChecker.Context := { env := ctx.env }
  for index in [0, 7, 1048574] do
    let loose := Expr.bvar index
    checkBounded loose
    unless loose.looseBVarRange == index + 1 && loose.hasLooseBVars do
      throwError "bounded-closure highest representable native BVar range changed"
    let sources := #[
      Expr.forallE `index loose sortType .default,
      Expr.letE `unused (.const ``Nat []) loose dependent true,
      Expr.app (.lam `unused (.const ``Nat []) dependent .default) loose,
      Expr.forallE `index (binary ``optParam [.succ .zero] (.const ``Nat []) loose) sortType .default]
    for source in sources do
      checkBounded source
      rejectGuardCheck reader source
      let .ok () := ctx.env.checkNoMVarNoFVar `BoundedClosureLoose source
        | throwError "bounded-closure loose negative control unexpectedly contains metavariables/FVars"
      match checkInductiveTypes 0 #[header `BoundedClosureLoose source] (fun _ => pure ()) ctx with
      | .error (.other reason) =>
        unless reason.startsWith "type checker does not support loose bound variables" do
          throwError "bounded-closure checked header failed through the wrong loose-BVar guard"
      | _ => throwError "bounded-closure checked header incorrectly accepts a bounded but loose source"
  logInfo "12 bounded loose-source rejections / 48 poisoned-cache and uncached infer/check rejections, through native-valid index 1048574"

private def rejectedMetaSources (ctx : Context) : MetaM Unit := do
  let expressionMeta := Expr.mvar ⟨`BoundedClosureExprMeta⟩
  let levelMeta := Level.mvar ⟨`BoundedClosureLevelMeta⟩
  for domain in [expressionMeta, Expr.sort levelMeta, Expr.const ``Nat [levelMeta],
      binary ``optParam [.succ .zero] (.const ``Nat []) expressionMeta] do
    let source := Expr.forallE `index domain sortType .default
    checkBounded source
    match checkInductiveTypes 0 #[header `BoundedClosureMeta source] (fun _ => pure ()) ctx with
    | .error (.declHasMVars _ name original) =>
      unless name == `BoundedClosureMeta && original == source do
        throwError "bounded-closure meta guard rejected the wrong bounded source"
    | _ => throwError "bounded-closure numeric bound incorrectly excludes or licenses source metavariables"
  logInfo "four bounded expr/sort-level/const-level/default-expression meta sources fail the checked-source guard"

private def cachedMetaBoundary (ctx : Context) : MetaM Unit := do
  let reader : TypeChecker.Context := { env := ctx.env }
  let expressionMeta := Expr.mvar ⟨`BoundedClosureCachedMeta⟩
  checkBounded expressionMeta
  let cache := ({} : InferCache).insert expressionMeta sortType
  let state : TypeChecker.State := { inferTypeC := cache, inferTypeI := cache }
  for action in [TypeChecker.checkType, TypeChecker.inferType] do
    let .ok (inferred, _) := action expressionMeta reader state
      | throwError "bounded-closure cached meta negative control unexpectedly failed"
    unless inferred == sortType && !expressionMeta.hasLooseBVars && expressionMeta.hasExprMVar do
      throwError "bounded-closure cached meta incorrectly establishes expression-meta freedom"
  match ctx.env.checkNoMVarNoFVar `BoundedClosureCachedMeta expressionMeta with
  | .error (.declHasMVars ..) => pure ()
  | _ => throwError "bounded-closure checked-source guard incorrectly licenses a cache-accepted expression meta"
  logInfo "two bounded cache-accepted expression-meta controls retain the separate source-integrity premise"

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless axiomName != ``Expr.looseBVarRange_eq && axiomName != ``sorryAx && allowed.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

private def auditModules (modules : List Name) (allowed : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut totalDeclarations := 0
  let mut totalTheorems := 0
  for moduleName in modules do
    let some moduleIndex := env.getModuleIdx? moduleName
      | throwError "bounded-closure audited module absent: {moduleName}"
    let mut declarations := 0
    let mut theorems := 0
    for (name, info) in env.constants do
      if env.getModuleIdxFor? name == some moduleIndex then
        declarations := declarations + 1
        if info matches .thmInfo _ then
          theorems := theorems + 1
        audit name allowed
    totalDeclarations := totalDeclarations + declarations
    totalTheorems := totalTheorems + theorems
    logInfo m!"{moduleName}: declarations = {declarations}; theorems = {theorems}"
  logInfo m!"bounded-module census incl private: declarations = {totalDeclarations}; theorems = {totalTheorems}"

private def auditNativeProvenance (nativeInterfaces nativeBitAxioms : List Name) : MetaM Unit := do
  let env ← getEnv
  for (moduleName, names) in [(`Lean4Lean.Verify.Axioms, nativeInterfaces),
      (`Lean4Lean.Verify.Expr, nativeBitAxioms)] do
    let some expectedModule := env.getModuleIdx? moduleName
      | throwError "bounded-closure native-axiom provenance module absent: {moduleName}"
    for name in names do
      let some (.axiomInfo _) := env.find? name
        | throwError "bounded-closure native provenance name is not an existing axiom: {name}"
      unless env.getModuleIdxFor? name == some expectedModule do
        throwError "bounded-closure native axiom originates outside its pinned existing module: {name}"
      logInfo m!"native provenance: {name} from {moduleName}"

#print axioms BVarRangeFits.rangeAccurate
#print axioms CheckedHeaderSource.sourceClosed_of_bvarRangeFits
#print axioms checkInductiveTypes.safeRegisteredWrappedBinderClosure_of_bvarRangeFits

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``Expr.mkData_eq, ``Expr.mkAppData_eq]
  let nativeBitAxioms := [
    `Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9,
    `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7,
    `Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8]
  let native := nativeInterfaces ++ nativeBitAxioms
  auditNativeProvenance nativeInterfaces nativeBitAxioms
  let binding := [``Expr.instantiate1_eq, ``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  let expressions := [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``PersistentHashMap.findAux_isSome]
  for theoremName in [``bindManyClosed, ``bindManyFits, ``closedTallSourceCanExceedLeafBound,
      ``arbitraryDepthClosureDoesNotSupplyLeafBound, ``largestRepresentableBVarFits,
      ``nextBVarDoesNotFit, ``boundDoesNotEstablishClosure, ``boundDoesNotExcludeExpressionMeta,
      ``boundDoesNotExcludeUniverseMeta, ``boundDoesNotExcludeFreeVariable,
      ``discardedDefaultDoesNotReflectBound, ``dependentFits, ``dependentShape,
      ``wrappedLetFits, ``wrappedBetaFits, ``provedSourceFits] do
    audit theoremName logical
  for theoremName in [``boundSuppliesRangeAccuracy, ``boundSuppliesZeroReflection] do
    audit theoremName (logical ++ native)
  audit ``boundAndIntegrityCloseAtArbitraryDepth (logical ++ native ++ [``Expr.hasExprMVar_eq])
  audit ``boundedClosureHasExactNativeCharacterization (logical ++ native ++ [``Expr.hasExprMVar_eq])
  audit ``guardedTypeCheckClosesWithBound (logical ++ native)
  for theoremName in [``wrappedLetTrace, ``wrappedBetaTrace, ``provedHeaders] do
    audit theoremName (logical ++ binding)
  for theoremName in [``checkedSourceBoundSuppliesClosure, ``checkedHeadersBoundSuppliesSourceClosure] do
    audit theoremName (logical ++ native ++ expressions)
  audit ``checkedWrappedHeadersBoundSuppliesNormalizedClosure (logical ++ native ++ binding ++ expressions)
  audit ``checkedNormalizedSourceBoundSuppliesClosure (logical ++ native ++ binding ++ expressions)
  for theoremName in [``boundOnlySafeWrappedRegistration, ``boundOnlySourceReceipt, ``boundOnlyGetter,
      ``boundOnlyCPS, ``boundOnlyRegistration] do
    audit theoremName (logical ++ native ++ binding ++ expressions ++ scope)
  auditModules [`Lean4Lean.Verify.ExprBoundedRange, `Lean4Lean.Verify.InductiveBoundedHeaderClosure,
    `Lean4Lean.Verify.InductiveBinderBoundedClosure] (logical ++ native ++ binding ++ expressions ++ scope)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BoundedClosureSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BoundedClosureSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BoundedClosureSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBoundedClosureSeed, idx := 71 } }] do
    fixtures reader
  rejectedLooseSources ctx
  rejectedMetaSources ctx
  cachedMetaBoundary ctx
  logInfo "27 full registrations / 45 parent pairs / 141 paired raw domains / 90 paired index declarations / three readers satisfy numeric bounds and agree on native/structural ranges"

end InductiveBoundedClosureTest
