import Lean4Lean.Verify.InductiveBinderClosure
import Lean4Lean.Verify.InductiveHeaderClosureGuard
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveBinderClosureTest

private def sortType : Expr := .sort (.succ .zero)

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr :=
  .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`BinderClosureTag, .ofNat 41)] }

private theorem modelPreservesArbitraryDepth {value : Expr} {depth : Nat}
    (closed : value.Closed depth) : (peelTypeAnnotations value).Closed depth :=
  closed.peelTypeAnnotations

private theorem substitutionPreservesDepth {value replacement : Expr} {depth offset : Nat}
    (closed : value.Closed (depth + 1)) (replacementClosed : replacement.Closed 0)
    (offsetWithin : offset ≤ depth) : (value.instantiate1' replacement offset).Closed depth :=
  closed.instantiate1_offset replacementClosed offsetWithin

private theorem actualOpeningPreservesDepth {value : Expr} {depth : Nat} (id : FVarId)
    (closed : value.Closed (depth + 1)) : (value.instantiate1 (.fvar id)).Closed depth :=
  closed.instantiate1_native (by trivial)

private theorem universeMetasRemainClosed (metavar : LMVarId) :
    (Expr.sort (.mvar metavar)).Closed 0 ∧ (Expr.const ``Nat [.mvar metavar]).Closed 0 ∧
      ¬ (Expr.sort (.mvar metavar)).FVarsIn (fun _ => False) ∧
      ¬ (Expr.const ``Nat [.mvar metavar]).FVarsIn (fun _ => False) := by
  simp [Closed, FVarsIn, Level.hasMVar']

private theorem expressionMetasAreNotClosed (metavar : MVarId) :
    ¬ (Expr.mvar metavar).Closed 0 := by
  simp [Closed]

private theorem fvarClosureDoesNotEstablishIntegrity (id : FVarId) :
    (Expr.fvar id).Closed 0 ∧ ¬ (Expr.fvar id).FVarsIn (fun _ => False) := by
  simp [Closed, FVarsIn]

private theorem fvarIntegrityDoesNotEstablishClosure (index : Nat) :
    (Expr.bvar index).FVarsIn (fun _ => False) ∧ ¬ (Expr.bvar index).Closed 0 := by
  simp [Closed, FVarsIn]

private theorem annotationOutputDoesNotReflectClosure :
    (peelTypeAnnotations (binary ``optParam [] (.const ``Nat []) (.bvar 1048576))).Closed 0 ∧
      ¬ (binary ``optParam [] (.const ``Nat []) (.bvar 1048576)).Closed 0 := by
  simp [peelTypeAnnotations, binary, Closed]

private theorem metadataBarrierRetainsLooseBVars :
    ¬ (peelTypeAnnotations (.mdata tagged (unary ``outParam [] (.bvar 1048576)))).Closed 0 := by
  simp [peelTypeAnnotations, unary, Closed]

private theorem wrongArityRetainsLooseBVars :
    ¬ (peelTypeAnnotations (binary ``outParam [] (.const ``Nat []) (.bvar 1048576))).Closed 0 := by
  simp [peelTypeAnnotations, binary, Closed]

private theorem nonclosedReplacementCanEscape :
    (Expr.bvar 0).Closed 1 ∧ ¬ ((Expr.bvar 0).instantiate1' (.bvar 0)).Closed 0 := by
  simp [Expr.instantiate1', Expr.liftLooseBVars', Closed]

private theorem nonclosedReplacementCanEscapeUnderBinder :
    (Expr.forallE `inner sortType (.bvar 1) .default).Closed 1 ∧
      ¬ ((Expr.forallE `inner sortType (.bvar 1) .default).instantiate1' (.bvar 0)).Closed 0 := by
  simp [sortType, Expr.instantiate1', Expr.liftLooseBVars', Closed]

private theorem telescopeShapeAndIntegrityDoNotEstablishClosure :
    SortTelescope (.forallE `index (.bvar 0) sortType .default) ∧
      (Expr.forallE `index (.bvar 0) sortType .default).FVarsIn (fun _ => False) ∧
      ¬ (Expr.forallE `index (.bvar 0) sortType .default).Closed 0 := by
  refine ⟨.forallE `index (.bvar 0) .default (.sort (.succ .zero)), ?_⟩
  simp [FVarsIn, Closed, sortType, Level.hasMVar']

private def discardedLet : Expr :=
  .letE `unused (.const ``Nat []) (.bvar 1048576) sortType true

private theorem normalizationDoesNotReflectClosure :
    WrappedSortTelescope discardedLet sortType ∧
      sortType.Closed 0 ∧ ¬ discardedLet.Closed 0 := by
  refine ⟨?_, ?_⟩
  · unfold discardedLet
    apply WrappedSortTelescope.letE
    rw [Expr.instantiate1_eq]
    exact .telescope (.sort (.succ .zero))
  · simp [discardedLet, sortType, Closed]

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

private theorem dependentClosed : dependent.Closed 0 := by
  simp [dependent, sortType, unary, binary, equalityDomain, mkApp2, mkApp3, Closed]

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

private theorem wrappedLetClosed (data : MData) : (wrappedLet data).Closed 0 := by
  exact ⟨True.intro, True.intro, dependentClosed.mono (by omega)⟩

private theorem wrappedBetaClosed (data : MData) : (wrappedBeta data).Closed 0 := by
  exact ⟨⟨True.intro, dependentClosed.mono (by omega)⟩, True.intro⟩

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

private theorem wrappedLetNormalizesClosed (data : MData) : dependent.Closed 0 :=
  (wrappedLetTrace data).closed (wrappedLetClosed data)

private theorem wrappedBetaNormalizesClosed (data : MData) : dependent.Closed 0 :=
  (wrappedBetaTrace data).closed (wrappedBetaClosed data)

private theorem actualOpenedRawDomainsAreClosed {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (closed : type.Closed 0)
    (values : BinderValuesClosed steps) : BinderRawDomainClosed steps :=
  opened.rawDomainClosed closed values

private theorem actualOpenedTerminalIsClosed {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (closed : type.Closed 0)
    (values : BinderValuesClosed steps) : terminal.Closed 0 :=
  opened.terminalClosed closed values

private theorem actualStoredIndexTypesAreClosed {ctx : Context} {steps : List BinderStep}
    (closed : BinderRawDomainClosed steps) (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeClosed ctx steps := closed.storedIndexTypeClosed declared

private theorem actualLookupTypeClosureIsUsable {ctx : Context} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (closed : BinderStoredIndexTypeClosed ctx steps) (selected : steps[position]? = some step)
    (index : step.role = .index) (lookup : ctx.lctx.find? step.value.fvarId! = some decl) :
    decl.type.Closed 0 := closed position step decl selected index lookup

private theorem parentClosureRetainsIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderClosure stats types parent checked current info) :
    ParentBinderIntegrity stats types parent checked current info := receipt.toBinderIntegrity

private theorem recursorClosureRetainsIntegrity {stats : InductiveStats} {types : Array InductiveType}
    {checked current : Context} {infos : Array RecInfo}
    (receipt : RecursorBinderClosure stats types checked current infos) :
    RecursorBinderIntegrity stats types checked current infos := receipt.toBinderIntegrity

private theorem upgradeKeepsNormalizedClosurePremise {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checked current : Context} {info : RecInfo}
    (receipt : ParentBinderIntegrity stats types parent checked current info)
    (shapes : ∀ value ∈ stats.params.toList, ∃ id, value = .fvar id)
    (closed : ∀ normalized, NormalizedSortTelescope types[parent]!.type normalized → normalized.Closed 0) :
    ParentBinderClosure stats types parent checked current info := receipt.closure shapes closed

private theorem sameWitnessRawStoredNativeClosure {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderClosure stats types parent checkedRoot current info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧ OpenedTelescope normalized generated generatedTerminal ∧
      BinderStepsIndexDeclared checkedRoot checked ∧ BinderStepsIndexDeclared current generated ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧ BinderIndexAllocations current generatedStart generated ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!) (info.indices.toList.map Expr.fvarId!) ∧
      BinderLookupCorrespondence [] checked generated pairs ∧
      normalized.Closed 0 ∧ BinderRawDomainClosed checked ∧ BinderRawDomainClosed generated ∧
      BinderStoredIndexDomainClosed checked ∧ BinderStoredIndexDomainClosed generated ∧
      BinderStoredIndexTypeClosed checkedRoot checked ∧ BinderStoredIndexTypeClosed current generated ∧
      checkedTerminal.Closed 0 ∧ generatedTerminal.Closed 0 := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, _, _, _, _, hcheckedDeclared,
    hgeneratedDeclared, _, _, _, _, _, hcheckedAlloc, hgeneratedAlloc, _, hpairs, _, _, _, hlookup,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnormalizedClosed,
    hcheckedClosed, hgeneratedClosed, hcheckedStored, hgeneratedStored,
    hcheckedType, hgeneratedType, hcheckedTerminal, hgeneratedTerminal⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedDeclared, hgeneratedDeclared,
    hcheckedAlloc, hgeneratedAlloc, hpairs, hlookup, hnormalizedClosed, hcheckedClosed,
    hgeneratedClosed, hcheckedStored, hgeneratedStored, hcheckedType, hgeneratedType,
    hcheckedTerminal, hgeneratedTerminal⟩

private theorem successfulTypeCheckPassesLooseBVarGuard {value inferred : Expr}
    {context : TypeChecker.Context} {state nextState : TypeChecker.State}
    (success : TypeChecker.checkType value context state = .ok (inferred, nextState)) :
    value.hasLooseBVars = false := TypeChecker.checkType_hasLooseBVars_eq_false success

private theorem guardedSourcePassesLooseBVarGuard {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    types[parent]!.type.hasLooseBVars = false := source.sourceHasLooseBVars_eq_false

private theorem sourceClosureKeepsRangeAccuracyPremise {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (accurate : types[parent]!.type.looseBVarRange = types[parent]!.type.looseBVarRange') :
    types[parent]!.type.Closed 0 := source.sourceClosed_of_rangeAccurate accurate

private theorem sourceClosureKeepsZeroReflectionPremise {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (reflects : types[parent]!.type.looseBVarRange = 0 → types[parent]!.type.looseBVarRange' = 0) :
    types[parent]!.type.Closed 0 := source.sourceClosed_of_rangeZeroReflects reflects

private theorem structuralRangeAndIntegrityEstablishClosure {value : Expr} {depth : Nat}
    {predicate : FVarId → Prop} (within : value.FVarsIn predicate)
    (range : value.looseBVarRange' ≤ depth) : value.Closed depth :=
  within.closed_of_looseBVarRange'_le range

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `BinderClosureProvedLet (wrappedLet data), header `BinderClosureProvedBeta (wrappedBeta data)]

private theorem provedSourceClosed (data : MData) : HeaderSourceClosed (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact wrappedLetClosed data
  · exact wrappedBetaClosed data

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have small : parent < 2 := by simpa [provedTypes] using bound
  have cases : parent = 0 ∨ parent = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedLetTrace data⟩
  · exact ⟨dependent, wrappedBetaTrace data⟩

private theorem provedSafeRegistrationKeepsSourceClosure (data : MData) (ctx : Context)
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
  checkInductiveTypes.safeRegisteredWrappedBinderClosure 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf reserved (provedSourceClosed data)

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

private def checkClosed (value : Expr) : MetaM Unit := do
  unless !value.hasLooseBVars && !value.hasExprMVar do
    throwError "binder-closure source/raw/peeled/stored expression is not closed"

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some declaration := ctx.lctx.getAt? (start + offset)
      | throwError "binder-closure actual index points at a local-context hole"
    values := values.push declaration.toExpr
  return values

private def checkDeclaration (ctx : Context) (value : Expr) (domain : Expr)
    (position : Nat) : MetaM Unit := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "binder-closure actual index lookup is missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations domain &&
      declaration.index == position do
    throwError "binder-closure actual index stored-type/value/native-position anchor changed"
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
      | throwError "binder-closure checked opening ended before actual values"
    let .forallE _ rightRaw rightBody _ := right
      | throwError "binder-closure generated opening ended before actual values"
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
    throwError "binder-closure actual checked/generated terminal changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  for type in types do
    checkClosed type.type
  let .ok (stats, checked, generatorRoot, env, infos, generated) := stage nparams types ctx
    | throwError "binder-closure actual safe/header/recursor registration failed"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "binder-closure actual count alignment changed"
  for parent in [:types.size] do
    let preceding := (expected.toList.take parent).sum
    let checkedStart := ctx.lctx.numIndices + nparams + preceding
    let generatedStart := generatorRoot.lctx.numIndices + preceding + 2 * parent
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "binder-closure actual checked source normalization failed"
    checkClosed normalized
    checkOpening checked generated nparams checkedStart generatedStart normalized stats.params
      checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "binder-closure registered recursor missing"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "binder-closure registered recursor parameters/indices changed"

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `BinderClosureSort sortType] #[0]
  for nparams in [0, 1, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `BinderClosureDependent nparams) dependent] #[4 - nparams]
    checkFixture ctx nparams #[header (Name.mkNum `BinderClosureMutualFirst nparams) dependent,
      header (Name.mkNum `BinderClosureMutualSecond nparams) dependent] #[4 - nparams, 4 - nparams]
  checkFixture ctx 1 #[header `BinderClosureLet (wrappedLet tagged),
    header `BinderClosureBeta (wrappedBeta tagged)] #[3, 3]
  let nat := Expr.const ``Nat []
  checkFixture ctx 0 #[
    header `BinderClosureOut (.forallE `index (unary ``outParam [.succ .zero] nat) sortType .default),
    header `BinderClosureAuto (.forallE `index
      (binary ``autoParam [.succ .zero] nat (.const ``Lean.Syntax.missing [])) sortType .default),
    header `BinderClosureMetadata (.forallE `index (.mdata tagged
      (unary ``outParam [.succ .zero] nat)) sortType .default)] #[1, 1, 1]

private def successfulGuardChecks (ctx : Context) : MetaM Unit := do
  let reader : TypeChecker.Context := { env := ctx.env }
  for source in [sortType, dependent, wrappedLet tagged, wrappedBeta tagged] do
    let .ok _ := TypeChecker.checkType source reader {}
      | throwError "binder-closure source type check unexpectedly failed"
    unless !source.hasLooseBVars do
      throwError "binder-closure successful source bypassed its loose-BVar guard"
  let cached := Expr.const `BinderClosureCacheControl []
  let cache := ({} : InferCache).insert cached sortType
  let state : TypeChecker.State := { inferTypeC := cache, inferTypeI := cache }
  for action in [TypeChecker.checkType, TypeChecker.inferType] do
    let .ok (inferred, _) := action cached reader state
      | throwError "binder-closure loose-BVar-free cache control failed"
    unless inferred == sortType do
      throwError "binder-closure cache control returned the wrong inferred type"
  logInfo "four successful checked sources and two loose-BVar-free infer/check cache hits retain the operational guard"

private def rejectGuardCheck (reader : TypeChecker.Context) (source : Expr) : MetaM Unit := do
  let cache := ({} : InferCache).insert source sortType
  let state : TypeChecker.State := { inferTypeC := cache, inferTypeI := cache }
  for initial in [({} : TypeChecker.State), state] do
    for action in [TypeChecker.checkType, TypeChecker.inferType] do
      match action source reader initial with
      | .error (.other reason) =>
        unless reason.startsWith "type checker does not support loose bound variables" do
          throwError "binder-closure loose-BVar check failed through the wrong guard"
      | _ => throwError "binder-closure loose-BVar check incorrectly accepted a cached/uncached source"

private def rejectedLooseSources (ctx : Context) : MetaM Unit := do
  let reader : TypeChecker.Context := { env := ctx.env }
  for index in [0, 7, 1048574] do
    let loose := Expr.bvar index
    let sources := #[
      Expr.forallE `index loose sortType .default,
      Expr.letE `unused (.const ``Nat []) loose dependent true,
      Expr.app (.lam `unused (.const ``Nat []) dependent .default) loose,
      Expr.forallE `index (binary ``optParam [.succ .zero] (.const ``Nat []) loose) sortType .default]
    for position in [:sources.size] do
      let source := sources[position]!
      unless source.hasLooseBVars do
        throwError "binder-closure loose-BVar boundary unexpectedly has zero native range"
      rejectGuardCheck reader source
      let .ok () := ctx.env.checkNoMVarNoFVar `BinderClosureLoose source
        | throwError "binder-closure negative control unexpectedly contains metavariables/FVars"
      match checkInductiveTypes 0 #[header `BinderClosureLoose source] (fun _ => pure ()) ctx with
      | .error (.other reason) =>
        unless reason.startsWith "type checker does not support loose bound variables" do
          throwError "binder-closure checked header failed through the wrong loose-BVar guard"
      | _ => throwError "binder-closure checked header incorrectly accepts a loose-BVar source"
  logInfo "12 checked source rejections and 48 cached/uncached infer/check controls reject loose binder domains, discarded lets/beta values and discarded annotation defaults through index 1048574"

private def uncheckedHelperBoundary (ctx : Context) : MetaM Unit := do
  let loose := Expr.bvar 7
  let stats : InductiveStats := {
    lctx := ctx.lctx, levels := [], resultLevel := .succ .zero
    indConsts := #[], params := #[], nindices := #[], isNotZero := true }
  let type := Expr.forallE `index loose sortType .default
  let .ok (values, current) := mkRecInfos.loopArgs1 stats type 0 #[] ctx.fuel.inductiveFuel
      (fun values => do return (values, ← readThe Context)) ctx
    | throwError "binder-closure unchecked helper control unexpectedly rejects a raw loose domain"
  let some declaration := current.lctx.find? values[0]!.fvarId!
    | throwError "binder-closure unchecked helper control did not allocate an index"
  unless declaration.type == loose && declaration.type.hasLooseBVars do
    throwError "binder-closure unchecked helper falsely acquired source closure"
  let discarded := binary ``optParam [.succ .zero] (.const ``Nat []) loose
  let .ok (discardedValues, discardedCtx) := mkRecInfos.loopArgs1 stats
      (.forallE `index discarded sortType .default) 0 #[] ctx.fuel.inductiveFuel
      (fun values => do return (values, ← readThe Context)) ctx
    | throwError "binder-closure unchecked discarded-default helper failed"
  let some discardedDeclaration := discardedCtx.lctx.find? discardedValues[0]!.fvarId!
    | throwError "binder-closure unchecked discarded-default helper did not allocate an index"
  unless discarded.hasLooseBVars && !discardedDeclaration.type.hasLooseBVars &&
      discardedDeclaration.type == (.const ``Nat [] : Expr) do
    throwError "binder-closure clean stored output incorrectly reflects raw source closure"
  logInfo "two unchecked helper controls separate persistent loose domains from discarded-default closure"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless axiomName != ``Expr.looseBVarRange_eq &&
        ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

#print axioms Closed.peelTypeAnnotations
#print axioms Closed.instantiate1_offset
#print axioms Closed.instantiate1_native
#print axioms TypeChecker.checkType_hasLooseBVars_eq_false

run_meta
  let binding := [``Expr.instantiate1_eq]
  let expressions := [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let normalized := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  for theoremName in [``modelPreservesArbitraryDepth, ``substitutionPreservesDepth,
      ``universeMetasRemainClosed, ``expressionMetasAreNotClosed, ``fvarClosureDoesNotEstablishIntegrity,
      ``fvarIntegrityDoesNotEstablishClosure, ``annotationOutputDoesNotReflectClosure,
      ``metadataBarrierRetainsLooseBVars, ``wrongArityRetainsLooseBVars,
      ``nonclosedReplacementCanEscape, ``nonclosedReplacementCanEscapeUnderBinder,
      ``telescopeShapeAndIntegrityDoNotEstablishClosure, ``dependentClosed, ``dependentShape,
      ``wrappedLetClosed, ``wrappedBetaClosed, ``actualStoredIndexTypesAreClosed,
      ``actualLookupTypeClosureIsUsable, ``successfulTypeCheckPassesLooseBVarGuard,
      ``parentClosureRetainsIntegrity, ``recursorClosureRetainsIntegrity, ``sameWitnessRawStoredNativeClosure,
      ``provedSourceClosed,
      ``guardedSourcePassesLooseBVarGuard, ``structuralRangeAndIntegrityEstablishClosure,
      ``Closed.peelTypeAnnotations, ``Closed.instantiate1_offset,
      ``TypeChecker.Inner.inferType'_hasLooseBVars_eq_false,
      ``TypeChecker.Methods.withFuel_inferType_hasLooseBVars_eq_false,
      ``TypeChecker.checkType_hasLooseBVars_eq_false, ``TypeChecker.checkType_run_hasLooseBVars_eq_false,
      ``FVarsIn.closed_of_looseBVarRange'_le, ``CheckedHeaderSource.sourceHasLooseBVars_eq_false,
      ``HeaderSourceClosed, ``NormalizedHeaderClosed, ``BinderRawDomainClosed, ``BinderValuesClosed,
      ``BinderStoredIndexDomainClosed, ``BinderStoredIndexTypeClosed,
      ``BinderRawDomainClosed.storedIndexDomainClosed, ``BinderRawDomainClosed.storedIndexTypeClosed] do
    audit theoremName
  for theoremName in [``actualOpeningPreservesDepth, ``normalizationDoesNotReflectClosure,
      ``wrappedLetTrace, ``wrappedBetaTrace, ``wrappedLetNormalizesClosed, ``wrappedBetaNormalizesClosed,
      ``actualOpenedRawDomainsAreClosed, ``actualOpenedTerminalIsClosed,
      ``Closed.instantiate1_native, ``WrappedSortTelescope.closed, ``OpenedTelescope.rawDomainClosed,
      ``OpenedTelescope.terminalClosed, ``upgradeKeepsNormalizedClosurePremise, ``provedHeaders,
      ``ParentBinderIntegrity.closure, ``RecursorBinderIntegrity.closure] do
    audit theoremName binding
  audit ``sourceClosureKeepsRangeAccuracyPremise expressions
  audit ``sourceClosureKeepsZeroReflectionPremise expressions
  audit ``CheckedHeaderSource.sourceClosed_of_rangeAccurate expressions
  audit ``CheckedHeaderSource.sourceClosed_of_rangeZeroReflects expressions
  audit ``BinderStepsIndexDeclared.valuesClosed
  audit ``CheckedHeaderSource.normalizedClosed_of_wrapped normalized
  audit ``CheckedHeaderSupportSources.wrappedClosed normalized
  for theoremName in [``ParentBinderClosure, ``RecursorBinderClosure,
      ``ParentBinderClosure.toBinderIntegrity, ``RecursorBinderClosure.toBinderIntegrity,
      ``BinderValuesBefore.closedShapes] do
    audit theoremName
  for theoremName in [``CheckedHeaderSupportSources.normalizedBinderClosure,
      ``mkRecInfos.scopedNormalizedBinderClosure, ``mkRecInfos.getNormalizedBinderClosure,
      ``checkInductiveTypes.safeRegisteredBinderClosure,
      ``checkInductiveTypes.safeRegisteredNormalizedBinderClosure] do
    audit theoremName (binding ++ scope)
  for theoremName in [``CheckedHeaderSupportSources.wrappedBinderClosure,
      ``mkRecInfos.scopedWrappedBinderClosure, ``mkRecInfos.getWrappedBinderClosure,
      ``checkInductiveTypes.safeRegisteredWrappedBinderClosure, ``provedSafeRegistrationKeepsSourceClosure] do
    audit theoremName (normalized ++ expressions ++ scope)
  audit ``mkRecInfos.registeredNormalizedBinderClosure
    (binding ++ scope ++ [``PersistentHashMap.findAux_isSome])
  audit ``mkRecInfos.registeredWrappedBinderClosure
    (normalized ++ expressions ++ scope ++ [``PersistentHashMap.findAux_isSome])
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `BinderClosureSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `BinderClosureSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `BinderClosureSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherBinderClosureSeed, idx := 71 } }] do
    fixtures reader
  successfulGuardChecks ctx
  rejectedLooseSources ctx
  uncheckedHelperBoundary ctx
  logInfo "27 full registrations / 45 parent pairs / 141 paired binder domains / 90 paired actual index declarations / three dense readers preserve source/raw/peeled/native stored closure"

end InductiveBinderClosureTest
