import Lean4Lean.Verify.InductiveMutualHeaderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ParameterPrefix ContextReserved)

namespace InductiveMutualHeaderTypingTest

example (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {candidate stored : Expr} {candidateSemantic storedSemantic : VExpr}
    (candidateTranslated : checker.TrExprS candidate candidateSemantic)
    (storedTranslated : checker.TrExprS stored storedSemantic)
    (accepted : (monadLift (TypeChecker.isDefEq candidate stored) : M Bool) reader = .ok true) :
    checker.IsDefEqU candidateSemantic storedSemantic :=
  acceptedHeaderParameterEquality checker reader aligned initialWF candidateTranslated storedTranslated accepted

example (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {identifier : FVarId} {declaration : LocalDecl} {name : Name} {domain body stored normalized : Expr}
    {binder : BinderInfo} {semantic : VExpr}
    (lookup : reader.lctx.find? identifier = some declaration)
    (translated : checker.TrExprS (.forallE name domain body binder) semantic)
    (storedCall : getType (.fvar identifier) reader = .ok stored)
    (equalCall : (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true)
    (normalizedCall : (monadLift (TypeChecker.whnf (body.instantiate1 (.fvar identifier))) : M Expr)
      reader = .ok normalized) :
    ∃ result, checker.TrExprS normalized result :=
  translatedReusedHeaderParameter checker reader aligned initialWF lookup translated storedCall equalCall normalizedCall

example {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (translated : ∃ semantic, checker.TrExprS type semantic) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      ∃ semantic, finalChecker.TrExprS terminal semantic :=
  trace.checkerModels checker aligned initialWF reserved different constants definitions parameterCount parameters translated

example {root checker : TypeChecker.VContext} {identifiers : List FVarId} {source : InductiveType}
    (history : ParameterPrefix root.mlctx checker.mlctx identifiers)
    (sameEnv : checker.venv = root.venv) (sameUniverses : checker.lparams = root.lparams)
    (empty : root.mlctx = .nil) {semantic : VExpr}
    (translated : checker.TrExprS source.type semantic) (typed : checker.IsType semantic)
    (supported : source.type.FVarsIn (fun _ => False)) :
    ∃ header, TrInductiveHeader root.venv root.lparams source header ∧ header.toVConstant.WF root.venv :=
  history.closedHeaderWF sameEnv sameUniverses empty translated typed supported

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M α)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size,
        ∃ header, TrInductiveHeader checker.venv reader.lparams types[parent] header ∧
          header.toVConstant.WF checker.venv :=
  checkInductiveTypes.headersWF nparams types next checker reader aligned empty different constants definitions

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (safety : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types
      (fun stats => declareInductiveTypes stats nparams types numNested isUnsafe) reader).WF fun result =>
      ∃ headers final, List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types.toList headers ∧
        (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
        checker.venv.addInductHeaders headers = some final ∧ CheckerEnv checker.safety result final :=
  checkInductiveTypes.headersChecker nparams types numNested isUnsafe checker reader aligned empty
    different constants definitions safety

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) :
    (AddInductive.run nparams types numNested reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.length,
        ∃ header, TrInductiveHeader checker.venv reader.lparams types.toArray[parent] header ∧
          header.toVConstant.WF checker.venv :=
  AddInductive.run.headersWF nparams types numNested checker reader aligned empty different constants definitions

private def missingParameter : InductiveStats := {
  (default : InductiveStats) with params := #[.fvar ⟨`MissingHeaderParameter⟩] }

example : ¬HeaderParameterModels missingParameter [] := by
  intro models
  obtain ⟨identifier, _, present⟩ := models (.fvar ⟨`MissingHeaderParameter⟩) (by simp [missingParameter])
  simpa [VLCtx.fvars] using present

private def sortType : Expr := .sort (.succ .zero)

private def sortAlias : DefinitionVal := {
  name := `MutualHeaderSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
  value := sortType, hints := .abbrev, safety := .safe }

private def betaSort : Expr :=
  .app (.lam `A (.sort (.succ (.succ .zero))) (.bvar 0) .default) sortType

private def family (name : Name) (parameters indices : Nat) (domain : Expr := sortType)
    (binder : BinderInfo := .default) : InductiveType :=
  let tail := (List.range indices).foldr (fun _ result =>
    .forallE `sameName (.const ``Nat []) result binder) sortType
  let type := (List.range parameters).foldr (fun _ result =>
    .forallE `sameName domain result binder) tail
  { name, type, ctors := [] }

private def context (env : Kernel.Environment) (isUnsafe : Bool) : Context := {
  env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment)
    (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] nparams types.toList false) none).isOk do
    throwError "mutual typed-header fixture fails native kernel validation"
  for isUnsafe in [false, true] do
    let .ok headers := checkInductiveTypes nparams types
        (fun stats => declareInductiveTypes stats nparams types 0 isUnsafe) (context env isUnsafe)
      | throwError "mutual typed-header registration failed"
    let .ok final := AddInductive.run nparams types.toList 0 (context env isUnsafe)
      | throwError "mutual typed-header full runner failed"
    for result in [headers, final] do
      for type in types do
        let some (.inductInfo info) := result.find? type.name
          | throwError "mutual typed-header registration lost a source header"
        unless info.type == type.type && info.numParams == nparams && info.isUnsafe == isUnsafe do
          throwError "mutual typed-header registration changed source type/count/safety"
      let some (.defnInfo retained) := result.find? sortAlias.name
        | throwError "mutual typed-header registration lost its checked source definition"
      unless retained == sortAlias do throwError "mutual typed-header registration changed its seed definition"
    for type in types do
      let some (.recInfo _) := final.find? (mkRecName type.name)
        | throwError "mutual typed-header runner did not reach recursor registration"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveMutualHeaderTyping
    | throwError "mutual typed-header module absent"
  let mut allowed := []
  for name in [``TypeChecker.checkType.WF, ``TypeChecker.whnf.WF, ``TypeChecker.ensureSort.WF,
      ``TypeChecker.isDefEq.WF, ``checkNoMVarNoFVar.WF, ``translatedHeaderContext,
      ``TrExprS.strengthenIsType, ``checkInductiveTypes.refinesHeadersChecker] do
    allowed := allowed ++ (← collectAxioms name).toList
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "mutual typed-header module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "mutual typed-header unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"mutual typed-header: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let .ok seededHost := host.addDeclCore 0 (.defnDecl sortAlias) none
    | throwError "native kernel rejected mutual header seed definition"
  let .ok env := Lean4Lean.addDecl host.toKernelEnv (.defnDecl sortAlias) true
    | throwError "cannot seed the mutual header definition"
  for parameters in [0, 1, 2] do
    checkBatch seededHost env parameters #[family `TypedMutualFirst parameters 0,
      family `TypedMutualSecond parameters 1 (.const sortAlias.name []) .implicit,
      family `TypedMutualThird parameters 2 betaSort .instImplicit]
  let annotated := .app (.const ``outParam [.max .zero (.succ (.succ .zero))]) sortType
  checkBatch seededHost env 1 #[family `TypedAnnotatedFirst 1 2 annotated,
    family `TypedAnnotatedSecond 1 1 betaSort .implicit]
  let dependent (name : Name) (domain : Expr) : InductiveType := {
    name, type := .forallE `A domain (.forallE `value (.bvar 0)
      (.forallE `index (.const ``Nat []) sortType .implicit) .default) .implicit, ctors := [] }
  checkBatch seededHost env 2 #[dependent `TypedDependentFirst sortType,
    dependent `TypedDependentSecond (.const sortAlias.name []), dependent `TypedDependentThird betaSort]
  checkBatch seededHost env 0 #[family `TypedIndexFirst 0 3, family `TypedIndexSecond 0 0,
    family `TypedIndexThird 0 2]
  checkBatch seededHost env 1 #[family `TypedNoIndicesFirst 1 0,
    family `TypedNoIndicesSecond 1 0 betaSort]
  for isUnsafe in [false, true] do
    let reader := context env isUnsafe
    unless (checkInductiveTypes 0 #[] pure reader).isOk do throwError "empty header batch failed"
    for types in [#[family `BadDomainFirst 1 0,
        family `BadDomainSecond 1 0 (.sort .zero)],
        #[family `BadTermFirst 0 2, { name := `BadTermSecond, type := .const ``Nat.zero [], ctors := [] }],
        #[family `BadVariableFirst 1 1,
          { name := `BadVariableSecond, type := .fvar ⟨Name.num `_ind_fresh 0⟩, ctors := [] }]] do
      if (checkInductiveTypes (if types[0]!.name == `BadTermFirst then 0 else 1) types pure reader).isOk then
        throwError "mutual header checker accepted a later invalid source/domain"
    if (checkInductiveTypes 1 #[family `NoFuelFirst 1 1, family `NoFuelSecond 1 1] pure
        { reader with fuel := { inductiveFuel := 0 } }).isOk then
      throwError "mutual header checker accepted zero fuel"
    if (TypeChecker.Inner.inferFVar
        { env, lctx := {}, safety := reader.safety } ⟨`MissingHeaderParameter⟩).isOk then
      throwError "native typed lookup accepted the missing unchecked parameter"
  logInfo "7 native-accepted mutual fixtures preserve every source header through registration/full runs under both safety flags; dependent reuse, accumulated indices, annotations, empty batches and later-source/domain/fuel/missing-lookup controls passed"

end InductiveMutualHeaderTypingTest
