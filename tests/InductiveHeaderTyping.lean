import Lean4Lean.Verify.InductiveHeaderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveHeaderTypingTest

example (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {source result : Expr} {semantic : VExpr}
    (translated : checker.TrExprS source semantic)
    (accepted : (monadLift (TypeChecker.ensureSort source) : M Expr) reader = .ok result) :
    checker.IsType semantic :=
  acceptedHeaderSortIsType checker reader aligned initialWF translated accepted

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M α)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) (nonempty : 0 < types.size) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∃ semantic, checker.TrExprS types[0]!.type semantic ∧ checker.IsType semantic :=
  checkInductiveTypes.firstHeaderIsType nparams types next checker reader aligned initialWF nonempty

example (nparams : Nat) (types : Array InductiveType) (next : InductiveStats → M α)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (empty : checker.mlctx = .nil)
    (nonempty : 0 < types.size) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∃ header, TrInductiveHeader checker.venv reader.lparams types[0]! header ∧
        header.toVConstant.WF checker.venv :=
  checkInductiveTypes.firstHeaderWF nparams types next checker reader aligned empty nonempty

example (nparams : Nat) (type : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (empty : checker.mlctx = .nil)
    (safety : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams #[type]
      (fun stats => declareInductiveTypes stats nparams #[type] numNested isUnsafe) reader).WF
      fun result => ∃ header final,
        TrInductiveHeader checker.venv reader.lparams type header ∧
        header.toVConstant.WF checker.venv ∧
        checker.venv.addInductHeaders [header] = some final ∧
        CheckerEnv checker.safety result final :=
  checkInductiveTypes.singleHeaderChecker nparams type numNested isUnsafe checker reader
    aligned empty safety

example {nparams numNested : Nat} {type : InductiveType} {isUnsafe : Bool}
    {checker : TypeChecker.VContext} {reader : Context} {result : Kernel.Environment}
    (aligned : HeaderCheckerAligned checker reader)
    (empty : checker.mlctx = .nil)
    (safety : checker.safety ≤ if isUnsafe then .unsafe else .safe)
    (accepted : checkInductiveTypes nparams #[type]
      (fun stats => declareInductiveTypes stats nparams #[type] numNested isUnsafe) reader = .ok result) :
    ∃ (header : VInductiveType) (final : VEnv), header.toVConstant.WF checker.venv ∧ final.WF ∧
      final.constants type.name = some header.toVConstant := by
  obtain ⟨header, final, translated, typed, registered, checked⟩ :=
    checkInductiveTypes.singleHeaderChecker nparams type numNested isUnsafe checker reader
      aligned empty safety result accepted
  refine ⟨header, final, typed, checked.wf, ?_⟩
  rw [translated.1]
  exact VEnv.addInductHeaders.constants registered (by simp)

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (nonempty : 0 < types.length) :
    (AddInductive.run nparams types numNested reader).WF fun _ =>
      ∃ header, TrInductiveHeader checker.venv reader.lparams types.toArray[0]! header ∧
        header.toVConstant.WF checker.venv :=
  AddInductive.run.firstHeaderWF nparams types numNested checker reader aligned empty nonempty

private def sortType : Expr := .sort (.succ .zero)

private def sortAlias : DefinitionVal := {
  name := `CheckedHeaderSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
  value := sortType, hints := .abbrev, safety := .safe }

private def piAlias : DefinitionVal := {
  sortAlias with
  name := `CheckedHeaderPiAlias
  value := .forallE `A sortType sortType .implicit }

private def betaSort : Expr :=
  .app (.lam `A (.sort (.succ (.succ .zero))) (.bvar 0) .default) sortType

private def datatype (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def context (env : Kernel.Environment) (isUnsafe : Bool) : Context := {
  env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }

private def checkHeader (host : Lean.Environment) (env : Kernel.Environment)
    (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] nparams types.toList false) none).isOk do
    throwError "typed-header fixture fails native kernel validation"
  for isUnsafe in [false, true] do
    let .ok headers := checkInductiveTypes nparams types
        (fun stats => declareInductiveTypes stats nparams types 0 isUnsafe) (context env isUnsafe)
      | throwError "typed-header registration failed"
    let .ok final := AddInductive.run nparams types.toList 0 (context env isUnsafe)
      | throwError "typed-header full runner failed"
    for result in [headers, final] do
      for type in types do
        let some (.inductInfo info) := result.find? type.name
          | throwError "typed-header registration lost its record"
        unless info.type == type.type && info.numParams == nparams && info.isUnsafe == isUnsafe do
          throwError "typed-header registration changed the original source type or flags"
      for definition in [sortAlias, piAlias] do
        let some (.defnInfo info) := result.find? definition.name
          | throwError "typed-header registration lost a source normalization definition"
        unless info == definition do throwError "typed-header registration changed a source definition"
    for type in types do
      let some (.recInfo _) := final.find? (mkRecName type.name)
        | throwError "typed-header full runner did not reach recursor registration"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderTyping
    | throwError "typed-header proof module absent"
  let mut allowed := []
  for name in [``TypeChecker.checkType.WF, ``TypeChecker.whnf.WF, ``TypeChecker.ensureSort.WF,
      ``checkNoMVarNoFVar.WF, ``VEnv.IsType.defeqU_l,
      ``checkInductiveTypes.refinesHeadersChecker] do
    allowed := allowed ++ (← collectAxioms name).toList
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "typed-header module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "typed-header unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"typed-header: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let mut host ← getEnv
  let mut env := host.toKernelEnv
  for definition in [sortAlias, piAlias] do
    let .ok nextHost := host.addDeclCore 0 (.defnDecl definition) none
      | throwError "native kernel rejected a header normalization definition"
    let .ok nextEnv := Lean4Lean.addDecl env (.defnDecl definition) true
      | throwError "cannot seed the checked header normalization definition"
    host := nextHost
    env := nextEnv
  for source in [sortType, .const sortAlias.name [], betaSort, .mdata {} betaSort] do
    checkHeader host env 0 #[datatype `TypedHeader source]
  checkHeader host env 0 #[datatype `TypedPiAlias (.const piAlias.name [])]
  for domain in [sortType, betaSort, .const sortAlias.name []] do
    checkHeader host env 1 #[datatype `TypedParameter (.forallE `A domain sortType .implicit)]
  checkHeader host env 0 #[datatype `TypedIndex (.forallE `index (.const ``Nat []) sortType .default)]
  let dependent : Expr := .forallE `A sortType (.forallE `element (.bvar 0) sortType .default) .implicit
  checkHeader host env 1 #[datatype `TypedDependent dependent]
  checkHeader host env 1 #[datatype `TypedMutualLeft dependent, datatype `TypedMutualRight dependent]
  for isUnsafe in [false, true] do
    for source in [.const ``Nat.zero [], .const ``False []] do
      unless (Lean4Lean.TypeChecker.M.run env (if isUnsafe then .unsafe else .safe) {} [] {}
          (Lean4Lean.TypeChecker.checkType source)).isOk do
        throwError "ill-shaped header control did not pass standalone expression checking"
      if (checkInductiveTypes 0 #[datatype `TypedInvalid source] pure (context env isUnsafe)).isOk then
        throwError "header checking accepted a term or non-sort terminal as an inductive header"
    if (checkInductiveTypes 1 #[datatype `TypedWrongParameters sortType] pure (context env isUnsafe)).isOk then
      throwError "typed-header checker accepted a mismatched parameter count"
    if (checkInductiveTypes 0 #[datatype `TypedNoFuel sortType] pure
        { context env isUnsafe with fuel := { inductiveFuel := 0 } }).isOk then
      throwError "typed-header checker accepted zero binder fuel"
    if (checkInductiveTypes 0 #[datatype `TypedFreeVariable (.fvar ⟨Name.num `_ind_fresh 0⟩)] pure
        (context env isUnsafe)).isOk then
      throwError "typed-header checker bypassed its source-variable guard"
  logInfo "11 native-accepted singleton/mutual fixtures preserve original source types through header registration and full runs under both safety flags; term/non-sort, parameter-count, fuel and source-variable controls passed"

end InductiveHeaderTypingTest
