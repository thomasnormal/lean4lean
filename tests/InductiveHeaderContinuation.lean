import Lean4Lean.Verify.InductiveHeaderContinuation

namespace InductiveHeaderContinuationTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix)

example {root : TypeChecker.VContext} {reader current : Context} {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual : Kernel.Environment}
    (stage : HeaderAxiomContinuation root reader nparams types stats current actual) :
    actual.constants.WF :=
  stage.actualWF

example {base : MLCtx} {stats : InductiveStats} {reader : Context}
    (model : TypedHeaderReader base stats reader) :
    HeaderParameterModels stats model.checker.vlctx :=
  model.parameterModels

example {base : MLCtx} {stats : InductiveStats} {reader : Context}
    (model : TypedHeaderReader base stats reader) :
    ParameterPrefix base model.checker.mlctx
      (model.parameterIdentifiers ++ model.ambientIdentifiers) :=
  model.history

example {base : MLCtx} {stats : InductiveStats} {reader : Context}
    (model : TypedHeaderReader base stats reader) :
    model.checker.mlctx.dropN model.ambientIdentifiers.length model.ambient.bound =
      model.parameterModel :=
  model.parameterBase

example {base : MLCtx} {stats : InductiveStats} {reader : Context}
    (model : TypedHeaderReader base stats reader) :
    model.parameterModel.WF model.checker.venv model.checker.lparams :=
  model.parameterWF

example {base : MLCtx} {stats : InductiveStats} {reader : Context}
    (model : TypedHeaderReader base stats reader) (shadow : Kernel.Environment)
    (semantic : VEnv) (increase : model.checker.venv ≤ semantic)
    (history : TrEnv model.checker.safety shadow semantic)
    (primitives : NativePrimitiveFrame model.checker.env shadow) :
    HeaderCheckerAligned (model.inHeaderAxiomView shadow semantic increase history primitives).checker
      { reader with env := shadow } :=
  (model.inHeaderAxiomView shadow semantic increase history primitives).aligned

example (nparams : Nat) (types : Array InductiveType) (root : TypeChecker.VContext)
    (reader : Context) (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) :
    (checkInductiveTypes nparams types (fun stats => return (stats, ← read)) reader).WF fun result =>
      Nonempty (CheckedHeaderContinuation root reader nparams types result.1 result.2) :=
  checkInductiveTypes.typedContinuation nparams types root reader aligned empty different constants definitions

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        pure () ) reader).WF fun _ => ∃ stats current actual,
      ∃ _stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        checkConstructors types stats isUnsafe { current with env := actual } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { current with env := actual } :=
  checkInductiveTypes.constructorAxiomContinuation nparams types numNested isUnsafe (fun _ _ => pure ())
    root reader aligned empty different constants definitions ordinary safetyBound

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual,
      ∃ _stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () ∧
        stats.AcceptedConstructorTraces types.toArray (reader.safety != .safe)
          { current with env := actual } :=
  run.constructorAxiomContinuation nparams types numNested root reader aligned empty different constants
    definitions ordinary ordinarySafety

example {root : TypeChecker.VContext} {original reader : Context} {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual : Kernel.Environment}
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual) (isUnsafe : Bool) :
    (checkConstructors types stats isUnsafe { reader with env := stage.shadow }).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ finalReader finalIndex terminal finalTarget,
          ∃ trace : AcceptedConstructorTrace stats isUnsafe parent { reader with env := stage.shadow }
            0 constructor.type finalReader finalIndex terminal,
          CheckedConstructorDomainReceipts stage.model.checker.venv stage.model.checker.lparams trace
            root.mlctx.vlctx.toCtx root.mlctx.vlctx.toCtx stage.model.parameterModel.vlctx.toCtx finalTarget ∧
          stage.model.checker.venv.IsDefEqCtx stage.model.checker.lparams.length root.mlctx.vlctx.toCtx
            stage.model.parameterModel.vlctx.toCtx finalTarget ∧
          finalTarget.length = root.mlctx.vlctx.toCtx.length + stats.params.size :=
  checkConstructors.domainReceiptsAtParameterModel types stats isUnsafe stage.model.checker
    { reader with env := stage.shadow } stage.model.aligned stage.model.initialWF
    stage.model.history stage.model.ambient stage.model.parameterBase stage.model.statsParams

private def sortType : Expr := .sort (.succ .zero)

private def family (name : Name) (parameters fields : Nat) (indices : Nat := 0)
    (domain : Expr := sortType) : InductiveType :=
  let result := mkAppN (.const name [])
    (((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1)) ++
      (List.replicate indices (.const ``Nat.zero [])).toArray)
  let ctorType := (List.range fields).foldr (fun _ body =>
    .forallE `value (.const ``Nat []) body .default) result
  let close := fun body => (List.range parameters).foldr (fun _ body =>
    .forallE `parameter domain body .implicit) body
  let indexedType := (List.range indices).foldr (fun _ body =>
    .forallE `index (.const ``Nat []) body .default) sortType
  { name, type := close indexedType, ctors := [{ name := name ++ `mk, type := close ctorType }] }

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment)
    (parameters : Nat) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] parameters types.toList false) none).isOk do
    throwError "native constructor continuation fixture rejected"
  let some (.defnInfo originalAlias) := env.find? `ContinuationSortAlias
    | throwError "constructor continuation fixture lacks its seed definition"
  for unsafeMode in [false, true] do
    let reader : Context := {
      env := env
      lparams := []
      safety := if unsafeMode then .unsafe else .safe
      allowPrimitive := false }
    let .ok result := run parameters types.toList 0 reader
      | throwError "native constructor continuation runner failed"
    let some (.defnInfo retainedAlias) := result.find? originalAlias.name
      | throwError "constructor continuation fixture lost its seed definition"
    unless retainedAlias == originalAlias do throwError "constructor continuation changed its old definition"
    for type in types do
      let some (.inductInfo info) := result.find? type.name
        | throwError "constructor continuation fixture lost an inductive"
      unless info.type == type.type && info.numParams == parameters && info.isUnsafe == unsafeMode do
        throwError "constructor continuation fixture changed source metadata"
      let some (.ctorInfo ctor) := result.find? (type.name ++ `mk)
        | throwError "constructor continuation fixture lost a constructor"
      unless ctor.numParams == parameters && ctor.numFields == 1 do
        throwError "constructor continuation fixture changed constructor arity"
    let .ok (stats, current) := checkInductiveTypes parameters types
        (fun stats => return (stats, ← read)) reader
      | throwError "constructor continuation context checkpoint failed"
    let indices := types.toList.foldl (fun total type =>
      total + (declareConstructors.arity 0 type.type - parameters)) 0
    unless current.lctx.decls.size == parameters + indices && stats.params.size == parameters do
      throwError "constructor continuation lost the exact parameter/accumulated-index context"
    for parameter in stats.params do
      unless parameter.isFVar && (current.lctx.find? parameter.fvarId!).isSome do
        throwError "constructor continuation lost shared parameter lookup support"
    let .ok actual := declareInductiveTypes stats parameters types 0 unsafeMode current
      | throwError "constructor continuation header staging failed"
    unless (checkConstructors types stats unsafeMode { current with env := actual }).isOk do
      throwError "constructor continuation lost accepted constructor checking at its exact reader"
    for type in types do
      unless (result.find? (mkRecName type.name)).isSome do
        throwError "constructor continuation fixture did not register a recursor"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderContinuation
    | throwError "constructor continuation module absent"
  let mut allowed := []
  for name in [``TypeChecker.checkType.WF, ``checkConstructors.acceptedTraces,
      ``checkInductiveTypes.headersWF, ``AddInductive.declareInductiveTypes.strongHeaderAxiomView,
      ``TypeChecker.VState.WF.reset, ``ParameterPrefix.insertion,
      ``AcceptedConstructorTrace.domainReceipts] do
    allowed := allowed ++ (← collectAxioms name).toList
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "constructor continuation module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "constructor continuation unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"constructor continuation: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let .ok seededHost := host.addDeclCore 0 (.defnDecl {
      name := `ContinuationSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
      value := sortType, hints := .abbrev, safety := .safe }) none
    | throwError "native continuation seed failed"
  let .ok env := Lean4Lean.addDecl host.toKernelEnv (.defnDecl {
      name := `ContinuationSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
      value := sortType, hints := .abbrev, safety := .safe }) true
    | throwError "continuation seed environment failed"
  for parameters in [0, 1, 2] do
    checkBatch seededHost env parameters #[family `ContinuationFirst parameters 1,
      family `ContinuationSecond parameters 1 0 (.const `ContinuationSortAlias [])]
  checkBatch seededHost env 0 #[family `ContinuationIndexed 0 1 2]
  checkBatch seededHost env 1 #[family `ContinuationIndexedFirst 1 1 3,
    family `ContinuationIndexedSecond 1 1 0, family `ContinuationIndexedThird 1 1 2]
  let dependent (name : Name) (domain : Expr) : InductiveType := {
    name
    type := .forallE `A domain (.forallE `value (.bvar 0)
      (.forallE `index (.const ``Nat []) sortType .default) .default) .implicit
    ctors := [{
      name := name ++ `mk
      type := .forallE `A domain (.forallE `value (.bvar 0)
        (.forallE `field (.const ``Nat [])
          (mkAppN (.const name []) #[.bvar 2, .bvar 1, .const ``Nat.zero []]) .default) .default) .implicit }] }
  checkBatch seededHost env 2 #[dependent `ContinuationDependentFirst sortType,
    dependent `ContinuationDependentSecond (.const `ContinuationSortAlias [])]
  for unsafeMode in [false, true] do
    let reader : Context := {
      env := env
      lparams := []
      safety := if unsafeMode then .unsafe else .safe
      allowPrimitive := false }
    if (run 0 [family `ContinuationFuel 0 1] 0 { reader with fuel := { inductiveFuel := 0 } }).isOk then
      throwError "constructor continuation fixture accepted zero fuel"
    let .ok (emptyStats, emptyReader) := checkInductiveTypes 0 #[] (fun stats => return (stats, ← read)) reader
      | throwError "empty typed continuation checkpoint failed"
    unless emptyStats.params.isEmpty && emptyReader.lctx.decls.size == 0 do
      throwError "empty typed continuation invented a parameter/local"
    let invalid : InductiveType := {
      name := `ContinuationBadReturn
      type := sortType
      ctors := [⟨`ContinuationBadReturn.mk, .const ``Nat []⟩] }
    if (run 0 [invalid] 0 reader).isOk then throwError "constructor continuation accepted an invalid return"
    let captured : InductiveType := {
      name := `ContinuationCaptured
      type := .fvar ⟨`UnboundContinuationSource⟩
      ctors := [] }
    if (run 0 [captured] 0 reader).isOk then throwError "constructor continuation accepted a captured header"
    if (run 1 [family `ContinuationMismatchFirst 1 1,
        family `ContinuationMismatchSecond 1 1 0 (.sort .zero)] 0 reader).isOk then
      throwError "constructor continuation accepted a later parameter-domain mismatch"
    if (run 0 [family `ContinuationDuplicate 0 1, family `ContinuationDuplicate 0 1] 0 reader).isOk then
      throwError "constructor continuation accepted duplicate headers"
  logInfo "6 native-accepted constructor continuation fixtures preserve exact parameter/accumulated-index contexts, source metadata, old definitions, constructor arity and recursors under both safeties; dependent reuse, empty and 10 failure controls passed"

end InductiveHeaderContinuationTest
