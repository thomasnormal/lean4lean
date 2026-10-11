import Lean4Lean.Verify.InductiveHeaderApplicationBatch

namespace InductiveHeaderApplicationBatchTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterApplications)

example (input : HeaderParameterApplicationInput environment universes model stats source)
    (parameters : targetStats.params = stats.params) :
    HeaderParameterApplicationInput environment universes model targetStats source :=
  input.withStats parameters

example (before : CheckedHeaderContinuation root original nparams types stats reader)
    (parent : Nat) (bound : parent < types.size) :
    Nonempty (HeaderParameterApplicationInput root.venv root.lparams before.model.checker.mlctx
      stats types[parent].type) := before.parameterApplications parent bound

example (before : CheckedHeaderContinuation root original nparams types stats reader)
    (parent : Nat) (bound : parent < types.size) : stats.levels = root.lparams.map Level.param :=
  before.levels (by omega)

example (before : CheckedHeaderContinuation root original nparams types stats reader)
    (parent : Nat) (bound : parent < types.size) :
    ∃ semantic values result,
      TrExprS root.venv root.lparams before.model.checker.vlctx types[parent].type semantic ∧
      TypedParameterApplications root.venv root.lparams before.model.checker.mlctx
        semantic stats.params.toList values result := by
  obtain ⟨input⟩ := before.parameterApplications parent bound
  exact ⟨input.semantic, input.values, input.result, input.sourceTranslated, input.arguments⟩

example (nparams : Nat) (types : Array InductiveType) (root : TypeChecker.VContext)
    (reader : Context) (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) :
    (checkInductiveTypes nparams types (fun stats => return (stats, ← read)) reader).WF fun result =>
      Nonempty (CheckedHeaderContinuation root reader nparams types result.1 result.2) :=
  checkInductiveTypes.typedContinuation nparams types root reader aligned empty different constants definitions

section Registration
variable {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
  {receipts : ConstructorSemanticReceipts stage isUnsafe}
  (registration : ConstructorConstantRegistration receipts final)

example (parent : Nat) (bound : parent < types.size) :
    Nonempty (HeaderParameterApplicationInput registration.semantic root.lparams
      stage.before.model.checker.mlctx stats types[parent].type) :=
  registration.parentParameterInput parent bound

example : stage.before.model.checker.mlctx.WF registration.semantic root.lparams :=
  registration.parentParameterModelWF

example : HeaderParameterApplicationBatch registration.semantic root.lparams
    stage.before.model.checker.mlctx stats types := registration.parentParameterApplications

example (parent : Nat) (bound : parent < types.size) :
    ∃ input : HeaderParameterApplicationInput registration.semantic root.lparams
        stage.before.model.checker.mlctx stats types[parent].type,
      ∃ value, TrExprS registration.semantic root.lparams stage.before.model.checker.vlctx
        (mkAppN stats.indConsts[parent]! stats.params) value ∧
      registration.semantic.HasType root.lparams.length stage.before.model.checker.vlctx.toCtx
        value input.result := registration.parentParameterApplications parent bound

end Registration

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          ∃ registration : ConstructorConstantRegistration receipts final,
            HeaderParameterApplicationBatch registration.semantic root.lparams
              stage.before.model.checker.mlctx stats types :=
  checkInductiveTypes.headerParameterApplicationContinuation nparams types numNested isUnsafe next
    root reader aligned empty different constants definitions ordinary safetyBound constructors recursors

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          ∃ registration : ConstructorConstantRegistration receipts final,
            HeaderParameterApplicationBatch registration.semantic root.lparams
              stage.before.model.checker.mlctx stats types.toArray :=
  run.headerParameterApplicationContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []
private def betaSort : Expr :=
  .app (.lam `carrier (.sort (.succ (.succ .zero))) (.bvar 0) .default) sortType

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `delay sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `delay sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters indices : Nat)
    (domain : Expr := sortType) (mode : Nat := 0) : InductiveType :=
  let closeIndices := fun body => (List.range indices).foldr
    (fun _ body => .forallE `index natural body .default) body
  let closeParameters := fun header body => (List.range parameters).foldr
    (fun index body => .forallE `carrier (if header then domain else sortType)
      (if header && index + 1 == parameters then delay body mode else body) .implicit) body
  let arguments := (List.range (parameters + indices)).toArray.map
    fun index => Expr.bvar (parameters + indices - index - 1)
  { name, type := closeParameters true (closeIndices sortType),
    ctors := [⟨name ++ `mk, closeParameters false (closeIndices (mkAppN (.const name []) arguments))⟩] }

private def consumeParameters (parameters : Array Expr) (source : Expr) (reader : Context)
    (index : Nat := 0) : Except Kernel.Exception (Expr × Nat) :=
  if index < parameters.size then
    match source with
    | .forallE _ _ body _ => do
      let opened := body.instantiate1 parameters[index]!
      let normalized ← (monadLift (TypeChecker.whnf opened) : M Expr) reader
      let (residual, changes) ← consumeParameters parameters normalized reader (index + 1)
      return (residual, changes + if opened == normalized then 0 else 1)
    | _ => .error .deepRecursion
  else .ok (source, 0)
termination_by parameters.size - index

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected complete header-application batch"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, _, registered) := checkInductiveTypes parameters types (fun stats => do
          let current ← read
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          withEnv actual do
            checkConstructors types stats isUnsafe
            let registered ← declareConstructors stats types isUnsafe
            return (stats, current, actual, registered)) reader
        | throwError "complete header/constructor continuation failed"
      let .ok final := run parameters types.toList 0 reader | throwError "complete inductive run failed"
      unless stats.levels == universes.map Level.param do throwError "batch lost original universe mapping"
      let expectedIndices := stats.nindices.foldl (· + ·) 0
      unless current.lctx.decls.size == parameters + expectedIndices do
        throwError "batch lost accumulated mixed header contexts"
      for environment in [registered, final] do
        let original := { current with env := environment }
        let localReader := recursorIndexContext original `extra .default natural
        let saved : Context := {
          localReader with
          ngen := localReader.ngen.next
          lctx := localReader.lctx.mkLetDecl ⟨localReader.ngen.curr⟩ `saved natural (.lit (.natVal 0)) }
        for reached in [original, localReader, saved] do
          for parent in [:types.size] do
            unless stats.indConsts[parent]! == .const types[parent]!.name stats.levels do
              throwError "batch lost its actual registered parent head"
            let .ok normalized := (monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) reached
              | throwError "batch original signature normalization failed"
            let .ok (residual, changed) := consumeParameters stats.params normalized reached
              | throwError "batch original signature lost a parameter"
            unless declareConstructors.arity 0 residual == stats.nindices[parent]! do
              throwError "batch index count differs from independently normalized signature"
            let .ok inferred := (monadLift (TypeChecker.checkType
                (mkAppN stats.indConsts[parent]! stats.params)) : M Expr) reached
              | throwError "registered batch parameter application failed"
            let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
              | throwError "registered batch residual differs from exact inferred type"
            let .ok kind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
              | throwError "registered batch residual strict checking failed"
            unless ((monadLift (TypeChecker.ensureSort kind) : M Expr) reached).isOk do
              throwError "registered batch residual lacks sort-valued typehood"
            outcomes := outcomes + 1
            changes := changes + changed
            unless parameters == 0 do
              let wrongReader := recursorIndexContext reached `wrong .default natural
              let wrong := stats.params.set! 0 (.fvar ⟨reached.ngen.curr⟩)
              unless wrong.all (·.isFVar) do throwError "batch negative arguments are not all free variables"
              if ((monadLift (TypeChecker.checkType (mkAppN stats.indConsts[parent]! wrong)) : M Expr)
                  wrongReader).isOk then throwError "batch accepted incompatible free-variable parameters"
              rejected := rejected + 1
  return (outcomes, changes, rejected)

private def auditModule (moduleName : Name) (foundations : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "batch audit module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in foundations do allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "batch owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "batch unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      count := count + 1
  logInfo m!"{moduleName}: {count} exhaustive owned declarations audited against genuine earlier foundations"

run_meta
  auditModule `Lean4Lean.Verify.InductiveHeaderContinuation
    [``TypeChecker.checkType.WF, ``checkConstructors.acceptedTraces, ``checkInductiveTypes.headersWF,
      ``declareInductiveTypes.strongHeaderAxiomView, ``TypeChecker.VState.WF.reset,
      ``ElimNestedInductive.ParameterPrefix.insertion, ``AcceptedConstructorTrace.domainReceipts,
      ``CheckedHeaderTrace.parameterApplicationsFromSource, ``TrLCtx.fvars_eq]
  auditModule `Lean4Lean.Verify.InductiveHeaderApplicationBatch
    [``ConstructorConstantRegistration.headerInput, ``ConstructorConstantRegistration.increase,
      ``checkInductiveTypes.constructorConstantContinuation, ``run.constructorConstantContinuation,
      ``TypeChecker.MLCtx.WF.monoEnv, ``RecursorConstantInput.applyHeaderParameters]
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for (types, parameters) in [
      (#[], 0), (#[{ name := `BatchEmpty, type := sortType, ctors := [] }], 0),
      (#[family `BatchZero 0 2], 0), (#[family `BatchOne 1 0], 1),
      (#[family `BatchTwo 2 1 betaSort 1], 2),
      (#[family `BatchMutualFirst 2 0 betaSort 1, family `BatchMutualSecond 2 1 sortType 2,
        family `BatchMutualThird 2 2 (.mdata {} betaSort) 3], 2)] do
    let (passed, changed, failed) ← checkBatch types parameters
    outcomes := outcomes + passed
    changes := changes + changed
    rejected := rejected + failed
  let dependent : InductiveType := {
    name := `BatchDependent,
    type := .forallE `carrier betaSort (.forallE `value (.bvar 0)
      (delay (.forallE `index natural sortType .default) 2) .default) .implicit,
    ctors := [⟨`BatchDependent.mk, .forallE `carrier sortType (.forallE `value (.bvar 0)
      (.forallE `index natural (mkAppN (.const `BatchDependent [])
        #[.bvar 2, .bvar 1, .bvar 0]) .default) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[dependent] 2
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  let universeLevel := Level.param `universe
  let polymorphic : InductiveType := {
    name := `BatchPolymorphic,
    type := .forallE `carrier (.sort universeLevel)
      (delay (.forallE `value (.bvar 0) (.sort universeLevel) .default) 1) .implicit,
    ctors := [⟨`BatchPolymorphic.mk, .forallE `carrier (.sort universeLevel)
      (.forallE `value (.bvar 0) (mkAppN (.const `BatchPolymorphic [universeLevel])
        #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[polymorphic] 1 [`universe]
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  let normalizedUniverse : InductiveType := {
    name := `BatchNormalizedUniverse,
    type := .forallE `carrier (.sort (.max universeLevel .zero))
      (.forallE `value (.bvar 0) (.sort (.max universeLevel .zero)) .default) .implicit,
    ctors := [⟨`BatchNormalizedUniverse.mk, .forallE `carrier (.sort universeLevel)
      (.forallE `value (.bvar 0) (mkAppN (.const `BatchNormalizedUniverse [universeLevel])
        #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  if normalizedUniverse.type.instantiateLevelParams [`universe] [universeLevel] == normalizedUniverse.type then
    throwError "batch universe control fails to exercise nonidentity original-level substitution"
  let (passed, changed, failed) ← checkBatch #[normalizedUniverse] 1 [`universe]
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  unless changes > 0 && rejected > 0 do throwError "batch controls miss conversion/domain rejection"
  let host ← getEnv
  let incompatible := #[family `BatchWrongFirst 1 0,
    { name := `BatchWrongSecond, type := .forallE `carrier natural sortType .implicit, ctors := [] }]
  for isUnsafe in [false, true] do
    if (host.addDeclCore 0 (.inductDecl [] 1 incompatible.toList isUnsafe) none).isOk then
      throwError "native kernel accepted incompatible later-header batch domains"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      if (checkInductiveTypes 1 incompatible (fun _ => pure ()) reader).isOk then
        throwError "incompatible later-header domains acquired complete batch eligibility"
  logInfo m!"{outcomes} complete registered batch parameter applications passed; {changes} nonidentity parameter-opening normalizations; {rejected} incompatible all-free-variable arrays rejected; accumulated mutual index contexts, original universes, exact residual equality and strict typehood checked in constructor-registered/full-run environments and original/local/let contexts, both safeties/primitive modes; runtime controls do not fabricate semantic contexts"

end InductiveHeaderApplicationBatchTest
