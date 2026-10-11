import Lean4Lean.Verify.InductiveConstructorSemanticReceipts

namespace InductiveConstructorSemanticReceiptsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

example (model : TypedHeaderReader base stats reader) (constructor : Constructor) (result : Expr)
    (guarded : reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok ())
    (checked : (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok result) :
    ∃ semantic, TrExprS model.checker.venv model.checker.lparams base.vlctx constructor.type semantic :=
  model.constructorTranslation constructor result guarded checked

example (signatures : List.Forall₂ (fun complete header : VInductiveType =>
    complete.toVConstVal = header.toVConstVal) complete headers) (environment : VEnv) :
    environment.addInductHeaders complete = environment.addInductHeaders headers :=
  VEnv.addInductHeaders.sameConstructorLists signatures environment

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (receipts : ConstructorSemanticReceipts stage isUnsafe) :
    TrInductDecl root.venv stage.semantic root.lparams nparams types.toList receipts.declaration ∧
      root.venv.addInductHeaders receipts.declaration.types = some stage.semantic ∧
      receipts.declaration.HeadersWF root.venv :=
  ⟨receipts.translated, receipts.registered, receipts.headersWF⟩

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual) :
    stage.model.checker.lparams = root.lparams :=
  stage.shadowUniverses

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (receipts : ConstructorSemanticReceipts stage isUnsafe) :
    receipts.declaration.uvars = root.lparams.length ∧ receipts.declaration.nparams = nparams :=
  ⟨receipts.translated.1.symm, receipts.translated.2.1.symm⟩

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (parent : Nat) (bound : parent < types.size) (constructor : Constructor)
    (member : constructor ∈ types[parent].ctors) :
    ∃ finalReader finalIndex terminal finalTarget,
      ∃ trace : AcceptedConstructorTrace stats isUnsafe parent { reader with env := stage.shadow }
        0 constructor.type finalReader finalIndex terminal,
      CheckedConstructorDomainReceipts stage.semantic root.lparams trace
        root.mlctx.vlctx.toCtx root.mlctx.vlctx.toCtx stage.model.parameterModel.vlctx.toCtx finalTarget ∧
      stage.semantic.IsDefEqCtx root.lparams.length root.mlctx.vlctx.toCtx
        stage.model.parameterModel.vlctx.toCtx finalTarget ∧
      finalTarget.length = root.mlctx.vlctx.toCtx.length + stats.params.size :=
  receipts.domains parent bound constructor member

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (isUnsafe : Bool)
    (accepted : checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok ()) :
    Nonempty (ConstructorSemanticReceipts stage isUnsafe) :=
  stage.shadowConstructorSemantics empty isUnsafe accepted

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (isUnsafe : Bool) (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env)
    (accepted : checkConstructors types stats isUnsafe { reader with env := actual } = .ok ()) :
    Nonempty (ConstructorSemanticReceipts stage isUnsafe) :=
  stage.constructorSemantics empty isUnsafe fresh constructors recursors () accepted

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
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
        withEnv final (pure ())) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        NativeValueFrame actual final ∧ Nonempty (ConstructorSemanticReceipts stage isUnsafe) :=
  checkInductiveTypes.semanticConstructorAxiomContinuation nparams types numNested isUnsafe
    (fun _ _ => pure ()) root reader aligned empty different constants definitions ordinary safetyBound
    constructors recursors

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
        NativeValueFrame actual final ∧ Nonempty (ConstructorSemanticReceipts stage (reader.safety != .safe)) :=
  run.semanticConstructorAxiomContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def family (name : Name) (parameters : Nat := 0) : InductiveType :=
  let close := fun body => (List.range parameters).foldr
    (fun _ body => .forallE `parameter sortType body .implicit) body
  let parent := fun fields => mkAppN (.const name [])
    ((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1))
  { name, type := close sortType
    ctors := [⟨name ++ `base, close (parent 0)⟩,
      ⟨name ++ `step, close (.forallE `child (parent 0) (parent 1) .default)⟩,
      ⟨name ++ `higher, close (.forallE `children (.forallE `index natural (parent 1) .default)
        (parent 1) .default)⟩] }

private def polymorphicFamily : InductiveType :=
  let close := fun body => Expr.forallE `parameter (.sort (.param `universe)) body .implicit
  let parent := fun index => mkApp (.const `SemanticPoly [.param `universe]) (.bvar index)
  { name := `SemanticPoly, type := close (.sort (.param `universe))
    ctors := [⟨`SemanticPoly.base, close (parent 0)⟩,
      ⟨`SemanticPoly.step, close (.forallE `child (parent 0) (parent 1) .default)⟩] }

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM Nat := do
  let host ← getEnv
  let environment := host.toKernelEnv
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected semantic receipt controls"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 3 isUnsafe
          return (stats, ← read, actual)) reader | throwError "semantic receipt header staging failed"
      unless stats.params.size == parameters do throwError "parameter prefix length differs"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      let shadowReader := { current with env := shadow }
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
        throwError "actual constructor acceptance absent"
      unless (checkConstructors types stats isUnsafe shadowReader).isOk do
        throwError "shadow constructor acceptance absent"
      for type in types do
        for constructor in type.ctors do
          unless (shadow.checkNoMVarNoFVar constructor.name constructor.type).isOk do
            throwError "accepted constructor source guard absent"
          unless ((monadLift (TypeChecker.checkType constructor.type) : M Expr) shadowReader).isOk do
            throwError "accepted lifted constructor source checking absent"
      for expression in [Expr.fvar ⟨`escaped⟩, Expr.mvar ⟨`unsolved⟩] do
        if (shadow.checkNoMVarNoFVar `SemanticInvalid expression).isOk then
          throwError "unsupported source expression accepted"
      if ((monadLift (TypeChecker.checkType (.const `SemanticMissing [])) : M Expr) shadowReader).isOk then
        throwError "missing constructor source accepted"
      unless ((monadLift (TypeChecker.checkType (.const ``Nat.zero [])) : M Expr) shadowReader).isOk do
        throwError "checked source translation was confused with sort-valued typing"
      unless types.isEmpty do
        let invalid := types.map fun type =>
          { type with ctors := [⟨type.name ++ `invalid, .const ``Nat.zero []⟩] }
        if (checkConstructors invalid stats isUnsafe shadowReader).isOk then
          throwError "non-type constructor accepted by complete constructor checker"
      unless (run parameters types.toList 3 reader).isOk do throwError "full actual run rejected"
  return 4

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorSemanticReceipts |
    throwError "semantic receipt module absent"
  let logicalAllowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let strongInputAllowed := logicalAllowed ++ (← collectAxioms ``HeaderAxiomContinuation)
  let translationAllowed := logicalAllowed ++ (← collectAxioms ``acceptedSourceTranslation) ++
    (← collectAxioms ``TrExprS.weakFV'_inv) ++ (← collectAxioms ``checkNoMVarNoFVar.WF)
  let domainAllowed := logicalAllowed ++ (← collectAxioms ``checkConstructors.domainReceiptsAtParameterModel)
  let stageAllowed := translationAllowed ++ domainAllowed ++ (← collectAxioms ``HeaderAxiomContinuation) ++
    (← collectAxioms ``checkConstructors.acceptedTraces)
  let actualAllowed := stageAllowed ++ (← collectAxioms ``HeaderAxiomContinuation.acceptedConstructorsFromInitial)
  let prefixAllowed := stageAllowed ++ (← collectAxioms ``checkInductiveTypes.nativeConstructorAxiomContinuation)
  let runAllowed := stageAllowed ++ (← collectAxioms ``run.nativeConstructorAxiomContinuation)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "semantic receipt module-owned axiom {name}"
      let text := name.toString
      let allowed := if name == ``checkInductiveTypes.semanticConstructorAxiomContinuation then prefixAllowed
        else if name == ``run.semanticConstructorAxiomContinuation then runAllowed
        else if name == ``HeaderAxiomContinuation.constructorSemantics then actualAllowed
        else if name == ``TypedHeaderReader.constructorDomains then domainAllowed
        else if name == ``HeaderAxiomContinuation.shadowUniverses ||
          name == ``ConstructorSemanticReceipts || text.startsWith "Lean4Lean.AddInductive.ConstructorSemanticReceipts." then
          strongInputAllowed
        else if name == ``VEnv.addInductHeaders.sameConstructorLists || text.contains "relatedMember" then logicalAllowed
        else if name == ``TypedHeaderReader.constructorTranslation || text.contains "constructorModels" ||
          text.contains "completeHeaderModels" then translationAllowed
        else stageAllowed
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "semantic receipt unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"semantic receipts: {count} exhaustive production declarations audited against logical, existing source/domain, strong-stage and native-prefix/run baselines"

run_meta
  auditModule
  let mut outcomes ← checkBatch #[]
  outcomes := outcomes + (← checkBatch #[{ name := `SemanticEmpty, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch #[family `SemanticSingle])
  outcomes := outcomes + (← checkBatch #[family `SemanticParameters 2] 2)
  outcomes := outcomes + (← checkBatch #[polymorphicFamily] 1 [`universe])
  outcomes := outcomes + (← checkBatch #[{
    name := `SemanticIndexed, type := .forallE `index natural sortType .default,
    ctors := [⟨`SemanticIndexed.base, mkApp (.const `SemanticIndexed []) (.const ``Nat.zero [])⟩] }])
  let first := family `SemanticFirst
  let second := family `SemanticSecond
  outcomes := outcomes + (← checkBatch #[
    { first with ctors := first.ctors ++ [⟨`SemanticFirst.cross,
      .forallE `other (.const `SemanticSecond []) (.const `SemanticFirst []) .default⟩] },
    { second with ctors := second.ctors ++ [⟨`SemanticSecond.cross,
      .forallE `other (.const `SemanticFirst []) (.const `SemanticSecond []) .default⟩] }])
  logInfo m!"{outcomes} semantic-source controls passed: accepted actual/shadow constructors and lifted source checks, parameter scopes, universe alignment, full runs, unsupported-source rejection and checked-term/non-type-constructor boundary; runtime checks do not fabricate a semantic context"

end InductiveConstructorSemanticReceiptsTest
