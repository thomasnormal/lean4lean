import Lean4Lean.Verify.InductiveHeaderNativeMetadata

namespace InductiveHeaderNativeMetadataTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

example (trace : FreshRegistrationTrace allowed original result) :
    result.quotInit = original.quotInit := trace.quotInit

example (trace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (wellFormed : original.constants.WF) (name : Name) (information : ConstructorVal)
    (found : actual.find? name = some (.ctorInfo information)) :
    original.find? name = some (.ctorInfo information) :=
  trace.headerConstructorOrigins wellFormed name information found

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual) :
    FreshRegistrationTrace HeaderRegistrationRecord reader.env actual ∧
      FreshRegistrationTrace HeaderAxiomRegistrationRecord reader.env stage.shadow :=
  ⟨stage.actualRegistration, stage.shadowRegistration⟩

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env) :
    NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual stage.shadow :=
  stage.nativeFrame fresh constructors recursors

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (fresh : ConstructorsFresh actual types) (isUnsafe : Bool)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env)
    (accepted : checkConstructors types stats isUnsafe { reader with env := actual } = .ok ()) :
    checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok () ∧
      stats.AcceptedConstructorTraces types isUnsafe { reader with env := stage.shadow } :=
  stage.acceptedConstructorsFromInitial isUnsafe fresh constructors recursors () accepted

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) (result : Kernel.Environment)
    (accepted : run nparams types numNested reader = .ok result) :
    ∃ stats current actual,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types.toArray, type.name = name) actual stage.shadow ∧
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := stage.shadow } = .ok () := by
  obtain ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    metadata, actualAccepted, shadowAccepted, traces⟩ :=
    run.nativeConstructorAxiomContinuation nparams types numNested root reader aligned empty different
      constants definitions ordinary ordinarySafety constructors recursors result accepted
  exact ⟨stats, current, actual, stage, metadata, shadowAccepted⟩

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []
private def zero : Expr := .const ``Nat.zero []

private def headerFields (header : InductiveVal) :=
  (header.name, header.levelParams, header.type, header.numParams, header.numIndices,
    header.all, header.ctors, header.numNested, header.isRec, header.isUnsafe, header.isReflexive)

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

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default
    ctors := [⟨name ++ `base, mkApp (.const name []) zero⟩,
      ⟨name ++ `step, .forallE `index natural (.forallE `child (mkApp (.const name []) (.bvar 0))
        (mkApp (.const name []) (.bvar 1)) .default) .default⟩] }

private def checkInitial (environment : Kernel.Environment) : MetaM Unit := do
  for (name, information) in environment.constants.toList do
    if let .ctorInfo information := information then
      let some (.inductInfo parent) := environment.find? information.induct |
        throwError "initial native constructor parent missing"
      unless parent.ctors.contains name do throwError "initial native constructor parent membership missing"
    if let .recInfo information := information then
      let some (.inductInfo _) := environment.find? information.getMajorInduct |
        throwError "initial native recursor parent missing"

private def checkStage (original actual shadow : Kernel.Environment) : MetaM Unit := do
  unless actual.quotInit == original.quotInit && shadow.quotInit == original.quotInit do
    throwError "header trace changed quotient initialization"
  for (name, information) in actual.constants.toList do
    if let .ctorInfo information := information then
      let some (.ctorInfo initial) := original.find? name |
        throwError "header registration introduced a constructor"
      unless initial == information do throwError "header registration changed an old constructor record"
      let some (.inductInfo initialParent) := original.find? information.induct |
        throwError "original constructor parent absent"
      let some (.inductInfo actualParent) := actual.find? information.induct |
        throwError "actual constructor parent lost"
      let some (.inductInfo shadowParent) := shadow.find? information.induct |
        throwError "shadow constructor parent lost"
      unless headerFields initialParent == headerFields actualParent &&
          headerFields initialParent == headerFields shadowParent && initialParent.ctors.contains name do
        throwError "native constructor-parent closure/retention changed"
    if let .recInfo information := information then
      let some (.recInfo initial) := original.find? name |
        throwError "header registration introduced a recursor"
      unless initial == information do throwError "header registration changed an old recursor record"
      let some (.inductInfo initialParent) := original.find? information.getMajorInduct |
        throwError "original recursor parent absent"
      let some (.inductInfo shadowParent) := shadow.find? information.getMajorInduct |
        throwError "shadow recursor parent lost"
      unless headerFields initialParent == headerFields shadowParent do
        throwError "old recursor shadow-parent metadata changed"

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (types : Array InductiveType) (parameters : Nat := 0) : MetaM Nat := do
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl [] parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected the metadata fixture"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment
        lparams := []
        safety := if isUnsafe then .unsafe else .safe
        allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 7 isUnsafe
          return (stats, ← read, actual)) reader | throwError "native header staging failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      checkStage environment actual shadow
      for type in types do
        let some (.inductInfo header) := actual.find? type.name | throwError "actual entered header absent"
        unless header.numNested == 7 && header.ctors == type.ctors.map Constructor.name do
          throwError "actual header metadata differs"
        for constructor in type.ctors do
          unless (actual.find? constructor.name).isNone && (shadow.find? constructor.name).isNone do
            throwError "constructor registration freshness absent"
      let .ok () := checkConstructors types stats isUnsafe { current with env := actual } |
        throwError "actual constructor checker rejected"
      let .ok () := checkConstructors types stats isUnsafe { current with env := shadow } |
        throwError "shadow constructor checker rejected"
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual } |
        throwError "constructor registration rejected"
      for type in types do
        for constructor in type.ctors do
          let some (.ctorInfo _) := registered.find? constructor.name |
            throwError "registered constructor absent"
      unless (run parameters types.toList 7 reader).isOk do throwError "full actual inductive run rejected"
  return 4

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderNativeMetadata |
    throwError "native metadata module absent"
  let nativeAllowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let strongAllowed := nativeAllowed ++ (← collectAxioms ``HeaderAxiomContinuation)
  let prefixAllowed := strongAllowed ++ (← collectAxioms ``checkInductiveTypes.freshConstructorAxiomContinuation)
  let runAllowed := strongAllowed ++ (← collectAxioms ``run.freshConstructorAxiomContinuation)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "native metadata module-owned axiom {name}"
      let allowed := if name == ``checkInductiveTypes.nativeConstructorAxiomContinuation then prefixAllowed
        else if name == ``run.nativeConstructorAxiomContinuation then runAllowed
        else if name.toString.startsWith "Lean4Lean.AddInductive." then strongAllowed else nativeAllowed
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "native metadata unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native metadata: {count} exhaustive production declarations audited; native lookup interface and strong input/source-pipeline dependencies remain explicit"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  checkInitial environment
  let mut outcomes ← checkBatch host environment #[]
  outcomes := outcomes + (← checkBatch host environment #[{ name := `NativeNoConstructors, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch host environment #[family `NativeSingle])
  outcomes := outcomes + (← checkBatch host environment #[family `NativeParams 2] 2)
  outcomes := outcomes + (← checkBatch host environment #[indexedFamily `NativeIndexed])
  let first := family `NativeFirst
  let second := family `NativeSecond
  outcomes := outcomes + (← checkBatch host environment
    #[{ first with ctors := first.ctors ++ [⟨`NativeFirst.cross,
        .forallE `other (.const `NativeSecond []) (.const `NativeFirst []) .default⟩] },
      { second with ctors := second.ctors ++ [⟨`NativeSecond.cross,
        .forallE `other (.const `NativeFirst []) (.const `NativeSecond []) .default⟩] }])
  let uninitialized := Kernel.Environment.empty `NativeMetadataEmpty
  checkInitial uninitialized
  outcomes := outcomes + (← checkBatch host uninitialized
    #[{ name := `NativeQuotientFlag, type := sortType, ctors := [⟨`NativeQuotientFlag.mk, .const `NativeQuotientFlag []⟩] }])
  logInfo m!"{outcomes} metadata-stage/constructor/full-run combinations passed: native origin, all parent fields, quotient retention and derived shadow acceptance"

end InductiveHeaderNativeMetadataTest
