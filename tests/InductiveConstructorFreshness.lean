import Lean4Lean.Verify.InductiveConstructorFreshness

namespace InductiveConstructorFreshnessTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive

example {before after : Kernel.Environment} {name : Name}
    (frame : NativeValueFrame before after) (beforeWF : before.constants.WF)
    (absent : after.find? name = none) : before.find? name = none :=
  frame.absentBefore beforeWF absent

example {actual shadow : Kernel.Environment} {types : Array InductiveType}
    (fresh : ConstructorsFresh actual types) (agreement : HeaderAxiomAgreement actual shadow) :
    ConstructorsFresh shadow types :=
  fresh.inShadow agreement

example (stats : InductiveStats) (types : Array InductiveType) (isUnsafe : Bool)
    (reader : Context) (envWF : reader.env.constants.WF) :
    (declareConstructors stats types isUnsafe reader).WF fun final =>
      NativeValueFrame reader.env final ∧ ConstructorsFresh reader.env types ∧ (ConstructorNames types).Nodup :=
  declareConstructors.freshness stats types isUnsafe reader envWF

example {stats : InductiveStats} {nparams numNested : Nat} {types : Array InductiveType}
    {isUnsafe : Bool} {universes : List Name} {actual : Kernel.Environment}
    (metadata : stats.HeaderMetadata nparams types numNested isUnsafe universes actual)
    (fresh : ConstructorsFresh actual types) (parent : Nat) (bound : parent < types.size) :
    ∃ header, actual.find? types[parent].name = some (.inductInfo header) ∧
      ∀ constructor ∈ header.ctors, actual.find? constructor = none :=
  metadata.constructorsMissing fresh parent bound

example (nparams : Nat) (types : List InductiveType) (numNested : Nat) (reader : Context)
    (envWF : reader.env.constants.WF) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      reader.HeaderFrame current ∧
      stats.HeaderMetadata nparams types.toArray numNested (reader.safety != .safe) current.lparams actual ∧
      ConstructorsFresh actual types.toArray ∧ (ConstructorNames types.toArray).Nodup ∧
      NativeValueFrame actual final ∧
      checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () :=
  run.registeredConstructorFreshness nparams types numNested reader envWF

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ConstructorsFresh actual types.toArray ∧ ConstructorsFresh stage.shadow types.toArray ∧
        (ConstructorNames types.toArray).Nodup ∧ NativeValueFrame actual final ∧
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () :=
  run.freshConstructorAxiomContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state finalState : TypeChecker.State)
    (requested : Name) (position : Nat) (value source normalized : Expr) (header : InductiveVal)
    (levels : List Level)
    (normalization : methods.whnf source context state = .ok (normalized, finalState))
    (head : normalized.getAppFn = .const header.name levels)
    (lookup : context.env.find? header.name = some (.inductInfo header))
    (missing : ∀ constructor ∈ header.ctors, context.env.find? constructor = none) :
    (TypeChecker.Inner.inferProj requested position value source methods context state).WF fun _ => False :=
  TypeChecker.Inner.inferProj.missingConstructors methods context state finalState requested position
    value source normalized header levels normalization head lookup missing

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (value constructor : Expr) (name : Name) (levels : List Level)
    (head : constructor.getAppFn = .const name levels) (missing : context.env.find? name = none) :
    (TypeChecker.Inner.tryEtaStructCore value constructor methods context state).WF fun _ => False :=
  TypeChecker.Inner.tryEtaStructCore.missingConstructor methods context state value constructor name levels head missing

example (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state inferredState finalState : TypeChecker.State) (first second source normalized : Expr)
    (header : InductiveVal) (constructor : Name) (levels : List Level)
    (inferred : methods.inferType first true context state = .ok (source, inferredState))
    (normalization : methods.whnf source context inferredState = .ok (normalized, finalState))
    (head : normalized.getAppFn = .const header.name levels)
    (lookup : context.env.find? header.name = some (.inductInfo header))
    (notRecursive : header.isRec = false) (constructors : header.ctors = [constructor])
    (noIndices : header.numIndices = 0) (missing : context.env.find? constructor = none) :
    (TypeChecker.Inner.isDefEqUnitLike first second methods context state).WF fun _ => False :=
  TypeChecker.Inner.isDefEqUnitLike.missingConstructor methods context state inferredState finalState
    first second source normalized header constructor levels inferred normalization head lookup
    notRecursive constructors noIndices missing

private def sortType : Expr := .sort (.succ .zero)

private def family (name : Name) (parameters fields : Nat) (constructorCount : Nat := 1)
    (indices : Nat := 0) : InductiveType :=
  let result := mkAppN (.const name [])
    (((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1)) ++
      (List.replicate indices (.const ``Nat.zero [])).toArray)
  let constructorType := (List.range fields).foldr (fun _ body =>
    .forallE `field (.const ``Nat []) body .default) result
  let close := fun body => (List.range parameters).foldr (fun _ body =>
    .forallE `parameter sortType body .implicit) body
  let header := (List.range indices).foldr (fun _ body =>
    .forallE `index (.const ``Nat []) body .default) sortType
  { name, type := close header, ctors := (List.range constructorCount).map fun index =>
    { name := name ++ Name.mkSimple s!"ctor{index}", type := close constructorType } }

private def checkpoint (reader : Context) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe : Bool) : Except Kernel.Exception (InductiveStats × Context × Kernel.Environment) :=
  checkInductiveTypes nparams types (fun stats => do
    let actual ← declareInductiveTypes stats nparams types 0 isUnsafe
    return (stats, ← read, actual)) reader

private def shadowAt (env actual : Kernel.Environment) (types : Array InductiveType) : Kernel.Environment :=
  headerAxiomView env (types.toList.map fun type =>
    match actual.find? type.name with
    | some (.inductInfo header) => header
    | _ => default)

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment)
    (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] nparams types.toList false) none).isOk do
    throwError "native kernel rejected constructor freshness fixture"
  for isUnsafe in [false, true] do
    let reader : Context := {
      env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }
    let .ok (stats, current, actual) := checkpoint reader nparams types isUnsafe
      | throwError "constructor freshness header checkpoint failed"
    let shadow := shadowAt env actual types
    let names := ConstructorNames types
    unless names.eraseDups.length == names.length do
      throwError "accepted fixture constructor names are not globally distinct"
    for type in types do
      let some (.inductInfo header) := actual.find? type.name
        | throwError "constructor freshness lost installed header metadata"
      unless header.ctors == type.ctors.map Constructor.name do
        throwError "constructor freshness changed the header constructor list"
      for constructor in type.ctors do
        if (actual.find? constructor.name).isSome || (shadow.find? constructor.name).isSome then
          throwError "constructor freshness checkpoint contains a future constructor"
    unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
        (checkConstructors types stats isUnsafe { current with env := shadow }).isOk do
      throwError "constructor freshness fixture did not check in both header stages"
    let .ok registered := declareConstructors stats types isUnsafe { current with env := actual }
      | throwError "constructor freshness fixture failed eventual registration"
    let .ok final := run nparams types.toList 0 reader
      | throwError "constructor freshness fixture failed complete run"
    let some (.defnInfo original) := env.find? `FreshnessSeed
      | throwError "constructor freshness fixture lost its seed definition"
    for stage in [actual, shadow, registered, final] do
      let some (.defnInfo retained) := stage.find? original.name
        | throwError "constructor freshness stage lost an old definition"
      unless retained == original do
        throwError "constructor freshness stage changed an exact old definition"
    for type in types do
      for constructor in type.ctors do
        let some (.ctorInfo staged) := registered.find? constructor.name
          | throwError "constructor freshness lost a registered constructor"
        let some (.ctorInfo completed) := final.find? constructor.name
          | throwError "constructor freshness lost a completed constructor"
        unless staged == completed && staged.induct == type.name && staged.type == constructor.type do
          throwError "constructor freshness changed constructor metadata"
      unless (final.find? (mkRecName type.name)).isSome do
        throwError "constructor freshness run did not register a recursor"

private def checkCollision (reader : Context) (types : Array InductiveType) (isUnsafe : Bool)
    (checkingAccepts := true) : MetaM Unit := do
  let .ok (stats, current, actual) := checkpoint reader 0 types isUnsafe
    | throwError "constructor collision fixture failed before its intended registration boundary"
  unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk == checkingAccepts do
    throwError "constructor collision control has unexpected checking result: {types.toList.map InductiveType.name}"
  if (declareConstructors stats types isUnsafe { current with env := actual }).isOk then
    throwError "constructor registration accepted a colliding name"
  if (run 0 types.toList 0 reader).isOk then
    throwError "complete runner accepted a colliding constructor name"

private def checkMetadataBarriers (reader : Context) (isUnsafe : Bool) : MetaM Unit := do
  let type := family `FreshnessProjection 0 1
  let .ok (stats, current, actual) := checkpoint reader 0 #[type] isUnsafe
    | throwError "projection freshness checkpoint failed"
  let shadow := shadowAt reader.env actual #[type]
  unless actual.isStructureLike type.name do
    throwError "header-only structure predicate unexpectedly requires constructor registration"
  if shadow.isStructureLike type.name then
    throwError "axiom shadow unexpectedly exposes structure metadata"
  let localName : FVarId := ⟨`FreshnessProjectionLocal⟩
  let locals := current.lctx.mkLocalDecl localName `value (.const type.name []) .default
  let projection := .proj type.name 0 (.fvar localName)
  let .error (.unknownConstant _ missingProjection) :=
      TypeChecker.checkType projection { env := actual, lctx := locals, safety := reader.safety } {}
    | throwError "actual projection did not fail at the missing constructor lookup"
  unless missingProjection == (type.ctors.head!).name do
    throwError "actual projection failed at an unrelated missing name"
  let .error (.invalidProj _ _ _) :=
      TypeChecker.checkType projection { env := shadow, lctx := locals, safety := reader.safety } {}
    | throwError "shadow projection did not fail at its axiom metadata"
  let .ok registered := declareConstructors stats #[type] isUnsafe { current with env := actual }
    | throwError "projection control failed constructor registration"
  unless (TypeChecker.checkType projection { env := registered, lctx := locals, safety := reader.safety } {}).isOk do
    throwError "projection control did not become available after constructor registration"
  let unitType := family `FreshnessUnitLike 0 0
  let .ok (unitStats, unitReader, unitActual) := checkpoint reader 0 #[unitType] isUnsafe
    | throwError "unit-like freshness checkpoint failed"
  let unitShadow := shadowAt reader.env unitActual #[unitType]
  let first : FVarId := ⟨`FreshnessUnitFirst⟩
  let second : FVarId := ⟨`FreshnessUnitSecond⟩
  let unitLocals := (unitReader.lctx.mkLocalDecl first `first (.const unitType.name []) .default)
    |>.mkLocalDecl second `second (.const unitType.name []) .default
  let unitAction := (TypeChecker.Inner.isDefEqUnitLike (.fvar first) (.fvar second)).run
  let .error (.unknownConstant _ missingUnit) :=
      unitAction { env := unitActual, lctx := unitLocals, safety := reader.safety } {}
    | throwError "actual unit-like helper did not fail at its missing constructor lookup"
  unless missingUnit == (unitType.ctors.head!).name do
    throwError "actual unit-like helper failed at an unrelated missing name"
  let .ok (false, _) := unitAction { env := unitShadow, lctx := unitLocals, safety := reader.safety } {}
    | throwError "shadow unit-like helper did not reject its axiom metadata"
  let etaAction := (TypeChecker.Inner.tryEtaStructCore (.fvar first)
    (.const (unitType.ctors.head!).name [])).run
  for stage in [unitActual, unitShadow] do
    let .error (.unknownConstant _ missingEta) :=
        etaAction { env := stage, lctx := unitLocals, safety := reader.safety } {}
      | throwError "structure eta helper did not fail at its missing constructor lookup"
    unless missingEta == (unitType.ctors.head!).name do
      throwError "structure eta helper failed at an unrelated missing name"
  let .ok unitRegistered := declareConstructors unitStats #[unitType] isUnsafe { unitReader with env := unitActual }
    | throwError "unit-like control failed constructor registration"
  let .ok (true, _) := unitAction { env := unitRegistered, lctx := unitLocals, safety := reader.safety } {}
    | throwError "unit-like control did not become available after registration"
  let .ok (true, _) := etaAction { env := unitRegistered, lctx := unitLocals, safety := reader.safety } {}
    | throwError "structure eta control did not become available after registration"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorFreshness
    | throwError "constructor freshness production module absent"
  let mut allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``checkName.WF, ``declareInductiveTypes.preservesValues,
      ``declareInductiveTypes.metadata, ``checkInductiveTypes.frameHeaderSizes,
      ``checkInductiveTypes.withHeaderAxiomContinuation, ``Expr.withApp_eq] do
    allowed := allowed ++ (← collectAxioms name).toList
  let typed := [``checkInductiveTypes.freshConstructorAxiomContinuation, ``run.freshConstructorAxiomContinuation]
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "constructor freshness module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "constructor freshness unexpected dependency {dependency} in {name}"
        if dependency == ``sorryAx && !typed.contains name then
          throwError "constructor freshness raw contract unexpectedly inherits sorryAx: {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"constructor freshness: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let imported ← getEnv
  let seed : DefinitionVal := {
    name := `FreshnessSeed, levelParams := [], type := .sort (.succ (.succ .zero)),
    value := sortType, hints := .abbrev, safety := .safe }
  let .ok host := imported.addDeclCore 0 (.defnDecl seed) none
    | throwError "native constructor freshness seed failed"
  let .ok env := Lean4Lean.addDecl imported.toKernelEnv (.defnDecl seed) true
    | throwError "constructor freshness seed failed"
  checkBatch host env 0 #[family `FreshnessSingle 0 1]
  checkBatch host env 0 #[family `FreshnessMultiple 0 1 3]
  checkBatch host env 0 #[family `FreshnessLeft 0 1 2, family `FreshnessRight 0 0 2]
  checkBatch host env 1 #[family `FreshnessParameter 1 1]
  checkBatch host env 2 #[family `FreshnessParameters 2 1]
  checkBatch host env 1 #[family `FreshnessIndexed 1 1 1 2]
  let dependent : InductiveType := {
    name := `FreshnessDependent
    type := .forallE `A sortType (.forallE `value (.bvar 0) sortType .default) .implicit
    ctors := [⟨`FreshnessDependent.mk, .forallE `A sortType
      (.forallE `value (.bvar 0)
        (mkAppN (.const `FreshnessDependent []) #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  checkBatch host env 2 #[dependent]
  for isUnsafe in [false, true] do
    let reader : Context := {
      env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }
    let existing := family `FreshnessExistingCollision 0 0
    checkCollision reader #[{ existing with ctors := [⟨``Nat.zero, .const existing.name []⟩] }] isUnsafe
    let own := family `FreshnessOwnCollision 0 0
    checkCollision reader #[{ own with ctors := [⟨own.name, .const own.name []⟩] }] isUnsafe
    let left := family `FreshnessOtherLeft 0 0
    let right := family `FreshnessOtherRight 0 0
    checkCollision reader #[{ left with ctors := [⟨right.name, .const left.name []⟩] }, right] isUnsafe
    let first := family `FreshnessRepeatedLeft 0 0
    let second := family `FreshnessRepeatedRight 0 0
    checkCollision reader #[{ first with ctors := [⟨`FreshnessSharedCtor, .const first.name []⟩] },
      { second with ctors := [⟨`FreshnessSharedCtor, .const second.name []⟩] }] isUnsafe
    let repeated := family `FreshnessRepeatedOwn 0 0
    checkCollision reader #[{ repeated with ctors := [⟨`FreshnessRepeatedOwn.mk, .const repeated.name []⟩,
      ⟨`FreshnessRepeatedOwn.mk, .const repeated.name []⟩] }] isUnsafe (checkingAccepts := false)
    let .ok (emptyStats, emptyReader, emptyActual) := checkpoint reader 0 #[] isUnsafe
      | throwError "empty constructor freshness checkpoint failed"
    let .ok emptyRegistered := declareConstructors emptyStats #[] isUnsafe { emptyReader with env := emptyActual }
      | throwError "empty constructor registration failed"
    unless emptyRegistered.constants.toList.length == env.constants.toList.length do
      throwError "empty constructor registration changed the environment"
    checkMetadataBarriers reader isUnsafe
  logInfo "7 native-accepted freshness fixtures passed both safeties, actual/shadow constructor absence, global distinctness, exact old definitions, eventual registration and full recursors; 8 checking-versus-registration collisions, 2 within-parent duplicate-checking rejections, empty and projection/structure-eta/unit-like metadata barriers passed"

end InductiveConstructorFreshnessTest
