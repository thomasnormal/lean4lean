import Lean4Lean.Verify.InductiveConstructorRegistration
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveConstructorRegistrationTest

example (environment : VEnv) (constructors : List VConstVal)
    (fresh : ∀ constructor ∈ constructors, environment.constants constructor.name = none)
    (distinct : (constructors.map VConstVal.name).Nodup) :
    ∃ extended, environment.addConstructorHeaders constructors = some extended :=
  VEnv.addConstructorHeaders.exists fresh distinct

example (translated : TrInductDecl headerEnvironment constructorEnvironment universes nparams types declaration) :
    List.Forall₂ (TrConstructor constructorEnvironment universes)
      (types.flatMap (fun type => type.ctors)) declaration.constructorHeaders :=
  translated.constructorModels

example (translated : TrInductDecl headerEnvironment constructorEnvironment universes nparams types declaration) :
    declaration.constructorHeaders.map VConstVal.name =
      types.flatMap (fun type => type.ctors.map Constructor.name) :=
  translated.constructorNames

example (model : TypedHeaderReader base stats reader) : stats.ParamsAreFVars := model.paramsAreFVars
example (model : TypedHeaderReader base stats reader) : stats.params.toList.Nodup := model.paramsNodup

section Receipts

variable {root : TypeChecker.VContext} {original reader : Context} {nparams : Nat}
  {types : Array InductiveType} {stats : InductiveStats} {actual final : Kernel.Environment}
  {stage : HeaderAxiomContinuation root original nparams types stats reader actual} {isUnsafe : Bool}
  (receipts : ConstructorSemanticReceipts stage isUnsafe)

example : ∀ constructor ∈ receipts.declaration.constructorHeaders,
    constructor.toVConstant.WF stage.semantic := receipts.flatTypesWF

example (fresh : ConstructorsFresh stage.shadow types) :
    ∀ constructor ∈ receipts.declaration.constructorHeaders, stage.semantic.constants constructor.name = none :=
  receipts.constantsFresh fresh

example (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (checked : checkConstructors types stats isUnsafe { reader with env := actual } = .ok ())
    (accepted : declareConstructors stats types isUnsafe { reader with env := actual } = .ok final) :
    Nonempty (ConstructorConstantRegistration receipts final) :=
  receipts.registeredConstants safetyBound checked accepted

variable (registration : ConstructorConstantRegistration receipts final)

example : stage.semantic.addConstructorHeaders receipts.declaration.constructorHeaders =
    some registration.semantic := registration.registered
example : registration.semantic.WF := registration.semanticWF
example : registration.semantic.Ordered := registration.semanticWF.ordered
example : stage.semantic ≤ registration.semantic := registration.increase
example : registration.semantic.defeqs = stage.semantic.defeqs := registration.definitions
example : final.constants.WF := registration.nativeWF
example : NativeValueFrame actual final := registration.values
example : stats.ConstructorMetadata root.lparams types isUnsafe final := registration.metadata
example : root.safety ≤ if isUnsafe then .unsafe else .safe := registration.safetyBound

example (member : constructor ∈ receipts.declaration.constructorHeaders) :
    registration.semantic.constants constructor.name = some constructor.toVConstant :=
  registration.constants member

example (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source) :
    ∃ constructor ∈ receipts.declaration.constructorHeaders,
      final.find? source.name = some (.ctorInfo
        (declareConstructors.metadataVal stats root.lparams isUnsafe type.name index source)) ∧
      registration.semantic.constants source.name = some constructor.toVConstant ∧
      TrConstant root.safety registration.semantic
        (.ctorInfo (declareConstructors.metadataVal stats root.lparams isUnsafe type.name index source))
        constructor.toVConstant :=
  registration.constructorConstant typeMember index source sourceGet

end Receipts

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
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          Nonempty (ConstructorConstantRegistration receipts final) :=
  checkInductiveTypes.constructorConstantContinuation nparams types numNested isUnsafe
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
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          Nonempty (ConstructorConstantRegistration receipts final) :=
  run.constructorConstantContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors

private def parentHeaders : List VInductiveType := boolInductDecl.types ++ natInductDecl.types
private def semanticConstructors : List VConstVal := parentHeaders.flatMap (fun header => header.ctors)
private def headerEnvironment : VEnv := (VEnv.empty.addInductHeaders parentHeaders).getD VEnv.empty
private def constructorEnvironment : VEnv :=
  (headerEnvironment.addConstructorHeaders semanticConstructors).getD headerEnvironment

example : boolInductDecl.constructorHeaders = boolInductDecl.types.flatMap (fun header => header.ctors) := rfl
example : headerEnvironment.addConstructorHeaders [] = some headerEnvironment := rfl
example : headerEnvironment.addConstructorHeaders semanticConstructors = some constructorEnvironment := rfl
example : constructorEnvironment.constants ``Nat.succ = some {
    uvars := 0, type := .forallE (.const ``Nat []) (.const ``Nat []) } := rfl
example : constructorEnvironment.constants ``Bool.true = some { uvars := 0, type := .const ``Bool [] } := rfl
example : constructorEnvironment.defeqs = headerEnvironment.defeqs :=
  VEnv.addConstructorHeaders.defeqs_eq (ctors := semanticConstructors) rfl
example : constructorEnvironment.constants ``Nat.rec = none := rfl
example : (constructorEnvironment.addConstructorHeaders semanticConstructors).isSome = false := by decide
example : (headerEnvironment.addConstructorHeaders (semanticConstructors ++ semanticConstructors)).isSome = false :=
  by decide

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def family (name : Name) (parameters : Nat := 0) : InductiveType :=
  let close := fun body => (List.range parameters).foldr
    (fun _ body => .forallE `parameter sortType body .implicit) body
  let parent := fun fields => mkAppN (.const name [])
    ((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1))
  { name, type := close sortType,
    ctors := [⟨name ++ `base, close (parent 0)⟩,
      ⟨name ++ `step, close (.forallE `child (parent 0) (parent 1) .default)⟩,
      ⟨name ++ `higher, close (.forallE `children (.forallE `index natural (parent 1) .default)
        (parent 1) .default)⟩] }

private def checkpoint (reader : Context) (parameters : Nat) (types : Array InductiveType)
    (isUnsafe : Bool) :=
  checkInductiveTypes parameters types (fun stats => do
    let actual ← declareInductiveTypes stats parameters types 3 isUnsafe
    return (stats, ← read, actual)) reader

private def headerFields (header : InductiveVal) :=
  (header.name, header.levelParams, header.type, header.numParams, header.numIndices,
    header.all, header.ctors, header.numNested, header.isRec, header.isUnsafe, header.isReflexive)

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (types : Array InductiveType) (parameters : Nat := 0) (universes : List Name := []) : MetaM Nat := do
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected constructor registration controls"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkpoint reader parameters types isUnsafe
        | throwError "constructor registration header staging failed"
      unless stats.params.size == parameters && stats.params.toList.eraseDups.length == parameters do
        throwError "constructor registration parameter count or distinctness differs"
      for parameter in stats.params do
        unless parameter.isFVar do throwError "constructor registration parameter is not an FVar"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (checkConstructors types stats isUnsafe { current with env := shadow }).isOk do
        throwError "constructor registration checking rejected an actual/shadow control"
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual }
        | throwError "constructor registration rejected fresh signatures"
      let .ok final := run parameters types.toList 3 reader
        | throwError "constructor registration complete run failed"
      for name in [`RegistrationSeed, ``Nat.zero, ``Nat.succ, ``outParam] do
        for extended in [actual, shadow, registered, final] do
          match environment.find? name, extended.find? name with
          | some (.defnInfo original), some (.defnInfo retained) =>
            unless retained == original do throwError "constructor registration changed old definition metadata"
          | some (.ctorInfo original), some (.ctorInfo retained) =>
            unless retained == original do throwError "constructor registration changed old constructor metadata"
          | _, _ => throwError "constructor registration lost old metadata"
      let names := ConstructorNames types
      unless names.eraseDups.length == names.length do throwError "constructor registration names repeat"
      for type in types do
        let some (.inductInfo oldHeader) := actual.find? type.name
          | throwError "constructor registration lost native header"
        for extended in [registered, final] do
          let some (.inductInfo retained) := extended.find? type.name
            | throwError "constructor registration lost native header"
          unless headerFields retained == headerFields oldHeader do
            throwError "constructor registration changed exact native header metadata"
        for (source, index) in type.ctors.zipIdx do
          if (actual.find? source.name).isSome || (shadow.find? source.name).isSome then
            throwError "constructor registration freshness is false"
          let expected := declareConstructors.metadataVal stats universes isUnsafe type.name index source
          unless expected.numParams + expected.numFields == declareConstructors.arity 0 source.type do
            throwError "constructor registration arity metadata differs"
          for extended in [registered, final] do
            let some (.ctorInfo retained) := extended.find? source.name
              | throwError "constructor registration lost exact metadata"
            unless retained == expected do throwError "constructor registration exact metadata differs"
        unless (final.find? (mkRecName type.name)).isSome do throwError "complete run omitted recursor"
  return 4

private def checkCollision (environment : Kernel.Environment) (types : Array InductiveType)
    (checkingAccepts := true) : MetaM Nat := do
  for isUnsafe in [false, true] do
    let reader : Context := {
      env := environment, lparams := [],
      safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }
    let .ok (stats, current, actual) := checkpoint reader 0 types isUnsafe
      | throwError "constructor collision failed before registration boundary"
    unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk == checkingAccepts do
      throwError "constructor collision checking boundary differs"
    if (declareConstructors stats types isUnsafe { current with env := actual }).isOk ||
        (run 0 types.toList 3 reader).isOk then
      throwError "constructor collision was registered"
  return 2

private def auditModule (moduleName : Name) (allowed : Array Name) (rawAllowed : Array Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "registration module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "constructor registration owned axiom {name}"
      let text := name.toString
      let baseline := if moduleName == `Lean4Lean.Theory.ConstructorHeaders then
          if text.contains "Headers.wf" || text.contains "Headers.ordered" then allowed else rawAllowed
        else if text.contains "appendRelated" || text.contains "flattenConstructorModels" ||
          text.contains "relatedConstructorNames" || name == ``TrInductDecl.constructorModels ||
          name == ``TrInductDecl.constructorNames then rawAllowed else allowed
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless baseline.contains dependency do throwError "registration unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"{moduleName}: {count} exhaustive owned declarations audited"

run_meta
  let logical := #[``propext, ``Classical.choice, ``Quot.sound]
  let rawAllowed := logical ++ (← collectAxioms ``TrInductDecl)
  let mut allowed := rawAllowed
  for name in [``TypeChecker.VContext.Δwf, ``TypedHeaderReader,
      ``ConstructorSemanticReceipts.constructorTypesWF, ``declareConstructors.metadata,
      ``declareConstructors.freshness, ``TrEnv.find?_iff, ``checkConstructors.arity,
      ``ElimNestedInductive.ParameterPrefix.nodup, ``TrExprS.mono,
      ``checkInductiveTypes.typedConstructorAxiomContinuation, ``run.typedConstructorAxiomContinuation] do
    allowed := allowed ++ (← collectAxioms name)
  auditModule `Lean4Lean.Theory.ConstructorHeaders
    (logical ++ (← collectAxioms ``VEnv.WF) ++ (← collectAxioms ``VConstant.WF.mono)) logical
  auditModule `Lean4Lean.Verify.InductiveConstructorRegistration allowed rawAllowed
  let host ← getEnv
  let .ok seededHost := host.addDeclCore 0 (.defnDecl {
      name := `RegistrationSeed, levelParams := [], type := natural,
      value := .const ``Nat.zero [], hints := .opaque, safety := .safe }) none
    | throwError "constructor registration seed rejected by native kernel"
  let environment := seededHost.toKernelEnv
  let mut outcomes ← checkBatch seededHost environment #[]
  outcomes := outcomes + (← checkBatch seededHost environment #[{
    name := `RegistrationEmpty, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch seededHost environment #[family `RegistrationSingle])
  outcomes := outcomes + (← checkBatch seededHost environment #[family `RegistrationParameters 2] 2)
  let dependent : InductiveType := {
    name := `RegistrationDependent,
    type := .forallE `carrier sortType (.forallE `value (.bvar 0) sortType .default) .implicit,
    ctors := [⟨`RegistrationDependent.mk, .forallE `carrier sortType
      (.forallE `value (.bvar 0)
        (mkAppN (.const `RegistrationDependent []) #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  outcomes := outcomes + (← checkBatch seededHost environment #[dependent] 2)
  let parameterIndexed : InductiveType := {
    name := `RegistrationParameterIndex,
    type := .forallE `carrier sortType (.forallE `index natural sortType .default) .implicit,
    ctors := [⟨`RegistrationParameterIndex.mk, .forallE `carrier sortType
      (mkAppN (.const `RegistrationParameterIndex []) #[.bvar 0, .const ``Nat.zero []]) .implicit⟩] }
  outcomes := outcomes + (← checkBatch seededHost environment #[parameterIndexed] 1)
  let dependentFields : InductiveType := {
    name := `RegistrationDependentFields, type := .sort (.succ (.succ .zero)),
    ctors := [⟨`RegistrationDependentFields.mk,
      .forallE `carrier (mkApp (.const ``outParam [.succ (.succ .zero)]) sortType)
        (.forallE `value (.bvar 0) (.const `RegistrationDependentFields []) .default) .default⟩] }
  outcomes := outcomes + (← checkBatch seededHost environment #[dependentFields])
  let universeLevel := Level.param `universe
  let polySort := Expr.sort (.succ universeLevel)
  let polyReturn := fun name arguments => mkAppN (.const name [universeLevel]) arguments
  outcomes := outcomes + (← checkBatch seededHost environment #[{
    name := `RegistrationPolyFirst, type := .forallE `carrier polySort polySort .default,
    ctors := [⟨`RegistrationPolyFirst.base, polyReturn `RegistrationPolyFirst #[.sort universeLevel]⟩] }, {
    name := `RegistrationPolySecond, type := polySort,
    ctors := [⟨`RegistrationPolySecond.base, polyReturn `RegistrationPolySecond #[]⟩] }, {
    name := `RegistrationPolyThird,
    type := .forallE `carrier polySort (.forallE `index natural polySort .default) .default,
    ctors := [⟨`RegistrationPolyThird.base,
      polyReturn `RegistrationPolyThird #[.sort universeLevel, .const ``Nat.zero []]⟩] }] 0 [`universe])
  let polymorphic : InductiveType := {
    name := `RegistrationPolyParameter,
    type := .forallE `carrier (.sort universeLevel) (.sort universeLevel) .implicit,
    ctors := [⟨`RegistrationPolyParameter.mk, .forallE `carrier (.sort universeLevel)
      (mkApp (.const `RegistrationPolyParameter [universeLevel]) (.bvar 0)) .implicit⟩] }
  outcomes := outcomes + (← checkBatch seededHost environment #[polymorphic] 1 [`universe])
  let first := family `RegistrationMutualFirst
  let second := family `RegistrationMutualSecond
  outcomes := outcomes + (← checkBatch seededHost environment #[
    { first with ctors := first.ctors ++ [⟨`RegistrationMutualFirst.cross,
      .forallE `other (.const second.name []) (.const first.name []) .default⟩] },
    { second with ctors := second.ctors ++ [⟨`RegistrationMutualSecond.cross,
      .forallE `other (.const first.name []) (.const second.name []) .default⟩] }])
  let existing := family `RegistrationExistingCollision
  let mut collisions ← checkCollision environment #[
    { existing with ctors := [⟨``Nat.zero, .const existing.name []⟩] }]
  let own := family `RegistrationOwnCollision
  collisions := collisions + (← checkCollision environment #[{ own with ctors := [⟨own.name, .const own.name []⟩] }])
  let left := family `RegistrationOtherLeft
  let right := family `RegistrationOtherRight
  collisions := collisions + (← checkCollision environment #[
    { left with ctors := [⟨right.name, .const left.name []⟩] }, right])
  collisions := collisions + (← checkCollision environment #[
    { left with ctors := [⟨`RegistrationSharedCtor, .const left.name []⟩] },
    { right with ctors := [⟨`RegistrationSharedCtor, .const right.name []⟩] }])
  collisions := collisions + (← checkCollision environment #[
    { own with ctors := [⟨`RegistrationRepeatedCtor, .const own.name []⟩,
      ⟨`RegistrationRepeatedCtor, .const own.name []⟩] }] false)
  logInfo m!"{outcomes} registration controls passed both safeties and primitive modes with exact constructor/header/old metadata, distinct FVar parameters, actual/shadow freshness and complete runs; {collisions} collision boundaries rejected; native controls do not fabricate semantic contexts"

end InductiveConstructorRegistrationTest
