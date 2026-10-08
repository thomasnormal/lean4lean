import Lean4Lean.Verify.ConstructorMetadata
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace ConstructorMetadataTest

example (stats : InductiveStats) (types : Array InductiveType) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF)
    (harity : ∀ type ∈ types, ∀ ctor ∈ type.ctors,
      stats.params.size ≤ declareConstructors.arity 0 ctor.type) :
    (declareConstructors stats types isUnsafe ctx).WF fun env => env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.ConstructorMetadata ctx.lparams types isUnsafe env :=
  declareConstructors.metadata stats types isUnsafe ctx hwf harity

example (stats : InductiveStats) (types : Array InductiveType) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF) (hfvars : stats.ParamsAreFVars)
    (hnodup : stats.params.toList.Nodup) :
    ((checkConstructors types stats isUnsafe >>= fun _ =>
      declareConstructors stats types isUnsafe) ctx).WF fun env => env.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
        stats.ConstructorMetadata ctx.lparams types isUnsafe env :=
  checkConstructors.declareMetadata stats types isUnsafe ctx hwf hfvars hnodup

example (nparams : Nat) (types : Array InductiveType) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes nparams types (fun stats => do
      checkConstructors types stats isUnsafe
      let env ← declareConstructors stats types isUnsafe
      pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
        result.1.ConstructorMetadata ctx.lparams types isUnsafe result.2 :=
  checkInductiveTypes.checkedConstructorMetadata nparams types isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (isUnsafe : Bool)
    (ctx : Context) (env : Kernel.Environment) (hwf : ctx.env.constants.WF)
    (harity : ∀ type ∈ types, ∀ ctor ∈ type.ctors,
      stats.params.size ≤ declareConstructors.arity 0 ctor.type)
    (hdeclare : declareConstructors stats types isUnsafe ctx = .ok env)
    (name : Name) (info : ConstantInfo) (hold : ctx.env.find? name = some info) :
    env.find? name = some info :=
  (declareConstructors.metadata stats types isUnsafe ctx hwf harity _ hdeclare).2.1 name info hold

example (stats : InductiveStats) (lparams : List Name) (types : Array InductiveType)
    (isUnsafe : Bool) (env : Kernel.Environment)
    (hmetadata : stats.ConstructorMetadata lparams types isUnsafe env)
    (type : InductiveType) (htype : type ∈ types) (index : Nat) (ctor : Constructor)
    (hctor : type.ctors[index]? = some ctor) :
    env.find? ctor.name = some (.ctorInfo {
      name := ctor.name, levelParams := lparams, type := ctor.type, induct := type.name,
      cidx := index, numParams := stats.params.size,
      numFields := declareConstructors.arity 0 ctor.type - stats.params.size, isUnsafe }) :=
  (hmetadata type htype index ctor hctor).1

example (stats : InductiveStats) (lparams : List Name) (types : Array InductiveType)
    (isUnsafe : Bool) (env : Kernel.Environment)
    (hmetadata : stats.ConstructorMetadata lparams types isUnsafe env)
    (type : InductiveType) (htype : type ∈ types) (index : Nat) (ctor : Constructor)
    (hctor : type.ctors[index]? = some ctor) (info : ConstructorVal)
    (hlookup : env.find? ctor.name = some (.ctorInfo info)) :
    info.numParams + info.numFields = declareConstructors.arity 0 ctor.type := by
  obtain ⟨hrecord, htotal⟩ := hmetadata type htype index ctor hctor
  rw [hlookup] at hrecord
  have heq := ConstantInfo.ctorInfo.inj (Option.some.inj hrecord)
  simpa only [heq] using htotal

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def checkedStage (nparams : Nat) (types : Array InductiveType) (isUnsafe : Bool) :
    M (InductiveStats × Kernel.Environment × Kernel.Environment) :=
  checkInductiveTypes nparams types fun stats => do
    let headers ← declareInductiveTypes stats nparams types 0 isUnsafe
    withEnv headers do
      checkConstructors types stats isUnsafe
      let env ← declareConstructors stats types isUnsafe
      pure (stats, headers, env)

private def checkInfo (stats : InductiveStats) (ctx : Context) (env : Kernel.Environment)
    (isUnsafe : Bool) (type : InductiveType) (index : Nat) (ctor : Constructor) : MetaM Unit := do
  let some (.ctorInfo actual) := env.find? ctor.name | throwError "missing constructor {ctor.name}"
  let expected := declareConstructors.metadataVal stats ctx.lparams isUnsafe type.name index ctor
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.induct == expected.induct &&
      actual.cidx == expected.cidx && actual.numParams == expected.numParams &&
      actual.numFields == expected.numFields && actual.isUnsafe == expected.isUnsafe do
    throwError "incorrect registered metadata for {ctor.name}"
  unless actual.numParams + actual.numFields == declareConstructors.arity 0 ctor.type do
    throwError "registered constructor field subtraction truncated"

private def checkPreserved (headers env : Kernel.Environment) (name : Name) : MetaM Unit := do
  let some original := headers.find? name | throwError "missing preservation fixture {name}"
  let some retained := env.find? name | throwError "registration dropped {name}"
  unless original.name == retained.name && original.type == retained.type &&
      original.levelParams == retained.levelParams && original.safety == retained.safety do
    throwError "registration changed {name}"

private def checkStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe expected : Bool) : MetaM Unit := do
  let result := checkedStage nparams types isUnsafe ctx
  unless result.isOk == expected do
    throwError "incorrect metadata staging outcome for {types.map (·.name)}"
  if let .ok (stats, headers, env) := result then
    unless stats.params.size == nparams do
      throwError "incorrect checked parameter count"
    for type in types do
      checkPreserved headers env type.name
      for index in [:type.ctors.length] do
        checkInfo stats ctx env isUnsafe type index type.ctors[index]!
      if env.contains (type.name ++ `rec) then
        throwError "constructor registration installed a recursor"
    for name in [``Nat, ``Nat.zero, ``Nat.succ, ``List] do
      checkPreserved headers env name

private def checkImportedStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe expected : Bool) : MetaM Unit := do
  let result := checkInductiveTypes nparams types (fun stats => do
    checkConstructors types stats isUnsafe
    let env ← declareConstructors stats types isUnsafe
    pure (stats, env)) ctx
  unless result.isOk == expected do
    throwError "incorrect checked-type/check/register composition outcome"
  if let .ok (stats, env) := result then
    for type in types do
      checkPreserved ctx.env env type.name
      for index in [:type.ctors.length] do
        checkInfo stats ctx env isUnsafe type index type.ctors[index]!

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        interfaces.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let maps := [``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert]
  let guarded := maps ++ [``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq,
    ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``declareConstructors.metadata maps
  audit ``checkConstructors.declareMetadata guarded
  audit ``checkInductiveTypes.checkedConstructorMetadata guarded
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let zero := Expr.const `MetadataZero []
  let other := Expr.const `MetadataOther []
  let one := Expr.const `MetadataOne []
  let two := Expr.const `MetadataTwo []
  let indexed := Expr.const `MetadataIndexed []
  let negative := Expr.const `MetadataNegative []
  let natType := Expr.const ``Nat []
  let zeroCtor : Constructor := { name := `MetadataZero.base, type := zero }
  let zeroField : Constructor := {
    name := `MetadataZero.field, type := .forallE `value natType zero .default }
  let zeroFields : Constructor := {
    name := `MetadataZero.fields, type := .forallE `first natType
      (.forallE `second natType zero .implicit) .strictImplicit }
  let oneCtor : Constructor := {
    name := `MetadataOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let oneField : Constructor := {
    name := `MetadataOne.field, type := closeParams 1
      (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let twoCtor : Constructor := {
    name := `MetadataTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let twoField : Constructor := {
    name := `MetadataTwo.field, type := closeParams 2
      (.forallE `value (.bvar 1) (.mkAppList two [.bvar 2, .bvar 1]) .default) }
  let missing : Constructor := {
    name := `MetadataTwo.missing, type := closeParams 1 (.mkAppList two [.bvar 0, natType]) }
  let otherCtor : Constructor := { name := `MetadataOther.base, type := other }
  let otherField : Constructor := {
    name := `MetadataOther.field, type := .forallE `value zero other .default }
  let indexedHeader : InductiveType := {
    name := `MetadataIndexed, type := closeParams 1 (.forallE `index natType sortType .default),
    ctors := [
      { name := `MetadataIndexed.base,
        type := closeParams 1 (.mkAppList indexed [.bvar 0, .const ``Nat.zero []]) },
      { name := `MetadataIndexed.field,
        type := closeParams 1
          (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }
  let polySort := Expr.sort (.param `u)
  let polyCtor := Expr.forallE `parameter polySort
    (.forallE `value (.bvar 0) (.app (.const `MetadataPoly [.param `u]) (.bvar 1)) .default)
      .implicit
  let polymorphic : InductiveType := {
    name := `MetadataPoly, type := .forallE `parameter polySort polySort .implicit,
    ctors := [{ name := `MetadataPoly.mk, type := polyCtor }] }
  let negativeType := Expr.forallE `function
    (.forallE `input negative negative .default) negative .default
  let negativeHeader := header `MetadataNegative 0
    [{ name := `MetadataNegative.mk, type := negativeType }]
  let importedNat := header ``Nat 0 [
    { name := `MetadataImportedZero, type := natType },
    { name := `MetadataImportedSucc, type := .forallE `value natType natType .default }]
  let polyLevel := Level.param `u
  let importedList : InductiveType := {
    name := ``List, type := .forallE `parameter (.sort (.succ polyLevel))
      (.sort (.succ polyLevel)) .default,
    ctors := [
      { name := `MetadataImportedList,
        type := .forallE `parameter (.sort (.succ polyLevel))
          (.app (.const ``List [polyLevel]) (.bvar 0)) .default }] }
  for isUnsafe in [false, true] do
    let ctx := { ctx with safety := if isUnsafe then .unsafe else .safe }
    checkStage ctx 0 #[] isUnsafe true
    checkStage ctx 1 #[header `MetadataOne 1 []] isUnsafe true
    checkStage ctx 0 #[header `MetadataZero 0 [zeroCtor, zeroField, zeroFields]] isUnsafe true
    checkStage ctx 1 #[header `MetadataOne 1 [oneCtor, oneField]] isUnsafe true
    checkStage ctx 2 #[header `MetadataTwo 2 [twoCtor, twoField]] isUnsafe true
    checkStage ctx 0 #[header `MetadataZero 0 [zeroCtor, zeroField, zeroFields],
      header `MetadataEmpty 0 [], header `MetadataOther 0 [otherCtor, otherField]] isUnsafe true
    checkStage ctx 1 #[indexedHeader] isUnsafe true
    checkStage { ctx with lparams := [`u] } 1 #[polymorphic] isUnsafe true
    checkStage ctx 0 #[negativeHeader] isUnsafe isUnsafe
    checkStage ctx 0 #[header `MetadataZero 0 [zeroCtor, zeroCtor]] isUnsafe false
    checkStage ctx 0 #[header `MetadataZero 0 [zeroCtor],
      header `MetadataOther 0 [{ otherCtor with name := zeroCtor.name }]] isUnsafe false
    checkStage ctx 0 #[header `MetadataZero 0 [{ zeroCtor with name := ``Nat.zero }]] isUnsafe false
    checkStage ctx 2 #[header `MetadataTwo 2 [twoCtor, missing]] isUnsafe false
    checkImportedStage ctx 0 #[importedNat] isUnsafe true
    checkImportedStage ctx 0 #[{ importedNat with ctors := importedNat.ctors ++ importedNat.ctors }]
      isUnsafe false
    checkImportedStage { ctx with lparams := [`u] } 1 #[importedList] isUnsafe true

end ConstructorMetadataTest
