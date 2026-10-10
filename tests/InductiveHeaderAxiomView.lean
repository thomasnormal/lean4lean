import Lean4Lean.Verify.InductiveHeaderAxiomView

open Lean Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

namespace InductiveHeaderAxiomViewTest

example (info : InductiveVal) :
    headerTypeValue (headerAxiomInfo info) = headerTypeValue (.inductInfo info) :=
  headerAxiomInfo.typeValue info

example (agreement : HeaderAxiomAgreement actual shadow) (name : Name) :
    actual.find? name = none ↔ shadow.find? name = none := agreement.none_iff name

example (agreement : HeaderAxiomAgreement actual shadow) (name : Name) :
    (actual.find? name).bind ConstantInfo.value? = (shadow.find? name).bind ConstantInfo.value? :=
  agreement.values name

example (history : TrEnv safety env semantic) : TrEnv safety (headerAxiomView env []) semantic := history

example (checker : TypeChecker.VContext) (shadow : Kernel.Environment) (semantic : VEnv)
    (increase : checker.venv ≤ semantic) (history : TrEnv checker.safety shadow semantic)
    (primitives : NativePrimitiveFrame checker.env shadow) :
    (checker.inHeaderAxiomView shadow semantic increase history primitives).toContext =
      { checker.toContext with env := shadow } :=
  TypeChecker.VContext.inHeaderAxiomView.context checker shadow semantic increase history primitives

example (checker : TypeChecker.VContext) (shadow : Kernel.Environment) (semantic : VEnv)
    (increase : checker.venv ≤ semantic) (history : TrEnv checker.safety shadow semantic)
    (primitives : NativePrimitiveFrame checker.env shadow) :
    (checker.inHeaderAxiomView shadow semantic increase history primitives).mlctx = checker.mlctx := rfl

example (reader : Context) (stats : InductiveStats) (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (history : TrEnv safety reader.env semantic)
    (safetyBound : safety ≤ if isUnsafe then .unsafe else .safe)
    (sizes : stats.nindices.size = types.size)
    (models : List.Forall₂ (TrInductiveHeader semantic reader.lparams) types.toList headers)
    (typesWF : ∀ header ∈ headers, header.toVConstant.WF semantic) :
    (declareInductiveTypes stats nparams types numNested isUnsafe reader).WF fun actual =>
      ∃ shadow final, semantic.addInductHeaders headers = some final ∧ TrEnv safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) :=
  declareInductiveTypes.strongHeaderAxiomView reader stats nparams types numNested isUnsafe
    history safetyBound sizes models typesWF

example (checker : TypeChecker.VContext) (shadow : Kernel.Environment) (semantic : VEnv)
    (increase : checker.venv ≤ semantic) (history : TrEnv checker.safety shadow semantic)
    (primitives : NativePrimitiveFrame checker.env shadow)
    (initialWF : ({} : TypeChecker.VState).WF checker) :
    ({} : TypeChecker.VState).WF (checker.inHeaderAxiomView shadow semantic increase history primitives) :=
  TypeChecker.VState.WF.headerAxiomReset checker shadow semantic increase history primitives initialWF

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (safetyBound : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types
      (fun stats => declareInductiveTypes stats nparams types numNested isUnsafe) reader).WF
      fun actual => ∃ headers shadow final,
        List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types.toList headers ∧
        (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
        checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) :=
  checkInductiveTypes.strongHeaderAxiomView nparams types numNested isUnsafe checker reader
    aligned empty different constants definitions safetyBound

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (ordinarySafety : checker.safety ≠ .partial) :
    (AddInductive.run nparams types numNested reader).WF fun _ => ∃ headers actual shadow final,
      List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types headers ∧
      (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
      checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
      HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
      (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) :=
  AddInductive.run.headerAxiomViewStage nparams types numNested checker reader aligned empty
    different constants definitions ordinarySafety

example : ¬((.partial : DefinitionSafety) ≤ .unsafe) := by decide

private def sortType : Expr := .sort (.succ .zero)

private def sortAlias : DefinitionVal := {
  name := `HeaderViewSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
  value := sortType, hints := .abbrev, safety := .safe }

private def family (name : Name) (parameters indices : Nat) (domain : Expr := sortType) : InductiveType :=
  let tail := (List.range indices).foldr (fun _ body =>
    .forallE `index (.const ``Nat []) body .default) sortType
  let type := (List.range parameters).foldr (fun _ body => .forallE `parameter domain body .implicit) tail
  { name, type, ctors := [] }

private def sameConstant : Option ConstantInfo → Option ConstantInfo → Bool
  | none, none => true
  | some (.axiomInfo first), some (.axiomInfo second) => first == second
  | some (.defnInfo first), some (.defnInfo second) => first == second
  | some (.thmInfo first), some (.thmInfo second) => first == second
  | some (.opaqueInfo first), some (.opaqueInfo second) => first == second
  | some (.quotInfo first), some (.quotInfo second) =>
    first.toConstantVal == second.toConstantVal && match first.kind, second.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | some (.inductInfo first), some (.inductInfo second) =>
    first.toConstantVal == second.toConstantVal && first.numParams == second.numParams &&
      first.numIndices == second.numIndices && first.all == second.all && first.ctors == second.ctors &&
      first.numNested == second.numNested && first.isRec == second.isRec &&
      first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive
  | some (.ctorInfo first), some (.ctorInfo second) => first == second
  | some (.recInfo first), some (.recInfo second) => first == second
  | _, _ => false

private def checkAgreement (actual shadow : Kernel.Environment) : MetaM Unit := do
  for (name, info) in actual.constants.toList do
    let some reflected := shadow.find? name | throwError "header axiom view lost an actual row"
    unless headerTypeValue info == headerTypeValue reflected do
      throwError "header axiom view changed an actual type/value/safety/level/name signature"
  for (name, info) in shadow.constants.toList do
    let some reflected := actual.find? name | throwError "header axiom view invented a row"
    unless headerTypeValue info == headerTypeValue reflected do
      throwError "header axiom view changed a reflected signature"

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment)
    (nparams : Nat) (types : Array InductiveType) (universes : List Name := []) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl universes nparams types.toList false) none).isOk do
    throwError "native kernel rejected header axiom view fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let checked := checkInductiveTypes nparams types (fun stats => do
        let actual ← declareInductiveTypes stats nparams types 0 isUnsafe
        let infos := types.toList.map fun type =>
          match actual.find? type.name with
          | some (.inductInfo info) => info
          | _ => default
        let shadow := headerAxiomView env infos
        let current ← read
        pure (actual, shadow, stats, current)) reader
      let .ok (actual, shadow, stats, current) := checked
        | throwError "header axiom view checkpoint failed"
      checkAgreement actual shadow
      for (name, info) in env.constants.toList do
        unless sameConstant (actual.find? name) (some info) && sameConstant (shadow.find? name) (some info) do
          throwError "header axiom view changed an exact old record"
      for type in types do
        let some (.inductInfo actualInfo) := actual.find? type.name
          | throwError "header axiom view lost actual inductive metadata"
        let some (.axiomInfo shadowInfo) := shadow.find? type.name
          | throwError "header axiom view did not install its typed axiom row"
        unless actualInfo.type == type.type && shadowInfo.type == type.type &&
            shadowInfo.levelParams == universes && shadowInfo.isUnsafe == isUnsafe do
          throwError "header axiom view did not retain the exact source signature"
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (checkConstructors types stats isUnsafe { current with env := shadow }).isOk do
        throwError "ordinary constructor fixture did not check in both actual and axiom stages"
      let .ok final := AddInductive.run nparams types.toList 0 reader
        | throwError "header axiom view fixture did not complete its actual runner"
      for type in types do
        unless (final.find? (mkRecName type.name)).isSome do
          throwError "header axiom view fixture failed to reach recursor registration"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderAxiomView
    | throwError "header axiom view module absent"
  let mut allowed := []
  for name in [``checkName.WF, ``checkInductiveTypes.headersWF, ``checkInductiveTypes.headersChecker,
      ``NativeValueFrame.addConst, ``NativePrimitiveFrame.addConst,
      ``VEnv.HasPrimitives.mono_of_primitiveConstants] do
    allowed := allowed ++ (← collectAxioms name).toList
  for name in [``headerAxiomInfo, ``headerTypeValue, ``headerAxiomInfo.typeValue,
      ``HeaderAxiomAgreement, ``HeaderAxiomAgreement.refl, ``HeaderAxiomAgreement.none_iff,
      ``HeaderAxiomAgreement.values, ``HeaderAxiomAgreement.addHeader, ``headerAxiomView] do
    if (← collectAxioms name).contains ``sorryAx then
      throwError "header axiom view signature contract acquired an admission in {name}"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "header axiom view module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "header axiom view unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"header axiom view: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let .ok seededHost := host.addDeclCore 0 (.defnDecl sortAlias) none
    | throwError "native kernel rejected header axiom view seed definition"
  let .ok env := Lean4Lean.addDecl host.toKernelEnv (.defnDecl sortAlias) true
    | throwError "header axiom view seed definition failed"
  for parameters in [0, 1, 2] do
    checkBatch seededHost env parameters #[family `HeaderViewFirst parameters 0,
      family `HeaderViewSecond parameters 2 (.const sortAlias.name [])]
  let plain : InductiveType := {
    name := `HeaderViewPlain, type := sortType,
    ctors := [⟨`HeaderViewPlain.mk, .forallE `value (.const ``Nat []) (.const `HeaderViewPlain []) .default⟩] }
  checkBatch seededHost env 0 #[plain]
  let parametric : InductiveType := {
    name := `HeaderViewParametric,
    type := .forallE `A sortType sortType .implicit,
    ctors := [⟨`HeaderViewParametric.mk, .forallE `A sortType
      (.forallE `value (.bvar 0) (.app (.const `HeaderViewParametric []) (.bvar 1)) .default) .implicit⟩] }
  checkBatch seededHost env 1 #[parametric]
  let indexed : InductiveType := {
    name := `HeaderViewIndexed,
    type := .forallE `index (.const ``Nat []) sortType .default,
    ctors := [⟨`HeaderViewIndexed.mk, .forallE `index (.const ``Nat [])
      (.app (.const `HeaderViewIndexed []) (.bvar 0)) .default⟩] }
  checkBatch seededHost env 0 #[indexed]
  checkBatch seededHost env 0 #[{ name := `HeaderViewUniverse, type := .sort (.param `u), ctors := [] }] [`u]
  for isUnsafe in [false, true] do
    let reader : Context := {
      env, lparams := [], safety := if isUnsafe then .unsafe else .safe,
      allowPrimitive := false }
    let .ok empty := checkInductiveTypes 0 #[]
        (fun stats => declareInductiveTypes stats 0 #[] 0 isUnsafe) reader
      | throwError "empty header axiom view checkpoint failed"
    checkAgreement empty env
    for (name, info) in env.constants.toList do
      unless sameConstant (empty.find? name) (some info) do throwError "empty checkpoint changed its base"
    for types in [#[family `HeaderViewDuplicate 0 0, family `HeaderViewDuplicate 0 0],
        #[family sortAlias.name 0 0], #[family `HeaderViewBadFirst 1 0,
          family `HeaderViewBadSecond 1 0 (.sort .zero)]] do
      let nparams := if types.size == 2 && types[0]!.name == `HeaderViewBadFirst then 1 else 0
      if (checkInductiveTypes nparams types
          (fun stats => declareInductiveTypes stats nparams types 0 isUnsafe) reader).isOk then
        throwError "header axiom view accepted duplicate/colliding/later-domain failure"
    if (checkInductiveTypes 0 #[family `HeaderViewFuel 0 0] pure
        { reader with fuel := { inductiveFuel := 0 } }).isOk then
      throwError "header axiom view accepted zero fuel"
  let reader : Context := { env, lparams := [], safety := .safe, allowPrimitive := false }
  let .ok (actual, shadow) := checkInductiveTypes 0 #[plain] (fun stats => do
      let headers ← declareInductiveTypes stats 0 #[plain] 0 false
      let some (.inductInfo info) := headers.find? plain.name | throw .deepRecursion
      let shadowHeaders := headerAxiomView env [info]
      let actual ← withEnv headers (declareConstructors stats #[plain] false)
      let shadow ← withEnv shadowHeaders (declareConstructors stats #[plain] false)
      pure (actual, shadow)) reader
    | throwError "metadata transport negative fixture failed to stage"
  checkAgreement actual shadow
  let projection := .proj plain.name 0 (.app (.const `HeaderViewPlain.mk []) (.const ``Nat.zero []))
  unless (TypeChecker.checkType projection { env := actual } {}).isOk do
    throwError "actual metadata projection control failed"
  if (TypeChecker.checkType projection { env := shadow } {}).isOk then
    throwError "type/value agreement incorrectly preserved metadata-sensitive projection checking"
  logInfo "7 native-accepted header axiom views preserve all signatures and exact old records; both safeties/primitive flags, constructors, universes, empty/failure controls and metadata-sensitive projection non-transport passed"

end InductiveHeaderAxiomViewTest
