import Lean4Lean.Verify.InductiveMetadata
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveMetadataTest

example (numParams : Nat) (types : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams types (fun stats => do
      let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
      withEnv headers do
        checkConstructors types stats isUnsafe
        let env ← declareConstructors stats types isUnsafe
        pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
          (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
          result.1.HeaderMetadata numParams types numNested isUnsafe ctx.lparams result.2 ∧
          result.1.ConstructorMetadata ctx.lparams types isUnsafe result.2 ∧
          result.1.ParamsCount numParams types.size ∧
          DeclaredParameterMetadata numParams types result.2 :=
  checkInductiveTypes.registeredParameterMetadata numParams types numNested isUnsafe ctx hwf

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (lparams : List Name) (env : Kernel.Environment)
    (hcount : stats.ParamsCount numParams types.size)
    (hheaders : stats.HeaderMetadata numParams types numNested isUnsafe lparams env)
    (hctors : stats.ConstructorMetadata lparams types isUnsafe env) :
    DeclaredParameterMetadata numParams types env :=
  stats.declaredParameterMetadata numParams types numNested isUnsafe lparams env
    hcount hheaders hctors

example (numParams : Nat) (env : Kernel.Environment) :
    DeclaredParameterMetadata numParams #[] env := by
  intro index hindex
  simp only [Array.size_empty] at hindex
  omega

example (numParams : Nat) (types : Array InductiveType) (env : Kernel.Environment)
    (hmetadata : DeclaredParameterMetadata numParams types env)
    (index : Nat) (hindex : index < types.size) (ctorIndex : Nat) (ctor : Constructor)
    (hctor : types[index].ctors[ctorIndex]? = some ctor)
    (header : InductiveVal) (info : ConstructorVal)
    (hheader : env.find? types[index].name = some (.inductInfo header))
    (hlookup : env.find? ctor.name = some (.ctorInfo info)) :
    header.numParams = info.numParams ∧ info.numParams = numParams ∧
      info.numParams + info.numFields = declareConstructors.arity 0 ctor.type := by
  obtain ⟨header', info', hheader', hlookup', hparams, hcount, harity⟩ :=
    hmetadata index hindex ctorIndex ctor hctor
  rw [hheader] at hheader'
  rw [hlookup] at hlookup'
  have hheaders := ConstantInfo.inductInfo.inj (Option.some.inj hheader')
  have hinfos := ConstantInfo.ctorInfo.inj (Option.some.inj hlookup')
  subst header'
  subst info'
  exact ⟨hparams.trans hcount.symm, hcount, harity⟩

example (numParams : Nat) (types : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (hnonempty : types.size ≠ 0) :
    (checkInductiveTypes numParams types (fun stats => do
      let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
      withEnv headers do
        checkConstructors types stats isUnsafe
        let env ← declareConstructors stats types isUnsafe
        pure (stats, env)) ctx).WF fun result => result.1.params.size = numParams ∧
          DeclaredParameterMetadata numParams types result.2 :=
  (checkInductiveTypes.registeredParameterMetadata numParams types numNested isUnsafe ctx
    hwf).mono fun _ hmetadata =>
      ⟨by simpa only [InductiveStats.ParamsCount, hnonempty, ite_false] using
          hmetadata.2.2.2.2.1, hmetadata.2.2.2.2.2⟩

example (numParams numNested : Nat) (isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams #[] (fun stats => do
      let headers ← declareInductiveTypes stats numParams #[] numNested isUnsafe
      withEnv headers do
        checkConstructors #[] stats isUnsafe
        let env ← declareConstructors stats #[] isUnsafe
        pure (stats, env)) ctx).WF fun result => result.1.params.size = 0 ∧
          DeclaredParameterMetadata numParams #[] result.2 :=
  (checkInductiveTypes.registeredParameterMetadata numParams #[] numNested isUnsafe ctx
    hwf).mono fun _ hmetadata =>
      ⟨by simpa only [InductiveStats.ParamsCount, Array.size_empty, ite_true] using
          hmetadata.2.2.2.2.1, hmetadata.2.2.2.2.2⟩

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (hsize : stats.nindices.size = types.size) :
    (declareInductiveTypes stats numParams types numNested isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
        stats.HeaderMetadata numParams types numNested isUnsafe ctx.lparams env :=
  declareInductiveTypes.metadata stats numParams types numNested isUnsafe ctx hwf hsize

example (numParams : Nat) (types : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams types (fun stats => do
      let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
      withEnv headers do
        checkConstructors types stats isUnsafe
        let env ← declareConstructors stats types isUnsafe
        pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
          (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
          result.1.HeaderMetadata numParams types numNested isUnsafe ctx.lparams result.2 ∧
          result.1.ConstructorMetadata ctx.lparams types isUnsafe result.2 :=
  checkInductiveTypes.registeredConstructorMetadata numParams types numNested isUnsafe ctx hwf

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (lparams : List Name) (env : Kernel.Environment)
    (hheaders : stats.HeaderMetadata numParams types numNested isUnsafe lparams env)
    (index : Nat) (hindex : index < types.size) :
    env.find? types[index].name = some (.inductInfo
      (declareInductiveTypes.metadataVal stats numParams types numNested isUnsafe lparams
        types[index] stats.nindices[index]!)) :=
  hheaders index hindex

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (hsize : stats.nindices.size = types.size) (env : Kernel.Environment)
    (hdeclare : declareInductiveTypes stats numParams types numNested isUnsafe ctx = .ok env)
    (name : Name) (info : ConstantInfo) (hold : ctx.env.find? name = some info) :
    env.find? name = some info :=
  (declareInductiveTypes.metadata stats numParams types numNested isUnsafe ctx hwf hsize
    _ hdeclare).2.1 name info hold

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (lparams : List Name) (env : Kernel.Environment)
    (hheaders : stats.HeaderMetadata numParams types numNested isUnsafe lparams env)
    (index : Nat) (hindex : index < types.size) (info : InductiveVal)
    (hlookup : env.find? types[index].name = some (.inductInfo info)) :
    info.numParams = numParams ∧ info.numIndices = stats.nindices[index]! ∧
      info.numNested = numNested ∧ info.all = (types.map (·.name)).toList ∧
      info.ctors = types[index].ctors.map (·.name) := by
  have hrecord := hheaders index hindex
  rw [hlookup] at hrecord
  have heq := ConstantInfo.inductInfo.inj (Option.some.inj hrecord)
  rw [heq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

example (numParams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) :
    let ctx : Context := {
      env := .empty `InductiveMetadataTest, lparams, safety := .safe, allowPrimitive := false }
    (checkInductiveTypes numParams types (fun stats => do
      let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
      withEnv headers do
        checkConstructors types stats isUnsafe
        let env ← declareConstructors stats types isUnsafe
        pure (stats, env)) ctx).WF fun result =>
          result.1.HeaderMetadata numParams types numNested isUnsafe lparams result.2 ∧
          result.1.ConstructorMetadata lparams types isUnsafe result.2 :=
  (checkInductiveTypes.registeredConstructorMetadata numParams types numNested isUnsafe _
    SMap.WF.empty).mono fun _ hmetadata => hmetadata.2.2

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (numParams : Nat) (body : Expr) : Expr :=
  numParams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (numParams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams numParams sortType, ctors }

private def checkedPrefix (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) : M (InductiveStats × Kernel.Environment) :=
  checkInductiveTypes numParams types fun stats => do
    let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
    withEnv headers do
      checkConstructors types stats isUnsafe
      let env ← declareConstructors stats types isUnsafe
      pure (stats, env)

private def checkHeader (stats : InductiveStats) (ctx : Context) (env : Kernel.Environment)
    (numParams : Nat) (types : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (index : Nat) : MetaM Unit := do
  let type := types[index]!
  let some (.inductInfo actual) := env.find? type.name | throwError "missing header {type.name}"
  let expected := declareInductiveTypes.metadataVal stats numParams types numNested isUnsafe
    ctx.lparams type stats.nindices[index]!
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.numParams == expected.numParams &&
      actual.numIndices == expected.numIndices && actual.numNested == expected.numNested &&
      actual.all == expected.all && actual.ctors == expected.ctors &&
      actual.isRec == expected.isRec && actual.isReflexive == expected.isReflexive &&
      actual.isUnsafe == expected.isUnsafe do
    throwError "incorrect final header metadata for {type.name}"

private def checkCtor (stats : InductiveStats) (ctx : Context) (env : Kernel.Environment)
    (numParams : Nat) (isUnsafe : Bool) (type : InductiveType) (index : Nat)
    (ctor : Constructor) : MetaM Unit := do
  let some (.ctorInfo actual) := env.find? ctor.name | throwError "missing constructor {ctor.name}"
  let some (.inductInfo parent) := env.find? type.name | throwError "missing final parent"
  let expected := declareConstructors.metadataVal stats ctx.lparams isUnsafe type.name index ctor
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.induct == expected.induct &&
      actual.cidx == expected.cidx && actual.numParams == expected.numParams &&
      actual.numFields == expected.numFields && actual.isUnsafe == expected.isUnsafe do
    throwError "incorrect final constructor metadata for {ctor.name}"
  unless actual.numParams + actual.numFields == declareConstructors.arity 0 ctor.type do
    throwError "final field subtraction truncated"
  unless parent.numParams == numParams && actual.numParams == numParams &&
      parent.numParams == actual.numParams do
    throwError "declared header/constructor parameter counts disagree"

private def checkPrefix (ctx : Context) (numParams : Nat) (types : Array InductiveType)
    (isUnsafe expected : Bool) (numNested : Nat := 0) : MetaM Unit := do
  let result := checkedPrefix numParams types numNested isUnsafe ctx
  unless result.isOk == expected do
    throwError "incorrect registered-prefix outcome for {types.map (·.name)}"
  if let .ok (stats, env) := result then
    unless stats.nindices.size == types.size && stats.indConsts.size == types.size &&
        stats.params.size == (if types.isEmpty then 0 else numParams) do
      throwError "incorrect full-prefix statistics"
    for index in [:types.size] do
      checkHeader stats ctx env numParams types numNested isUnsafe index
      let type := types[index]!
      for ctorIndex in [:type.ctors.length] do
        checkCtor stats ctx env numParams isUnsafe type ctorIndex type.ctors[ctorIndex]!
      if env.contains (type.name ++ `rec) then
        throwError "numeric prefix generated a recursor"
    for name in [``Nat, ``Nat.zero, ``Nat.succ, ``List] do
      let some original := ctx.env.find? name | throwError "missing old-entry fixture"
      let some retained := env.find? name | throwError "numeric prefix dropped {name}"
      unless original.name == retained.name && original.type == retained.type &&
          original.levelParams == retained.levelParams && original.safety == retained.safety do
        throwError "numeric prefix changed {name}"

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
  let arity := [``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq,
    ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``declareInductiveTypes.metadata maps
  audit ``InductiveStats.declaredParameterMetadata []
  audit ``checkInductiveTypes.registeredParameterMetadata (maps ++ arity)
  audit ``checkInductiveTypes.registeredConstructorMetadata (maps ++ arity)
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let leaf := Expr.const `PrefixLeaf []
  let one := Expr.const `PrefixOne []
  let two := Expr.const `PrefixTwo []
  let left := Expr.const `PrefixLeft []
  let right := Expr.const `PrefixRight []
  let indexed := Expr.const `PrefixIndexed []
  let natType := Expr.const ``Nat []
  let leafCtor : Constructor := { name := `PrefixLeaf.base, type := leaf }
  let recursive : Constructor := {
    name := `PrefixLeaf.recursive, type := .forallE `previous leaf leaf .default }
  let reflexive : Constructor := {
    name := `PrefixLeaf.reflexive,
    type := .forallE `function (.forallE `index natType leaf .default) leaf .default }
  let oneCtor : Constructor := { name := `PrefixOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let twoCtor : Constructor := {
    name := `PrefixTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let twoField : Constructor := {
    name := `PrefixTwo.field, type := closeParams 2
      (.forallE `value (.bvar 1) (.mkAppList two [.bvar 2, .bvar 1]) .strictImplicit) }
  let missing : Constructor := {
    name := `PrefixTwo.missing, type := closeParams 1 (.mkAppList two [.bvar 0, natType]) }
  let mutualTypes : Array InductiveType := #[
    header `PrefixLeft 0 [{ name := `PrefixLeft.base, type := left },
      { name := `PrefixLeft.link, type := .forallE `right right left .default }],
    header `PrefixEmpty 0 [],
    header `PrefixRight 0 [{ name := `PrefixRight.link, type := .forallE `left left right .default }]]
  let indexedHeader : InductiveType := {
    name := `PrefixIndexed, type := closeParams 1 (.forallE `index natType sortType .default),
    ctors := [
      { name := `PrefixIndexed.base,
        type := closeParams 1 (.mkAppList indexed [.bvar 0, .const ``Nat.zero []]) }] }
  let polySort := Expr.sort (.param `u)
  let polyBody := Expr.forallE `value (.bvar 0)
    (.app (.const `PrefixPoly [.param `u]) (.bvar 1)) .default
  let polymorphic : InductiveType := {
    name := `PrefixPoly, type := .forallE `parameter polySort polySort .implicit,
    ctors := [{ name := `PrefixPoly.mk, type := .forallE `parameter polySort polyBody .implicit }] }
  let natZero := Expr.const ``Nat.zero []
  let doubleCtor : Constructor := {
    name := `PrefixDouble.base, type := .mkAppList (.const `PrefixDouble []) [natZero, natZero] }
  let doubleIndexed : InductiveType := {
    name := `PrefixDouble,
    type := .forallE `first natType (.forallE `second natType sortType .default) .implicit,
    ctors := [doubleCtor] }
  let singleIndexed : InductiveType := {
    name := `PrefixSingle, type := .forallE `index natType sortType .default,
    ctors := [{ name := `PrefixSingle.base, type := .app (.const `PrefixSingle []) natZero }] }
  for isUnsafe in [false, true] do
    let ctx := { ctx with safety := if isUnsafe then .unsafe else .safe }
    checkPrefix ctx 0 #[] isUnsafe true
    checkPrefix ctx 1 #[header `PrefixOne 1 []] isUnsafe true
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [leafCtor]] isUnsafe true
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [leafCtor, recursive]] isUnsafe true
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [leafCtor, reflexive]] isUnsafe true
    checkPrefix ctx 1 #[header `PrefixOne 1 [oneCtor]] isUnsafe true
    checkPrefix ctx 2 #[header `PrefixTwo 2 [twoCtor, twoField]] isUnsafe true
    checkPrefix ctx 0 mutualTypes isUnsafe true 7
    checkPrefix ctx 1 #[indexedHeader] isUnsafe true
    checkPrefix ctx 0 #[doubleIndexed, header `PrefixNoIndex 0 [], singleIndexed] isUnsafe true
    checkPrefix { ctx with lparams := [`u] } 1 #[polymorphic] isUnsafe true
    checkPrefix { ctx with
      lctx := ctx.lctx.mkLocalDecl ⟨`Ambient⟩ `ambient sortType,
      ngen := { namePrefix := `PrefixFresh, idx := 11 }, allowPrimitive := true }
      1 #[header `PrefixOne 1 [oneCtor]] isUnsafe true
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [leafCtor], header `PrefixLeaf 0 []] isUnsafe false
    checkPrefix ctx 0 #[header ``Nat 0 []] isUnsafe false
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [leafCtor, leafCtor]] isUnsafe false
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [{ leafCtor with name := `PrefixOther }],
      header `PrefixOther 0 []] isUnsafe false
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [{ leafCtor with name := ``Nat.zero }]] isUnsafe false
    checkPrefix ctx 2 #[header `PrefixTwo 2 [twoCtor, missing]] isUnsafe false
    checkPrefix ctx 0 #[header `PrefixLeaf 0 [{ leafCtor with type := natType }]] isUnsafe false
    checkPrefix { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
      0 #[header `PrefixLeaf 0 [leafCtor]] isUnsafe false
    checkPrefix { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
      2 #[header `PrefixTwo 2 [twoCtor, twoField]] isUnsafe false

end InductiveMetadataTest
