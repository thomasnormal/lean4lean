import Lean4Lean.Verify.InductiveMetadata
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveArityTest

example (type : Expr) (ctx : Context) :
    ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF fun result =>
      declareConstructors.arity 0 type ≤ declareConstructors.arity 0 result :=
  whnf_arity type ctx

example (name : Name) (domain body : Expr) (bi : BinderInfo) (param : Expr) (ctx : Context)
    (hfvar : param.isFVar = true) :
    ((monadLift (TypeChecker.whnf (body.instantiate1 param)) : M Expr) ctx).WF fun result =>
      declareConstructors.arity 0 (.forallE name domain body bi) ≤
        1 + declareConstructors.arity 0 result :=
  whnf_instantiate_arity name domain body bi param ctx hfvar

example (numParams : Nat) (types : Array InductiveType) (ctx : Context) :
    (checkInductiveTypes numParams types pure ctx).WF fun stats =>
      stats.HeaderArities numParams types :=
  checkInductiveTypes.getHeaderArities numParams types ctx

example (numParams : Nat) (types : Array InductiveType) (ctx : Context)
    (stats : InductiveStats) (hcheck : checkInductiveTypes numParams types pure ctx = .ok stats)
    (index : Nat) (hindex : index < types.size) :
    declareConstructors.arity 0 types[index].type ≤ numParams + stats.nindices[index]! :=
  checkInductiveTypes.getHeaderArities numParams types ctx stats hcheck index hindex

example (numParams : Nat) (types : Array InductiveType) (ctx : Context)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats current, stats.HeaderArities numParams types → (next stats current).WF post) :
    (checkInductiveTypes numParams types next ctx).WF post :=
  checkInductiveTypes.headerArities numParams types next ctx post hnext

example (numParams : Nat) (types : Array InductiveType) (ctx : Context)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats current, stats.HeaderSizes types.size → stats.HeaderArities numParams types →
      stats.ParamsCount numParams types.size → stats.ParamsAreFVars →
      stats.params.toList.Nodup → ctx.HeaderFrame current → (next stats current).WF post) :
    (checkInductiveTypes numParams types next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct numParams types next ctx post hnext

example (numParams : Nat) (ctx : Context) :
    (checkInductiveTypes numParams #[] pure ctx).WF fun stats =>
      stats.HeaderArities numParams #[] :=
  checkInductiveTypes.getHeaderArities numParams #[] ctx

example (stats : InductiveStats) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (lparams : List Name) (env : Kernel.Environment)
    (harities : stats.HeaderArities numParams types)
    (hheaders : stats.HeaderMetadata numParams types numNested isUnsafe lparams env) :
    DeclaredHeaderArities numParams types env :=
  stats.declaredHeaderArities numParams types numNested isUnsafe lparams env harities hheaders

example (numParams : Nat) (types : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams types (fun stats => do
      let headers ← declareInductiveTypes stats numParams types numNested isUnsafe
      withEnv headers do
        checkConstructors types stats isUnsafe
        let env ← declareConstructors stats types isUnsafe
        pure (stats, env)) ctx).WF fun result =>
          result.1.HeaderArities numParams types ∧ DeclaredHeaderArities numParams types result.2 :=
  (checkInductiveTypes.registeredHeaderArities numParams types numNested isUnsafe ctx hwf).mono
    fun _ hmetadata => hmetadata.2.2.2.2.2.2

example (numParams : Nat) (types : Array InductiveType) (env : Kernel.Environment)
    (harities : DeclaredHeaderArities numParams types env) (index : Nat)
    (hindex : index < types.size) (header : InductiveVal)
    (hlookup : env.find? types[index].name = some (.inductInfo header)) :
    declareConstructors.arity 0 header.type ≤ header.numParams + header.numIndices := by
  obtain ⟨header', hheader', _, hbound⟩ := harities index hindex
  rw [hlookup] at hheader'
  have heq := ConstantInfo.inductInfo.inj (Option.some.inj hheader')
  subst header'
  exact hbound

abbrev HiddenIndex := Nat → Type
abbrev HiddenParameter := Type → Type
abbrev HiddenTail (parameter : Type) := parameter → Type

private def sortType : Expr := .sort (.succ .zero)

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def checkedPrefix (numParams : Nat) (types : Array InductiveType)
    (isUnsafe : Bool) : M (InductiveStats × Kernel.Environment) :=
  checkInductiveTypes numParams types fun stats => do
    let headers ← declareInductiveTypes stats numParams types 0 isUnsafe
    withEnv headers do
      checkConstructors types stats isUnsafe
      let env ← declareConstructors stats types isUnsafe
      pure (stats, env)

private def checkFixture (env : Lean.Environment) (numParams : Nat)
    (types : Array InductiveType) (indices rawArities : Array Nat) (isUnsafe : Bool)
    (nativeAccepted : Bool := true) : MetaM Unit := do
  let ctx : Context := {
    env := env.toKernelEnv, lparams := [], allowPrimitive := false,
    safety := if isUnsafe then .unsafe else .safe }
  let .ok (stats, checked) := checkedPrefix numParams types isUnsafe ctx
    | throwError "rejected normalized header fixture {types.map (·.name)}"
  unless stats.nindices == indices && stats.params.size == numParams do
    throwError "incorrect normalized header counts"
  logInfo m!"normalization fixture {types.map (·.name)}: parameters = {numParams}, indices = {indices}"
  let native := env.addDeclCore 0
    (.inductDecl [] numParams types.toList isUnsafe) none
  let complete := Lean4Lean.addDecl env.toKernelEnv
    (.inductDecl [] numParams types.toList isUnsafe)
  unless complete.isOk == nativeAccepted do
    throwError "full frontend disagrees with native parameter-prefix acceptance"
  match native with
  | .ok _ =>
    unless nativeAccepted do throwError "native kernel accepted a hidden-parameter fixture"
  | .error (.other message) =>
    unless !nativeAccepted &&
        message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected native kernel rejection: {message}"
  | .error _ => throwError "unexpected native kernel error"
  for index in [:types.size] do
    let type := types[index]!
    let some (.inductInfo actual) := checked.find? type.name
      | throwError "missing normalized header"
    let raw := declareConstructors.arity 0 type.type
    unless raw == rawArities[index]! && actual.type == type.type &&
        actual.numParams == numParams && actual.numIndices == indices[index]! &&
        raw ≤ actual.numParams + actual.numIndices do
      throwError "incorrect normalization-aware header metadata"
    if let .ok native := native then
      let some (.inductInfo reference) := native.find? type.name
        | throwError "missing native normalized header"
      unless actual.numParams == reference.numParams && actual.numIndices == reference.numIndices do
        throwError "normalized header counts disagree with native kernel"
    if let .ok complete := complete then
      let some (.inductInfo installed) := complete.find? type.name
        | throwError "missing full-frontend normalized header"
      unless installed.numParams == actual.numParams && installed.numIndices == actual.numIndices &&
          complete.contains (type.name ++ `rec) do
        throwError "incorrect full-frontend normalized header or missing recursor"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        interfaces.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``whnf_arity
  audit ``whnf_instantiate_arity [``Expr.instantiate1_eq]
  let instantiate := [``Expr.instantiate1_eq]
  audit ``checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct instantiate
  audit ``checkInductiveTypes.headerArities instantiate
  audit ``checkInductiveTypes.getHeaderArities instantiate
  audit ``InductiveStats.declaredHeaderArities
  audit ``checkInductiveTypes.registeredHeaderArities (instantiate ++
    [``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
      ``Lean.PersistentHashMap.WF.toList'_insert, ``Expr.eqv_eq, ``Expr.hasFVar_eq,
      ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq])
  let env ← Lean.getEnv
  let explicit := Expr.forallE `parameter sortType
    (.forallE `index (.const ``Nat []) sortType .default) .implicit
  let hiddenTail := Expr.forallE `parameter sortType
    (.app (.const ``HiddenTail []) (.bvar 0)) .implicit
  let beta := Expr.app (.lam `unused sortType explicit .default) (.const ``Nat [])
  let letType := Expr.letE `family (.sort (.succ (.succ .zero))) explicit (.bvar 0) false
  for isUnsafe in [false, true] do
    checkFixture env 1 #[header `ArityExplicit explicit] #[1] #[2] isUnsafe
    checkFixture env 0 #[header `ArityIndex (.const ``HiddenIndex [])] #[1] #[0] isUnsafe
    checkFixture env 0 #[header `ArityParameterIndex (.const ``HiddenParameter [])] #[1] #[0] isUnsafe
    checkFixture env 1 #[header `ArityParameter (.const ``HiddenParameter [])] #[0] #[0] isUnsafe false
    checkFixture env 1 #[header `ArityTail hiddenTail] #[1] #[1] isUnsafe
    checkFixture env 2 #[header `ArityTailParameter hiddenTail] #[0] #[1] isUnsafe false
    checkFixture env 0 #[header `ArityAnnotatedIndices (.mdata {} explicit)] #[2] #[0] isUnsafe
    checkFixture env 0 #[header `ArityBetaIndices beta] #[2] #[0] isUnsafe
    checkFixture env 0 #[header `ArityLetIndices letType] #[2] #[0] isUnsafe
    checkFixture env 1 #[header `ArityAnnotated (.mdata {} explicit)] #[1] #[0] isUnsafe false
    checkFixture env 1 #[header `ArityBeta beta] #[1] #[0] isUnsafe false
    checkFixture env 1 #[header `ArityLet letType] #[1] #[0] isUnsafe false
    checkFixture env 1 #[header `ArityLeft hiddenTail, header `ArityRight hiddenTail]
      #[1, 1] #[1, 1] isUnsafe

end InductiveArityTest
