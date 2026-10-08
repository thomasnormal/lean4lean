import Lean4Lean.Verify.InductiveParams
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamContextTest

example : ParamContext 0 {} #[] := ParamContext.empty

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hcontext : ParamContext numParams lctx params) (fvar : FVarId) (name : Name)
    (domain : Expr) (bi : BinderInfo) :
    ParamContext (numParams + 1) (lctx.mkLocalDecl fvar name domain bi)
      (params.push (.fvar fvar)) :=
  hcontext.push fvar name domain bi

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hcontext : ParamContext numParams lctx params) : lctx.toList.length = numParams :=
  hcontext.length

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hcontext : ParamContext numParams lctx params) (param : Expr) (hparam : param ∈ params) :
    ∃ decl ∈ lctx.toList, decl.toExpr = param ∧
      decl.value? (allowNondep := true) = none ∧ decl.kind = .default :=
  hcontext.declaration hparam

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment)
    (state : State) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamContext numParams lctx params →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.context type numParams next env state post hnext

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamContext numParams result.1.1 result.1.2.2 :=
  withParams.getContext type numParams env state

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamPrefix numParams type result.1.2.1 result.1.2.2 ∧
        ParamContext numParams result.1.1 result.1.2.2 :=
  withParams.getContextPrefix type numParams env state

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run.loop numParams lctx params index fuel env state).WF fun result =>
      result.1.nparams = params.size ∧ result.1.lctx = lctx :=
  ElimNestedInductive.run.loop.frame numParams lctx params index fuel env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.ParamContext numParams :=
  ElimNestedInductive.run.paramContext fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.lctx.numIndices = numParams ∧ result.1.lctx.toList.length = numParams :=
  ElimNestedInductive.run.contextCount fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.ParamContext numParams :=
  ElimNestedInductive.run.paramContext_run' fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.nparams = result.1.lctx.numIndices :=
  (ElimNestedInductive.run.paramContext fuel numParams types env state).mono fun _ hcontext => by
    rcases hcontext.2 with ⟨params, hparams⟩
    exact hcontext.1.trans hparams.count.symm

private structure ExpectedParam where
  name : Name
  domain : Array Expr → Expr
  binderInfo : BinderInfo

private def checkDeclarations (lctx : LocalContext) (params : Array Expr)
    (expected : Array ExpectedParam) : MetaM Unit := do
  let entries := lctx.decls.toList
  unless lctx.numIndices == params.size && entries.length == params.size &&
      params.size == expected.size do
    throwError "incorrect extracted local-context size"
  for index in [:params.size] do
    let some (some decl) := entries[index]? | throwError "hole in parameter local declarations"
    let some specification := expected[index]? | throwError "missing parameter specification"
    unless decl.index == index && decl.toExpr == params[index]! &&
        decl.userName == specification.name && decl.type == specification.domain params &&
        decl.binderInfo == specification.binderInfo && decl.kind == .default &&
        !(decl.isLet (allowNondep := true)) do
      throwError "incorrect parameter declaration order, shape, or instantiated metadata"
    let some found := lctx.find? decl.fvarId | throwError "parameter absent from executable lookup"
    unless found.index == index && found.toExpr == decl.toExpr && found.type == decl.type do
      throwError "executable parameter lookup disagrees with declaration array"

private def checkExtraction (env : Kernel.Environment) (state : State) (type : Expr)
    (numParams : Nat) (expected : Array ExpectedParam) (accepted : Bool := true) : MetaM Unit := do
  match withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state with
  | .ok ((lctx, _, params), _) =>
    unless accepted && params.size == numParams do
      throwError "unexpected parameter-context extraction success"
    checkDeclarations lctx params expected
  | .error (.other message) =>
    unless !accepted && message ==
        "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected parameter-context extraction rejection: {message}"
  | .error _ => throwError "unexpected parameter-context extraction exception"

private def checkFixtures (env : Kernel.Environment) (state : State) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let tail := Expr.forallE Name.anonymous
    (.forallE `argument (.bvar 1) (.bvar 2) .default)
    (.forallE `namespaced.predicate (.sort .zero) sortType .default) .instImplicit
  let type := Expr.forallE `repeated sortType
    (.forallE `repeated (.bvar 0) tail .strictImplicit) .implicit
  let expected : Array ExpectedParam := #[
    { name := `repeated, domain := fun _ => sortType, binderInfo := .implicit },
    { name := `repeated, domain := fun params => params[0]!, binderInfo := .strictImplicit },
    { name := Name.anonymous,
      domain := fun params => .forallE `argument params[0]! params[0]! .default,
      binderInfo := .instImplicit },
    { name := `namespaced.predicate, domain := fun _ => .sort .zero, binderInfo := .default }]
  for numParams in [0, 1, 2, 3, 4] do
    checkExtraction env state type numParams (expected.extract 0 numParams)
  checkExtraction env state type 5 #[] false
  checkExtraction env state (.mdata {} type) 0 #[]
  checkExtraction env state (.mdata {} type) 1 #[] false
  let maskedTail := Expr.forallE `repeated sortType
    (.forallE `repeated (.bvar 0) (.mdata {} tail) .strictImplicit) .implicit
  checkExtraction env state maskedTail 2 (expected.extract 0 2)
  checkExtraction env state maskedTail 3 #[] false
  for numParams in [31, 32, 33, 64, 65] do
    let wide := (List.range numParams).foldr (fun index body =>
      Expr.forallE (.num `wide index) sortType body .default) sortType
    let expected := ((List.range numParams).map fun index =>
      ({ name := .num `wide index, domain := fun _ => sortType, binderInfo := .default } :
        ExpectedParam)).toArray
    checkExtraction env state wide numParams expected

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``ParamContext.empty, ``ParamContext.length, ``ParamContext.declaration,
      ``ElimNestedInductive.run.loop.frame] do
    audit theoremName
  for theoremName in [``ParamContext.push, ``withParams.context, ``withParams.getContext,
      ``ElimNestedInductive.run.paramContext, ``ElimNestedInductive.run.contextCount,
      ``ElimNestedInductive.run.paramContext_run'] do
    audit theoremName [``PersistentArray.toList'_push]
  audit ``withParams.getContextPrefix [``PersistentArray.toList'_push, ``Expr.instantiate1_eq]
  let env := (← Lean.getEnv).toKernelEnv
  checkFixtures env { lvls := [], newTypes := #[] }
  let seeded : State := {
    ngen := { namePrefix := `ContextSeed, idx := 17 },
    lvls := [.param `u],
    nestedAux := #[(.const ``Nat [], `StoredAux)],
    nextIdx := 7,
    newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] }
  checkFixtures env seeded

end InductiveParamContextTest
