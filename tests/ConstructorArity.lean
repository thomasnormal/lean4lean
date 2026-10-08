import Lean4Lean.Verify.ConstructorArity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace ConstructorArityTest

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats)
    (param : Expr) (hparam : param ∈ stats.params) : param.isFVar = true :=
  checkInductiveTypes.getParamsFVars nparams types ctx stats hcheck param hparam

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (stats : InductiveStats) (hcheck : checkInductiveTypes nparams types pure ctx = .ok stats)
    (param : Expr) (hparam : param ∈ stats.params) (type : Expr) (index : Nat) :
    declareConstructors.arity index (type.instantiate1 param) =
      declareConstructors.arity index type :=
  checkInductiveTypes.parameterArity nparams types ctx stats hcheck param hparam type index

example (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (post : α → Prop)
    (hnext : ∀ stats ctx', stats.HeaderSizes types.size → stats.ParamsAreFVars →
      ctx'.env = ctx.env → (next stats ctx').WF post) :
    (checkInductiveTypes nparams types next ctx).WF post :=
  checkInductiveTypes.frameHeaderSizesParamsFVars nparams types next ctx post
    fun stats ctx' hsizes hfvars hframe => hnext stats ctx' hsizes hfvars hframe.env

example (stats : InductiveStats) (hfvars : stats.ParamsAreFVars)
    (param : Expr) (hparam : param ∈ stats.params) (body domain : Expr) (index : Nat) :
    declareConstructors.arity index (.forallE `field domain body .default) =
      declareConstructors.arity (index + 1) (body.instantiate1 param) :=
  hfvars.arity_consume hparam `field domain body .default index

private def nestedType (body : Expr) : Expr :=
  .forallE `first (.sort .zero)
    (.forallE `second (.bvar 0) (.forallE `third (.bvar 1) body .strictImplicit) .implicit)
    .default

private def expressions : Array Expr :=
  #[.bvar 0, .bvar 1, .bvar 2, .bvar 3, .fvar ⟨`existing⟩, .mvar ⟨`meta⟩,
    .sort .zero, .const ``Nat [], .lit (.natVal 3), .app (.bvar 0) (.bvar 1),
    .lam `value (.bvar 0) (nestedType (.bvar 1)) .default,
    .letE `value (.sort .zero) (.bvar 0) (nestedType (.bvar 1)) false,
    .mdata {} (nestedType (.bvar 0)), .proj `Record 0 (nestedType (.bvar 0)),
    nestedType (.bvar 3), nestedType (.app (.const `Result []) (.bvar 2))]

private def checkArity (type : Expr) (index depth : Nat) : MetaM Unit := do
  let param := Expr.fvar ⟨`parameter⟩
  let arity := declareConstructors.arity index type
  unless arity == index + declareConstructors.arity 0 type do
    throwError "incorrect constructor arity offset"
  unless declareConstructors.arity index (type.instantiate1' param depth) == arity &&
      declareConstructors.arity index (type.instantiate1 param) == arity do
    throwError "free-variable substitution changed the constructor telescope"
  let binder := Expr.forallE `field (.sort .zero) type .default
  unless declareConstructors.arity index binder ==
      declareConstructors.arity (index + 1) (type.instantiate1 param) do
    throwError "consuming a binder changed total constructor arity"

private def audit (theoremName : Name) (instantiation : Bool := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        (instantiation && axiomName == ``Expr.instantiate1_eq) do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``InductiveStats.ParamsAreFVars.push
  audit ``checkInductiveTypes.frameHeaderSizesParamsFVars
  audit ``checkInductiveTypes.paramsFVars
  audit ``checkInductiveTypes.getParamsFVars
  audit ``declareConstructors.arity_eq_add
  audit ``declareConstructors.arity_instantiate1'_fvar
  audit ``declareConstructors.arity_instantiate1_fvar true
  audit ``declareConstructors.arity_instantiate1_of_isFVar true
  audit ``InductiveStats.ParamsAreFVars.arity_instantiate1 true
  audit ``declareConstructors.arity_consume_fvar true
  audit ``InductiveStats.ParamsAreFVars.arity_consume true
  audit ``checkInductiveTypes.parameterArity true
  for type in expressions do
    for index in [0, 1, 4] do
      for depth in [0, 1, 2, 4] do
        checkArity type index depth
  let replacement := nestedType (.sort .zero)
  unless declareConstructors.arity 0 ((Expr.bvar 0).instantiate1 replacement) == 3 &&
      declareConstructors.arity 0 (.bvar 0) == 0 do
    throwError "arbitrary substitution must not satisfy the free-variable arity theorem"
  unless declareConstructors.arity 0 (.mdata {} replacement) == 0 &&
      declareConstructors.arity 0 (.letE `alias (.sort .zero) (.sort .zero) replacement false) == 0 do
    throwError "constructor metadata counts raw binders, not reduced or annotation-stripped types"

end ConstructorArityTest
