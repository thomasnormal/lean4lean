import Lean4Lean.Verify.InductiveStats

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem InductiveStats.ParamsAreFVars.arity_instantiate1
    {stats : InductiveStats} (hstats : stats.ParamsAreFVars)
    {param : Expr} (hparam : param ∈ stats.params) (type : Expr) (index : Nat) :
    declareConstructors.arity index (type.instantiate1 param) =
      declareConstructors.arity index type :=
  declareConstructors.arity_instantiate1_of_isFVar type param index (hstats param hparam)

theorem declareConstructors.arity_consume_fvar
    (name : Name) (domain body : Expr) (bi : BinderInfo) (fvar : FVarId) (index : Nat) :
    arity index (.forallE name domain body bi) =
      arity (index + 1) (body.instantiate1 (.fvar fvar)) :=
  (arity_instantiate1_fvar body fvar (index + 1)).symm

theorem InductiveStats.ParamsAreFVars.arity_consume
    {stats : InductiveStats} (hstats : stats.ParamsAreFVars)
    {param : Expr} (hparam : param ∈ stats.params)
    (name : Name) (domain body : Expr) (bi : BinderInfo) (index : Nat) :
    declareConstructors.arity index (.forallE name domain body bi) =
      declareConstructors.arity (index + 1) (body.instantiate1 param) :=
  (hstats.arity_instantiate1 hparam body (index + 1)).symm

theorem checkInductiveTypes.parameterArity (nparams : Nat) (indTypes : Array InductiveType)
    (ctx : Context) :
    (checkInductiveTypes nparams indTypes pure ctx).WF fun stats =>
      ∀ param ∈ stats.params, ∀ type index,
        declareConstructors.arity index (type.instantiate1 param) =
          declareConstructors.arity index type :=
  (checkInductiveTypes.getParamsFVars nparams indTypes ctx).mono
    fun _ hstats _ hparam type index => hstats.arity_instantiate1 hparam type index

end Lean4Lean.AddInductive
