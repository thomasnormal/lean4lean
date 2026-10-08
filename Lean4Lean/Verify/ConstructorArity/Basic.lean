import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem declareConstructors.arity_eq_add (type : Expr) (index : Nat) :
    arity index type = index + arity 0 type := by
  induction type generalizing index with
  | forallE name domain body bi ihDomain ihBody =>
    change arity (index + 1) body = index + arity 1 body
    rw [ihBody (index + 1), ihBody 1]
    omega
  | _ => simp [arity]

theorem declareConstructors.arity_instantiate1'_fvar
    (type : Expr) (fvar : FVarId) (index depth : Nat) :
    arity index (type.instantiate1' (.fvar fvar) depth) = arity index type := by
  induction type generalizing index depth with
  | bvar offset =>
    simp only [Expr.instantiate1']
    split
    · rfl
    · split <;> rfl
  | forallE name domain body bi ihDomain ihBody =>
    exact ihBody (index + 1) (depth + 1)
  | _ => rfl

theorem declareConstructors.arity_instantiate1_fvar
    (type : Expr) (fvar : FVarId) (index : Nat) :
    arity index (type.instantiate1 (.fvar fvar)) = arity index type := by
  rw [Expr.instantiate1_eq]
  exact arity_instantiate1'_fvar type fvar index 0

theorem declareConstructors.arity_instantiate1_of_isFVar
    (type param : Expr) (index : Nat) (hparam : param.isFVar = true) :
    arity index (type.instantiate1 param) = arity index type := by
  cases param <;> simp [Expr.isFVar] at hparam
  exact arity_instantiate1_fvar type _ index

theorem whnf_arity (type : Expr) (ctx : Context) :
    ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF fun result =>
      declareConstructors.arity 0 type ≤ declareConstructors.arity 0 result := by
  intro result hresult
  change (TypeChecker.whnf type).run ctx.env ctx.safety ctx.lctx ctx.lparams ctx.fuel =
    .ok result at hresult
  cases type <;> try exact Nat.zero_le _
  rename_i name domain body bi
  change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf
    (.forallE name domain body bi)
    { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
      lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
  cases hdepth : ctx.fuel.recDepth with
  | zero =>
    rw [hdepth] at hresult
    change Except.error Lean.Kernel.Exception.deepRecursion = .ok result at hresult
    cases hresult
  | succ depth =>
    rw [hdepth] at hresult
    change Except.ok (.forallE name domain body bi) = .ok result at hresult
    cases hresult
    exact Nat.le_refl _

theorem whnf_instantiate_arity (name : Name) (domain body : Expr) (bi : BinderInfo)
    (param : Expr) (ctx : Context) (hfvar : param.isFVar = true) :
    ((monadLift (TypeChecker.whnf (body.instantiate1 param)) : M Expr) ctx).WF fun result =>
      declareConstructors.arity 0 (.forallE name domain body bi) ≤
        1 + declareConstructors.arity 0 result := by
  refine (whnf_arity (body.instantiate1 param) ctx).mono ?_
  intro result hbound
  rw [declareConstructors.arity_instantiate1_of_isFVar body param 0 hfvar] at hbound
  change declareConstructors.arity 1 body ≤ _
  rw [declareConstructors.arity_eq_add]
  omega

end Lean4Lean.AddInductive
