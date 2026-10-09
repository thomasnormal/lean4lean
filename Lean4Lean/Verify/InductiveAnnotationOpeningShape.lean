import Lean4Lean.Verify.InductiveAnnotationModel

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem instantiate1'_fvar_isAppOfArity (expression : Expr) (id : FVarId) (depth : Nat)
    (name : Name) (arity : Nat) :
    (expression.instantiate1' (.fvar id) depth).isAppOfArity name arity =
      expression.isAppOfArity name arity := by
  induction expression generalizing depth arity with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · cases arity <;> rfl
      · cases arity <;> rfl
  | app function argument ihFn ihArg =>
    cases arity with
    | zero => rfl
    | succ arity => exact ihFn depth arity
  | _ => cases arity <;> rfl

theorem instantiate1'_fvar_eq_const_iff {expression : Expr} {id : FVarId} {depth : Nat}
    {name : Name} {levels : List Level} :
    expression.instantiate1' (.fvar id) depth = .const name levels ↔ expression = .const name levels := by
  cases expression with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · simp
    · split <;> simp [Expr.liftLooseBVars']
  | _ => simp [Expr.instantiate1']

theorem instantiate1'_fvar_app_inv {expression : Expr} {id : FVarId} {depth : Nat}
    {function argument : Expr}
    (happ : expression.instantiate1' (.fvar id) depth = .app function argument) :
    ∃ originalFunction originalArgument, expression = .app originalFunction originalArgument ∧
      originalFunction.instantiate1' (.fvar id) depth = function ∧
      originalArgument.instantiate1' (.fvar id) depth = argument := by
  cases expression with
  | bvar index =>
    simp only [Expr.instantiate1'] at happ
    split at happ
    · cases happ
    · split at happ
      · cases happ
      · cases happ
  | app originalFunction originalArgument =>
    obtain ⟨hfunction, hargument⟩ := Expr.app.inj happ
    exact ⟨originalFunction, originalArgument, rfl, hfunction, hargument⟩
  | _ => cases happ

theorem instantiate1'_fvar_preservesUnaryHead {expression : Expr} {id : FVarId} {depth : Nat}
    {name : Name} {levels : List Level} {carrier : Expr}
    (hhead : expression.instantiate1' (.fvar id) depth = .app (.const name levels) carrier) :
    ∃ originalCarrier, expression = .app (.const name levels) originalCarrier ∧
      originalCarrier.instantiate1' (.fvar id) depth = carrier := by
  obtain ⟨function, originalCarrier, hexpression, hfunction, hcarrier⟩ :=
    instantiate1'_fvar_app_inv hhead
  have hconstant := instantiate1'_fvar_eq_const_iff.mp hfunction
  exact ⟨originalCarrier, by rw [hexpression, hconstant], hcarrier⟩

theorem instantiate1'_fvar_preservesBinaryHead {expression : Expr} {id : FVarId} {depth : Nat}
    {name : Name} {levels : List Level} {carrier extra : Expr}
    (hhead : expression.instantiate1' (.fvar id) depth = .app (.app (.const name levels) carrier) extra) :
    ∃ originalCarrier originalExtra,
      expression = .app (.app (.const name levels) originalCarrier) originalExtra ∧
      originalCarrier.instantiate1' (.fvar id) depth = carrier ∧
      originalExtra.instantiate1' (.fvar id) depth = extra := by
  obtain ⟨function, originalExtra, hexpression, hfunction, hextra⟩ := instantiate1'_fvar_app_inv hhead
  obtain ⟨originalCarrier, hfunctionShape, hcarrier⟩ := instantiate1'_fvar_preservesUnaryHead hfunction
  exact ⟨originalCarrier, originalExtra, by rw [hexpression, hfunctionShape], hcarrier, hextra⟩

theorem arbitraryInstantiationMayCreateAnnotationHead :
    peelTypeAnnotations
        ((Expr.app (.bvar 0) (.const ``Nat [])).instantiate1' (.const ``_root_.outParam []) 0) ≠
      (peelTypeAnnotations (Expr.app (.bvar 0) (.const ``Nat []))).instantiate1'
        (.const ``_root_.outParam []) 0 := by
  simp [peelTypeAnnotations, Expr.instantiate1', Expr.liftLooseBVars']

end Lean4Lean.AddInductive
