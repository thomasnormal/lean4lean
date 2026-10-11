import Lean4Lean.Verify.InductiveHeaderCheckerTransport
import Lean4Lean.Verify.TypeChecker.Transport

namespace Lean4Lean
open Lean hiding Environment Exception

theorem TypeChecker.Inner.ensureSortCore.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression source : Expr)
    (normalization : ¬expression.isSort = true →
      TypeChecker.M.SuccessTransport (actualMethods.whnf expression) (shadowMethods.whnf expression)
      actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.ensureSortCore expression source actualMethods)
      (TypeChecker.Inner.ensureSortCore expression source shadowMethods) actualContext shadowContext state := by
  intro result accepted
  simp only [TypeChecker.Inner.ensureSortCore] at accepted ⊢
  by_cases direct : expression.isSort = true
  · simp only [direct, if_true] at accepted ⊢
    exact accepted
  · simp only [direct, Bool.false_eq_true, if_false] at accepted ⊢
    dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure,
      Except.pure, Except.bind, TypeChecker.Inner.whnf] at accepted ⊢
    cases found : actualMethods.whnf expression actualContext state with
    | error error => rw [found] at accepted; contradiction
    | ok returned =>
      have transported := normalization direct returned found
      rw [transported]
      rw [found] at accepted
      dsimp only [Except.bind] at accepted ⊢
      rcases returned with ⟨normalized, finalState⟩
      by_cases sorted : normalized.isSort = true
      · simpa only [sorted, if_true] using accepted
      · simp only [sorted, Bool.false_eq_true, if_false] at accepted
        change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
        contradiction

theorem TypeChecker.Inner.ensureForallCore.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression source : Expr)
    (normalization : ¬expression.isForall = true →
      TypeChecker.M.SuccessTransport (actualMethods.whnf expression) (shadowMethods.whnf expression)
      actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.ensureForallCore expression source actualMethods)
      (TypeChecker.Inner.ensureForallCore expression source shadowMethods) actualContext shadowContext state := by
  intro result accepted
  simp only [TypeChecker.Inner.ensureForallCore] at accepted ⊢
  by_cases direct : expression.isForall = true
  · simp only [direct, if_true] at accepted ⊢
    exact accepted
  · simp only [direct, Bool.false_eq_true, if_false] at accepted ⊢
    dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure,
      Except.pure, Except.bind, TypeChecker.Inner.whnf] at accepted ⊢
    cases found : actualMethods.whnf expression actualContext state with
    | error error => rw [found] at accepted; contradiction
    | ok returned =>
      have transported := normalization direct returned found
      rw [transported]
      rw [found] at accepted
      dsimp only [Except.bind] at accepted ⊢
      rcases returned with ⟨normalized, finalState⟩
      by_cases quantified : normalized.isForall = true
      · simpa only [quantified, if_true] using accepted
      · simp only [quantified, Bool.false_eq_true, if_false] at accepted
        change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
        contradiction

theorem TypeChecker.Inner.isProp.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr)
    (inference : TypeChecker.M.SuccessTransport (actualMethods.inferType expression true)
      (shadowMethods.inferType expression true) actualContext shadowContext state)
    (normalization : ∀ type finalState, actualMethods.inferType expression true actualContext state =
      .ok (type, finalState) → TypeChecker.M.SuccessTransport (actualMethods.whnf type)
        (shadowMethods.whnf type) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isProp expression actualMethods)
      (TypeChecker.Inner.isProp expression shadowMethods) actualContext shadowContext state := by
  dsimp only [TypeChecker.Inner.isProp, Bind.bind, ReaderT.bind,
    TypeChecker.Inner.inferType, TypeChecker.Inner.whnf]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ inference
  intro type finalState accepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (normalization type finalState accepted)
  intro normalized normalizedState _
  exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.isDefEq.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (comparison : TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore first second)
      (shadowMethods.isDefEqCore first second) actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEq first second actualMethods)
      (TypeChecker.Inner.isDefEq first second shadowMethods) actualContext shadowContext state := by
  dsimp only [TypeChecker.Inner.isDefEq, Bind.bind, ReaderT.bind, TypeChecker.Inner.isDefEqCore]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ comparison
  intro equal finalState _ result accepted
  cases equal <;> exact accepted

theorem TypeChecker.Inner.reduceProj.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (index : Nat) (structureExpr : Expr) (cheapRec cheapProj : Bool)
    (normalization : TypeChecker.M.SuccessTransport
      (if cheapProj then actualMethods.whnfCore structureExpr cheapRec cheapProj else actualMethods.whnf structureExpr)
      (if cheapProj then shadowMethods.whnfCore structureExpr cheapRec cheapProj else shadowMethods.whnf structureExpr)
      actualContext shadowContext state)
    (strings : ∀ text finalState,
      (if cheapProj then actualMethods.whnfCore structureExpr cheapRec cheapProj else actualMethods.whnf structureExpr)
        actualContext state = .ok (.lit (.strVal text), finalState) →
      TypeChecker.M.SuccessTransport (actualMethods.whnf (.strLitToConstructor text))
        (shadowMethods.whnf (.strLitToConstructor text)) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceProj index structureExpr cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceProj index structureExpr cheapRec cheapProj shadowMethods)
      actualContext shadowContext state := by
  have lookup : ∀ (expression : Expr) (finalState : TypeChecker.State),
      TypeChecker.M.SuccessTransport
        (((expression.withApp fun head arguments => do
          let .const name _ := head | return none
          let environment ← TypeChecker.getEnv
          let .ctorInfo information ← environment.get name | return none
          return arguments[information.numParams + index]?) : TypeChecker.RecM (Option Expr)) actualMethods)
        (((expression.withApp fun head arguments => do
          let .const name _ := head | return none
          let environment ← TypeChecker.getEnv
          let .ctorInfo information ← environment.get name | return none
          return arguments[information.numParams + index]?) : TypeChecker.RecM (Option Expr)) shadowMethods)
        actualContext shadowContext finalState := by
    intro expression finalState
    apply Expr.withApp_rel expression _ _
      (fun actual shadow : TypeChecker.RecM (Option Expr) =>
        TypeChecker.M.SuccessTransport (actual actualMethods) (shadow shadowMethods)
          actualContext shadowContext finalState)
    intro head arguments result accepted
    cases head <;> try exact accepted
    rename_i name levels
    dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
      ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted ⊢
    rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
    · cases found : actualContext.env.find? name with
      | none =>
        simp only [Kernel.Environment.get, found] at accepted
        change (Except.error _ : Except Kernel.Exception (Option Expr × TypeChecker.State)) = .ok result at accepted
        contradiction
      | some information =>
        have shadowFound := same.symm.trans found
        simp only [Kernel.Environment.get, found, shadowFound] at accepted ⊢
        dsimp only [StateT.lift, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted ⊢
        cases information <;> exact accepted
    · simp only [Kernel.Environment.get, actualLookup, shadowLookup] at accepted ⊢
      exact accepted
  dsimp only [TypeChecker.Inner.reduceProj, Bind.bind, ReaderT.bind,
    TypeChecker.Inner.whnf, TypeChecker.Inner.whnfCore]
  cases cheapProj
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true] at normalization strings ⊢
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ normalization
    intro normalized finalState accepted
    cases normalized <;> try exact lookup _ _
    rename_i literal
    cases literal with
    | natVal value => exact lookup _ _
    | strVal text =>
      dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (strings text finalState accepted)
      intro expanded expandedState _
      exact lookup expanded expandedState

end Lean4Lean
