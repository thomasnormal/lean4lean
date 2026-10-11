import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean.Expr

theorem withApp_rel (expression : Expr) (actual : Expr → Array Expr → actualType)
    (shadow : Expr → Array Expr → shadowType) (relation : actualType → shadowType → Prop)
    (continuation : ∀ head arguments, relation (actual head arguments) (shadow head arguments)) :
    relation (expression.withApp actual) (expression.withApp shadow) := by
  have auxiliary : ∀ expression arguments index,
      relation (Expr.withAppAux actual expression arguments index)
        (Expr.withAppAux shadow expression arguments index) := by
    intro expression arguments index
    induction expression generalizing arguments index with
    | app function argument functionIH argumentIH => exact functionIH _ _
    | _ => exact continuation _ _
  exact auxiliary expression _ _

end Lean.Expr

namespace Except

def SuccessTransport (actual : Except actualError resultType) (shadow : Except shadowError resultType) : Prop :=
  actual.WF fun result => shadow = .ok result

theorem SuccessTransport.refl (action : Except errorType resultType) : SuccessTransport action action :=
  fun _ accepted => accepted

theorem SuccessTransport.bind
    (actual : Except actualError firstType) (shadow : Except shadowError firstType)
    (actualNext : firstType → Except actualError resultType)
    (shadowNext : firstType → Except shadowError resultType)
    (initial : SuccessTransport actual shadow)
    (continuation : ∀ result, actual = .ok result → SuccessTransport (actualNext result) (shadowNext result)) :
    SuccessTransport (actual >>= actualNext) (shadow >>= shadowNext) := by
  intro result accepted
  cases found : actual with
  | error error =>
    change Except.bind actual actualNext = .ok result at accepted
    rw [found] at accepted
    contradiction
  | ok value =>
    have transported := initial value found
    change Except.bind shadow shadowNext = .ok result
    rw [transported]
    apply continuation value found result
    change Except.bind actual actualNext = .ok result at accepted
    simpa only [found, Except.bind] using accepted

end Except

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

def M.SuccessTransport (actual shadow : M resultType) (actualContext shadowContext : Context)
    (state : State) : Prop :=
  Except.SuccessTransport (actual actualContext state) (shadow shadowContext state)

theorem M.SuccessTransport.bind (actual shadow : M firstType)
    (actualNext shadowNext : firstType → M resultType) (actualContext shadowContext : Context) (state : State)
    (initial : M.SuccessTransport actual shadow actualContext shadowContext state)
    (continuation : ∀ result finalState, actual actualContext state = .ok (result, finalState) →
      M.SuccessTransport (actualNext result) (shadowNext result) actualContext shadowContext finalState) :
    M.SuccessTransport (actual >>= actualNext) (shadow >>= shadowNext) actualContext shadowContext state := by
  exact Except.SuccessTransport.bind _ _ _ _ initial fun ⟨result, finalState⟩ accepted =>
    continuation result finalState accepted

theorem M.SuccessTransport.pure (value : resultType) (actualContext shadowContext : Context) (state : State) :
    M.SuccessTransport (pure value) (pure value) actualContext shadowContext state :=
  .refl _

theorem M.SuccessTransport.withApp (expression : Expr)
    (actual shadow : Expr → Array Expr → M resultType) (actualContext shadowContext : Context) (state : State)
    (continuation : ∀ head arguments,
      M.SuccessTransport (actual head arguments) (shadow head arguments) actualContext shadowContext state) :
    M.SuccessTransport (expression.withApp actual) (expression.withApp shadow)
      actualContext shadowContext state := by
  exact Expr.withApp_rel expression actual shadow
    (fun actual shadow => M.SuccessTransport actual shadow actualContext shadowContext state) continuation

end Lean4Lean.TypeChecker
