import Lean4Lean.Verify.InductiveBinderIntegrity

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem BinderStep.indexIds_split
    {steps : List BinderStep} {selectedPrefix suffix : List FVarId} {identifier : FVarId}
    (split : (BinderStep.indexValues steps).map Expr.fvarId! =
      selectedPrefix ++ identifier :: suffix) :
    ∃ position step,
      steps[position]? = some step ∧ step.role = .index ∧
      step.value.fvarId! = identifier ∧
      (BinderStep.indexValues (steps.take position)).map Expr.fvarId! = selectedPrefix := by
  induction steps generalizing selectedPrefix with
  | nil =>
    cases selectedPrefix <;> cases split
  | cons step steps tailInduction =>
    cases role : step.role with
    | parameter =>
      have tailSplit : (BinderStep.indexValues steps).map Expr.fvarId! =
          selectedPrefix ++ identifier :: suffix := by
        simpa only [BinderStep.indexValues, role, BinderRole.noConfusion, ↓reduceIte] using split
      obtain ⟨position, selected, selectedAt, selectedRole, selectedId, prefixEq⟩ :=
        tailInduction tailSplit
      refine ⟨position + 1, selected, ?_, selectedRole, selectedId, ?_⟩
      · simpa only [List.getElem?_cons_succ] using selectedAt
      · simpa only [List.take_succ_cons, BinderStep.indexValues, role,
          BinderRole.noConfusion, ↓reduceIte] using prefixEq
    | index =>
      cases selectedPrefix with
      | nil =>
        have splitParts : step.value.fvarId! = identifier ∧
            (BinderStep.indexValues steps).map Expr.fvarId! = suffix := by
          simpa only [BinderStep.indexValues, role, ↓reduceIte, List.map_cons,
            List.nil_append, List.cons.injEq] using split
        exact ⟨0, step, rfl, role, splitParts.1, rfl⟩
      | cons first selectedPrefix =>
        have splitParts : step.value.fvarId! = first ∧
            (BinderStep.indexValues steps).map Expr.fvarId! =
              selectedPrefix ++ identifier :: suffix := by
          simpa only [BinderStep.indexValues, role, ↓reduceIte, List.map_cons,
            List.cons_append, List.cons.injEq] using split
        obtain ⟨position, selected, selectedAt, selectedRole, selectedId, prefixEq⟩ :=
          tailInduction splitParts.2
        refine ⟨position + 1, selected, ?_, selectedRole, selectedId, ?_⟩
        · simpa only [List.getElem?_cons_succ] using selectedAt
        · simpa only [List.take_succ_cons, BinderStep.indexValues, role, ↓reduceIte,
            List.map_cons, splitParts.1] using congrArg (List.cons first) prefixEq

end Lean4Lean.AddInductive
