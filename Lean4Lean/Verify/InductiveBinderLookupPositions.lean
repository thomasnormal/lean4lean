import Lean4Lean.Verify.InductiveBinderLookupCorrespondence

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem BinderLookupCorrespondence.length {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs) :
    left.length = right.length := by
  induction correspondence with
  | nil pairs => rfl
  | parameter name bi leftDomain rightDomain value rawDomain tail ih => exact congrArg (· + 1) ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain tail ih => exact congrArg (· + 1) ih

theorem BinderLookupCorrespondence.roles {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs) :
    left.map BinderStep.role = right.map BinderStep.role := by
  induction correspondence with
  | nil pairs => rfl
  | parameter name bi leftDomain rightDomain value rawDomain tail ih => exact congrArg (.parameter :: ·) ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain tail ih => exact congrArg (.index :: ·) ih

theorem BinderLookupCorrespondence.atPosition {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs)
    (position : Nat) (hposition : position < left.length) :
    ∃ leftStep rightStep priorPairs,
      left[position]? = some leftStep ∧ right[position]? = some rightStep ∧
      leftStep.role = rightStep.role ∧ leftStep.signature = rightStep.signature ∧
      priorPairs = pairs ++ List.zip ((BinderStep.indexValues (left.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (right.take position)).map Expr.fvarId!) ∧
      IndexLookupRenaming priorPairs leftStep.domain rightStep.domain := by
  induction correspondence generalizing position with
  | nil pairs => simp only [List.length_nil, Nat.not_lt_zero] at hposition
  | @parameter pairs finalPairs left right name bi leftDomain rightDomain value rawDomain tail ih =>
    cases position with
    | zero =>
      refine ⟨_, _, pairs, rfl, rfl, rfl, rfl, ?_, rawDomain⟩
      simp only [List.take_zero, BinderStep.indexValues, List.map_nil, List.zip_nil_left, List.append_nil]
    | succ position =>
      obtain ⟨leftStep, rightStep, priorPairs, hleft, hright, hrole, hsignature, hprior, hdomain⟩ :=
        ih position (Nat.lt_of_succ_lt_succ hposition)
      refine ⟨leftStep, rightStep, priorPairs, hleft, hright, hrole, hsignature, ?_, hdomain⟩
      simpa only [List.take_succ_cons, BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using hprior
  | @index pairs finalPairs left right name bi leftDomain rightDomain leftId rightId rawDomain tail ih =>
    cases position with
    | zero =>
      refine ⟨_, _, pairs, rfl, rfl, rfl, rfl, ?_, rawDomain⟩
      simp only [List.take_zero, BinderStep.indexValues, List.map_nil, List.zip_nil_left, List.append_nil]
    | succ position =>
      obtain ⟨leftStep, rightStep, priorPairs, hleft, hright, hrole, hsignature, hprior, hdomain⟩ :=
        ih position (Nat.lt_of_succ_lt_succ hposition)
      refine ⟨leftStep, rightStep, priorPairs, hleft, hright, hrole, hsignature, ?_, hdomain⟩
      simpa only [List.take_succ_cons, BinderStep.indexValues, ↓reduceIte, List.map_cons,
        Expr.fvarId!, List.zip_cons_cons, List.append_assoc, List.singleton_append] using hprior

theorem BinderLookupCorrespondence.atPosition_of_getElem? {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} {leftStep : BinderStep} {position : Nat}
    (correspondence : BinderLookupCorrespondence pairs left right finalPairs)
    (hleft : left[position]? = some leftStep) :
    ∃ rightStep priorPairs, right[position]? = some rightStep ∧
      leftStep.role = rightStep.role ∧ leftStep.signature = rightStep.signature ∧
      priorPairs = pairs ++ List.zip ((BinderStep.indexValues (left.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (right.take position)).map Expr.fvarId!) ∧
      IndexLookupRenaming priorPairs leftStep.domain rightStep.domain := by
  have hposition : position < left.length := List.getElem?_eq_some_iff.mp hleft |>.1
  obtain ⟨selected, rightStep, priorPairs, hselected, hright, hrole, hsignature, hprior, hdomain⟩ :=
    correspondence.atPosition position hposition
  have heq : selected = leftStep := Option.some.inj (hselected.symm.trans hleft)
  subst selected
  exact ⟨rightStep, priorPairs, hright, hrole, hsignature, hprior, hdomain⟩

theorem BinderIndexAllocations.atPosition {ctx : Context} {start position : Nat}
    {steps : List BinderStep} {step : BinderStep} (allocated : BinderIndexAllocations ctx start steps)
    (hstep : steps[position]? = some step) (hindex : step.role = .index) :
    BinderPositionedAt ctx step.value step.name step.localDomain step.bi
      (start + (BinderStep.indexValues (steps.take position)).length) := by
  induction steps generalizing start position with
  | nil => cases hstep
  | cons head steps ih =>
    cases position with
    | zero =>
      obtain rfl := Option.some.inj hstep
      simp only [BinderIndexAllocations, hindex] at allocated
      simpa only [List.take_zero, BinderStep.indexValues, List.length_nil, Nat.add_zero] using allocated.1
    | succ position =>
      simp only [List.getElem?_cons_succ] at hstep
      cases hrole : head.role with
      | parameter =>
        simp only [BinderIndexAllocations, hrole] at allocated
        simpa only [List.take_succ_cons, BinderStep.indexValues, hrole, BinderRole.noConfusion,
          ↓reduceIte] using ih allocated hstep
      | index =>
        simp only [BinderIndexAllocations, hrole] at allocated
        simpa only [List.take_succ_cons, BinderStep.indexValues, hrole, ↓reduceIte, List.length_cons,
          Nat.add_assoc, Nat.add_comm 1] using ih allocated.2 hstep

end Lean4Lean.AddInductive
