import Lean4Lean.Verify.InductiveBinderRawScope
import Lean4Lean.Verify.InductiveBinderLookupCorrespondence

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def BinderRawIndexExclusion (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (domainStep : BinderStep) (futurePosition : Nat) (futureStep : BinderStep),
    steps[position]? = some domainStep → steps[futurePosition]? = some futureStep →
    futureStep.role = .index → position ≤ futurePosition →
    IndexAvoids futureStep.value.fvarId! domainStep.domain

private theorem indexValuesAppend (left right : List BinderStep) :
    BinderStep.indexValues (left ++ right) =
      BinderStep.indexValues left ++ BinderStep.indexValues right := by
  induction left with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.cons_append, BinderStep.indexValues]
    split <;> simp only [ih, List.cons_append]

private theorem indexIdsTakeDrop (steps : List BinderStep) (position : Nat) :
    (BinderStep.indexValues steps).map Expr.fvarId! =
      (BinderStep.indexValues (steps.take position)).map Expr.fvarId! ++
      (BinderStep.indexValues (steps.drop position)).map Expr.fvarId! := by
  calc
    _ = (BinderStep.indexValues (steps.take position ++ steps.drop position)).map Expr.fvarId! :=
      congrArg (fun selected => (BinderStep.indexValues selected).map Expr.fvarId!)
        (List.take_append_drop position steps).symm
    _ = _ := by rw [indexValuesAppend, List.map_append]

private theorem indexValueMem {steps : List BinderStep} {step : BinderStep}
    (hstep : step ∈ steps) (hindex : step.role = .index) : step.value ∈ BinderStep.indexValues steps := by
  induction steps with
  | nil => cases hstep
  | cons head steps ih =>
    obtain rfl | htail := List.mem_cons.mp hstep
    · simp only [BinderStep.indexValues, hindex, ↓reduceIte, List.mem_cons_self]
    · simp only [BinderStep.indexValues]
      split
      · exact List.mem_cons_of_mem _ (ih htail)
      · exact ih htail

theorem BinderLookupCorrespondence.indexLengths {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs) :
    (BinderStep.indexValues left).length = (BinderStep.indexValues right).length := by
  induction correspondence with
  | nil pairs => rfl
  | parameter name bi leftDomain rightDomain value rawDomain tail ih =>
    simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain tail ih =>
    simpa only [BinderStep.indexValues, ↓reduceIte, List.length_cons] using congrArg (· + 1) ih

theorem BinderLookupCorrespondence.indexIdsNodup {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs)
    (injection : IndexPairInjection finalPairs) :
    ((BinderStep.indexValues left).map Expr.fvarId!).Nodup ∧
      ((BinderStep.indexValues right).map Expr.fvarId!).Nodup := by
  have hlength : ((BinderStep.indexValues left).map Expr.fvarId!).length =
      ((BinderStep.indexValues right).map Expr.fvarId!).length := by
    simpa only [List.length_map] using correspondence.indexLengths
  obtain ⟨hfst, hsnd⟩ := indexZipExactProjections hlength
  rw [correspondence.finalPairs] at injection
  simp only [IndexPairInjection, List.map_append, hfst, hsnd] at injection
  exact ⟨(List.nodup_append.mp injection.1).2.1, (List.nodup_append.mp injection.2).2.1⟩

theorem indexIdsSuffixOutsidePrefix {steps : List BinderStep} {position : Nat} {id : FVarId}
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (suffix : id ∈ (BinderStep.indexValues (steps.drop position)).map Expr.fvarId!) :
    id ∉ (BinderStep.indexValues (steps.take position)).map Expr.fvarId! := by
  rw [indexIdsTakeDrop steps position] at distinct
  intro prefixMember
  exact (List.nodup_append.mp distinct).2.2 id prefixMember id suffix rfl

theorem indexRawDomain_avoidsSuffix {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {domain : Expr} {id : FVarId}
    (within : IndexFVarsWithin
      (params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!) domain)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (suffix : id ∈ (BinderStep.indexValues (steps.drop position)).map Expr.fvarId!) :
    IndexAvoids id domain := by
  have fullMember : id ∈ (BinderStep.indexValues steps).map Expr.fvarId! := by
    rw [indexIdsTakeDrop steps position]
    exact List.mem_append_right _ suffix
  apply within.avoids
  intro member
  obtain parameterMember | prefixMember := List.mem_append.mp member
  · exact disjoint parameterMember fullMember
  · exact indexIdsSuffixOutsidePrefix distinct suffix prefixMember

theorem BinderRawDomainScope.avoidsSuffixIndex {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} {id : FVarId}
    (scope : BinderRawDomainScope params steps) (hstep : steps[position]? = some step)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (suffix : id ∈ (BinderStep.indexValues (steps.drop position)).map Expr.fvarId!) :
    IndexAvoids id step.domain :=
  indexRawDomain_avoidsSuffix (scope position step hstep) distinct disjoint suffix

theorem BinderRawDomainScope.avoidsCurrentOrFutureIndex {params : List FVarId}
    {steps : List BinderStep} {position futurePosition : Nat} {domainStep futureStep : BinderStep}
    (scope : BinderRawDomainScope params steps)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (hdomain : steps[position]? = some domainStep)
    (hfuture : steps[futurePosition]? = some futureStep) (hfutureIndex : futureStep.role = .index)
    (hle : position ≤ futurePosition) : IndexAvoids futureStep.value.fvarId! domainStep.domain := by
  have hdrop : (steps.drop position)[futurePosition - position]? = some futureStep := by
    rw [List.getElem?_drop]
    simpa only [Nat.add_sub_of_le hle] using hfuture
  apply scope.avoidsSuffixIndex hdomain distinct disjoint
  exact List.mem_map.mpr ⟨futureStep.value,
    indexValueMem (List.mem_of_getElem? hdrop) hfutureIndex, rfl⟩

theorem BinderRawDomainScope.avoidsCurrentIndex {params : List FVarId}
    {steps : List BinderStep} {position : Nat} {step : BinderStep}
    (scope : BinderRawDomainScope params steps)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (hstep : steps[position]? = some step) (hindex : step.role = .index) :
    IndexAvoids step.value.fvarId! step.domain :=
  scope.avoidsCurrentOrFutureIndex distinct disjoint hstep hstep hindex (Nat.le_refl _)

theorem BinderRawDomainScope.avoidsCurrentOrFutureIndex_of_allocations {params : List FVarId}
    {steps : List BinderStep} {ctx : Context} {start position futurePosition : Nat}
    {domainStep futureStep : BinderStep} (scope : BinderRawDomainScope params steps)
    (allocated : BinderIndexAllocations ctx start steps)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!))
    (hdomain : steps[position]? = some domainStep)
    (hfuture : steps[futurePosition]? = some futureStep) (hfutureIndex : futureStep.role = .index)
    (hle : position ≤ futurePosition) : IndexAvoids futureStep.value.fvarId! domainStep.domain :=
  scope.avoidsCurrentOrFutureIndex allocated.indexIdsNodup disjoint hdomain hfuture hfutureIndex hle

theorem BinderRawDomainScope.indexExclusion {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps)
    (distinct : ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup)
    (disjoint : List.Disjoint params ((BinderStep.indexValues steps).map Expr.fvarId!)) :
    BinderRawIndexExclusion steps :=
  fun _ _ _ _ hdomain hfuture hfutureIndex hle =>
    scope.avoidsCurrentOrFutureIndex distinct disjoint hdomain hfuture hfutureIndex hle

end Lean4Lean.AddInductive
