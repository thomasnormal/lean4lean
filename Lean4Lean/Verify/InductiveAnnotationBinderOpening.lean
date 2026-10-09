import Lean4Lean.Verify.InductiveAnnotationModelOpening
import Lean4Lean.Verify.InductiveAnnotationNativeScope

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def peelTelescopeDomains : Expr → Expr
  | .forallE name domain body bi =>
    .forallE name (peelTypeAnnotations domain) (peelTelescopeDomains body) bi
  | expression => expression

def BinderStep.withModelDomain (step : BinderStep) : BinderStep :=
  { step with domain := peelTypeAnnotations step.domain }

theorem BinderStep.parameterValues_withModelDomains (steps : List BinderStep) :
    parameterValues (steps.map withModelDomain) = parameterValues steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.map_cons, parameterValues, withModelDomain, ih]

theorem BinderStep.indexValues_withModelDomains (steps : List BinderStep) :
    indexValues (steps.map withModelDomain) = indexValues steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.map_cons, indexValues, withModelDomain, ih]

theorem peelTelescopeDomains_instantiate1'_fvar (expression : Expr) (id : FVarId) (depth : Nat) :
    peelTelescopeDomains (expression.instantiate1' (.fvar id) depth) =
      (peelTelescopeDomains expression).instantiate1' (.fvar id) depth := by
  induction expression generalizing depth with
  | bvar index =>
    simp only [Expr.instantiate1', peelTelescopeDomains]
    split
    · rfl
    · split <;> rfl
  | forallE name domain body bi ihDomain ihBody =>
    simp only [Expr.instantiate1', peelTelescopeDomains,
      peelTypeAnnotations_instantiate1'_fvar, ihBody]
  | _ => rfl

theorem peelTelescopeDomains_instantiate1_fvar (expression : Expr) (id : FVarId) :
    peelTelescopeDomains (expression.instantiate1 (.fvar id)) =
      (peelTelescopeDomains expression).instantiate1 (.fvar id) := by
  simp only [Expr.instantiate1_eq, peelTelescopeDomains_instantiate1'_fvar]

theorem OpenedTelescope.withModelDomains {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal)
    (shapes : ∀ step ∈ steps, ∃ id, step.value = .fvar id) :
    OpenedTelescope (peelTelescopeDomains type) (steps.map BinderStep.withModelDomain) terminal := by
  induction opened with
  | sort level => exact .sort level
  | @bind role name domain bi value body terminal steps tail ih =>
    obtain ⟨id, hvalue⟩ := shapes _ (List.mem_cons_self ..)
    change value = .fvar id at hvalue
    subst value
    have htail := ih (fun step hstep => shapes step (List.mem_cons_of_mem _ hstep))
    refine .bind role name (peelTypeAnnotations domain) bi (.fvar id) ?_
    rw [← peelTelescopeDomains_instantiate1_fvar]
    exact htail

theorem BinderStepsIndexDeclared.fvarValues {steps : List BinderStep} {ctx : Context}
    (declared : BinderStepsIndexDeclared ctx steps)
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id, value = .fvar id) :
    ∀ step ∈ steps, ∃ id, step.value = .fvar id := by
  induction steps with
  | nil => intro step hstep; cases hstep
  | cons head steps ih =>
    have htail : ∀ step ∈ steps, ∃ id, step.value = .fvar id := by
      apply ih
      · exact fun step hstep hrole => declared step (List.mem_cons_of_mem _ hstep) hrole
      · intro value hvalue
        apply shapes value
        simp only [BinderStep.parameterValues]
        split
        · exact List.mem_cons_of_mem _ hvalue
        · exact hvalue
    intro step hstep
    obtain heq | hstep := List.mem_cons.mp hstep
    · subst step
      cases hrole : head.role with
      | parameter =>
        apply shapes head.value
        simp only [BinderStep.parameterValues, hrole, ↓reduceIte]
        exact List.mem_cons_self ..
      | index => exact (declared head (List.mem_cons_self ..) hrole).fvar
    · exact htail step hstep

theorem OpenedTelescope.withModelDomains_of_parameters_indices
    {type terminal : Expr} {steps : List BinderStep} {ctx : Context}
    (opened : OpenedTelescope type steps terminal)
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) :
    OpenedTelescope (peelTelescopeDomains type) (steps.map BinderStep.withModelDomain) terminal :=
  opened.withModelDomains (declared.fvarValues shapes)

theorem BinderLookupCorrespondence.withModelDomains {pairs finalPairs : List (FVarId × FVarId)}
    {checked generated : List BinderStep}
    (correspondence : BinderLookupCorrespondence pairs checked generated finalPairs) :
    BinderLookupCorrespondence pairs (checked.map BinderStep.withModelDomain)
      (generated.map BinderStep.withModelDomain) finalPairs := by
  induction correspondence with
  | nil pairs => exact .nil pairs
  | parameter name bi leftDomain rightDomain value rawDomain tail ih =>
    exact .parameter name bi (peelTypeAnnotations leftDomain) (peelTypeAnnotations rightDomain)
      value rawDomain.peelTypeAnnotations ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain tail ih =>
    exact .index name bi (peelTypeAnnotations leftDomain) (peelTypeAnnotations rightDomain)
      leftId rightId rawDomain.peelTypeAnnotations ih

theorem BinderRawDomainScope.withModelDomains {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) :
    BinderRawDomainScope params (steps.map BinderStep.withModelDomain) := by
  intro position modelStep hmodel
  rw [List.getElem?_map] at hmodel
  cases hstep : steps[position]? with
  | none => simp only [hstep, Option.map_none] at hmodel; cases hmodel
  | some step =>
    have heq : BinderStep.withModelDomain step = modelStep := by
      simpa only [hstep, Option.map_some, Option.some.injEq] using hmodel
    subst modelStep
    have hwithin := (scope position step hstep).peelTypeAnnotations
    simpa only [← List.map_take, BinderStep.indexValues_withModelDomains, BinderStep.withModelDomain] using hwithin

theorem NativeAnnotationModelAt.instantiate1_fvar_of_model {expression : Expr} (id : FVarId)
    (before : NativeAnnotationModelAt expression)
    (after : NativeAnnotationModelAt (expression.instantiate1 (.fvar id))) :
    (expression.instantiate1 (.fvar id)).consumeTypeAnnotations =
      expression.consumeTypeAnnotations.instantiate1 (.fvar id) := by
  rw [after, before, peelTypeAnnotations_instantiate1_fvar]

end Lean4Lean.AddInductive
