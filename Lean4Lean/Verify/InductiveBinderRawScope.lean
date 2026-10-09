import Lean4Lean.Verify.InductiveNormalizedFreeVars
import Lean4Lean.Verify.InductiveBinderCorrespondence

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open scoped List

def BinderRawDomainScope (params : List FVarId) (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step →
    IndexFVarsWithin (params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!) step.domain

theorem BinderRawDomainScope.domainSubset {params : List FVarId} {steps : List BinderStep}
    {position : Nat} {step : BinderStep} (scope : BinderRawDomainScope params steps)
    (hstep : steps[position]? = some step) :
    step.domain.fvarsList ⊆ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId! :=
  IndexFVarsWithin.iff_subset.mp (scope position step hstep)

theorem BinderRawDomainScope.mono {params wider : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) (hparams : params ⊆ wider) :
    BinderRawDomainScope wider steps := by
  intro position step hstep
  apply (scope position step hstep).mono
  intro id hid
  obtain hparam | hindex := List.mem_append.mp hid
  · exact List.mem_append_left _ (hparams hparam)
  · exact List.mem_append_right _ hindex

private theorem declaredRawTail {ctx : Context} {step : BinderStep} {steps : List BinderStep}
    (declared : BinderStepsIndexDeclared ctx (step :: steps)) : BinderStepsIndexDeclared ctx steps :=
  fun next hnext hrole => declared next (List.mem_cons_of_mem step hnext) hrole

theorem OpenedTelescope.rawDomainScope {params : List FVarId} {type terminal : Expr}
    {steps : List BinderStep} {ctx : Context} (opened : OpenedTelescope type steps terminal)
    (within : IndexFVarsWithin params type)
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id ∈ params, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) : BinderRawDomainScope params steps := by
  induction opened generalizing params with
  | sort level => intro position step hstep; cases hstep
  | @bind role name domain bi value body terminal steps opened ih =>
    cases role with
    | parameter =>
      obtain ⟨id, hid, rfl⟩ := shapes value (List.mem_cons_self ..)
      have hnextWithin := within.2.instantiate1 (show IndexFVarsWithin params (.fvar id) from hid)
      have htail := ih hnextWithin
        (fun next hnext => shapes next (List.mem_cons_of_mem _ hnext)) (declaredRawTail declared)
      intro position step hstep
      cases position with
      | zero =>
        obtain rfl := Option.some.inj hstep
        simpa only [List.take_zero, BinderStep.indexValues, List.map_nil, List.append_nil] using within.1
      | succ position =>
        simpa only [List.take_succ_cons, BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte]
          using htail position step hstep
    | index =>
      obtain ⟨id, hvalue⟩ := (declared _ (List.mem_cons_self ..) rfl).fvar
      change value = .fvar id at hvalue
      subst value
      have hnextWithin : IndexFVarsWithin (params ++ [id]) (body.instantiate1 (.fvar id)) :=
        (within.2.mono (List.subset_append_left _ _)).instantiate1
          (show IndexFVarsWithin (params ++ [id]) (.fvar id) from List.mem_append_right _ (List.mem_cons_self ..))
      have htail := ih hnextWithin
        (fun next hnext => by
          obtain ⟨param, hparam, hexpr⟩ := shapes next hnext
          exact ⟨param, List.mem_append_left _ hparam, hexpr⟩) (declaredRawTail declared)
      intro position step hstep
      cases position with
      | zero =>
        obtain rfl := Option.some.inj hstep
        simpa only [List.take_zero, BinderStep.indexValues, List.map_nil, List.append_nil] using within.1
      | succ position =>
        simpa only [List.take_succ_cons, BinderStep.indexValues, ↓reduceIte, List.map_cons,
          Expr.fvarId!, List.append_assoc, List.singleton_append] using htail position step hstep

end Lean4Lean.AddInductive
