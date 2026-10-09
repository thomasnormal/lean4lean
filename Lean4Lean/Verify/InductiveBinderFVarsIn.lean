import Lean4Lean.Verify.InductiveAnnotationModelFVarsIn
import Lean4Lean.Verify.InductiveBinderRawScopeAlignment

namespace Lean4Lean
open Lean hiding Environment Exception

theorem FVarsIn.instantiate1_native {predicate : FVarId → Prop} {value replacement : Expr}
    (within : value.FVarsIn predicate) (replacementWithin : replacement.FVarsIn predicate) :
    (value.instantiate1 replacement).FVarsIn predicate := by
  rw [Expr.instantiate1_eq]
  exact within.instantiate1_go replacementWithin

namespace AddInductive
open scoped List

theorem WrappedSortTelescope.fvarsIn {predicate : FVarId → Prop} {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (within : source.FVarsIn predicate) :
    normalized.FVarsIn predicate := by
  induction trace with
  | telescope _ => exact within
  | mdata _ _ ih => exact ih within
  | letE _ _ _ _ _ _ ih => exact ih (within.2.2.instantiate1_native within.2.1)
  | beta _ _ _ _ _ _ ih => exact ih (within.1.2.instantiate1_native within.2)

theorem CheckedHeaderSource.sourceFVarsIn {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    types[parent]!.type.FVarsIn (fun _ => False) :=
  checkNoMVarNoFVar.WF original.env types[parent]!.name types[parent]!.type () source.guarded

theorem CheckedHeaderSource.normalizedFVarsIn_of_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    normalized.FVarsIn (fun _ => False) := by
  have hwithin := hwrapped.fvarsIn source.sourceFVarsIn
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : normalized = wrapped :=
    (hnormalized.2 entry sourceNormalized hsourceNormalized).symm.trans
      (hwrapped.normalized.2 entry sourceNormalized hsourceNormalized)
  rw [heq]
  exact hwithin

def NormalizedHeaderFVarsIn (types : Array InductiveType) (ids : List FVarId) : Prop :=
  ∀ parent, parent < types.size → ∀ normalized,
    NormalizedSortTelescope types[parent]!.type normalized →
      normalized.FVarsIn (fun id => id ∈ ids)

theorem NormalizedHeaderFVarsIn.fvarsWithin {types : Array InductiveType} {ids : List FVarId}
    (within : NormalizedHeaderFVarsIn types ids) : NormalizedHeaderFVarsWithin types ids :=
  fun parent hparent normalized hnormalized => (within parent hparent normalized hnormalized).indexFVarsWithin

theorem CheckedHeaderSupportSources.wrappedFVarsIn {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) :
    NormalizedHeaderFVarsIn types (stats.params.toList.map Expr.fvarId!) := by
  intro parent hparent normalized hnormalized
  obtain ⟨wrapped, hwrapped⟩ := htypes parent hparent
  exact ((headers.2 parent hparent).toSource.normalizedFVarsIn_of_wrapped hwrapped hnormalized).mono
    (fun _ hfalse => False.elim hfalse)

def BinderRawDomainFVarsIn (params : List FVarId) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step →
    step.domain.FVarsIn
      (fun id => id ∈ params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!)

private theorem declaredFVarsInTail {ctx : Context} {step : BinderStep} {steps : List BinderStep}
    (declared : BinderStepsIndexDeclared ctx (step :: steps)) : BinderStepsIndexDeclared ctx steps :=
  fun next hnext hrole => declared next (List.mem_cons_of_mem step hnext) hrole

theorem OpenedTelescope.rawDomainFVarsIn {params : List FVarId} {type terminal : Expr}
    {steps : List BinderStep} {ctx : Context} (opened : OpenedTelescope type steps terminal)
    (within : type.FVarsIn (fun id => id ∈ params))
    (shapes : ∀ value ∈ BinderStep.parameterValues steps, ∃ id ∈ params, value = .fvar id)
    (declared : BinderStepsIndexDeclared ctx steps) : BinderRawDomainFVarsIn params steps := by
  induction opened generalizing params with
  | sort level => intro position step hstep; cases hstep
  | @bind role name domain bi value body terminal steps opened ih =>
    cases role with
    | parameter =>
      obtain ⟨id, hid, rfl⟩ := shapes value (List.mem_cons_self ..)
      have hnextWithin := within.2.instantiate1_native
        (show (Expr.fvar id).FVarsIn (fun free => free ∈ params) from hid)
      have htail := ih hnextWithin
        (fun next hnext => shapes next (List.mem_cons_of_mem _ hnext)) (declaredFVarsInTail declared)
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
      have hnextWithin : (body.instantiate1 (.fvar id)).FVarsIn (fun free => free ∈ params ++ [id]) :=
        (within.2.mono (fun _ hparam => List.mem_append_left _ hparam)).instantiate1_native
          (show (Expr.fvar id).FVarsIn (fun free => free ∈ params ++ [id]) from
            List.mem_append_right _ (List.mem_cons_self ..))
      have htail := ih hnextWithin
        (fun next hnext => by
          obtain ⟨param, hparam, hexpr⟩ := shapes next hnext
          exact ⟨param, List.mem_append_left _ hparam, hexpr⟩) (declaredFVarsInTail declared)
      intro position step hstep
      cases position with
      | zero =>
        obtain rfl := Option.some.inj hstep
        simpa only [List.take_zero, BinderStep.indexValues, List.map_nil, List.append_nil] using within.1
      | succ position =>
        simpa only [List.take_succ_cons, BinderStep.indexValues, ↓reduceIte, List.map_cons,
          Expr.fvarId!, List.append_assoc, List.singleton_append] using htail position step hstep

theorem BinderRawDomainFVarsIn.rawDomainScope {params : List FVarId} {steps : List BinderStep}
    (within : BinderRawDomainFVarsIn params steps) : BinderRawDomainScope params steps :=
  fun position step hstep => (within position step hstep).indexFVarsWithin

end AddInductive
end Lean4Lean
