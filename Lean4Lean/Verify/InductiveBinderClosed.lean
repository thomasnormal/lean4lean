import Lean4Lean.Verify.InductiveAnnotationModelClosed
import Lean4Lean.Verify.InductiveBinderFVarsIn

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem WrappedSortTelescope.closed {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (closed : source.Closed 0) :
    normalized.Closed 0 := by
  induction trace with
  | telescope _ => exact closed
  | mdata _ _ ih => exact ih closed
  | letE _ _ _ _ _ _ ih => exact ih (closed.2.2.instantiate1_native closed.2.1)
  | beta _ _ _ _ _ _ ih => exact ih (closed.1.2.instantiate1_native closed.2)

theorem CheckedHeaderSource.normalizedClosed_of_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (closed : types[parent]!.type.Closed 0)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    normalized.Closed 0 := by
  have hclosed := hwrapped.closed closed
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : normalized = wrapped :=
    (hnormalized.2 entry sourceNormalized hsourceNormalized).symm.trans
      (hwrapped.normalized.2 entry sourceNormalized hsourceNormalized)
  rw [heq]
  exact hclosed

def HeaderSourceClosed (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → types[parent]!.type.Closed 0

def NormalizedHeaderClosed (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → ∀ normalized,
    NormalizedSortTelescope types[parent]!.type normalized → normalized.Closed 0

theorem CheckedHeaderSupportSources.wrappedClosed {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (closed : HeaderSourceClosed types) :
    NormalizedHeaderClosed types := by
  intro parent hparent normalized hnormalized
  obtain ⟨wrapped, hwrapped⟩ := htypes parent hparent
  exact (headers.2 parent hparent).toSource.normalizedClosed_of_wrapped
    (closed parent hparent) hwrapped hnormalized

def BinderRawDomainClosed (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.domain.Closed 0

def BinderValuesClosed (steps : List BinderStep) : Prop :=
  ∀ step ∈ steps, step.value.Closed 0

private theorem parameterValueMem {step : BinderStep} {steps : List BinderStep}
    (hstep : step ∈ steps) (hrole : step.role = .parameter) :
    step.value ∈ BinderStep.parameterValues steps := by
  induction steps with
  | nil => cases hstep
  | cons first steps ih =>
    obtain rfl | hstep := List.mem_cons.mp hstep
    · simp [BinderStep.parameterValues, hrole]
    · have hmem := ih hstep
      simp only [BinderStep.parameterValues]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem

theorem BinderStepsIndexDeclared.valuesClosed {params : List Expr} {steps : List BinderStep}
    {ctx : Context} (declared : BinderStepsIndexDeclared ctx steps)
    (hparams : BinderStep.parameterValues steps = params)
    (shapes : ∀ value ∈ params, ∃ id, value = .fvar id) : BinderValuesClosed steps := by
  intro step hstep
  cases hrole : step.role with
  | parameter =>
    have hvalue := parameterValueMem hstep hrole
    obtain ⟨id, hvalue⟩ := shapes step.value (hparams ▸ hvalue)
    rw [hvalue]
    trivial
  | index =>
    obtain ⟨id, hvalue⟩ := (declared step hstep hrole).fvar
    change step.value = .fvar id at hvalue
    rw [hvalue]
    trivial

theorem OpenedTelescope.rawDomainClosed {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (closed : type.Closed 0)
    (values : BinderValuesClosed steps) : BinderRawDomainClosed steps := by
  induction opened with
  | sort level => intro position step hstep; cases hstep
  | @bind role name domain bi value body terminal steps opened ih =>
    have hvalue := values _ (List.mem_cons_self ..)
    have htail := ih (closed.2.instantiate1_native hvalue)
      (fun step hstep => values step (List.mem_cons_of_mem _ hstep))
    intro position step hstep
    cases position with
    | zero =>
      obtain rfl := Option.some.inj hstep
      exact closed.1
    | succ position => exact htail position step hstep

theorem OpenedTelescope.terminalClosed {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (closed : type.Closed 0)
    (values : BinderValuesClosed steps) : terminal.Closed 0 := by
  induction opened with
  | sort level => exact closed
  | @bind role name domain bi value body terminal steps opened ih =>
    exact ih (closed.2.instantiate1_native (values _ (List.mem_cons_self ..)))
      (fun step hstep => values step (List.mem_cons_of_mem _ hstep))

def BinderStoredIndexDomainClosed (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    step.localDomain.Closed 0

def BinderStoredIndexTypeClosed (ctx : Context) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep) (decl : LocalDecl),
    steps[position]? = some step → step.role = .index →
    ctx.lctx.find? step.value.fvarId! = some decl → decl.type.Closed 0

theorem BinderRawDomainClosed.storedIndexDomainClosed {steps : List BinderStep}
    (closed : BinderRawDomainClosed steps) : BinderStoredIndexDomainClosed steps :=
  fun position step hstep _ => (closed position step hstep).peelTypeAnnotations

theorem BinderRawDomainClosed.storedIndexTypeClosed {steps : List BinderStep} {ctx : Context}
    (closed : BinderRawDomainClosed steps) (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeClosed ctx steps := by
  intro position step decl hstep hindex hlookup
  obtain ⟨nativeDecl, hnativeLookup, _, htype, _, _⟩ := declared step (List.mem_of_getElem? hstep) hindex
  have heq : nativeDecl = decl := Option.some.inj (hnativeLookup.symm.trans hlookup)
  subst nativeDecl
  rw [htype]
  exact (closed position step hstep).peelTypeAnnotations

end Lean4Lean.AddInductive
