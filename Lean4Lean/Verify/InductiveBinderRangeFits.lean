import Lean4Lean.Verify.InductiveAnnotationModelRangeFits
import Lean4Lean.Verify.InductiveBoundedHeaderClosure
import Lean4Lean.Verify.InductiveBinderClosed

namespace Lean4Lean
open Lean hiding Environment Exception

def NativeBinderClosed (value : Expr) : Prop :=
  value.looseBVarRange = 0 ∧ value.hasExprMVar = false

theorem BVarRangeFits.nativeBinderClosed {value : Expr} (fits : BVarRangeFits value)
    (closed : value.Closed 0) : NativeBinderClosed value := by
  have native := fits.closed_iff_nativeRange.mp closed
  exact ⟨Nat.eq_zero_of_le_zero native.1, native.2⟩

namespace AddInductive

theorem WrappedSortTelescope.rangeFits {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (fits : BVarRangeFits source)
    (closed : source.Closed 0) : BVarRangeFits normalized := by
  induction trace with
  | telescope _ => exact fits
  | mdata _ _ ih => exact ih fits closed
  | letE _ _ _ _ _ _ ih =>
    exact ih (fits.2.2.instantiate1_native fits.2.1 closed.2.1)
      (closed.2.2.instantiate1_native closed.2.1)
  | beta _ _ _ _ _ _ ih =>
    exact ih (fits.1.2.instantiate1_native fits.2 closed.2)
      (closed.1.2.instantiate1_native closed.2)

theorem CheckedHeaderSource.normalizedRangeFits_of_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (fits : BVarRangeFits types[parent]!.type)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    BVarRangeFits normalized := by
  have hfits := hwrapped.rangeFits fits (source.sourceClosed_of_bvarRangeFits fits)
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : normalized = wrapped :=
    (hnormalized.2 entry sourceNormalized hsourceNormalized).symm.trans
      (hwrapped.normalized.2 entry sourceNormalized hsourceNormalized)
  rw [heq]
  exact hfits

def NormalizedHeaderRangeFits (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → ∀ normalized,
    NormalizedSortTelescope types[parent]!.type normalized → BVarRangeFits normalized

theorem CheckedHeaderSupportSources.wrappedRangeFits {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot : Context}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (fits : HeaderSourceBVarRangeFits types) :
    NormalizedHeaderRangeFits types := by
  intro parent hparent normalized hnormalized
  obtain ⟨wrapped, hwrapped⟩ := htypes parent hparent
  exact (headers.2 parent hparent).toSource.normalizedRangeFits_of_wrapped
    (fits parent hparent) hwrapped hnormalized

def BinderRawDomainRangeFits (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → BVarRangeFits step.domain

def BinderValuesRangeFits (steps : List BinderStep) : Prop :=
  ∀ step ∈ steps, BVarRangeFits step.value

private theorem parameterRangeFitsMem {step : BinderStep} {steps : List BinderStep}
    (hstep : step ∈ steps) (hrole : step.role = .parameter) :
    step.value ∈ BinderStep.parameterValues steps := by
  induction steps with
  | nil => cases hstep
  | cons first steps ih =>
    obtain rfl | hstep := List.mem_cons.mp hstep
    · simp only [BinderStep.parameterValues, hrole, ↓reduceIte]
      exact List.mem_cons_self ..
    · have hmem := ih hstep
      simp only [BinderStep.parameterValues]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem

theorem BinderStepsIndexDeclared.valuesRangeFits {params : List Expr} {steps : List BinderStep}
    {ctx : Context} (declared : BinderStepsIndexDeclared ctx steps)
    (hparams : BinderStep.parameterValues steps = params)
    (shapes : ∀ value ∈ params, ∃ id, value = .fvar id) : BinderValuesRangeFits steps := by
  intro step hstep
  cases hrole : step.role with
  | parameter =>
    have hvalue := parameterRangeFitsMem hstep hrole
    obtain ⟨id, hvalue⟩ := shapes step.value (hparams ▸ hvalue)
    rw [hvalue]
    trivial
  | index =>
    obtain ⟨id, hvalue⟩ := (declared step hstep hrole).fvar
    change step.value = .fvar id at hvalue
    rw [hvalue]
    trivial

theorem OpenedTelescope.rawDomainRangeFits {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) (fits : BVarRangeFits type)
    (valuesClosed : BinderValuesClosed steps) (valuesFits : BinderValuesRangeFits steps) :
    BinderRawDomainRangeFits steps := by
  induction opened with
  | sort level => intro position step hstep; cases hstep
  | @bind role name domain bi value body terminal steps opened ih =>
    have hvalueClosed := valuesClosed _ (List.mem_cons_self ..)
    have hvalueFits := valuesFits _ (List.mem_cons_self ..)
    have htail := ih (fits.2.instantiate1_native hvalueFits hvalueClosed)
      (fun step hstep => valuesClosed step (List.mem_cons_of_mem _ hstep))
      (fun step hstep => valuesFits step (List.mem_cons_of_mem _ hstep))
    intro position step hstep
    cases position with
    | zero =>
      obtain rfl := Option.some.inj hstep
      exact fits.1
    | succ position => exact htail position step hstep

theorem OpenedTelescope.terminalRangeFits {type terminal : Expr} {steps : List BinderStep}
    (opened : OpenedTelescope type steps terminal) : BVarRangeFits terminal := by
  induction opened with
  | sort level => trivial
  | bind _ _ _ _ _ _ ih => exact ih

def BinderStoredIndexDomainRangeFits (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    BVarRangeFits step.localDomain

def BinderStoredIndexTypeRangeFits (ctx : Context) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep) (decl : LocalDecl),
    steps[position]? = some step → step.role = .index →
    ctx.lctx.find? step.value.fvarId! = some decl → BVarRangeFits decl.type

theorem BinderRawDomainRangeFits.storedIndexDomainRangeFits {steps : List BinderStep}
    (fits : BinderRawDomainRangeFits steps) : BinderStoredIndexDomainRangeFits steps :=
  fun position step hstep _ => (fits position step hstep).peelTypeAnnotations

theorem BinderRawDomainRangeFits.storedIndexTypeRangeFits {steps : List BinderStep} {ctx : Context}
    (fits : BinderRawDomainRangeFits steps) (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeRangeFits ctx steps := by
  intro position step decl hstep hindex hlookup
  obtain ⟨nativeDecl, hnativeLookup, _, htype, _, _⟩ := declared step (List.mem_of_getElem? hstep) hindex
  have heq : nativeDecl = decl := Option.some.inj (hnativeLookup.symm.trans hlookup)
  subst nativeDecl
  rw [htype]
  exact (fits position step hstep).peelTypeAnnotations

def BinderRawDomainNativeClosed (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → NativeBinderClosed step.domain

def BinderStoredIndexDomainNativeClosed (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    NativeBinderClosed step.localDomain

def BinderStoredIndexTypeNativeClosed (ctx : Context) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep) (decl : LocalDecl),
    steps[position]? = some step → step.role = .index →
    ctx.lctx.find? step.value.fvarId! = some decl → NativeBinderClosed decl.type

theorem BinderRawDomainClosed.nativeClosed {steps : List BinderStep}
    (closed : BinderRawDomainClosed steps) (fits : BinderRawDomainRangeFits steps) :
    BinderRawDomainNativeClosed steps :=
  fun position step hstep => (fits position step hstep).nativeBinderClosed (closed position step hstep)

theorem BinderStoredIndexDomainClosed.nativeClosed {steps : List BinderStep}
    (closed : BinderStoredIndexDomainClosed steps) (fits : BinderStoredIndexDomainRangeFits steps) :
    BinderStoredIndexDomainNativeClosed steps :=
  fun position step hstep hindex =>
    (fits position step hstep hindex).nativeBinderClosed (closed position step hstep hindex)

theorem BinderStoredIndexTypeClosed.nativeClosed {ctx : Context} {steps : List BinderStep}
    (closed : BinderStoredIndexTypeClosed ctx steps) (fits : BinderStoredIndexTypeRangeFits ctx steps) :
    BinderStoredIndexTypeNativeClosed ctx steps :=
  fun position step decl hstep hindex hlookup =>
    (fits position step decl hstep hindex hlookup).nativeBinderClosed
      (closed position step decl hstep hindex hlookup)

end AddInductive
end Lean4Lean
