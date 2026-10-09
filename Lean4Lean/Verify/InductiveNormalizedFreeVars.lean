import Lean4Lean.Verify.InductiveIndexLookupSupport
import Lean4Lean.Verify.InductiveBinderSupport
import Lean4Lean.Verify.InductiveWrappedHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open scoped List

theorem IndexFVarsWithin.mono {ids wider : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) (hsubset : ids ⊆ wider) :
    IndexFVarsWithin wider value :=
  .of_subset ((IndexFVarsWithin.iff_subset.mp within).trans hsubset)

theorem IndexFVarsWithin.liftLooseBVars' {ids : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) (start amount : Nat) :
    IndexFVarsWithin ids (value.liftLooseBVars' start amount) := by
  induction value generalizing start with
  | bvar index => trivial
  | sort level => trivial
  | const name levels => trivial
  | lit literal => trivial
  | mvar id => trivial
  | fvar id => exact within
  | app function argument ihFn ihArg => exact ⟨ihFn within.1 start, ihArg within.2 start⟩
  | lam name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1 start, ihBody within.2 (start + 1)⟩
  | forallE name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1 start, ihBody within.2 (start + 1)⟩
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    exact ⟨ihDomain within.1 start, ihValue within.2.1 start, ihBody within.2.2 (start + 1)⟩
  | mdata data body ih => exact ih within start
  | proj name index body ih => exact ih within start

theorem IndexFVarsWithin.instantiate1' {ids : List FVarId} {value replacement : Expr}
    (within : IndexFVarsWithin ids value) (hreplacement : IndexFVarsWithin ids replacement)
    (depth : Nat) : IndexFVarsWithin ids (value.instantiate1' replacement depth) := by
  induction value generalizing depth with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact hreplacement.liftLooseBVars' 0 depth
      · trivial
  | sort level => trivial
  | const name levels => trivial
  | lit literal => trivial
  | mvar id => trivial
  | fvar id => exact within
  | app function argument ihFn ihArg => exact ⟨ihFn within.1 depth, ihArg within.2 depth⟩
  | lam name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1 depth, ihBody within.2 (depth + 1)⟩
  | forallE name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1 depth, ihBody within.2 (depth + 1)⟩
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    exact ⟨ihDomain within.1 depth, ihValue within.2.1 depth, ihBody within.2.2 (depth + 1)⟩
  | mdata data body ih => exact ih within depth
  | proj name index body ih => exact ih within depth

theorem IndexFVarsWithin.instantiate1 {ids : List FVarId} {value replacement : Expr}
    (within : IndexFVarsWithin ids value) (hreplacement : IndexFVarsWithin ids replacement) :
    IndexFVarsWithin ids (value.instantiate1 replacement) := by
  rw [Expr.instantiate1_eq]
  exact within.instantiate1' hreplacement 0

theorem instantiate1FreeVarsSubset (value replacement : Expr) :
    (value.instantiate1 replacement).fvarsList ⊆ value.fvarsList ++ replacement.fvarsList := by
  apply IndexFVarsWithin.iff_subset.mp
  exact (IndexFVarsWithin.of_subset (List.subset_append_left _ _)).instantiate1
    (IndexFVarsWithin.of_subset (List.subset_append_right _ _))

theorem WrappedSortTelescope.freeVarsSubset {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) : normalized.fvarsList ⊆ source.fvarsList := by
  induction trace with
  | telescope htype => exact .refl _
  | mdata data tail ih => exact ih
  | letE name domain value body nondep tail ih =>
    apply ih.trans ((instantiate1FreeVarsSubset body value).trans ?_)
    intro fvar hmem
    simp only [List.mem_append, Expr.fvarsList] at hmem ⊢
    exact hmem.elim (fun hbody => .inr hbody) (fun hvalue => .inl (.inr hvalue))
  | beta name domain value body bi tail ih =>
    apply ih.trans ((instantiate1FreeVarsSubset body value).trans ?_)
    intro fvar hmem
    simp only [List.mem_append, Expr.fvarsList] at hmem ⊢
    exact hmem.elim (fun hbody => .inl (.inr hbody)) (fun hvalue => .inr hvalue)

theorem WrappedSortTelescope.fvars_nil {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (hsource : source.fvarsList = []) :
    normalized.fvarsList = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun fvar hmem => by
    have hsourceMem := trace.freeVarsSubset hmem
    rw [hsource] at hsourceMem
    cases hsourceMem

theorem WrappedSortTelescope.noFVars {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (hsource : source.hasFVar = false) :
    normalized.hasFVar = false :=
  fvarsList_eq_nil.mp (trace.fvars_nil (fvarsList_eq_nil.mpr hsource))

theorem CheckedHeaderSource.sourceNoFVars {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    types[parent]!.type.hasFVar = false := by
  have guarded := checkNoMVarNoFVar.WF original.env types[parent]!.name types[parent]!.type () source.guarded
  apply fvarsList_eq_nil.mp
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro fvar hmem
  exact (fvarsIn_iff.mp guarded).1 fvar hmem

theorem CheckedHeaderSource.normalizedNoFVars_of_wrappedExact {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hwrapped : WrappedSortTelescope types[parent]!.type normalized) : normalized.hasFVar = false :=
  hwrapped.noFVars source.sourceNoFVars

theorem CheckedHeaderSource.normalizedNoFVars_of_normalized_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized)
    (hwrapped : ∃ wrapped, WrappedSortTelescope types[parent]!.type wrapped) :
    normalized.hasFVar = false := by
  obtain ⟨wrapped, hwrapped⟩ := hwrapped
  have hclosed := source.normalizedNoFVars_of_wrappedExact hwrapped
  obtain ⟨entry, stats, inferred, sourceNormalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hsourceNormalized, hind, hconst, hprefixParams, htrace, hparams,
    hsort, hcurrent⟩ := source
  have heq : normalized = wrapped :=
    (hnormalized.2 entry sourceNormalized hsourceNormalized).symm.trans
      (hwrapped.normalized.2 entry sourceNormalized hsourceNormalized)
  exact heq ▸ hclosed

theorem CheckedHeaderSource.normalizedNoFVars_of_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    normalized.fvarsList = [] :=
  fvarsList_eq_nil.mpr (source.normalizedNoFVars_of_normalized_wrapped hnormalized ⟨wrapped, hwrapped⟩)

theorem CheckedHeaderSupportSource.normalizedNoFVars_of_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    normalized.fvarsList = [] :=
  source.toSource.normalizedNoFVars_of_wrapped hwrapped hnormalized

theorem CheckedHeaderSupportSource.normalizedNoFVars_of_normalized_wrapped {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr} {normalized : Expr}
    (source : CheckedHeaderSupportSource nparams types parent original params count current)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized)
    (hwrapped : ∃ wrapped, WrappedSortTelescope types[parent]!.type wrapped) :
    normalized.hasFVar = false :=
  source.toSource.normalizedNoFVars_of_normalized_wrapped hnormalized hwrapped

end Lean4Lean.AddInductive
