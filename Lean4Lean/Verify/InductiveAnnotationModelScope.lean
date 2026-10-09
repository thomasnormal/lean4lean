import Lean4Lean.Verify.InductiveAnnotationModel
import Lean4Lean.Verify.InductiveIndexLookupSupport

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open scoped List

theorem peelTypeAnnotations_fvarsSubset (value : Expr) :
    (peelTypeAnnotations value).fvarsList ⊆ value.fvarsList := by
  induction value using peelTypeAnnotations.induct <;>
    simp_all [peelTypeAnnotations, Expr.fvarsList, List.subset_def]

theorem peelTypeAnnotations_idempotent (value : Expr) :
    peelTypeAnnotations (peelTypeAnnotations value) = peelTypeAnnotations value := by
  induction value using peelTypeAnnotations.induct <;> simp_all [peelTypeAnnotations]

theorem IndexFVarsWithin.peelTypeAnnotations {ids : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) : IndexFVarsWithin ids (peelTypeAnnotations value) :=
  .of_subset ((peelTypeAnnotations_fvarsSubset value).trans (IndexFVarsWithin.iff_subset.mp within))

theorem IndexAvoids.peelTypeAnnotations {id : FVarId} {value : Expr}
    (avoids : IndexAvoids id value) : IndexAvoids id (peelTypeAnnotations value) := by
  apply IndexAvoids.of_not_mem
  intro hmem
  exact (IndexAvoids.iff_not_mem.mp avoids) (peelTypeAnnotations_fvarsSubset value hmem)

end Lean4Lean.AddInductive
