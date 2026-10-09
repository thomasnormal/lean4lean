import Lean4Lean.Verify.InductiveAnnotationModelScope
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean
open Lean AddInductive

theorem FVarsIn.peelTypeAnnotations {fvars : FVarId → Prop} {value : Expr}
    (within : value.FVarsIn fvars) : (peelTypeAnnotations value).FVarsIn fvars := by
  induction value using AddInductive.peelTypeAnnotations.induct <;>
    simp_all [AddInductive.peelTypeAnnotations, FVarsIn]

theorem FVarsIn.indexFVarsWithin {ids : List FVarId} {value : Expr}
    (within : value.FVarsIn (fun id => id ∈ ids)) : IndexFVarsWithin ids value :=
  .of_subset (fvarsIn_iff.mp within).1

theorem AddInductive.peelTypeAnnotations_hasMVar_eq_false {value : Expr}
    (nometa : value.hasMVar = false) : (peelTypeAnnotations value).hasMVar = false :=
  fvarsIn_iff_hasMVar.mp (fvarsIn_iff_hasMVar.mpr nometa).peelTypeAnnotations

end Lean4Lean
