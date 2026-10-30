import Lean4Lean.Verify.CanonicalBoolRecursorSupport
import Lean4Lean.Verify.PrimitiveInductivePreprocessing

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem canonicalBoolParentPassSupport
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context} {elimLevel : Level}
    (trace : RecursorParentPassTrace stats
      #[canonicalBoolType] elimLevel 0 infos reader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[])) :
    RecursorParentPassTranslationSupport canonicalBoolModel [`u] trace := by
  cases trace with
  | stop complete => exact .stop complete
  | @step parent infos finalInfos reader finalReader indexReader normalized terminal finalIndex indices
      bound initialNormalization indicesTrace tail =>
    simp only [canonicalBoolType] at bound initialNormalization indicesTrace tail ⊢
    refine .step bound initialNormalization indicesTrace tail ?_ ?_
    · have normalizedEq : normalized = .sort (.succ .zero) := by
        rw [show normalized = _ from (Except.ok.inj (normalization.symm.trans initialNormalization)).symm]
      subst normalized
      cases indicesTrace with
      | stop notForall =>
        apply canonicalBoolStopParentSupport (params := params)
        rw [indConsts]
        rfl
    · cases tail with
      | stop complete => exact .stop complete
      | step bound2 _ _ =>
        have impossible : ¬ (0 + 1 < (#[(
          { name := ``Bool, type := .sort (.succ .zero),
            ctors := [⟨``Bool.false, .const ``Bool []⟩,
              ⟨``Bool.true, .const ``Bool []⟩] } : InductiveType)] : Array InductiveType).size) := by
          decide
        exact (impossible bound2).elim

end Lean4Lean.AddInductive
