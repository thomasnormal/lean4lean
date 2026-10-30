import Lean4Lean.Verify.CanonicalBoolParentPassSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolParentPassSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context} {elimLevel : Level}
    (trace : RecursorParentPassTrace stats
      #[canonicalBoolType] elimLevel 0 infos reader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[])) :
    RecursorParentPassTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolParentPassSupport trace normalization params levels indConsts nindices boolIndices

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool parent pass support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool parent pass support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool parent pass support has an admission: {name}"

run_meta
  auditTheorem ``canonicalBoolParentPassSupport
  logInfo "canonical Bool parent pass support is theorem-backed"

end CanonicalBoolParentPassSupportTest
