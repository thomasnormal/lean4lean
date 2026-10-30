import Lean4Lean.Verify.CanonicalBoolMinorPassSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolMinorPassSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats
      #[{name := ``Bool, type := .sort (.succ .zero),
          ctors := [⟨``Bool.false, .const ``Bool []⟩,
            ⟨``Bool.true, .const ``Bool []⟩]}] 0 infos reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorPassTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorPassSupport trace params levels indConsts nindices boolIndices motives motiveSupport

example {stats : InductiveStats} {types : Array InductiveType}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (typesEq : types = #[canonicalBoolType])
    (trace : RecursorMinorPassTrace stats types 0 infos reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorPassTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorPassSupport_of_types typesEq trace params levels indConsts nindices boolIndices
    motives motiveSupport

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool minor pass support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool minor pass support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool minor pass support has an admission: {name}"

run_meta
  for theoremName in [``canonicalBoolMinorPassSupport,
      ``canonicalBoolMinorPassSupport_of_types] do
    auditTheorem theoremName
  logInfo "canonical Bool minor pass support is theorem-backed"

end CanonicalBoolMinorPassSupportTest
