import Lean4Lean.Verify.CanonicalBoolPassSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolPassSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open ElimNestedInductive (ContextReserved)
open TypeChecker (MLCtx)

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {infos finalInfos : Array RecInfo} {reader parentReader finalReader : Context}
    (typesEq : types = #[canonicalBoolType])
    (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader infos parentReader)
    (minorTrace : RecursorMinorPassTrace stats types 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
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
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal)
    (model : MLCtx) (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel) :
    ∃ finalModel, RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader finalInfos finalReader model finalModel :=
  canonicalBoolPassModelEndpoint typesEq parentTrace minorTrace normalization params levels indConsts
    nindices boolIndices motives motiveSupport model modelWF native reserved mapped

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool pass support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool pass support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool pass support has an admission: {name}"

#check canonicalBoolPassModelEndpointWithParentMotiveSupport

run_meta
  auditTheorem ``canonicalBoolPassModelEndpointWithParentMotiveSupport
  auditTheorem ``canonicalBoolPassModelEndpoint
  logInfo "canonical Bool parent/minor pass endpoint and parent motive receipt are theorem-backed"

end CanonicalBoolPassSupportTest
