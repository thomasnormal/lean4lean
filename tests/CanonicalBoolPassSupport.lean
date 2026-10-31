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

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {infos finalInfos : Array RecInfo} {reader parentReader finalReader : Context}
    {model parentModel : MLCtx}
    (typesEq : types = #[canonicalBoolType])
    (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats types 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ finalModel, RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader finalInfos finalReader model finalModel :=
  canonicalBoolPassModelEndpointOfParentHistory typesEq parentTrace parentHistory minorTrace
    normalization params levels indConsts nindices boolIndices reserved

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {infos finalInfos : Array RecInfo} {reader parentReader finalReader : Context}
    {model parentModel : MLCtx}
    (typesEq : types = #[canonicalBoolType])
    (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats types 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ (finalModel : MLCtx) (major motive minorFalse minorTrue : FVarId),
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      infos[0]!.major = .fvar major ∧ infos[0]!.motive = .fvar motive ∧
      finalInfos[0]!.minors =
        (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel :=
  canonicalBoolPassModelEndpointWithAllocationOfParentHistory typesEq parentTrace parentHistory
    minorTrace normalization params levels indConsts nindices boolIndices reserved

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {infos finalInfos : Array RecInfo} {reader parentReader finalReader : Context}
    {model parentModel : MLCtx} {info : RecInfo}
    (typesEq : types = #[canonicalBoolType])
    (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats types 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen)
    (finalInfosEq : finalInfos = #[info])
    (initialIndices : infos[0]!.indices = #[])
    (initialMinors : infos[0]!.minors = #[]) :
    ∃ finalModel major motive minorFalse minorTrue chronological,
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      info.major = .fvar major ∧ info.motive = .fvar motive ∧
      info.indices = #[] ∧ info.minors = #[.fvar minorFalse, .fvar minorTrue] ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel ∧
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats finalInfos 0
        finalReader.lctx model finalModel chronological
        [motive, minorFalse, minorTrue, major] :=
  canonicalBoolPassModelEndpointWithKnownFinalInfoRebase typesEq parentTrace parentHistory minorTrace
    normalization params levels indConsts nindices boolIndices reserved finalInfosEq initialIndices initialMinors

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
  auditTheorem ``canonicalBoolPassModelEndpointWithKnownFinalInfoRebase
  auditTheorem ``canonicalBoolPassModelEndpoint
  auditTheorem ``canonicalBoolPassModelEndpointOfParentHistory
  auditTheorem ``canonicalBoolPassModelEndpointWithAllocationOfParentHistory
  logInfo "canonical Bool parent/minor pass endpoint and parent motive receipt are theorem-backed"

end CanonicalBoolPassSupportTest
