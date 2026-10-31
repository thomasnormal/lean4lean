import Lean4Lean.Verify.CanonicalBoolRecursorSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolRecursorSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

example {stats : InductiveStats} {reader : Context}
    {trace : RecursorIndexTrace stats (.sort (.succ .zero)) 0 #[] reader
      (.sort (.succ .zero)) 0 #[] reader}
    (head : stats.indConsts[0]! = .const ``Bool [])
    (params : stats.params = #[]) :
    ParentModelTranslationSupport canonicalBoolModel [`u] stats 0 trace :=
  canonicalBoolStopParentSupport head params

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
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
    MinorTraceTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorTraceSupport trace params levels indConsts nindices boolIndices motives motiveSupport

example {stats : InductiveStats} {infos : Array RecInfo}
    {terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context} {model fieldModel : MLCtx}
    {semantic motiveSemantic : VExpr} {motive : FVarId}
    {level : VLevel}
    {fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint canonicalBoolModel [`u]
      fieldTrace model fieldModel semantic)
    (fieldsEq : fields = #[])
    (terminalEq : terminal = .const ``Bool [])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal := by
  exact canonicalBoolCtorFieldEndpointIHMotiveApplicationSupport endpoint fieldsEq terminalEq
    boolIndices motiveEq motiveTranslated motiveTyped

example {stats : InductiveStats} {infos : Array RecInfo}
    {baseModel fieldModel : MLCtx} {ids : List FVarId}
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (extension : IndexMLCtxExtension baseModel ids fieldModel)
    (fieldWF : fieldModel.WF canonicalBoolModel [`u])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] baseModel.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 baseModel.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx
      (.const ``Bool []) := by
  exact canonicalBoolMotiveSupportOfExtension extension fieldWF rfl boolIndices motiveEq
    motiveTranslated motiveTyped

example {stats : InductiveStats} {elimLevel : Level} {indices : Array Expr}
    {indexReader : Context} {indexVirtual : VLCtx} {initial final : MLCtx}
    {ids : List FVarId}
    (step : RecursorParentModelStep canonicalBoolModel [`u] stats #[canonicalBoolType]
      elimLevel 0 indices indexReader indexVirtual initial final ids)
    (params : stats.params = #[])
    (indConsts : stats.indConsts = #[.const ``Bool []])
    (indicesEq : indices = #[]) :
    ∃ (bodyLevel : VLevel),
      TrExprS canonicalBoolModel [`u] final.vlctx
        (.fvar ⟨(recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats 0 indices)).ngen.curr⟩) (.bvar 0) ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx (.bvar 0)
        (.forallE (.const ``Bool []) (.sort bodyLevel)) := by
  exact canonicalBoolParentMotiveFVarPremises step params indConsts indicesEq

example {stats : InductiveStats} {elimLevel : Level}
    {infos : Array RecInfo} {reader parentReader : Context}
    {model parentModel : MLCtx}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u] parentTrace model parentModel)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[])
    (indConsts : stats.indConsts = #[.const ``Bool []])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[])) :
    ∀ {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] parentReader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ fieldModel, CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace parentModel fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal :=
  canonicalBoolParentHistoryMotiveSupport parentTrace parentHistory normalization params indConsts boolIndices

example {stats : InductiveStats} {elimLevel : Level}
    {infos : Array RecInfo} {reader parentReader : Context}
    {model parentModel : MLCtx}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u] parentTrace model parentModel)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[])
    (indConsts : stats.indConsts = #[.const ``Bool []]) :
    ∃ (motive : FVarId) (level : VLevel),
      infos[0]!.motive = .fvar motive ∧
      TrExprS canonicalBoolModel [`u] parentModel.vlctx
        (.fvar motive) (.bvar 0) ∧
      canonicalBoolModel.HasType 1 parentModel.vlctx.toCtx (.bvar 0)
        (.forallE (.const ``Bool []) (.sort level)) :=
  canonicalBoolParentHistoryMotiveReceipt parentTrace parentHistory normalization params indConsts

example {stats : InductiveStats} {elimLevel : Level}
    {infos : Array RecInfo} {reader parentReader : Context}
    {model parentModel : MLCtx}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[])
    (indConsts : stats.indConsts = #[.const ``Bool []]) :
    ∃ (major motive : FVarId),
      infos[0]!.major = .fvar major ∧ infos[0]!.motive = .fvar motive ∧
      ∃ ids, IndexMLCtxExtension model ids parentModel ∧ ids = [major, motive] :=
  canonicalBoolParentHistoryAllocation parentTrace parentHistory normalization params indConsts

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool support has an admission: {name}"

run_meta
  for theoremName in [``canonicalBoolStopParentSupport,
      ``canonicalBoolMinorSourceSupport,
      ``canonicalBoolMinorTraceSupport,
      ``canonicalBoolCtorFieldEndpointIHMotiveApplicationSupport,
      ``canonicalBoolMotiveSupportOfExtension,
      ``canonicalBoolParentMotiveFVarPremises,
      ``canonicalBoolParentHistoryMotiveSupport,
      ``canonicalBoolParentHistoryMotiveReceipt,
      ``canonicalBoolParentHistoryAllocation] do
    auditTheorem theoremName
  logInfo "canonical Bool parent stop, motive, and two-constructor minor support are theorem-backed"

end CanonicalBoolRecursorSupportTest
