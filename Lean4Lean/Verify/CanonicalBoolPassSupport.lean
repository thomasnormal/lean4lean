import Lean4Lean.Verify.CanonicalBoolParentPassSupport
import Lean4Lean.Verify.CanonicalBoolMinorPassSupport
import Lean4Lean.Verify.InductiveMinorPassTranslationCPS
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem canonicalBoolPassModelEndpointWithParentMotiveSupport
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
    ∃ finalModel parentModel,
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      ∃ parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
          parentTrace model parentModel,
        (∀ {terminal finalIndex fields recursiveFields fieldReader semantic},
          (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] parentReader
            terminal finalIndex fields recursiveFields fieldReader) →
          ∀ fieldModel, CtorFieldModelEndpoint canonicalBoolModel [`u]
            fieldTrace parentModel fieldModel semantic →
            IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos
              fieldModel.vlctx terminal) := by
  subst types
  have paramsSize : stats.params.size = 0 := by simp [params]
  have parentSupport := canonicalBoolParentPassSupport parentTrace normalization params levels
    indConsts nindices boolIndices
  obtain ⟨parentModel, parentHistory⟩ := parentTrace.translated parentSupport
    canonicalBoolModel.wf canonicalBoolModel.constants canonicalBoolModel.definitions paramsSize
    model modelWF native reserved mapped
  have parentFrame := parentTrace.scope (native ▸ modelWF.tr.1) reserved
  have minorSupport := canonicalBoolMinorPassSupport minorTrace params levels indConsts nindices
    boolIndices motives motiveSupport
  obtain ⟨finalModel, minorHistory⟩ := minorTrace.translated canonicalBoolModel.wf
    canonicalBoolModel.constants canonicalBoolModel.definitions paramsSize parentModel
    parentHistory.context.1 parentHistory.context.2.1 parentFrame.reserved minorSupport
  exact ⟨finalModel, parentModel,
    ⟨_, _, parentModel, parentTrace, minorTrace, parentHistory, minorHistory⟩,
    parentHistory, canonicalBoolParentHistoryMotiveSupport parentTrace parentHistory
      normalization params indConsts boolIndices⟩

/- Package the concrete translated Bool minor pass into the same endpoint
   shape used by the higher-level recursor pipeline.  The theorem consumes an
   already translated parent history, so it records the concrete path without
   discharging the generic support callback of the main endpoint theorem. -/
theorem canonicalBoolPassModelEndpointOfParentHistory
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
      reader finalInfos finalReader model finalModel := by
  subst types
  obtain ⟨finalModel, minorHistory⟩ :=
    canonicalBoolMinorPassTranslatedOfParentHistory parentTrace parentHistory minorTrace
      normalization params levels indConsts nindices boolIndices reserved
  exact ⟨finalModel,
    ⟨infos, parentReader, parentModel, parentTrace, minorTrace, parentHistory, minorHistory⟩⟩

theorem canonicalBoolPassModelEndpointWithAllocationOfParentHistory
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
      finalInfos[0]!.minors = (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel := by
  subst types
  obtain ⟨major, motive, majorEq, motiveEq, _, parentExt, parentIdsEq⟩ :=
    canonicalBoolParentHistoryAllocation parentTrace parentHistory normalization params indConsts
  rw [parentIdsEq] at parentExt
  have infoBound : 0 < infos.size := by
    have counts := parentTrace.counts
    have infoSize : infos.size = 1 := by
      simpa only [Array.size_empty, Array.size_singleton, Nat.sub_zero, Nat.zero_add] using counts
    omega
  unfold canonicalBoolType at minorTrace
  cases minorTrace with
  | stop complete => exact (complete (by decide)).elim
  | step bound head tail =>
    cases tail with
    | stop complete =>
      have motiveReceipt : ∃ motiveLevel,
          TrExprS canonicalBoolModel [`u] parentModel.vlctx
            (.fvar motive) (.bvar 0) ∧
          canonicalBoolModel.HasType 1 parentModel.vlctx.toCtx (.bvar 0)
            (.forallE (.const ``Bool []) (.sort motiveLevel)) := by
        obtain ⟨motive0, motiveLevel, motiveEq0, motiveTranslated0, motiveTyped0⟩ :=
          canonicalBoolParentHistoryMotiveReceipt parentTrace parentHistory normalization params indConsts
        have motiveIds : (Expr.fvar motive0 : Expr) = .fvar motive := motiveEq0.symm.trans motiveEq
        cases motiveIds
        exact ⟨motiveLevel, motiveTranslated0, motiveTyped0⟩
      obtain ⟨motiveLevel, motiveTranslated, motiveTyped⟩ := motiveReceipt
      obtain ⟨finalModel, minorFalse, minorTrue, minorHistory, minorExt, minorsEq⟩ :=
        canonicalBoolMinorTraceAllocationOfMotive head params levels indConsts nindices
          boolIndices parentHistory.context.1 parentHistory.context.2.1 reserved infoBound motiveEq
          motiveTranslated motiveTyped
      have passHistory : TranslatedRecursorMinorPass canonicalBoolModel [`u]
          (.step bound head (.stop complete)) parentModel finalModel :=
        .step bound head (.stop complete) minorHistory
          (.stop complete minorHistory.context.1 minorHistory.context.2.1)
      refine ⟨finalModel, major, motive, minorFalse, minorTrue,
        ⟨infos, parentReader, parentModel, parentTrace,
          (.step bound head (.stop complete)), parentHistory, passHistory⟩,
        majorEq, motiveEq, minorsEq, ?_⟩
      exact parentExt.trans minorExt
    | step bound2 _ _ =>
      have impossible : ¬ (1 : Nat) < #[canonicalBoolType].size := by decide
      exact (impossible bound2).elim

/- Compose the concrete endpoint/allocation receipt with the final-info
   preservation theorem and the existing grouped-order rebase consumer. -/
theorem canonicalBoolPassModelEndpointWithKnownFinalInfoRebase
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
        [motive, minorFalse, minorTrue, major] := by
  subst types
  obtain ⟨major, motive, majorEq, motiveEq, _, parentExt, parentIdsEq⟩ :=
    canonicalBoolParentHistoryAllocation parentTrace parentHistory normalization params indConsts
  rw [parentIdsEq] at parentExt
  have infoBound : 0 < infos.size := by
    have counts := parentTrace.counts
    have infoSize : infos.size = 1 := by
      simpa only [Array.size_empty, Array.size_singleton, Nat.sub_zero, Nat.zero_add] using counts
    omega
  obtain ⟨finalModel, major, motive, minorFalse, minorTrue, endpoint,
      majorEq, motiveEq, finalMinorsUpdate, known⟩ :=
    canonicalBoolPassModelEndpointWithAllocationOfParentHistory rfl parentTrace parentHistory
      minorTrace normalization params levels indConsts nindices boolIndices reserved
  have preserved := canonicalBoolMinorPassInfoPreservation minorTrace infoBound
  have infoEq : finalInfos[0]! = info := by
    simpa [finalInfosEq]
  have finalMajorEq : info.major = .fvar major := by
    rw [← infoEq, preserved.1, majorEq]
  have finalMotiveEq : info.motive = .fvar motive := by
    rw [← infoEq, preserved.2.1, motiveEq]
  have finalIndicesEq : info.indices = #[] := by
    rw [← infoEq, preserved.2.2, initialIndices]
  have finalMinorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue] := by
    rw [← infoEq, finalMinorsUpdate, initialMinors]
    rfl
  obtain ⟨chronological, rebase⟩ :=
    endpoint.canonicalBoolRebaseBinderOrderOfKnownExtension canonicalBoolModel.wf params
      finalInfosEq finalMotiveEq finalMinorsEq finalIndicesEq finalMajorEq known
  exact ⟨finalModel, major, motive, minorFalse, minorTrue, chronological,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase⟩

theorem canonicalBoolPassModelEndpointWithKnownFinalInfoBodyApplication
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
    (initialMinors : infos[0]!.minors = #[])
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader finalInfos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    ∃ finalModel major motive minorFalse minorTrue chronological bodySemantic level,
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      info.major = .fvar major ∧ info.motive = .fvar motive ∧
      info.indices = #[] ∧ info.minors = #[.fvar minorFalse, .fvar minorTrue] ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel ∧
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats finalInfos 0
        finalReader.lctx model finalModel chronological
        [motive, minorFalse, minorTrue, major] ∧
      TrExprS canonicalBoolModel [`u] finalModel.vlctx
        (recursorTypeBody finalInfos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 finalModel.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats finalInfos 0 finalReader.lctx =
        finalModel.lctx.mkForall
          ([motive, minorFalse, minorTrue, major].map Expr.fvar).toArray
          (recursorTypeBody finalInfos 0) := by
  obtain ⟨finalModel, major, motive, minorFalse, minorTrue, chronological,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase⟩ :=
    canonicalBoolPassModelEndpointWithKnownFinalInfoRebase typesEq parentTrace parentHistory
      minorTrace normalization params levels indConsts nindices boolIndices reserved finalInfosEq
      initialIndices initialMinors
  obtain ⟨_, bodySemantic, level, bodyReceipt, bodyTranslated, bodyTyped, bodyRaw⟩ :=
    endpoint.canonicalBoolRebasedFinalBodyApplicationReceipt canonicalBoolModel.wf
      params finalInfosEq finalMotiveEq finalMinorsEq finalIndicesEq finalMajorEq
      (canonicalBoolAllocationOfKnownExtension known) source
      mapped minorSemantics generatedRuleSemantics iotaSoundness
  exact ⟨finalModel, major, motive, minorFalse, minorTrue, chronological, bodySemantic, level,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase,
    bodyTranslated, bodyTyped, bodyRaw⟩

theorem canonicalBoolPassModelEndpointWithKnownFinalInfoDeclaredRecursor
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
    (initialMinors : infos[0]!.minors = #[])
    (modelWF : model.WF canonicalBoolModel [`u])
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader finalInfos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport canonicalBoolModel [`u] stats finalInfos 0
      finalReader.lctx model)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (recursorLevels : getRecLevelParams elimLevel lparams = [`u])
    (empty : model.vlctx = [])
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    ∃ finalModel major motive minorFalse minorTrue chronological bodySemantic level constant,
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      info.major = .fvar major ∧ info.motive = .fvar motive ∧
      info.indices = #[] ∧ info.minors = #[.fvar minorFalse, .fvar minorTrue] ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel ∧
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats finalInfos 0
        finalReader.lctx model finalModel chronological
        [motive, minorFalse, minorTrue, major] ∧
      TrExprS canonicalBoolModel [`u] finalModel.vlctx
        (recursorTypeBody finalInfos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 finalModel.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats finalInfos 0 finalReader.lctx =
        finalModel.lctx.mkForall
          ([motive, minorFalse, minorTrue, major].map Expr.fvar).toArray
          (recursorTypeBody finalInfos 0) ∧
      TrConstVal .safe canonicalBoolModel
        (.recInfo (declareRecursors.metadataVal stats types elimLevel finalInfos lparams
          finalReader.lctx isK false 0 rules)) constant ∧
      constant.toVConstant.WF canonicalBoolModel := by
  obtain ⟨finalModel, major, motive, minorFalse, minorTrue, chronological,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase⟩ :=
    canonicalBoolPassModelEndpointWithKnownFinalInfoRebase typesEq parentTrace parentHistory
      minorTrace normalization params levels indConsts nindices boolIndices reserved finalInfosEq
      initialIndices initialMinors
  have bodyReceipt := endpoint.canonicalBoolRebasedFinalBodyApplicationReceipt canonicalBoolModel.wf
      params finalInfosEq finalMotiveEq finalMinorsEq finalIndicesEq finalMajorEq
      (canonicalBoolAllocationOfKnownExtension known) source
      mapped minorSemantics generatedRuleSemantics iotaSoundness
  obtain ⟨_, bodySemantic, level, bodyReceipt, bodyTranslated, bodyTyped, bodyRaw⟩ := bodyReceipt
  have parameterFree : stats.params.size = 0 := by simpa [params]
  have bound : 0 < types.size := by simpa [typesEq]
  have order : ∀ ids, IndexMLCtxExtension model ids finalModel →
      [motive, minorFalse, minorTrue, major].Perm ids := by
    intro ids extension
    rw [canonicalBoolAllocationOfKnownExtension known ids extension]
    exact canonicalBoolRecursorBinderOrderPermutation
  have alignment : (recursorTypeBinders stats finalInfos 0).toList =
      [motive, minorFalse, minorTrue, major].map Expr.fvar := by
    simpa [recursorTypeBinders, params, finalInfosEq, finalMotiveEq, finalMinorsEq,
      finalIndicesEq, finalMajorEq]
  have finalMotiveEq' : finalInfos[0]!.motive = .fvar motive := by
    simpa [finalInfosEq] using finalMotiveEq
  have finalIndicesEq' : finalInfos[0]!.indices = #[] := by
    simpa [finalInfosEq] using finalIndicesEq
  have finalMajorEq' : finalInfos[0]!.major = .fvar major := by
    simpa [finalInfosEq] using finalMajorEq
  have finalMinorsEq' : finalInfos[0]!.minors = #[.fvar minorFalse, .fvar minorTrue] := by
    simpa [finalInfosEq] using finalMinorsEq
  obtain ⟨chronological', bodySemantic', bodyLevel', constant,
    declarationReceipt⟩ :=
    endpoint.canonicalBoolDeclaredRecursorReceipt canonicalBoolModel.wf modelWF parameterFree bound
      source mapped support [motive, minorFalse, minorTrue, major] order alignment
      (by simp) (by simp) finalMotiveEq' finalIndicesEq' finalMajorEq'
      lparams isK rules recursorLevels empty minorSemantics generatedRuleSemantics iotaSoundness
  obtain ⟨_, _, _, _, constantTranslated, constantWF⟩ := declarationReceipt
  exact ⟨finalModel, major, motive, minorFalse, minorTrue, chronological, bodySemantic, level,
    constant, endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase,
    bodyTranslated, bodyTyped, bodyRaw, constantTranslated, constantWF⟩

theorem canonicalBoolPassModelEndpointWithKnownFinalInfoRegisteredRecursorInsertion
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
    (initialMinors : infos[0]!.minors = #[])
    (modelWF : model.WF canonicalBoolModel [`u])
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader finalInfos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport canonicalBoolModel [`u] stats finalInfos 0
      finalReader.lctx model)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (recursorLevels : getRecLevelParams elimLevel lparams = [`u])
    (empty : model.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel finalInfos
      lparams finalReader.lctx isK false 0 rules) :
    ∃ finalModel major motive minorFalse minorTrue chronological constant extended,
      RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
        reader finalInfos finalReader model finalModel ∧
      info.major = .fvar major ∧ info.motive = .fvar motive ∧
      info.indices = #[] ∧ info.minors = #[.fvar minorFalse, .fvar minorTrue] ∧
      IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel ∧
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats finalInfos 0
        finalReader.lctx model finalModel chronological
        [motive, minorFalse, minorTrue, major] ∧
      registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt canonicalBoolModel [`u] stats finalInfos 0
        finalReader model finalModel ∧
      TrConstVal .safe canonicalBoolModel (.recInfo recursor) constant ∧
      constant.toVConstant.WF canonicalBoolModel ∧
      canonicalBoolModel.addConstructorHeaders [constant] = some extended ∧
      extended.WF := by
  obtain ⟨finalModel, major, motive, minorFalse, minorTrue, chronological,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase⟩ :=
    canonicalBoolPassModelEndpointWithKnownFinalInfoRebase typesEq parentTrace parentHistory
      minorTrace normalization params levels indConsts nindices boolIndices reserved finalInfosEq
      initialIndices initialMinors
  have parameterFree : stats.params.size = 0 := by simpa [params]
  have bound : 0 < types.size := by simpa [typesEq]
  have order : ∀ ids, IndexMLCtxExtension model ids finalModel →
      [motive, minorFalse, minorTrue, major].Perm ids := by
    intro ids extension
    rw [canonicalBoolAllocationOfKnownExtension known ids extension]
    exact canonicalBoolRecursorBinderOrderPermutation
  have alignment : (recursorTypeBinders stats finalInfos 0).toList =
      [motive, minorFalse, minorTrue, major].map Expr.fvar := by
    simpa [recursorTypeBinders, params, finalInfosEq, finalMotiveEq, finalMinorsEq,
      finalIndicesEq, finalMajorEq]
  have fresh : (canonicalBoolModel : VEnv).constants (mkRecName types[0]!.name) = none := by
    rw [typesEq]
    rfl
  obtain ⟨constant, extended, registeredLookup, typeReceipt, translated, wellFormed,
    insertion, extendedWF⟩ :=
    endpoint.registeredRecursorInsertionFromDomains canonicalBoolModel.wf modelWF parameterFree
      bound source mapped support lparams isK rules recursorLevels empty lookup metadata fresh
  exact ⟨finalModel, major, motive, minorFalse, minorTrue, chronological, constant, extended,
    endpoint, finalMajorEq, finalMotiveEq, finalIndicesEq, finalMinorsEq, known, rebase,
    registeredLookup, typeReceipt, translated, wellFormed, insertion, extendedWF⟩

theorem canonicalBoolPassModelEndpoint
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
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
      reader finalInfos finalReader model finalModel := by
  obtain ⟨finalModel, _, endpoint, _, _⟩ :=
    canonicalBoolPassModelEndpointWithParentMotiveSupport typesEq parentTrace minorTrace
      normalization params levels indConsts nindices boolIndices motives motiveSupport model modelWF
      native reserved mapped
  exact ⟨finalModel, endpoint⟩

end Lean4Lean.AddInductive
