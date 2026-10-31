import Lean4Lean.Verify.CanonicalBoolParentPassSupport
import Lean4Lean.Verify.CanonicalBoolMinorPassSupport
import Lean4Lean.Verify.InductiveMinorPassTranslationCPS

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
