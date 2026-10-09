import Lean4Lean.Verify.InductiveMotiveContextTranslationCPS
import Lean4Lean.Verify.InductiveParentPassTrace
import Lean4Lean.Verify.InductiveParentContextTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def ParentModelTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (parent : Nat)
    {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context}
    (trace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader) : Prop :=
  ∀ model : TypeChecker.MLCtx,
    model.WF env universes → model.lctx = reader.lctx →
    ∃ semantic,
      TrExprS env universes model.vlctx normalized semantic ∧
      IndexTraceAnnotationSupport env universes trace ∧
      IndexTraceNormalizationSupport env universes trace ∧
      ∀ finalVirtual finalSemantic,
        TranslatedRecursorIndexTrace env universes trace model.vlctx semantic finalVirtual finalSemantic →
        ∃ headSemantic level,
          TrExprS env universes model.vlctx stats.indConsts[parent]! headSemantic ∧
          env.HasType universes.length model.vlctx.toCtx headSemantic semantic ∧
          finalSemantic = .sort level ∧
          UniformAnnotationUniverse universes
            (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level

inductive RecursorParentPassTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} :
    {parent : Nat} → {infos finalInfos : Array RecInfo} → {reader finalReader : Context} →
    RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context}
      (complete : ¬ parent < types.size) :
      RecursorParentPassTranslationSupport env universes
        (.stop (parent := parent) (infos := infos) (reader := reader) complete)
  | step {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader indexReader : Context}
      {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
      (bound : parent < types.size)
      (initialNormalization :
        ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) reader) = .ok normalized)
      (indicesTrace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader)
      (tail : RecursorParentPassTrace stats types elimLevel (parent + 1)
        (infos.push (recursorParentPassInfo stats parent indices indexReader))
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent))
        finalInfos finalReader)
      (headSupport : ParentModelTranslationSupport env universes stats parent indicesTrace)
      (tailSupport : RecursorParentPassTranslationSupport env universes tail) :
      RecursorParentPassTranslationSupport env universes (.step bound initialNormalization indicesTrace tail)

theorem ParentModelTranslationSupport.translatedIndices
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context}
    {trace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader}
    (support : ParentModelTranslationSupport env universes stats parent trace)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ semantic finalVirtual finalSemantic,
      ∃ _history : TranslatedRecursorIndexTrace env universes trace model.vlctx semantic finalVirtual finalSemantic,
      ∃ headSemantic level,
      TrExprS env universes model.vlctx stats.indConsts[parent]! headSemantic ∧
      env.HasType universes.length model.vlctx.toCtx headSemantic semantic ∧
      finalSemantic = .sort level ∧
      UniformAnnotationUniverse universes
        (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level := by
  obtain ⟨semantic, translated, annotations, normalizations, majorSupport⟩ := support model modelWF native
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := native ▸ modelWF.tr
  obtain ⟨finalVirtual, finalSemantic, history⟩ := trace.translated envWF constants definitions
    (by omega) correspondence reserved translated annotations normalizations
  obtain ⟨headSemantic, level, headTranslated, headTyped, finalSort, uniform⟩ :=
    majorSupport finalVirtual finalSemantic history
  exact ⟨semantic, finalVirtual, finalSemantic, history, headSemantic, level,
    headTranslated, headTyped, finalSort, uniform⟩

inductive TranslatedRecursorParentPass (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} :
    {parent : Nat} → {infos finalInfos : Array RecInfo} → {reader finalReader : Context} →
    RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader →
    TypeChecker.MLCtx → TypeChecker.MLCtx → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context} {model : TypeChecker.MLCtx}
      (complete : ¬ parent < types.size)
      (modelWF : model.WF env universes) (native : model.lctx = reader.lctx) :
      TranslatedRecursorParentPass env universes
        (.stop (parent := parent) (infos := infos) (reader := reader) complete) model model
  | step {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader indexReader : Context}
      {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
      {model nextModel finalModel : TypeChecker.MLCtx} {semantic indexSemantic : VExpr}
      {indexVirtual : VLCtx} {allocated : List FVarId}
      (bound : parent < types.size)
      (initialNormalization :
        ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) reader) = .ok normalized)
      (indicesTrace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader)
      (tail : RecursorParentPassTrace stats types elimLevel (parent + 1)
        (infos.push (recursorParentPassInfo stats parent indices indexReader))
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent))
        finalInfos finalReader)
      (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
      (history : TranslatedRecursorIndexTrace env universes indicesTrace
        model.vlctx semantic indexVirtual indexSemantic)
      (modelStep : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
        indexVirtual model nextModel allocated)
      (translatedTail : TranslatedRecursorParentPass env universes tail nextModel finalModel) :
      TranslatedRecursorParentPass env universes
        (.step bound initialNormalization indicesTrace tail) model finalModel

theorem TranslatedRecursorParentPass.context
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (translated : TranslatedRecursorParentPass env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  induction translated with
  | stop _ modelWF native => exact ⟨modelWF, native, native ▸ modelWF.tr⟩
  | step _ _ _ _ _ _ _ _ _ tailInduction => exact tailInduction

theorem TranslatedRecursorParentPass.extension
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader}
    {initial final : TypeChecker.MLCtx}
    (translated : TranslatedRecursorParentPass env universes trace initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final := by
  induction translated with
  | stop => exact ⟨[], .nil⟩
  | step _ _ _ _ _ _ _ modelStep _ tailInduction =>
    obtain ⟨allocated, extension⟩ := tailInduction
    exact ⟨_, modelStep.extension.trans extension⟩

theorem RecursorParentPassTrace.translated
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader)
    (support : RecursorParentPassTranslationSupport env universes trace)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ finalModel, TranslatedRecursorParentPass env universes trace model finalModel := by
  induction support generalizing model with
  | stop complete => exact ⟨model, .stop complete modelWF native⟩
  | @step parent infos finalInfos reader finalReader indexReader normalized terminal finalIndex indices
      bound initialNormalization indicesTrace tail headSupport tailSupport tailInduction =>
    obtain ⟨semantic, indexVirtual, indexSemantic, history,
      headSemantic, level, headTranslated, headTyped, finalSort, uniform⟩ :=
      headSupport.translatedIndices envWF constants definitions indexOnly model modelWF native reserved
    obtain ⟨nextModel, allocated, modelStep⟩ := history.parentModelStep (types := types) (parent := parent)
      envWF constants definitions indexOnly model modelWF native rfl reserved
      headTranslated headTyped finalSort uniform mapped
    have nodeFrame : reader.RecursorScopeFrame
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)) := by
      obtain ⟨_, _, _, _, _, majorOpening, motiveOpening, _⟩ := modelStep
      exact (history.scope reserved).trans
        (majorOpening.2.2.2.2.2.2.2.trans motiveOpening.2.2.2)
    obtain ⟨nextWF, nextNative⟩ := modelStep.model
    obtain ⟨finalModel, translatedTail⟩ := tailInduction nextModel nextWF nextNative nodeFrame.reserved
    exact ⟨finalModel, .step bound initialNormalization indicesTrace tail modelWF native history
      modelStep translatedTail⟩

theorem mkRecInfos.loopInd1.getTranslatedParentPass
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (mkRecInfos.loopInd1 stats types elimLevel parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size + (types.size - parent) ∧
      ∃ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
      ∃ finalModel, TranslatedRecursorParentPass env universes trace model finalModel ∧
        finalModel.WF env universes ∧ finalModel.lctx = result.2.lctx ∧
        TrLCtx env universes result.2.lctx finalModel.vlctx ∧
        ∃ allocated, IndexMLCtxExtension model allocated finalModel := by
  intro result success
  obtain ⟨trace, frame, counts⟩ := mkRecInfos.loopInd1.getParentPassTrace stats types elimLevel parent infos
    reader (native ▸ modelWF.tr.1) reserved result success
  obtain ⟨finalModel, translated⟩ := trace.translated (support result success trace)
    envWF constants definitions indexOnly model modelWF native reserved mapped
  obtain ⟨finalWF, finalNative, correspondence⟩ := translated.context
  exact ⟨frame, counts, trace, finalModel, translated, finalWF, finalNative, correspondence, translated.extension⟩

theorem mkRecInfos.loopInd1.scopedTranslatedParentPass {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (mkRecInfos.loopInd1 stats types elimLevel parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel parent infos reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      TranslatedRecursorParentPass env universes trace model finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd1 stats types elimLevel parent infos next reader).WF post := by
  rw [mkRecInfos.loopInd1.morphism stats types elimLevel parent infos next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.loopInd1.getTranslatedParentPass stats types elimLevel parent infos reader
    envWF constants definitions indexOnly model modelWF native reserved mapped support).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, _, trace, finalModel, translated, _, _, correspondence, _⟩
  exact nextWF finalInfos finalReader trace finalModel frame translated correspondence

theorem mkRecInfos.fromTypedParentPass {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorWF : ∀ finalInfos parentReader
      (trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader finalInfos parentReader) finalModel,
      reader.RecursorScopeFrame parentReader →
      TranslatedRecursorParentPass env universes trace model finalModel →
      TrLCtx env universes parentReader.lctx finalModel.vlctx →
      (mkRecInfos.loopInd2 stats types 0 finalInfos next parentReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  exact mkRecInfos.loopInd1.scopedTranslatedParentPass stats types elimLevel 0 #[]
    (fun infos => mkRecInfos.loopInd2 stats types 0 infos next) reader post
    envWF constants definitions indexOnly model modelWF native reserved mapped support minorWF

end Lean4Lean.AddInductive
