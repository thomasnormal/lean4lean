import Lean4Lean.Verify.InductiveMinorPassTrace
import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveParentContextTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

inductive MinorPassTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {types : Array InductiveType} :
    {parent : Nat} → {infos finalInfos : Array RecInfo} → {reader finalReader : Context} →
    RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context}
      (complete : ¬ parent < types.size) :
      MinorPassTranslationSupport env universes
        (.stop (parent := parent) (infos := infos) (reader := reader) complete)
  | step {parent : Nat} {infos middleInfos finalInfos : Array RecInfo}
      {reader middleReader finalReader : Context}
      (bound : parent < types.size)
      (head : RecursorMinorTrace stats types[parent]!.name parent infos types[parent]!.ctors
        reader middleInfos middleReader)
      (tail : RecursorMinorPassTrace stats types (parent + 1) middleInfos middleReader
        finalInfos finalReader)
      (headSupport : MinorTraceTranslationSupport env universes head)
      (tailSupport : MinorPassTranslationSupport env universes tail) :
      MinorPassTranslationSupport env universes (.step bound head tail)

inductive TranslatedRecursorMinorPass (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {types : Array InductiveType} :
    {parent : Nat} → {infos finalInfos : Array RecInfo} → {reader finalReader : Context} →
    RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader →
      MLCtx → MLCtx → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context} {model : MLCtx}
      (complete : ¬ parent < types.size) (modelWF : model.WF env universes)
      (native : model.lctx = reader.lctx) :
      TranslatedRecursorMinorPass env universes
        (.stop (parent := parent) (infos := infos) (reader := reader) complete) model model
  | step {parent : Nat} {infos middleInfos finalInfos : Array RecInfo}
      {reader middleReader finalReader : Context} {initial middle final : MLCtx}
      (bound : parent < types.size)
      (head : RecursorMinorTrace stats types[parent]!.name parent infos types[parent]!.ctors
        reader middleInfos middleReader)
      (tail : RecursorMinorPassTrace stats types (parent + 1) middleInfos middleReader
        finalInfos finalReader)
      (headTranslated : TranslatedRecursorMinorTrace env universes head initial middle)
      (tailTranslated : TranslatedRecursorMinorPass env universes tail middle final) :
      TranslatedRecursorMinorPass env universes (.step bound head tail) initial final

theorem TranslatedRecursorMinorPass.context
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorMinorPass env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  induction history with
  | stop _ modelWF native => exact ⟨modelWF, native, native ▸ modelWF.tr⟩
  | step _ _ _ _ _ tailInduction => exact tailInduction

theorem TranslatedRecursorMinorPass.extension
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    {trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorMinorPass env universes trace initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final := by
  induction history with
  | stop => exact ⟨[], .nil⟩
  | step _ _ _ head _ tailInduction =>
    obtain ⟨headIds, headExtension⟩ := head.extension
    obtain ⟨tailIds, tailExtension⟩ := tailInduction
    exact ⟨headIds ++ tailIds, headExtension.trans tailExtension⟩

theorem RecursorMinorPassTrace.translated
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : MinorPassTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorMinorPass env universes trace model finalModel := by
  induction support generalizing model with
  | stop complete => exact ⟨model, .stop complete modelWF native⟩
  | @step parent infos middleInfos finalInfos reader middleReader finalReader bound
      head tail headSupport tailSupport tailInduction =>
    obtain ⟨middleModel, headHistory⟩ := head.translated envWF constants definitions fieldOnly
      model modelWF native reserved headSupport
    have headFrame := head.scope (native ▸ modelWF.tr.1) reserved
    obtain ⟨finalModel, tailHistory⟩ := tailInduction middleModel headHistory.context.1
      headHistory.context.2.1 headFrame.reserved
    exact ⟨finalModel, .step bound head tail headHistory tailHistory⟩

theorem mkRecInfos.loopInd2.getTranslatedMinorPass
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopInd2 stats types parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        MinorPassTranslationSupport env universes trace) :
    (mkRecInfos.loopInd2 stats types parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size ∧
      ∃ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorMinorPass env universes trace model finalModel := by
  intro result success
  obtain ⟨trace, frame, size⟩ := mkRecInfos.loopInd2.getMinorPassTrace stats types parent infos reader
    (native ▸ modelWF.tr.1) reserved result success
  obtain ⟨finalModel, history⟩ := trace.translated envWF constants definitions fieldOnly model
    modelWF native reserved (support result success trace)
  exact ⟨frame, size, trace, finalModel, history⟩

theorem mkRecInfos.loopInd2.scopedTranslatedMinorPass {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat)
    (infos : Array RecInfo) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopInd2 stats types parent infos
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorPassTrace stats types parent infos reader result.1 result.2,
        MinorPassTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorMinorPassTrace stats types parent infos reader finalInfos finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      TranslatedRecursorMinorPass env universes trace model finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopInd2 stats types parent infos next reader).WF post := by
  rw [mkRecInfos.loopInd2.morphism stats types parent infos next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.loopInd2.getTranslatedMinorPass stats types parent infos reader
    envWF constants definitions fieldOnly model modelWF native reserved support).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, _, trace, finalModel, history⟩
  exact nextWF finalInfos finalReader trace finalModel frame history history.context.2.2

def RecursorInfoModelEndpoint (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (reader : Context) (finalInfos : Array RecInfo) (finalReader : Context)
    (initial final : MLCtx) : Prop :=
  ∃ parentInfos parentReader parentModel,
    ∃ parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader,
    ∃ minorTrace : RecursorMinorPassTrace stats types 0 parentInfos parentReader finalInfos finalReader,
      TranslatedRecursorParentPass env universes parentTrace initial parentModel ∧
      TranslatedRecursorMinorPass env universes minorTrace parentModel final

theorem RecursorInfoModelEndpoint.context
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, _, _, _, minorHistory⟩ := endpoint
  exact minorHistory.context

theorem RecursorInfoModelEndpoint.extension
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    ∃ allocated, IndexMLCtxExtension initial allocated final := by
  obtain ⟨_, _, _, _, _, parentHistory, minorHistory⟩ := endpoint
  obtain ⟨parentIds, parentExtension⟩ := parentHistory.extension
  obtain ⟨minorIds, minorExtension⟩ := minorHistory.extension
  exact ⟨parentIds ++ minorIds, parentExtension.trans minorExtension⟩

theorem RecursorInfoModelEndpoint.infoSize
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {finalInfos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader finalInfos finalReader initial final) :
    finalInfos.size = types.size := by
  obtain ⟨_, _, _, parentTrace, minorTrace, _, _⟩ := endpoint
  rw [minorTrace.infoSize]
  simpa only [Array.size_empty, Nat.sub_zero, Nat.zero_add] using parentTrace.counts

theorem mkRecInfos.fromTypedPasses {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (nextWF : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel finalInfos finalReader
      (minorTrace : RecursorMinorPassTrace stats types 0 parentInfos parentReader finalInfos finalReader)
      finalModel,
      reader.RecursorScopeFrame parentReader → parentReader.RecursorScopeFrame finalReader →
      TranslatedRecursorParentPass env universes parentTrace model parentModel →
      TranslatedRecursorMinorPass env universes minorTrace parentModel finalModel →
      TrLCtx env universes finalReader.lctx finalModel.vlctx → (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  refine mkRecInfos.fromTypedParentPass stats types elimLevel next reader post envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport ?_
  intro parentInfos parentReader parentTrace parentModel parentFrame parentHistory parentCorrespondence
  refine mkRecInfos.loopInd2.scopedTranslatedMinorPass stats types 0 parentInfos next parentReader
    post envWF constants definitions fieldOnly parentModel parentHistory.context.1
    parentHistory.context.2.1 parentFrame.reserved
    (minorSupport parentInfos parentReader parentTrace parentModel parentHistory) ?_
  intro finalInfos finalReader minorTrace finalModel minorFrame minorHistory finalCorrespondence
  exact nextWF parentInfos parentReader parentTrace parentModel finalInfos finalReader minorTrace
    finalModel parentFrame minorFrame parentHistory minorHistory finalCorrespondence

theorem mkRecInfos.getTranslatedPasses
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = types.size ∧
      RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel := by
  have translated : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = types.size ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel := by
    refine mkRecInfos.fromTypedPasses stats types elimLevel _ reader _ envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport ?_
    intro parentInfos parentReader parentTrace parentModel finalInfos finalReader minorTrace finalModel
      parentFrame minorFrame parentHistory minorHistory finalCorrespondence
    have endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
        reader finalInfos finalReader model finalModel :=
      ⟨parentInfos, parentReader, parentModel, parentTrace, minorTrace, parentHistory, minorHistory⟩
    exact .pure ⟨parentFrame.trans minorFrame, endpoint.infoSize, finalModel, endpoint⟩
  intro result success
  obtain ⟨frame, size, finalModel, endpoint⟩ := translated result success
  obtain ⟨_, counts⟩ := mkRecInfos.getCounts stats types elimLevel reader result success
  exact ⟨frame, size, counts, finalModel, endpoint⟩

end Lean4Lean.AddInductive
