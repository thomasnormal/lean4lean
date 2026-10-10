import Lean4Lean.Verify.InductiveMinorTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def MinorSourceTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    (_source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (model : MLCtx) : Prop :=
  ∀ terminal finalIndex fields recursiveFields fieldReader hypotheses
    (fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader)
    (hypothesisTrace : RecursorIHTrace stats recursiveFields infos 0 #[] fieldReader
      hypotheses domainReader),
    domain = recursorMinorDomain stats infos constructor terminal fields hypotheses domainReader →
    ∃ sourceSemantic headSemantic,
      TrExprS env universes model.vlctx constructor.type sourceSemantic ∧
      TrExprS env universes model.vlctx
        (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic ∧
      env.HasType universes.length model.vlctx.toCtx headSemantic sourceSemantic ∧
      CtorFieldTraceAnnotationSupport env universes fieldTrace ∧
      IHTraceTranslationSupport env universes hypothesisTrace ∧
      IndexAnnotationSupport env universes domainReader domain ∧
      ∀ fieldModel, CtorFieldModelEndpoint env universes fieldTrace model fieldModel sourceSemantic →
        IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal

def MinorModelStep (env : VEnv) (universes : List Name) (parentName : Name)
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    (_source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (initial final : MLCtx) : Prop :=
  ∃ terminal finalIndex fields recursiveFields fieldReader hypotheses,
    ∃ fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader,
    ∃ hypothesisTrace : RecursorIHTrace stats recursiveFields infos 0 #[] fieldReader
      hypotheses domainReader,
    ∃ semantic fieldModel hypothesisModel rawSemantic peeled level,
      domain = recursorMinorDomain stats infos constructor terminal fields hypotheses domainReader ∧
      CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic ∧
      TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel ∧
      RecursorMinorOpening env universes domainReader hypothesisModel.vlctx parentName constructor
        domain rawSemantic peeled level ∧
      final = recursorMinorMLCtx domainReader hypothesisModel parentName constructor domain peeled ∧
      final.WF env universes ∧
      final.lctx = (recursorMinorContext domainReader parentName constructor domain).lctx

theorem MinorModelStep.context {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx} (step : MinorModelStep env universes parentName source initial final) :
    final.WF env universes ∧
      final.lctx = (recursorMinorContext domainReader parentName constructor domain).lctx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, modelWF, native⟩ := step
  exact ⟨modelWF, native⟩

theorem MinorModelStep.extension {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx} (step : MinorModelStep env universes parentName source initial final) :
    ∃ ids, IndexMLCtxExtension initial ids final := by
  obtain ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, modelWF, native⟩ := step
  obtain ⟨_, _, _, _, _, _, fieldIds, fieldExtension, _⟩ := endpoint
  obtain ⟨hypothesisIds, hypothesisExtension, _⟩ := history.extension
  rw [finalEq]
  exact ⟨_, fieldExtension.trans (hypothesisExtension.trans (opening.extension hypothesisModel))⟩

theorem RecursorMinorDomainSource.translatedStep {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (parentName : Name) (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : MinorSourceTranslationSupport env universes source model) :
    ∃ finalModel, MinorModelStep env universes parentName source model finalModel := by
  obtain ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, domainEq⟩ := source
  obtain ⟨semantic, headSemantic, sourceTranslated, headTranslated, headTyped,
    fieldAnnotations, hypothesisSupport, annotations, motiveSupport⟩ :=
    support terminal finalIndex fields recursiveFields fieldReader hypotheses fieldTrace
      hypothesisTrace domainEq
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  obtain ⟨fieldVirtual, terminalSemantic, fieldHistory⟩ := fieldTrace.translated envWF constants
    definitions (by omega) correspondence reserved sourceTranslated fieldAnnotations
  obtain ⟨fieldModel, fieldIds, fieldWF, fieldNative, fieldConverted, fieldExtension, fieldSelected⟩ :=
    fieldHistory.mixedContext model modelWF native rfl reserved
  have endpoint : CtorFieldModelEndpoint env universes fieldTrace model fieldModel semantic :=
    ⟨fieldVirtual, terminalSemantic, fieldHistory, fieldWF, fieldNative, fieldConverted,
      fieldIds, fieldExtension, by simpa only [Array.toList_empty, List.nil_append] using fieldSelected⟩
  have fieldFrame := fieldTrace.scope (native ▸ modelWF.tr.1) reserved
  obtain ⟨hypothesisModel, history⟩ := hypothesisTrace.translated envWF constants definitions
    fieldModel fieldWF fieldNative fieldFrame.reserved hypothesisSupport
  have domainAnnotations : IndexAnnotationSupport env universes domainReader
      (recursorMinorDomain stats infos constructor terminal fields hypotheses domainReader) := by
    simpa only [domainEq] using annotations
  obtain ⟨rawSemantic, peeled, level, receipt⟩ := endpoint.minorOpening history parentName
    envWF constants definitions modelWF fieldFrame.reserved headTranslated headTyped
      (motiveSupport fieldModel endpoint) domainAnnotations
  have opening : RecursorMinorOpening env universes domainReader hypothesisModel.vlctx
      parentName constructor domain rawSemantic peeled level := by
    simpa only [domainEq] using receipt
  have hypothesisFrame := hypothesisTrace.scope fieldFrame.wf fieldFrame.reserved
  obtain ⟨finalWF, finalNative, _⟩ := opening.mixedContext hypothesisModel history.context.1
    history.context.2.1 rfl hypothesisFrame.reserved
  exact ⟨_, terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, rfl, finalWF, finalNative⟩

inductive MinorTraceTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {parentName : Name} {parentIndex : Nat} :
    {infos : Array RecInfo} → {constructors : List Constructor} → {reader : Context} →
    {finalInfos : Array RecInfo} → {finalReader : Context} →
    RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader → Prop where
  | stop {infos : Array RecInfo} {reader : Context} :
      MinorTraceTranslationSupport env universes (.stop (infos := infos) (reader := reader))
  | step {infos finalInfos : Array RecInfo} {constructor : Constructor} {constructors : List Constructor}
      {reader domainReader finalReader : Context} {domain : Expr}
      (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
      (tail : RecursorMinorTrace stats parentName parentIndex
        (recursorMinorUpdate parentIndex infos (.fvar ⟨domainReader.ngen.curr⟩)) constructors
        (recursorMinorContext domainReader parentName constructor domain) finalInfos finalReader)
      (head : ∀ model : MLCtx, model.WF env universes → model.lctx = reader.lctx →
        MinorSourceTranslationSupport env universes source model)
      (rest : MinorTraceTranslationSupport env universes tail) :
      MinorTraceTranslationSupport env universes (.step source tail)

inductive TranslatedRecursorMinorTrace (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {parentName : Name} {parentIndex : Nat} :
    {infos : Array RecInfo} → {constructors : List Constructor} → {reader : Context} →
    {finalInfos : Array RecInfo} → {finalReader : Context} →
    RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader →
      MLCtx → MLCtx → Prop where
  | stop {infos : Array RecInfo} {reader : Context} {model : MLCtx}
      (modelWF : model.WF env universes) (native : model.lctx = reader.lctx) :
      TranslatedRecursorMinorTrace env universes (.stop (infos := infos) (reader := reader)) model model
  | step {infos finalInfos : Array RecInfo} {constructor : Constructor} {constructors : List Constructor}
      {reader domainReader finalReader : Context} {domain : Expr} {initial middle final : MLCtx}
      (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
      (tail : RecursorMinorTrace stats parentName parentIndex
        (recursorMinorUpdate parentIndex infos (.fvar ⟨domainReader.ngen.curr⟩)) constructors
        (recursorMinorContext domainReader parentName constructor domain) finalInfos finalReader)
      (head : MinorModelStep env universes parentName source initial middle)
      (rest : TranslatedRecursorMinorTrace env universes tail middle final) :
      TranslatedRecursorMinorTrace env universes (.step source tail) initial final

theorem TranslatedRecursorMinorTrace.context {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    {trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorMinorTrace env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  induction history with
  | stop modelWF native => exact ⟨modelWF, native, by simpa only [native] using modelWF.tr⟩
  | step _ _ _ _ tailInduction => exact tailInduction

theorem TranslatedRecursorMinorTrace.extension {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    {trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorMinorTrace env universes trace initial final) :
    ∃ ids, IndexMLCtxExtension initial ids final := by
  induction history with
  | stop => exact ⟨[], .nil⟩
  | step _ _ head _ tailInduction =>
    obtain ⟨headIds, headExtension⟩ := head.extension
    obtain ⟨tailIds, tailExtension⟩ := tailInduction
    exact ⟨headIds ++ tailIds, headExtension.trans tailExtension⟩

theorem RecursorMinorTrace.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {parentName : Name} {parentIndex : Nat}
    {infos finalInfos : Array RecInfo} {constructors : List Constructor} {reader finalReader : Context}
    (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : MinorTraceTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorMinorTrace env universes trace model finalModel := by
  induction support generalizing model with
  | stop => exact ⟨model, .stop modelWF native⟩
  | @step infos finalInfos constructor constructors reader domainReader finalReader domain
      source tail head rest tailInduction =>
    obtain ⟨middle, step⟩ := source.translatedStep parentName envWF constants definitions fieldOnly
      model modelWF native reserved (head model modelWF native)
    have domainFrame := source.scope (native ▸ modelWF.tr.1) reserved
    have pushed := Context.RecursorScopeFrame.push domainReader domainFrame.wf domainFrame.reserved
      (recursorMinorName parentName constructor) .default (peelTypeAnnotations domain)
    obtain ⟨finalModel, history⟩ := tailInduction middle step.context.1 step.context.2 pushed.reserved
    exact ⟨finalModel, .step source tail step history⟩

theorem mkRecInfos.loopCtors.getTranslatedMinors {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (parentName : Name) (parentIndex : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopCtors stats parentName parentIndex infos constructors
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader result.1 result.2,
        MinorTraceTranslationSupport env universes trace) :
    (mkRecInfos.loopCtors stats parentName parentIndex infos constructors
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ result.1.size = infos.size ∧
      ∃ trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorMinorTrace env universes trace model finalModel := by
  intro result success
  obtain ⟨trace, frame, size⟩ := mkRecInfos.loopCtors.getTrace stats parentName parentIndex infos
    constructors reader (native ▸ modelWF.tr.1) reserved result success
  obtain ⟨finalModel, history⟩ := trace.translated envWF constants definitions fieldOnly model
    modelWF native reserved (support result success trace)
  exact ⟨frame, size, trace, finalModel, history⟩

theorem mkRecInfos.loopCtors.scopedTranslatedMinors {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (parentName : Name) (parentIndex : Nat)
    (infos : Array RecInfo) (constructors : List Constructor) (next : Array RecInfo → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopCtors stats parentName parentIndex infos constructors
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader result.1 result.2,
        MinorTraceTranslationSupport env universes trace)
    (nextWF : ∀ finalInfos finalReader
      (trace : RecursorMinorTrace stats parentName parentIndex infos constructors reader finalInfos finalReader)
      finalModel, reader.RecursorScopeFrame finalReader →
      TranslatedRecursorMinorTrace env universes trace model finalModel →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos.loopCtors stats parentName parentIndex infos constructors next reader).WF post := by
  rw [mkRecInfos.loopCtors.morphism stats parentName parentIndex infos constructors next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.loopCtors.getTranslatedMinors stats parentName parentIndex infos constructors
    reader envWF constants definitions fieldOnly model modelWF native reserved support).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, _, trace, finalModel, history⟩
  exact nextWF finalInfos finalReader trace finalModel frame history

end Lean4Lean.AddInductive
