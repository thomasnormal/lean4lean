import Lean4Lean.Verify.InductiveIHTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def IHDomainSourceTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {infos : Array RecInfo} {argument domain : Expr} {reader : Context}
    (_source : RecursorIHDomainSource stats infos argument reader domain) (model : MLCtx) : Prop :=
  ∀ terminal arguments argumentReader
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments argumentReader),
    domain = recursorIHDomain stats infos argument terminal arguments argumentReader →
    UArgOpeningTranslationSupport env universes opening model.vlctx ∧
    IndexAnnotationSupport env universes reader domain ∧
    ∀ argumentModel, UArgModelEndpoint env universes opening model argumentModel →
      IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal

def IHModelStep (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {infos : Array RecInfo} {argument domain : Expr} {reader : Context}
    (_source : RecursorIHDomainSource stats infos argument reader domain)
    (initial final : MLCtx) : Prop :=
  ∃ terminal arguments argumentReader,
    ∃ opening : RecursorUArgOpeningTrace argument reader terminal arguments argumentReader,
    ∃ argumentModel rawSemantic peeled level,
      domain = recursorIHDomain stats infos argument terminal arguments argumentReader ∧
      UArgModelEndpoint env universes opening initial argumentModel ∧
      RecursorIHOpening env universes reader initial.vlctx argument domain rawSemantic peeled level ∧
      final = recursorIHMLCtx reader initial argument domain peeled ∧
      final.WF env universes ∧ final.lctx = (recursorIHContext reader argument domain).lctx

theorem IHModelStep.context {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {infos : Array RecInfo} {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain} {initial final : MLCtx}
    (step : IHModelStep env universes source initial final) :
    final.WF env universes ∧ final.lctx = (recursorIHContext reader argument domain).lctx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, modelWF, native⟩ := step
  exact ⟨modelWF, native⟩

theorem IHModelStep.extension {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {infos : Array RecInfo} {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain} {initial final : MLCtx}
    (step : IHModelStep env universes source initial final) :
    IndexMLCtxExtension initial [⟨reader.ngen.curr⟩] final := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, opening, finalEq, _, _⟩ := step
  rw [finalEq]
  exact opening.extension initial

theorem RecursorIHDomainSource.translatedStep {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {infos : Array RecInfo} {argument domain : Expr} {reader : Context}
    (source : RecursorIHDomainSource stats infos argument reader domain)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : IHDomainSourceTranslationSupport env universes source model) :
    ∃ finalModel, IHModelStep env universes source model finalModel := by
  obtain ⟨terminal, arguments, argumentReader, opening, domainEq⟩ := source
  obtain ⟨argumentSupport, annotations, motiveSupport⟩ :=
    support terminal arguments argumentReader opening domainEq
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  obtain ⟨finalVirtual, finalSemantic, history⟩ := opening.translated envWF constants definitions
    correspondence reserved argumentSupport
  obtain ⟨argumentModel, ids, finalWF, finalNative, finalConverted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  have endpoint : UArgModelEndpoint env universes opening model argumentModel :=
    ⟨finalVirtual, finalSemantic, history, finalWF, finalNative, finalConverted, ids, extension, selected⟩
  have domainAnnotations : IndexAnnotationSupport env universes reader
      (recursorIHDomain stats infos argument terminal arguments argumentReader) := by
    simpa only [domainEq] using annotations
  obtain ⟨rawSemantic, peeled, level, receipt⟩ := endpoint.ihOpening envWF constants definitions
    modelWF native reserved (motiveSupport argumentModel endpoint) domainAnnotations
  have domainOpening : RecursorIHOpening env universes reader model.vlctx argument domain
      rawSemantic peeled level := by
    simpa only [domainEq] using receipt
  obtain ⟨pushedWF, pushedNative, _⟩ := domainOpening.mixedContext model modelWF native rfl reserved
  exact ⟨_, terminal, arguments, argumentReader, opening, argumentModel, rawSemantic, peeled,
    level, domainEq, endpoint, domainOpening, rfl, pushedWF, pushedNative⟩

inductive IHTraceTranslationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo} :
    {index : Nat} → {hypotheses : Array Expr} → {reader : Context} →
    {finalHypotheses : Array Expr} → {finalReader : Context} →
    RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader → Prop where
  | stop {index : Nat} {hypotheses : Array Expr} {reader : Context}
      (complete : ¬ index < fields.size) :
      IHTraceTranslationSupport env universes (.stop (hypotheses := hypotheses) (reader := reader) complete)
  | step {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
      {domain : Expr} (bound : index < fields.size)
      (source : RecursorIHDomainSource stats infos fields[index]! reader domain)
      (tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader)
      (head : ∀ model : MLCtx, model.WF env universes → model.lctx = reader.lctx →
        IHDomainSourceTranslationSupport env universes source model)
      (rest : IHTraceTranslationSupport env universes tail) :
      IHTraceTranslationSupport env universes (.step bound source tail)

inductive TranslatedRecursorIHTrace (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo} :
    {index : Nat} → {hypotheses : Array Expr} → {reader : Context} →
    {finalHypotheses : Array Expr} → {finalReader : Context} →
    RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader →
      MLCtx → MLCtx → Prop where
  | stop {index : Nat} {hypotheses : Array Expr} {reader : Context} {model : MLCtx}
      (complete : ¬ index < fields.size) (modelWF : model.WF env universes)
      (native : model.lctx = reader.lctx) :
      TranslatedRecursorIHTrace env universes
        (.stop (hypotheses := hypotheses) (reader := reader) complete) model model
  | step {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
      {domain : Expr} {initial middle final : MLCtx} (bound : index < fields.size)
      (source : RecursorIHDomainSource stats infos fields[index]! reader domain)
      (tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader)
      (head : IHModelStep env universes source initial middle)
      (rest : TranslatedRecursorIHTrace env universes tail middle final) :
      TranslatedRecursorIHTrace env universes (.step bound source tail) initial final

theorem TranslatedRecursorIHTrace.context {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  induction history with
  | stop _ modelWF native => exact ⟨modelWF, native, by simpa only [native] using modelWF.tr⟩
  | step _ _ _ _ _ tailInduction => exact tailInduction

theorem TranslatedRecursorIHTrace.extension {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final) :
    ∃ ids, IndexMLCtxExtension initial ids final ∧
      finalHypotheses.toList = hypotheses.toList ++ ids.map Expr.fvar := by
  induction history with
  | stop => exact ⟨[], .nil, by simp only [List.map_nil, List.append_nil]⟩
  | @step index hypotheses finalHypotheses reader finalReader domain initial middle final
      bound source tail head rest tailInduction =>
    obtain ⟨ids, extension, selected⟩ := tailInduction
    refine ⟨⟨reader.ngen.curr⟩ :: ids, ?_, ?_⟩
    · simpa only [List.singleton_append] using (head.extension.trans extension)
    · simpa only [Array.toList_push, List.map_cons, List.append_assoc,
        List.singleton_append] using selected

theorem RecursorIHTrace.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
    (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : IHTraceTranslationSupport env universes trace) :
    ∃ finalModel, TranslatedRecursorIHTrace env universes trace model finalModel := by
  induction support generalizing model with
  | stop complete => exact ⟨model, .stop complete modelWF native⟩
  | @step index hypotheses finalHypotheses reader finalReader domain bound source tail
      head rest tailInduction =>
    obtain ⟨middle, step⟩ := source.translatedStep envWF constants definitions model modelWF native
      reserved (head model modelWF native)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ modelWF.tr.1) reserved
      (recursorIHName reader fields[index]!) .default (peelTypeAnnotations domain)
    obtain ⟨finalModel, history⟩ := tailInduction middle step.context.1 step.context.2 pushed.reserved
    exact ⟨finalModel, .step bound source tail step history⟩

theorem TranslatedRecursorIHTrace.typedHypothesisAbstraction
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {fields : Array Expr} {infos : Array RecInfo} {index : Nat}
    {finalHypotheses : Array Expr} {reader finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index #[] reader finalHypotheses finalReader}
    {initial final : MLCtx} (history : TranslatedRecursorIHTrace env universes trace initial final)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall finalHypotheses body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted := by
  obtain ⟨ids, extension, selected⟩ := history.extension
  have arrays : finalHypotheses = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [Array.toList_empty, List.nil_append, List.toList_toArray] using selected
  obtain ⟨abstracted, abstractedTyped⟩ :=
    extension.typedBodyAbstraction envWF history.context.1 translated typed
  exact ⟨_, by simpa only [history.context.2, arrays] using abstracted, abstractedTyped⟩

theorem mkRecInfos.loopU.getTranslatedHypotheses {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopU stats fields infos index hypotheses
      (fun finalHypotheses => do return (finalHypotheses, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        IHTraceTranslationSupport env universes trace) :
    (mkRecInfos.loopU stats fields infos index hypotheses
      (fun finalHypotheses => do return (finalHypotheses, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧
      result.1.size = hypotheses.size + (fields.size - index) ∧
      ∃ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        ∃ finalModel, TranslatedRecursorIHTrace env universes trace model finalModel := by
  intro result success
  obtain ⟨trace, frame, counts⟩ := mkRecInfos.loopU.getTrace stats fields infos index hypotheses reader
    (native ▸ modelWF.tr.1) reserved result success
  obtain ⟨finalModel, history⟩ := trace.translated envWF constants definitions model modelWF native
    reserved (support result success trace)
  exact ⟨frame, counts, trace, finalModel, history⟩

theorem mkRecInfos.loopU.scopedTranslatedHypotheses {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (fields : Array Expr) (infos : Array RecInfo)
    (index : Nat) (hypotheses : Array Expr) (next : Array Expr → M ResultType)
    (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopU stats fields infos index hypotheses
      (fun finalHypotheses => do return (finalHypotheses, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorIHTrace stats fields infos index hypotheses reader result.1 result.2,
        IHTraceTranslationSupport env universes trace)
    (nextWF : ∀ finalHypotheses finalReader
      (trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      TranslatedRecursorIHTrace env universes trace model finalModel →
      (next finalHypotheses finalReader).WF post) :
    (mkRecInfos.loopU stats fields infos index hypotheses next reader).WF post := by
  rw [mkRecInfos.loopU.morphism stats fields infos index hypotheses next
    (fun finalHypotheses => do return (finalHypotheses, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.loopU.getTranslatedHypotheses stats fields infos index hypotheses reader
    envWF constants definitions model modelWF native reserved support).bind ?_
  rintro ⟨finalHypotheses, finalReader⟩ ⟨frame, _, trace, finalModel, history⟩
  exact nextWF finalHypotheses finalReader trace finalModel frame history

end Lean4Lean.AddInductive
