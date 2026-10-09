import Lean4Lean.Verify.InductiveCtorFieldTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def CtorFieldModelEndpoint (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader)
    (initial final : MLCtx) (semantic : VExpr) : Prop :=
  ∃ finalVirtual finalSemantic,
    TranslatedRecursorCtorFieldTrace env universes trace initial.vlctx semantic
      finalVirtual finalSemantic ∧
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧ final.vlctx = finalVirtual ∧
    ∃ ids, IndexMLCtxExtension initial ids final ∧ fields.toList = ids.map Expr.fvar

theorem CtorFieldModelEndpoint.context
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    {initial final : MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, modelWF, native, _, _⟩ := endpoint
  exact ⟨modelWF, native, by simpa only [native] using modelWF.tr⟩

theorem CtorFieldModelEndpoint.terminalTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    {initial final : MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic) :
    ∃ finalSemantic, TrExprS env universes final.vlctx terminal finalSemantic := by
  obtain ⟨_, finalSemantic, history, _, _, converted, _⟩ := endpoint
  exact ⟨finalSemantic, by simpa only [converted] using history.finalTranslation.2⟩

theorem CtorFieldModelEndpoint.typedFieldAbstraction
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    {initial final : MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall fields body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted := by
  obtain ⟨_, _, _, modelWF, native, _, ids, extension, selected⟩ := endpoint
  have arrays : fields = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  obtain ⟨abstracted, abstractedTyped⟩ :=
    extension.typedBodyAbstraction envWF modelWF translated typed
  exact ⟨_, by simpa only [← native, arrays] using abstracted, abstractedTyped⟩

theorem mkRecInfos.loopCtorArgs.getTranslatedFields
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (source : Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semantic : VExpr} (translated : TrExprS env universes model.vlctx source semantic)
    (support : (mkRecInfos.loopCtorArgs stats source
      (fun terminal fields recursiveFields => do return (terminal, fields, recursiveFields, ← readThe Context))
      reader).WF fun result =>
      ∀ finalIndex (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2),
        CtorFieldTraceAnnotationSupport env universes trace) :
    (mkRecInfos.loopCtorArgs stats source
      (fun terminal fields recursiveFields => do return (terminal, fields, recursiveFields, ← readThe Context))
      reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2.2 ∧
      RecursorFieldsDeclared result.2.2.2.lctx result.2.1 ∧
      result.2.2.1.toList.Sublist result.2.1.toList ∧
      ∃ finalIndex, ∃ trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2, ∃ finalModel,
        CtorFieldModelEndpoint env universes trace model finalModel semantic := by
  intro result success
  obtain ⟨finalIndex, trace, frame, declared, subset⟩ :=
    mkRecInfos.loopCtorArgs.getTrace stats source reader (native ▸ modelWF.tr.1) reserved result success
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  obtain ⟨finalVirtual, finalSemantic, history⟩ := trace.translated envWF constants definitions
    (by omega) correspondence reserved translated (support result success finalIndex trace)
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  refine ⟨frame, declared, subset, finalIndex, trace, finalModel,
    finalVirtual, finalSemantic, history, finalWF, finalNative, finalConverted, ids, extension, ?_⟩
  simpa only [Array.toList_empty, List.nil_append] using selected

theorem mkRecInfos.loopCtorArgs.scopedTranslatedFields {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (source : Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semantic : VExpr} (translated : TrExprS env universes model.vlctx source semantic)
    (support : (mkRecInfos.loopCtorArgs stats source
      (fun terminal fields recursiveFields => do return (terminal, fields, recursiveFields, ← readThe Context))
      reader).WF fun result =>
      ∀ finalIndex (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2),
        CtorFieldTraceAnnotationSupport env universes trace)
    (nextWF : ∀ terminal finalIndex fields recursiveFields finalReader
      (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        terminal finalIndex fields recursiveFields finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      RecursorFieldsDeclared finalReader.lctx fields → recursiveFields.toList.Sublist fields.toList →
      CtorFieldModelEndpoint env universes trace model finalModel semantic →
      (next terminal fields recursiveFields finalReader).WF post) :
    (mkRecInfos.loopCtorArgs stats source next reader).WF post := by
  rw [mkRecInfos.loopCtorArgs.morphism stats source next
    (fun terminal fields recursiveFields => do return (terminal, fields, recursiveFields, ← readThe Context))
    (fun result => next result.1 result.2.1 result.2.2.1 result.2.2.2) reader (fun _ _ _ _ => rfl)]
  refine (mkRecInfos.loopCtorArgs.getTranslatedFields stats source reader envWF constants definitions
    fieldOnly model modelWF native reserved translated support).bind ?_
  rintro ⟨terminal, fields, recursiveFields, finalReader⟩
    ⟨frame, declared, subset, finalIndex, trace, finalModel, endpoint⟩
  exact nextWF terminal finalIndex fields recursiveFields finalReader trace finalModel frame declared subset endpoint

end Lean4Lean.AddInductive
