import Lean4Lean.Verify.InductiveUArgTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open Kernel (Exception)
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def UArgModelEndpoint (env : VEnv) (universes : List Name)
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader)
    (initial final : MLCtx) : Prop :=
  ∃ finalVirtual finalSemantic,
    TranslatedRecursorUArgOpening env universes opening initial.vlctx finalVirtual finalSemantic ∧
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧ final.vlctx = finalVirtual ∧
    ∃ ids, IndexMLCtxExtension initial ids final ∧ arguments.toList = ids.map Expr.fvar

theorem UArgModelEndpoint.context
    {env : VEnv} {universes : List Name} {argument terminal : Expr}
    {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, modelWF, native, _, _⟩ := endpoint
  exact ⟨modelWF, native, by simpa only [native] using modelWF.tr⟩

theorem UArgModelEndpoint.terminalTranslation
    {env : VEnv} {universes : List Name} {argument terminal : Expr}
    {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final) :
    ∃ finalSemantic, TrExprS env universes final.vlctx terminal finalSemantic := by
  obtain ⟨_, finalSemantic, history, _, _, converted, _⟩ := endpoint
  exact ⟨finalSemantic, by simpa only [converted] using history.finalTranslation.2⟩

theorem UArgModelEndpoint.application
    {env : VEnv} {universes : List Name} {argument terminal : Expr}
    {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) :
    ∃ value semantic,
      TrExprS env universes final.vlctx (mkAppN argument arguments) value ∧
      TrExprS env universes final.vlctx terminal semantic ∧
      env.HasType universes.length final.vlctx.toCtx value semantic := by
  obtain ⟨_, finalSemantic, history, _, _, converted, _⟩ := endpoint
  obtain ⟨value, translated, typed⟩ := history.application envWF
  refine ⟨value, finalSemantic, ?_, ?_, ?_⟩
  · simpa only [converted] using translated
  · simpa only [converted] using history.finalTranslation.2
  · simpa only [converted] using typed

theorem UArgModelEndpoint.typedArgumentAbstraction
    {env : VEnv} {universes : List Name} {argument terminal : Expr}
    {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall arguments body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted := by
  obtain ⟨_, _, _, modelWF, native, _, ids, extension, selected⟩ := endpoint
  have arrays : arguments = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  obtain ⟨abstracted, abstractedTyped⟩ :=
    extension.typedBodyAbstraction envWF modelWF translated typed
  exact ⟨_, by simpa only [← native, arrays] using abstracted, abstractedTyped⟩

theorem mkRecInfos.loopUArgs.getTranslatedOpening
    {env : VEnv} {universes : List Name}
    (argument : Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopUArgs argument
      (fun terminal arguments => do return (terminal, arguments, ← readThe Context)) reader).WF fun result =>
      ∀ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        UArgOpeningTranslationSupport env universes opening model.vlctx) :
    (mkRecInfos.loopUArgs argument
      (fun terminal arguments => do return (terminal, arguments, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorFieldsDeclared result.2.2.lctx result.2.1 ∧
      ∃ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        ∃ finalModel, UArgModelEndpoint env universes opening model finalModel := by
  intro result success
  obtain ⟨opening, frame, declared⟩ :=
    mkRecInfos.loopUArgs.getTrace argument reader (native ▸ modelWF.tr.1) reserved result success
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  obtain ⟨finalVirtual, finalSemantic, history⟩ := opening.translated envWF constants definitions
    correspondence reserved (support result success opening)
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  refine ⟨frame, declared, opening, finalModel, finalVirtual, finalSemantic, history,
    finalWF, finalNative, finalConverted, ids, extension, ?_⟩
  simpa only [Array.toList_empty, List.nil_append] using selected

theorem mkRecInfos.loopUArgs.scopedTranslatedOpening {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (argument : Expr) (next : Expr → Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos.loopUArgs argument
      (fun terminal arguments => do return (terminal, arguments, ← readThe Context)) reader).WF fun result =>
      ∀ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        UArgOpeningTranslationSupport env universes opening model.vlctx)
    (nextWF : ∀ terminal arguments finalReader
      (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader) finalModel,
      reader.RecursorScopeFrame finalReader → RecursorFieldsDeclared finalReader.lctx arguments →
      UArgModelEndpoint env universes opening model finalModel →
      (next terminal arguments finalReader).WF post) :
    (mkRecInfos.loopUArgs argument next reader).WF post := by
  rw [mkRecInfos.loopUArgs.morphism argument next
    (fun terminal arguments => do return (terminal, arguments, ← readThe Context))
    (fun result => next result.1 result.2.1 result.2.2) reader (fun _ _ _ => rfl)]
  refine (mkRecInfos.loopUArgs.getTranslatedOpening argument reader envWF constants definitions
    model modelWF native reserved support).bind ?_
  rintro ⟨terminal, arguments, finalReader⟩ ⟨frame, declared, opening, finalModel, endpoint⟩
  exact nextWF terminal arguments finalReader opening finalModel frame declared endpoint

end Lean4Lean.AddInductive
