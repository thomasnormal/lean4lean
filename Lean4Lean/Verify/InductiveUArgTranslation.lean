import Lean4Lean.Verify.InductiveCtorFieldTranslation
import Lean4Lean.Verify.InductiveUArgTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def UArgSourceTranslation (env : VEnv) (universes : List Name) (virtual : VLCtx)
    (argument inferred normalized : Expr) (normalizedSemantic : VExpr) : Prop :=
  ∃ argumentSemantic inferredSemantic,
    TrExprS env universes virtual argument argumentSemantic ∧
    TrExpr env universes virtual inferred inferredSemantic ∧
    env.HasType universes.length virtual.toCtx argumentSemantic inferredSemantic ∧
    TrExprS env universes virtual normalized normalizedSemantic ∧
    env.IsDefEqU universes.length virtual.toCtx normalizedSemantic inferredSemantic

theorem UArgSourceTranslation.normalizedTranslation
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument inferred normalized : Expr} {normalizedSemantic : VExpr}
    (source : UArgSourceTranslation env universes virtual argument inferred normalized normalizedSemantic) :
    TrExprS env universes virtual normalized normalizedSemantic := by
  obtain ⟨_, _, _, _, _, translated, _⟩ := source
  exact translated

theorem UArgSourceTranslation.normalizedArgumentTyping
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument inferred normalized : Expr} {normalizedSemantic : VExpr}
    (source : UArgSourceTranslation env universes virtual argument inferred normalized normalizedSemantic)
    (envWF : env.WF) (contextWF : virtual.WF env universes.length) :
    ∃ argumentSemantic,
      TrExprS env universes virtual argument argumentSemantic ∧
        env.HasType universes.length virtual.toCtx argumentSemantic normalizedSemantic := by
  obtain ⟨argumentSemantic, _, translated, _, typed, _, equality⟩ := source
  exact ⟨argumentSemantic, translated, typed.defeqU_r envWF contextWF.toCtx equality.symm⟩

inductive UArgOpeningTranslationSupport (env : VEnv) (universes : List Name)
    {argument : Expr} {reader : Context} :
    {terminal : Expr} → {arguments : Array Expr} → {finalReader : Context} →
    RecursorUArgOpeningTrace argument reader terminal arguments finalReader → VLCtx → Prop where
  | mk {inferred normalized terminal : Expr} {arguments : Array Expr} {finalReader : Context}
      {virtual : VLCtx} {normalizedSemantic : VExpr}
      (inference : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
      (initialNormalization : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
      (argumentsTrace : RecursorUArgTrace normalized #[] reader terminal arguments finalReader)
      (source : UArgSourceTranslation env universes virtual argument inferred normalized normalizedSemantic)
      (annotations : IndexTraceAnnotationSupport env universes argumentsTrace)
      (normalizations : IndexTraceNormalizationSupport env universes argumentsTrace) :
      UArgOpeningTranslationSupport env universes (.mk inference initialNormalization argumentsTrace) virtual

inductive TranslatedRecursorUArgOpening (env : VEnv) (universes : List Name)
    {argument : Expr} {reader : Context} :
    {terminal : Expr} → {arguments : Array Expr} → {finalReader : Context} →
    RecursorUArgOpeningTrace argument reader terminal arguments finalReader →
      VLCtx → VLCtx → VExpr → Prop where
  | mk {inferred normalized terminal : Expr} {arguments : Array Expr} {finalReader : Context}
      {virtual finalVirtual : VLCtx} {normalizedSemantic finalSemantic : VExpr}
      (inference : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
      (initialNormalization : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
      (argumentsTrace : RecursorUArgTrace normalized #[] reader terminal arguments finalReader)
      (correspondence : TrLCtx env universes reader.lctx virtual)
      (source : UArgSourceTranslation env universes virtual argument inferred normalized normalizedSemantic)
      (history : TranslatedRecursorIndexTrace env universes argumentsTrace virtual normalizedSemantic
        finalVirtual finalSemantic) :
      TranslatedRecursorUArgOpening env universes (.mk inference initialNormalization argumentsTrace)
        virtual finalVirtual finalSemantic

theorem RecursorUArgOpeningTrace.translated {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual : VLCtx}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : UArgOpeningTranslationSupport env universes opening virtual) :
    ∃ finalVirtual finalSemantic,
      TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic := by
  cases support with
  | mk inference initialNormalization argumentsTrace source annotations normalizations =>
    obtain ⟨finalVirtual, finalSemantic, history⟩ := argumentsTrace.translated envWF constants
      definitions (by simp only [recursorUArgStats, Array.size_empty, Nat.le_refl])
      correspondence reserved source.normalizedTranslation annotations normalizations
    exact ⟨finalVirtual, finalSemantic,
      .mk inference initialNormalization argumentsTrace correspondence source history⟩

theorem TranslatedRecursorUArgOpening.finalTranslation {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic) :
    TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic := by
  cases translated with
  | mk _ _ _ _ _ history => exact history.finalTranslation

theorem TranslatedRecursorUArgOpening.scope {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) : reader.RecursorScopeFrame finalReader := by
  cases translated with
  | mk _ _ _ _ _ history => exact history.scope reserved

theorem TranslatedRecursorUArgOpening.application {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic)
    (envWF : env.WF) :
    ∃ finalValue,
      TrExprS env universes finalVirtual (mkAppN argument arguments) finalValue ∧
        env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic := by
  cases translated with
  | mk _ _ _ correspondence source history =>
    obtain ⟨argumentSemantic, argumentTranslated, argumentTyped⟩ :=
      source.normalizedArgumentTyping envWF correspondence.wf
    exact history.application envWF argumentTranslated argumentTyped

theorem TranslatedRecursorUArgOpening.mixedContext {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      arguments.toList = ids.map Expr.fvar := by
  cases translated with
  | mk _ _ _ _ _ history =>
    obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
      history.mixedContext model modelWF native converted reserved
    exact ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension,
      by simpa only [Array.toList_empty, List.nil_append] using array⟩

theorem TranslatedRecursorUArgOpening.typedAbstraction {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic)
    (envWF : env.WF) (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {body : Expr} {bodySemantic : VExpr}
    (bodyTranslated : TrExpr env universes finalVirtual body bodySemantic)
    (bodyTyped : env.IsType universes.length finalVirtual.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes virtual (finalReader.lctx.mkForall arguments body) abstracted ∧
        env.IsType universes.length virtual.toCtx abstracted := by
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
    translated.mixedContext model modelWF native converted reserved
  have selected : arguments = (ids.map Expr.fvar).toArray := by
    rw [← array, Array.toArray_toList]
  have translatedInModel : TrExpr env universes finalModel.vlctx body bodySemantic := by
    simpa only [finalConverted] using bodyTranslated
  have typedInModel : env.IsType universes.length finalModel.vlctx.toCtx bodySemantic := by
    simpa only [finalConverted] using bodyTyped
  obtain ⟨abstracted, typed⟩ :=
    extension.typedBodyAbstraction envWF finalWF translatedInModel typedInModel
  exact ⟨_, by simpa only [selected, finalNative, converted] using abstracted,
    by simpa only [converted] using typed⟩

theorem TranslatedRecursorUArgOpening.typedAbstractionAtFinal
    {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {finalSemantic : VExpr}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (translated : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic)
    (envWF : env.WF) (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {body : Expr} {bodySemantic : VExpr}
    (bodyTranslated : TrExpr env universes finalVirtual body bodySemantic)
    (bodyTyped : env.IsType universes.length finalVirtual.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes finalVirtual (finalReader.lctx.mkForall arguments body) abstracted ∧
        env.IsType universes.length finalVirtual.toCtx abstracted := by
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
    translated.mixedContext model modelWF native converted reserved
  have selected : arguments = (ids.map Expr.fvar).toArray := by
    rw [← array, Array.toArray_toList]
  have translatedInModel : TrExpr env universes finalModel.vlctx body bodySemantic := by
    simpa only [finalConverted] using bodyTranslated
  have typedInModel : env.IsType universes.length finalModel.vlctx.toCtx bodySemantic := by
    simpa only [finalConverted] using bodyTyped
  obtain ⟨abstracted, typed⟩ :=
    extension.typedBodyAbstractionAtFinal envWF finalWF translatedInModel typedInModel
  exact ⟨_, by simpa only [selected, finalNative, finalConverted] using abstracted,
    by simpa only [finalConverted] using typed⟩

end Lean4Lean.AddInductive
