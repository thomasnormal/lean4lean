import Lean4Lean.Verify.InductiveRecursiveTailInputs
import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveParameterPrefixReplacement

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved TypedParameterApplications)

/-- A generated recursive value can be consumed by the actual annotation-peeled
IH binder recorded in one translated IH step.  The value and its native domain
are still supplied by the rule producer; this theorem only performs the
opening/domain conversion that the RHS consumer needs. -/
theorem IHModelStep.acceptsGeneratedValue
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {nativeValue : Expr} {valueSemantic domainSemantic : VExpr}
    (valueTranslated : TrExprS env universes initial.vlctx nativeValue valueSemantic)
    (domainTranslated : TrExprS env universes initial.vlctx domain domainSemantic)
    (valueTyped : env.HasType universes.length initial.vlctx.toCtx valueSemantic domainSemantic) :
    ∃ peeled, TrExprS env universes initial.vlctx nativeValue valueSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx valueSemantic peeled := by
  obtain ⟨terminal, arguments, argumentReader, opening, argumentModel, rawSemantic,
    peeled, level, domainEq, endpoint, ihOpening, finalEq, finalWF, finalNative⟩ := step
  refine ⟨peeled, valueTranslated, ?_⟩
  exact ihOpening.acceptsValue envWF initialWF domainTranslated valueTyped

/-- The preceding generated-value theorem can be fed directly to the actual
IH step.  This is the producer/consumer seam used by a constructor RHS: the
producer supplies the native recursive value and its domain, while the step
supplies the annotation-peeled binder expected by the minor. -/
theorem IHModelStep.acceptsGeneratedRecursiveValue
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {nativeValue : Expr}
    (generated : ∃ value domainSemantic,
      TrExprS env universes initial.vlctx nativeValue value ∧
      TrExprS env universes initial.vlctx domain domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx value domainSemantic) :
    ∃ peeled value, TrExprS env universes initial.vlctx nativeValue value ∧
      env.HasType universes.length initial.vlctx.toCtx value peeled := by
  obtain ⟨value, domainSemantic, valueTranslated, domainTranslated, valueTyped⟩ := generated
  obtain ⟨peeled, valueTranslated, valueTyped⟩ := step.acceptsGeneratedValue envWF initialWF
    valueTranslated domainTranslated valueTyped
  exact ⟨peeled, value, valueTranslated, valueTyped⟩

/-- Assemble a minor application once its actual peeled domain and all field/IH
arguments have been checked.  `TypedParameterApplications` retains each
argument translation and typing, so the result is the RHS application rather
than an assumed conversion. -/
theorem RecursorMinorOpening.applyArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {replacements : List Expr}
    {argumentSemantics : List VExpr} {resultSemantic : VExpr}
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (arguments : TypedParameterApplications env universes model peeled replacements
      argumentSemantics resultSemantic)
    (envWF : env.WF) (modelWF : model.WF env universes) :
    TrExprS env universes model.vlctx (minor.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments minorSemantic argumentSemantics) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic argumentSemantics) resultSemantic := by
  exact arguments.apply envWF modelWF minorTranslated minorTyped

/-- The native telescope proof used by a generated rule can be converted to the
peeled minor application without hiding the individual argument checks. -/
theorem RecursorMinorOpening.applyNativeArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {source : Expr} {replacements : List Expr}
    {terminal : Expr}
    (sourceTranslated : TrExprS env universes model.vlctx source peeled)
    (nativeArguments : NativeTelescopeArguments env universes model source replacements terminal)
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (modelWF : model.WF env universes) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes model peeled replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx (minor.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  obtain ⟨values, terminalSemantic, typedArguments, terminalTranslated⟩ :=
    nativeArguments.translated envWF modelWF sourceTranslated
  obtain ⟨appliedTranslated, appliedTyped⟩ :=
    (TypedParameterApplications.ofTypedArguments typedArguments).apply
      envWF modelWF minorTranslated minorTyped
  exact ⟨values, terminalSemantic, .ofTypedArguments typedArguments,
    appliedTranslated, appliedTyped⟩

/-- The common peeled-domain case uses the opening's own native translation;
the producer only supplies the checked native argument telescope. -/
theorem RecursorMinorOpening.applyNativePeeledArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {replacements : List Expr} {terminal : Expr}
    (nativeArguments : NativeTelescopeArguments env universes model
      (peelTypeAnnotations domain) replacements terminal)
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (converted : model.vlctx = virtual) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes model peeled replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx (minor.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  exact opening.applyNativeArguments (by simpa only [converted] using opening.peeledTranslated)
    nativeArguments minorTranslated minorTyped envWF modelWF

/-- Native argument receipts transport across a context extension without
changing the native telescope or replacement expressions. -/
theorem NativeTelescopeArguments.weakFV
    (arguments : NativeTelescopeArguments env universes model source replacements terminal)
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    NativeTelescopeArguments env universes target source replacements terminal := by
  induction arguments with
  | nil => exact .nil
  | cons domainTranslated argumentTranslated argumentTyped remaining induction =>
    exact .cons (domainTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf)
      (argumentTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf)
      (argumentTyped.weak' envWF.ordered insertion.toCtx) induction

end Lean4Lean.AddInductive
