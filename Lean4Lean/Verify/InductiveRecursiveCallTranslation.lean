import Lean4Lean.Verify.InductiveRuleTranslation
import Lean4Lean.Verify.InductiveRecursorSignatureInputs
import Lean4Lean.Verify.InductiveRecursorApplicationTranslation
import Lean4Lean.Verify.InductiveUArgTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterArguments)

/-- Individual arguments checked against the successively instantiated native
telescope. This contains neither a translation nor typing of the application. -/
inductive NativeTelescopeArguments (env : VEnv) (universes : List Name) (model : MLCtx) :
    Expr → List Expr → Expr → Prop where
  | nil : NativeTelescopeArguments env universes model source [] source
  | cons {name : Name} {domain body argument : Expr} {binder : BinderInfo}
      {arguments : List Expr} {terminal : Expr} {domainSemantic argumentSemantic : VExpr}
      (domainTranslated : TrExprS env universes model.vlctx domain domainSemantic)
      (argumentTranslated : TrExprS env universes model.vlctx argument argumentSemantic)
      (argumentTyped : env.HasType universes.length model.vlctx.toCtx
        argumentSemantic domainSemantic)
      (remaining : NativeTelescopeArguments env universes model
        (body.instantiate1' argument) arguments terminal) :
      NativeTelescopeArguments env universes model (.forallE name domain body binder)
        (argument :: arguments) terminal

theorem NativeTelescopeArguments.append
    (first : NativeTelescopeArguments env universes model source arguments middle)
    (second : NativeTelescopeArguments env universes model middle more terminal) :
    NativeTelescopeArguments env universes model source (arguments ++ more) terminal := by
  induction first with
  | nil => exact second
  | cons domainTranslated argumentTranslated argumentTyped _ induction =>
    exact .cons domainTranslated argumentTranslated argumentTyped (induction second)

/-- A local declaration supplies its own argument translation and typing. -/
theorem NativeTelescopeArguments.cdeclCons
    (envWF : env.WF) (modelWF : model.WF env universes)
    (lookup : model.lctx.find? identifier =
      some (.cdecl index identifier localName domain localBinder kind))
    (remaining : NativeTelescopeArguments env universes model
      (body.instantiate1' (.fvar identifier)) arguments terminal) :
    NativeTelescopeArguments env universes model (.forallE name domain body binder)
      (.fvar identifier :: arguments) terminal := by
  obtain ⟨_, _, _, translated, domainTranslated, typed⟩ :=
    modelWF.cdeclTranslation envWF lookup
  exact .cons domainTranslated translated typed remaining

/-- Shared parameters, motives and minors can be discharged directly from the
selected declarations; no argument translation or typing receipts are needed. -/
theorem NativeTelescopeArguments.selected
    (envWF : env.WF) (modelWF : model.WF env universes)
    (identifiers : List FVarId) (distinct : identifiers.Nodup)
    (bindings : SelectedCDeclBindings model.lctx identifiers)
    (bodyClosed : body.looseBVarRange' = 0) :
    NativeTelescopeArguments env universes model
      (model.lctx.mkForall (identifiers.map Expr.fvar).toArray body)
      (identifiers.map Expr.fvar) body := by
  induction identifiers with
  | nil =>
    rw [mkForall_selected_fold [] modelWF.bindingScope bodyClosed distinct bindings]
    exact .nil
  | cons identifier identifiers induction =>
    obtain ⟨index, name, domain, binder, kind, lookup⟩ := bindings identifier (by simp)
    rw [mkForall_selected_cons identifier identifiers modelWF.bindingScope bodyClosed distinct
      bindings index name domain binder kind lookup]
    refine cdeclCons envWF modelWF lookup ?_
    rw [Expr.instantiate1'_abstract1]
    exact induction distinct.tail (bindings.subset
      (fun selected member => List.mem_cons_of_mem identifier member))

/-- Substitute actual arguments through dependent binder bodies, aligning each
domain by translation uniqueness rather than assuming the resulting call. -/
theorem NativeTelescopeArguments.translated
    (arguments : NativeTelescopeArguments env universes model source replacements terminal)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (sourceTranslated : TrExprS env universes model.vlctx source sourceSemantic) :
    ∃ values terminalSemantic,
      TypedParameterArguments env universes model sourceSemantic replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx terminal terminalSemantic := by
  induction arguments generalizing sourceSemantic with
  | nil => exact ⟨[], sourceSemantic, .nil, sourceTranslated⟩
  | cons domainTranslated argumentTranslated argumentTyped _ induction =>
    cases sourceTranslated with
    | forallE _ _ actualDomainTranslated bodyTranslated =>
      have equality := domainTranslated.uniq envWF
        (.refl envWF modelWF.tr.wf) actualDomainTranslated
      have converted := argumentTyped.defeqU_r envWF modelWF.tr.wf.toCtx equality
      obtain ⟨values, terminalSemantic, typed, terminalTranslated⟩ :=
        induction (bodyTranslated.inst envWF.ordered converted argumentTranslated)
      exact ⟨_, terminalSemantic, .cons argumentTranslated converted typed, terminalTranslated⟩

theorem NativeTelescopeArguments.application
    (arguments : NativeTelescopeArguments env universes model source replacements terminal)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (sourceTranslated : TrExprS env universes model.vlctx source sourceSemantic)
    (headTranslated : TrExprS env universes model.vlctx head headSemantic)
    (headTyped : env.HasType universes.length model.vlctx.toCtx headSemantic sourceSemantic) :
    ∃ value terminalSemantic,
      TrExprS env universes model.vlctx (head.mkAppList replacements) value ∧
      TrExprS env universes model.vlctx terminal terminalSemantic ∧
      env.HasType universes.length model.vlctx.toCtx value terminalSemantic := by
  obtain ⟨values, terminalSemantic, typedArguments, terminalTranslated⟩ :=
    arguments.translated envWF modelWF sourceTranslated
  obtain ⟨translated, typed⟩ := typedArguments.apply headTranslated headTyped
  exact ⟨_, terminalSemantic, translated, terminalTranslated, typed⟩

/-- The existing closed-signature instantiation proof also supplies the type
of a freshly inserted recursor, in the caller's universes and local context. -/
theorem recursorInputAfterInsertion
    {safety : DefinitionSafety} {before after : VEnv} {models : List VConstVal}
    {info : RecursorVal} {constant : VConstVal}
    (signature : TrConstVal safety before (.recInfo info) constant)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some after)
    {model : MLCtx} (afterWF : after.WF) (modelWF : model.WF after universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length) :
    Nonempty (RecursorConstantInput after universes model.vlctx info.name levels
      (info.type.instantiateLevelParams info.levelParams levels)) := by
  have lookup := VEnv.addConstructorHeaders.constants inserted member
  rw [← signature.2] at lookup
  exact RecursorConstantInput.ofTranslation afterWF lookup
    (signature.1.2.2.mono (VEnv.addConstructorHeaders.le inserted)) signature.1.2.1
    model modelWF mapped arity

/-- The recursive call generated inside `mkRecRules.loopU`: apply the signature
to parameters, motives, minors and actual indices, then to the opened field.
Only individual prefix arguments and the existing field-opening trace are
assumed; the complete call's translation, typing and result are derived. -/
theorem UArgModelEndpoint.recursiveCallAfterInsertion
    {env before : VEnv} {universes : List Name} {models : List VConstVal}
    {safety : DefinitionSafety} {info : RecursorVal} {constant : VConstVal}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF)
    {levels : List Level} {semanticLevels : List VLevel}
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length)
    (stats : InductiveStats) (motives minors indices : Array Expr)
    {majorName : Name} {majorBody : Expr} {majorBinder : BinderInfo}
    (prefixArguments : NativeTelescopeArguments env universes final
      (info.type.instantiateLevelParams info.levelParams levels)
      (stats.params ++ motives ++ minors ++ indices).toList
      (.forallE majorName terminal majorBody majorBinder)) :
    ∃ value resultType,
      TrExprS env universes final.vlctx
        ((mkAppN (mkAppN (mkAppN (mkAppN (.const info.name levels) stats.params)
          motives) minors) indices).app (mkAppN argument arguments)) value ∧
      TrExprS env universes final.vlctx
        (majorBody.instantiate1' (mkAppN argument arguments)) resultType ∧
      env.HasType universes.length final.vlctx.toCtx value resultType := by
  have modelWF := endpoint.context.1
  obtain ⟨input⟩ := recursorInputAfterInsertion signature member inserted envWF modelWF mapped arity
  obtain ⟨prefixValue, prefixType, prefixTranslated, prefixTypeTranslated, prefixTyped⟩ :=
    prefixArguments.application envWF modelWF input.sourceTranslated input.valueTranslated input.valueTyped
  cases prefixTypeTranslated with
  | forallE _ _ domainTranslated bodyTranslated =>
    obtain ⟨majorValue, majorType, majorTranslated, majorTypeTranslated, majorTyped⟩ :=
      endpoint.application envWF
    have equality := majorTypeTranslated.uniq envWF
      (.refl envWF modelWF.tr.wf) domainTranslated
    have converted := majorTyped.defeqU_r envWF modelWF.tr.wf.toCtx equality
    refine ⟨_, _, ?_, bodyTranslated.inst envWF.ordered converted majorTranslated,
      prefixTyped.app converted⟩
    have translated := TrExprS.app prefixTyped converted prefixTranslated majorTranslated
    have applicationConstructor : mkApp = Expr.app := rfl
    simpa only [Array.toList_append, Expr.mkAppList_append, Expr.mkAppList_eq_foldl,
      mkAppN, ← Array.foldl_toList, List.foldl_append, applicationConstructor] using translated

theorem IndexMLCtxExtension.typedValueAbstraction
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    (translated : TrExprS env universes final.vlctx body semantic)
    (typed : env.HasType universes.length final.vlctx.toCtx semantic type) :
    TrExprS env universes initial.vlctx
        (final.lctx.mkLambda (ids.map Expr.fvar).toArray body)
        (final.mkLambda' ids.length extension.bound semantic) ∧
      env.HasType universes.length initial.vlctx.toCtx
        (final.mkLambda' ids.length extension.bound semantic)
        (final.mkForall' ids.length extension.bound type) := by
  have closed : body.looseBVarRange' = 0 :=
    (final.noBV ▸ translated.closed).looseBVarRange_zero
  rw [modelWF.mkLambda_eq ids.length extension.bound
    (by simp only [List.map_reverse, extension.selection]) closed]
  simpa only [extension.drop_eq] using
    modelWF.mkLambda_trS envWF translated typed ids.length extension.bound

/-- Close the `xs` introduced by the actual field-opening trace, producing the
lambda value stored by `mkRecRules`, including higher-order recursive fields. -/
theorem UArgModelEndpoint.typedValueAbstraction
    {env : VEnv} {universes : List Name} {argument terminal : Expr}
    {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) (translated : TrExprS env universes final.vlctx body semantic)
    (typed : env.HasType universes.length final.vlctx.toCtx semantic type) :
    ∃ value valueType,
      TrExprS env universes initial.vlctx (finalReader.lctx.mkLambda arguments body) value ∧
      env.HasType universes.length initial.vlctx.toCtx value valueType := by
  obtain ⟨_, _, _, modelWF, native, _, ids, extension, selected⟩ := endpoint
  have arrays : arguments = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  obtain ⟨abstracted, abstractedTyped⟩ :=
    extension.typedValueAbstraction envWF modelWF translated typed
  exact ⟨_, _, by simpa only [← native, arrays] using abstracted, abstractedTyped⟩

/-- Translate and type the complete recursive value, including the lambdas
over higher-order field arguments, in the context preceding their opening. -/
theorem UArgModelEndpoint.recursiveValueAfterInsertion
    {env before : VEnv} {universes : List Name} {models : List VConstVal}
    {safety : DefinitionSafety} {info : RecursorVal} {constant : VConstVal}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF)
    {levels : List Level} {semanticLevels : List VLevel}
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length)
    (stats : InductiveStats) (motives minors indices : Array Expr)
    {majorName : Name} {majorBody : Expr} {majorBinder : BinderInfo}
    (prefixArguments : NativeTelescopeArguments env universes final
      (info.type.instantiateLevelParams info.levelParams levels)
      (stats.params ++ motives ++ minors ++ indices).toList
      (.forallE majorName terminal majorBody majorBinder)) :
    ∃ value valueType,
      TrExprS env universes initial.vlctx
        (finalReader.lctx.mkLambda arguments
          ((mkAppN (mkAppN (mkAppN (mkAppN (.const info.name levels) stats.params)
            motives) minors) indices).app (mkAppN argument arguments))) value ∧
      TrExprS env universes initial.vlctx
        (finalReader.lctx.mkForall arguments
          (majorBody.instantiate1' (mkAppN argument arguments))) valueType ∧
      env.HasType universes.length initial.vlctx.toCtx value valueType := by
  obtain ⟨_, _, translated, resultTranslated, typed⟩ := endpoint.recursiveCallAfterInsertion signature member
    inserted envWF mapped arity stats motives minors indices prefixArguments
  obtain ⟨_, _, _, modelWF, native, _, ids, extension, selected⟩ := endpoint
  have arrays : arguments = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  obtain ⟨valueTranslated, valueTyped⟩ :=
    extension.typedValueAbstraction envWF modelWF translated typed
  have closed : (majorBody.instantiate1' (mkAppN argument arguments)).looseBVarRange' = 0 :=
    (final.noBV ▸ resultTranslated.closed).looseBVarRange_zero
  have resultBinding := extension.nativeBodyAbstraction modelWF closed
  have typeTranslated := (modelWF.mkForall_trS envWF resultTranslated
    (typed.isType envWF modelWF.tr.wf.toCtx) ids.length extension.bound).1
  rw [extension.drop_eq, ← resultBinding] at typeTranslated
  refine ⟨_, _, ?_, ?_, valueTyped⟩
  · simpa only [← native, arrays] using valueTranslated
  · simpa only [← native, arrays] using typeTranslated

end Lean4Lean.AddInductive
