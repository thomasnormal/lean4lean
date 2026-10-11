import Lean4Lean.Verify.InductiveHeaderParameterUniverses
import Lean4Lean.Verify.InductiveRecursorIndexParameters

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem TypedParameterApplications.emptyResultEquality
    (arguments : TypedParameterApplications environment universes model source [] values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    environment.IsDefEqU universes.length model.vlctx.toCtx source result := by
  have empty : ∀ {source replacements values result},
      TypedParameterApplications environment universes model source replacements values result →
      replacements = [] → VExpr.WF environment universes.length model.vlctx.toCtx source →
      environment.IsDefEqU universes.length model.vlctx.toCtx source result := by
    intro source replacements values result history
    induction history with
    | nil => intro _ typed; exact typed
    | cons => intro impossible; cases impossible
    | convertInput equality _ induction =>
      intro selected _
      obtain ⟨kind, typed⟩ := equality
      exact VEnv.IsDefEqU.trans environmentWF modelWF.tr.wf.toCtx ⟨kind, typed⟩
        (induction selected ⟨kind, typed.hasType.2⟩)
  exact empty arguments rfl sourceWF

theorem TypedParameterApplications.consView
    (arguments : TypedParameterApplications environment universes model source
      (replacement :: replacements) values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (sourceWF : VExpr.WF environment universes.length model.vlctx.toCtx source) :
    ∃ domain body argument remainingValues,
      values = argument :: remainingValues ∧
      environment.IsDefEqU universes.length model.vlctx.toCtx source (.forallE domain body) ∧
      TrExprS environment universes model.vlctx replacement argument ∧
      environment.HasType universes.length model.vlctx.toCtx argument domain ∧
      TypedParameterApplications environment universes model (body.inst argument) replacements remainingValues result := by
  have invert : ∀ {source selected values result},
      TypedParameterApplications environment universes model source selected values result →
      VExpr.WF environment universes.length model.vlctx.toCtx source →
      ∀ replacement replacements, selected = replacement :: replacements →
      ∃ domain body argument remainingValues,
        values = argument :: remainingValues ∧
        environment.IsDefEqU universes.length model.vlctx.toCtx source (.forallE domain body) ∧
        TrExprS environment universes model.vlctx replacement argument ∧
        environment.HasType universes.length model.vlctx.toCtx argument domain ∧
        TypedParameterApplications environment universes model (body.inst argument) replacements remainingValues result := by
    intro source selected values result history
    induction history with
    | nil => intro _ replacement replacements impossible; cases impossible
    | cons translated typed remaining _ =>
      intro sourceWF replacement replacements selected
      cases selected
      exact ⟨_, _, _, _, rfl, sourceWF, translated, typed, remaining⟩
    | convertInput equality _ induction =>
      intro _ replacement replacements selected
      obtain ⟨kind, typed⟩ := equality
      obtain ⟨domain, body, argument, remainingValues, valuesEq, converted, translated, argumentTyped, remaining⟩ :=
        induction ⟨kind, typed.hasType.2⟩ replacement replacements selected
      exact ⟨domain, body, argument, remainingValues, valuesEq,
        VEnv.IsDefEqU.trans environmentWF modelWF.tr.wf.toCtx ⟨kind, typed⟩ converted,
        translated, argumentTyped, remaining⟩
  exact invert arguments sourceWF replacement replacements rfl

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterApplications ContextReserved)

theorem RecursorIndexParameterPrefix.normalizedApplications
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (environmentWF : environment.WF) (model : MLCtx) (modelWF : model.WF environment universes)
    (arguments : TypedParameterApplications environment universes model semantic
      (stats.params.toList.drop index) values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (support : IndexParameterNormalizationSupport environment universes model.vlctx parameters) :
    TrExpr environment universes model.vlctx residual resultSemantic := by
  induction parameters generalizing semantic values with
  | done complete =>
    have empty : stats.params.toList.drop _ = [] :=
      List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using complete)
    rw [empty] at arguments
    exact translated.defeq environmentWF modelWF.tr.wf.toCtx
      (arguments.emptyResultEquality environmentWF modelWF translated.wf)
  | @parameter name domain body normalized residual binder index afterIndex bound normalization remaining induction =>
    have listed : stats.params.toList[index] = stats.params[index]! := by
      simpa only [getElem!_pos stats.params index bound] using (Array.getElem_toList (xs := stats.params) bound)
    have drop : stats.params.toList.drop index = stats.params[index]! :: stats.params.toList.drop (index + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using bound), listed]
    rw [drop] at arguments
    obtain ⟨expectedDomain, expectedBody, argumentSemantic, remainingValues, _, converted,
      argumentTranslated, argumentTyped, remainingArguments⟩ :=
      arguments.consView environmentWF modelWF translated.wf
    have translated := translated.defeq environmentWF modelWF.tr.wf.toCtx converted
    obtain ⟨actualSemantic, actualTranslated, sourceEquality⟩ := translated
    cases actualTranslated with
    | forallE domainIsType bodyIsType domainTranslated bodyTranslated =>
      obtain ⟨⟨_, domainEquality⟩, ⟨_, bodyEquality⟩⟩ :=
        VEnv.IsDefEqU.forallE_inv environmentWF modelWF.tr.wf.toCtx sourceEquality
      have actualArgumentTyped := domainEquality.symm.defeq argumentTyped
      have opened := TrExprS.inst environmentWF.ordered actualArgumentTyped bodyTranslated argumentTranslated
      have openedEquality := bodyEquality.instN environmentWF.ordered actualArgumentTyped (.zero)
      have nextTranslated : TrExpr environment universes model.vlctx
          (body.instantiate1 stats.params[index]!) (expectedBody.inst argumentSemantic) := by
        refine ⟨_, ?_, _, openedEquality⟩
        simpa only [Expr.instantiate1_eq] using opened
      cases support with
      | done complete => exact False.elim (Nat.not_lt_of_ge complete bound)
      | parameter _ actual _ headSupported tailSupported =>
        have same := Except.ok.inj (normalization.symm.trans actual)
        cases same
        exact induction remainingArguments (headSupported _ nextTranslated) tailSupported

def HeaderRecursorIndexModelEndpoint (environment : VEnv) (universes : List Name)
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (initial final : MLCtx) (semantic resultSemantic : VExpr) : Prop :=
  ∃ residual afterIndex values residualSemantic finalVirtual finalSemantic,
    ∃ parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex,
      TrExpr environment universes initial.vlctx source semantic ∧
      TypedParameterApplications environment universes initial semantic stats.params.toList values resultSemantic ∧
      TrExprS environment universes initial.vlctx residual residualSemantic ∧
      environment.IsDefEqU universes.length initial.vlctx.toCtx residualSemantic resultSemantic ∧
      TranslatedRecursorIndexTrace environment universes (parameters.indexSuffix trace)
        initial.vlctx residualSemantic finalVirtual finalSemantic ∧
      final.WF environment universes ∧ final.lctx = finalReader.lctx ∧ final.vlctx = finalVirtual ∧
      ∃ identifiers, IndexMLCtxExtension initial identifiers final ∧ indices.toList = identifiers.map Expr.fvar

theorem ParameterizedRecursorIndexModelEndpoint.withHeaderApplications
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic) :
    ∃ resultSemantic, HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic := by
  obtain ⟨residual, afterIndex, values, resultSemantic, residualSemantic, finalVirtual, finalSemantic,
    parameters, translated, arguments, residualTranslated, equality, history, finalWF, native, converted, more⟩ := endpoint
  exact ⟨resultSemantic, residual, afterIndex, values, residualSemantic, finalVirtual, finalSemantic,
    parameters, translated, TypedParameterApplications.ofTypedArguments arguments, residualTranslated, equality, history,
    finalWF, native, converted, more⟩

theorem RecursorIndexTrace.headerApplications
    {stats : InductiveStats} {source residual terminal : Expr} {afterIndex finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex)
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (model : MLCtx) (modelWF : model.WF environment universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (arguments : TypedParameterApplications environment universes model semantic stats.params.toList values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (parameterSupport : IndexParameterNormalizationSupport environment universes model.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport environment universes trace)
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    ∃ finalModel, HeaderRecursorIndexModelEndpoint environment universes trace model finalModel semantic resultSemantic := by
  obtain ⟨residualSemantic, residualTranslated, residualEquality⟩ := parameters.normalizedApplications
    environmentWF model modelWF (by simpa only [List.drop_zero] using arguments) translated parameterSupport
  obtain ⟨finalVirtual, finalSemantic, history⟩ := (parameters.indexSuffix trace).translated
    environmentWF constants definitions parameters.complete (native ▸ modelWF.tr) reserved residualTranslated
    (parameters.annotationSuffix annotations) (parameters.normalizationSuffix normalizations)
  obtain ⟨finalModel, identifiers, finalWF, finalNative, converted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  exact ⟨finalModel, _, _, _, _, _, _, parameters, translated, arguments, residualTranslated,
    residualEquality, history, finalWF, finalNative, converted, identifiers, extension,
    by simpa only [Array.toList_empty, List.nil_append] using selected⟩

theorem RecursorIndexTrace.headerApplicationsOfChecker
    {stats : InductiveStats} {source headerSource terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats headerSource)
    (normalized : (monadLift (TypeChecker.whnf headerSource) : M Expr) reader = .ok source)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ finalModel, HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx
      finalModel input.semantic input.result := by
  obtain ⟨residual, afterIndex, parameters⟩ := trace.parameterPrefix complete
  have translated := acceptedHeaderNormalization checker reader aligned initialWF
    (input.sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalized
  exact trace.headerApplications parameters checker.Ewf constants definitions checker.mlctx checker.mlctx_wf
    (checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)) reserved input.arguments translated
    (parameters.normalizationSupport checker aligned initialWF) annotations normalizations

theorem HeaderRecursorIndexModelEndpoint.context
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic) :
    final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx environment universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, finalWF, native, _⟩ := endpoint
  exact ⟨finalWF, native, by simpa only [native] using finalWF.tr⟩

theorem HeaderRecursorIndexModelEndpoint.applicationOfPartial
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (translated : TrExprS environment universes initial.vlctx (mkAppN head stats.params) value)
    (typed : environment.HasType universes.length initial.vlctx.toCtx value resultSemantic) :
    ∃ finalValue terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx finalValue terminalSemantic := by
  obtain ⟨_, _, _, _, _, finalSemantic, _, _, _, _, equality, history, _, _, converted, _⟩ := endpoint
  have normalizedTyped := typed.defeqU_r environmentWF initialWF.tr.wf.toCtx equality.symm
  obtain ⟨finalValue, translated, typed⟩ := history.application environmentWF
    (by simpa only [mkAppN, Array.foldl_empty] using translated) normalizedTyped
  exact ⟨finalValue, finalSemantic, by simpa only [converted] using translated,
    by simpa only [converted] using history.finalTranslation.2, by simpa only [converted] using typed⟩

theorem HeaderRecursorIndexModelEndpoint.application
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  have receipt := endpoint
  obtain ⟨_, _, _, _, _, _, _, _, arguments, _⟩ := receipt
  obtain ⟨translated, typed⟩ := arguments.apply environmentWF initialWF headTranslated headTyped
  exact endpoint.applicationOfPartial environmentWF initialWF
    (by simpa only [mkAppN, Array.foldl_toList, Expr.mkAppList_eq_foldl] using translated) typed

theorem HeaderRecursorIndexModelEndpoint.constantInputApplication
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : HeaderParameterApplicationInput environment universes initial stats headerSource)
    (input : RecursorConstantInput environment universes initial.vlctx name levels headerSource)
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final
      parameters.semantic parameters.result)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic :=
  endpoint.application environmentWF initialWF input.valueTranslated
    (input.alignedType environmentWF initialWF.tr.wf parameters.sourceTranslated)

theorem HeaderRecursorIndexModelEndpoint.parentTypehoodOfPartial
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexModelEndpoint environment universes trace initial final semantic resultSemantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (translated : TrExprS environment universes initial.vlctx (mkAppN head stats.params) value)
    (typed : environment.HasType universes.length initial.vlctx.toCtx value resultSemantic)
    (sorted : terminal.isSort = true) :
    ∃ finalValue, TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      environment.IsType universes.length final.vlctx.toCtx finalValue := by
  obtain ⟨finalValue, terminalSemantic, translated, terminalTranslated, typed⟩ :=
    endpoint.applicationOfPartial environmentWF initialWF translated typed
  cases terminal <;> simp [Expr.isSort] at sorted
  cases terminalTranslated with
  | sort mapped => exact ⟨finalValue, translated, _, typed⟩

theorem RecursorIndexTrace.applicationOfHeaderBatch
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalModel, HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx
        finalModel input.semantic input.result ∧
        ∃ value terminalSemantic, TrExprS checker.venv checker.lparams finalModel.vlctx
          (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          TrExprS checker.venv checker.lparams finalModel.vlctx terminal terminalSemantic ∧
          checker.venv.HasType checker.lparams.length finalModel.vlctx.toCtx value terminalSemantic := by
  obtain ⟨input, partialValue, translated, typed⟩ := batch parent bound
  obtain ⟨finalModel, endpoint⟩ := trace.headerApplicationsOfChecker checker aligned initialWF constants definitions
    reserved complete input normalized annotations normalizations
  exact ⟨input, finalModel, endpoint, endpoint.applicationOfPartial checker.Ewf checker.mlctx_wf translated typed⟩

theorem mkRecInfos.loopArgs1.headerBatchTraceOfChecker {resultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat) (bound : parent < types.size)
    (source : Expr) (fuel : Nat) (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (supports : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current),
      IndexTraceAnnotationSupport checker.venv checker.lparams trace ∧
        IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current)
      (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type) finalModel,
      HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace checker.mlctx finalModel input.semantic input.result →
      (∃ value terminalSemantic, TrExprS checker.venv checker.lparams finalModel.vlctx
          (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
        TrExprS checker.venv checker.lparams finalModel.vlctx terminal terminalSemantic ∧
        checker.venv.HasType checker.lparams.length finalModel.vlctx.toCtx value terminalSemantic) →
      (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post := by
  have native : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  apply mkRecInfos.loopArgs1.scopedTrace stats source 0 #[] fuel next reader post (native ▸ checker.trlctx.1) reserved
  intro terminal finalIndex indices current trace frame
  obtain ⟨annotations, normalizations⟩ := supports terminal finalIndex indices current trace
  have complete := trace.completeParameters parameterFVars (by simpa only [Nat.zero_add] using arity)
  obtain ⟨input, finalModel, endpoint, application⟩ := trace.applicationOfHeaderBatch checker aligned initialWF
    constants definitions reserved complete batch parent bound normalized annotations normalizations
  exact nextWF terminal finalIndex indices current trace input finalModel endpoint application

end Lean4Lean.AddInductive
