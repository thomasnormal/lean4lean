import Lean4Lean.Verify.InductiveRecursorParameterPrefixes
import Lean4Lean.Verify.InductiveIndexApplicationTranslation
import Lean4Lean.Verify.InductiveMotiveContextTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterArguments ContextReserved)

inductive RecursorIndexParameterPrefix (stats : InductiveStats) (reader : Context) :
    Expr → Nat → Expr → Nat → Prop where
  | done (complete : stats.params.size ≤ index) :
      RecursorIndexParameterPrefix stats reader source index source index
  | parameter {name : Name} {domain body normalized residual : Expr} {binder : BinderInfo}
      {index afterIndex : Nat}
      (bound : index < stats.params.size)
      (normalization : (monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr)
        reader = .ok normalized)
      (remaining : RecursorIndexParameterPrefix stats reader normalized (index + 1) residual afterIndex) :
      RecursorIndexParameterPrefix stats reader (.forallE name domain body binder) index residual afterIndex

theorem RecursorIndexParameterPrefix.complete
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex) :
    stats.params.size ≤ afterIndex := by
  induction parameters with
  | done complete => exact complete
  | parameter _ _ _ induction => exact induction

theorem RecursorIndexParameterPrefix.count
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex) :
    afterIndex = max index stats.params.size := by
  induction parameters with
  | done complete => exact (Nat.max_eq_left complete).symm
  | parameter bound _ _ induction => omega

theorem RecursorIndexTrace.parameterPrefix
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (complete : stats.params.size ≤ finalIndex) :
    ∃ residual afterIndex, RecursorIndexParameterPrefix stats reader source index residual afterIndex := by
  induction trace with
  | stop => exact ⟨_, _, .done complete⟩
  | parameter bound normalization tail induction =>
    obtain ⟨residual, afterIndex, parameters⟩ := induction complete
    exact ⟨residual, afterIndex, .parameter bound normalization parameters⟩
  | index notParameter => exact ⟨_, _, .done (Nat.le_of_not_gt notParameter)⟩

theorem RecursorIndexTrace.completeParameters
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ index + declareConstructors.arity 0 source) :
    stats.params.size ≤ finalIndex := by
  induction trace with
  | @stop source index indices reader notForall =>
    have zero : declareConstructors.arity 0 source = 0 := by
      cases source <;> try rfl
      exact False.elim (notForall _ _ _ _ rfl)
    simpa only [zero, Nat.add_zero] using arity
  | @parameter name domain body binder index indices reader normalized terminal finalIndex finalIndices finalReader
      bound normalization tail induction =>
    have free : stats.params[index]!.isFVar = true := by
      simpa only [getElem!_pos, bound] using parameterFVars _ (Array.getElem_mem bound)
    have preserved := whnf_instantiate_arity name domain body binder _ reader free normalized normalization
    exact induction (by omega)
  | index notParameter _ tail induction =>
    exact induction (by omega)

theorem RecursorIndexParameterPrefix.indexSuffix
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader) :
    RecursorIndexTrace stats residual afterIndex indices reader terminal finalIndex finalIndices finalReader := by
  induction parameters with
  | done => exact trace
  | parameter bound normalization remaining induction =>
    cases trace with
    | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
    | parameter _ actual tail =>
      have same := Except.ok.inj (normalization.symm.trans actual)
      cases same
      exact induction tail
    | index notParameter => exact False.elim (notParameter bound)

theorem RecursorIndexParameterPrefix.annotationSuffix
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (annotations : IndexTraceAnnotationSupport environment universes trace) :
    IndexTraceAnnotationSupport environment universes (parameters.indexSuffix trace) := by
  induction parameters with
  | done => exact annotations
  | parameter bound normalization remaining induction =>
    cases annotations with
    | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
    | parameter _ actual tail supported =>
      have same := Except.ok.inj (normalization.symm.trans actual)
      cases same
      exact induction supported
    | index notParameter => exact False.elim (notParameter bound)

theorem RecursorIndexParameterPrefix.normalizationSuffix
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    IndexTraceNormalizationSupport environment universes (parameters.indexSuffix trace) := by
  induction parameters with
  | done => exact normalizations
  | parameter bound normalization remaining induction =>
    cases normalizations with
    | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
    | parameter _ actual tail supported =>
      have same := Except.ok.inj (normalization.symm.trans actual)
      cases same
      exact induction supported
    | index notParameter => exact False.elim (notParameter bound)

inductive IndexParameterNormalizationSupport (environment : VEnv) (universes : List Name)
    (virtual : VLCtx) {stats : InductiveStats} {reader : Context} :
    {source : Expr} → {index : Nat} → {residual : Expr} → {afterIndex : Nat} →
    RecursorIndexParameterPrefix stats reader source index residual afterIndex → Prop where
  | done (complete : stats.params.size ≤ index) :
      IndexParameterNormalizationSupport environment universes virtual (.done (source := source) complete)
  | parameter {name : Name} {domain body normalized residual : Expr} {binder : BinderInfo}
      {index afterIndex : Nat}
      (bound : index < stats.params.size)
      (normalization : (monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr)
        reader = .ok normalized)
      (remaining : RecursorIndexParameterPrefix stats reader normalized (index + 1) residual afterIndex)
      (headSupported : ∀ semantic,
        TrExpr environment universes virtual (body.instantiate1 stats.params[index]!) semantic →
        TrExpr environment universes virtual normalized semantic)
      (tailSupported : IndexParameterNormalizationSupport environment universes virtual remaining) :
      IndexParameterNormalizationSupport environment universes virtual
        (.parameter (name := name) (domain := domain) (binder := binder) bound normalization remaining)

theorem RecursorIndexParameterPrefix.normalizationSupport
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) :
    IndexParameterNormalizationSupport checker.venv checker.lparams checker.vlctx parameters := by
  induction parameters with
  | done complete => exact .done complete
  | parameter bound normalization remaining induction =>
    exact .parameter bound normalization remaining
      (fun _ translated => acceptedHeaderNormalization checker reader aligned initialWF translated normalization)
      induction

theorem RecursorIndexParameterPrefix.normalizationSupport_ofSortTelescope
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (telescope : SortTelescope source) :
    IndexParameterNormalizationSupport environment universes virtual parameters := by
  induction parameters with
  | done complete => exact .done complete
  | @parameter name domain body normalized residual binder index afterIndex bound normalization remaining induction =>
    cases telescope with
    | forallE _ _ _ bodyTelescope =>
      have nextTelescope := (bodyTelescope.whnfStep name domain binder stats.params[index]!
        reader normalized normalization).1
      exact .parameter bound normalization remaining
        (fun _ translated => bodyTelescope.normalizedTranslation normalization translated)
        (induction nextTelescope)

theorem RecursorIndexParameterPrefix.normalizedTranslation
    (parameters : RecursorIndexParameterPrefix stats reader source index residual afterIndex)
    (environmentWF : environment.WF) (model : MLCtx) (modelWF : model.WF environment universes)
    (arguments : TypedParameterArguments environment universes model semantic
      (stats.params.toList.drop index) values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (support : IndexParameterNormalizationSupport environment universes model.vlctx parameters) :
    TrExpr environment universes model.vlctx residual resultSemantic := by
  induction parameters generalizing semantic values with
  | done complete =>
    have empty : stats.params.toList.drop _ = [] :=
      List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using complete)
    rw [empty] at arguments
    cases arguments
    exact translated
  | @parameter name domain body normalized residual binder index afterIndex bound normalization remaining induction =>
    have listed : stats.params.toList[index] = stats.params[index]! := by
      simpa only [getElem!_pos stats.params index bound] using
        (Array.getElem_toList (xs := stats.params) bound)
    have drop : stats.params.toList.drop index = stats.params[index]! :: stats.params.toList.drop (index + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using bound), listed]
    rw [drop] at arguments
    cases arguments with
    | cons argumentTranslated argumentTyped remainingArguments =>
      rename_i argumentSemantic expectedDomain remainingValues expectedBody
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

def ParameterizedRecursorIndexModelEndpoint (environment : VEnv) (universes : List Name)
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (initial final : MLCtx) (semantic : VExpr) : Prop :=
  ∃ residual afterIndex values resultSemantic residualSemantic finalVirtual finalSemantic,
    ∃ parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex,
      TrExpr environment universes initial.vlctx source semantic ∧
      TypedParameterArguments environment universes initial semantic stats.params.toList values resultSemantic ∧
      TrExprS environment universes initial.vlctx residual residualSemantic ∧
      environment.IsDefEqU universes.length initial.vlctx.toCtx residualSemantic resultSemantic ∧
      TranslatedRecursorIndexTrace environment universes (parameters.indexSuffix trace)
        initial.vlctx residualSemantic finalVirtual finalSemantic ∧
      final.WF environment universes ∧ final.lctx = finalReader.lctx ∧ final.vlctx = finalVirtual ∧
      ∃ identifiers, IndexMLCtxExtension initial identifiers final ∧ indices.toList = identifiers.map Expr.fvar

theorem RecursorIndexTrace.parameterized
    {stats : InductiveStats} {source residual terminal : Expr} {afterIndex finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (parameters : RecursorIndexParameterPrefix stats reader source 0 residual afterIndex)
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (model : MLCtx) (modelWF : model.WF environment universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (arguments : TypedParameterArguments environment universes model semantic stats.params.toList values resultSemantic)
    (translated : TrExpr environment universes model.vlctx source semantic)
    (parameterSupport : IndexParameterNormalizationSupport environment universes model.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport environment universes trace)
    (normalizations : IndexTraceNormalizationSupport environment universes trace) :
    ∃ finalModel, ParameterizedRecursorIndexModelEndpoint environment universes trace model finalModel semantic := by
  obtain ⟨residualSemantic, residualTranslated, residualEquality⟩ := parameters.normalizedTranslation
    environmentWF model modelWF (by simpa only [List.drop_zero] using arguments) translated parameterSupport
  obtain ⟨finalVirtual, finalSemantic, history⟩ := (parameters.indexSuffix trace).translated
    environmentWF constants definitions parameters.complete (native ▸ modelWF.tr) reserved residualTranslated
    (parameters.annotationSuffix annotations) (parameters.normalizationSuffix normalizations)
  obtain ⟨finalModel, identifiers, finalWF, finalNative, converted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  exact ⟨finalModel, _, _, _, _, _, _, _, parameters, translated, arguments, residualTranslated,
    residualEquality, history, finalWF, finalNative, converted, identifiers, extension,
    by simpa only [Array.toList_empty, List.nil_append] using selected⟩

theorem RecursorIndexTrace.parameterizedOfChecker
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (arguments : TypedParameterArguments checker.venv checker.lparams checker.mlctx semantic
      stats.params.toList values resultSemantic)
    (translated : checker.TrExpr source semantic)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace) :
    ∃ finalModel, ParameterizedRecursorIndexModelEndpoint checker.venv checker.lparams trace
      checker.mlctx finalModel semantic := by
  obtain ⟨residual, afterIndex, parameters⟩ := trace.parameterPrefix complete
  exact trace.parameterized parameters checker.Ewf constants definitions checker.mlctx checker.mlctx_wf
    (checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)) reserved arguments translated
    (parameters.normalizationSupport checker aligned initialWF) annotations normalizations

theorem mkRecInfos.loopArgs1.parameterizedTraceOfChecker {resultType : Type}
    (stats : InductiveStats) (source : Expr) (fuel : Nat)
    (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (arguments : TypedParameterArguments checker.venv checker.lparams checker.mlctx semantic
      stats.params.toList values resultSemantic)
    (translated : checker.TrExpr source semantic)
    (supports : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current),
      IndexTraceAnnotationSupport checker.venv checker.lparams trace ∧
        IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current) finalModel,
      ParameterizedRecursorIndexModelEndpoint checker.venv checker.lparams trace
        checker.mlctx finalModel semantic → (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post := by
  have native : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  apply mkRecInfos.loopArgs1.scopedTrace stats source 0 #[] fuel next reader post
    (native ▸ checker.trlctx.1) reserved
  intro terminal finalIndex indices current trace frame
  obtain ⟨annotations, normalizations⟩ := supports terminal finalIndex indices current trace
  have complete := trace.completeParameters parameterFVars (by simpa only [Nat.zero_add] using arity)
  obtain ⟨finalModel, endpoint⟩ := trace.parameterizedOfChecker checker aligned initialWF
    constants definitions reserved complete arguments translated annotations normalizations
  exact nextWF terminal finalIndex indices current trace finalModel endpoint

theorem ParameterizedRecursorIndexModelEndpoint.context
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic) :
    final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx environment universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, finalWF, native, _⟩ := endpoint
  exact ⟨finalWF, native, by simpa only [native] using finalWF.tr⟩

theorem ParameterizedRecursorIndexModelEndpoint.application
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  obtain ⟨_, _, values, _, _, finalVirtual, finalSemantic, _, _, arguments, _, equality,
    history, _, _, converted, _⟩ := endpoint
  obtain ⟨appliedTranslated, appliedTyped⟩ := arguments.apply headTranslated headTyped
  have appliedTranslated : TrExprS environment universes initial.vlctx (mkAppN head stats.params)
      (ElimNestedInductive.applyParameterArguments headSemantic values) := by
    simpa only [mkAppN, Array.foldl_toList, Expr.mkAppList_eq_foldl] using appliedTranslated
  have normalizedTyped := appliedTyped.defeqU_r environmentWF initialWF.tr.wf.toCtx equality.symm
  obtain ⟨value, translated, typed⟩ := history.application environmentWF
    (by simpa only [mkAppN, Array.foldl_empty] using appliedTranslated) normalizedTyped
  exact ⟨value, finalSemantic, by simpa only [converted] using translated,
    by simpa only [converted] using history.finalTranslation.2,
    by simpa only [converted] using typed⟩

theorem ParameterizedRecursorIndexModelEndpoint.constantInputApplication
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic :=
  endpoint.application environmentWF initialWF input.valueTranslated input.valueTyped

theorem ParameterizedRecursorIndexModelEndpoint.parentTypehood
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (sorted : terminal.isSort = true) :
    ∃ value, TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) indices) value ∧
      environment.IsType universes.length final.vlctx.toCtx value := by
  obtain ⟨value, terminalSemantic, translated, terminalTranslated, typed⟩ :=
    endpoint.application environmentWF initialWF headTranslated headTyped
  cases terminal <;> simp [Expr.isSort] at sorted
  cases terminalTranslated with
  | sort mapped => exact ⟨value, translated, _, typed⟩

theorem ParameterizedRecursorIndexModelEndpoint.constantInputParentTypehood
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (sorted : terminal.isSort = true) :
    ∃ value, TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) indices) value ∧
      environment.IsType universes.length final.vlctx.toCtx value :=
  endpoint.parentTypehood environmentWF initialWF input.valueTranslated input.valueTyped sorted

theorem ParameterizedRecursorIndexModelEndpoint.indexAbstraction
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ identifiers : List FVarId, ∃ bound : identifiers.length ≤ final.length,
      indices.toList = identifiers.map Expr.fvar ∧
      ∃ abstraction level,
        TrExprS environment universes final.vlctx
          (final.mkForall identifiers.length bound (.sort elimLevel)) abstraction ∧
        environment.HasType universes.length final.vlctx.toCtx abstraction (.sort level) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, finalWF, _, _, identifiers, extension, selected⟩ := endpoint
  exact ⟨identifiers, extension.bound, selected, extension.typedAbstraction environmentWF finalWF mapped⟩

theorem ParameterizedRecursorIndexModelEndpoint.majorOpening
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS environment universes initial.vlctx stats.indConsts[parent]! headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (terminalSort : terminal = .sort terminalLevel)
    (mapped : VLevel.ofLevel universes terminalLevel = some level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled, RecursorMajorOpening environment universes stats parent indices
      finalReader final.vlctx rawSemantic peeled level := by
  have endpointCopy := endpoint
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, history, _, _, _, _⟩ := endpointCopy
  obtain ⟨rawSemantic, terminalSemantic, translated, terminalTranslated, typed⟩ :=
    endpoint.application environmentWF initialWF headTranslated headTyped
  rw [terminalSort] at terminalTranslated
  cases terminalTranslated with
  | sort actualMapped =>
    have equal := Option.some.inj (actualMapped.symm.trans mapped)
    cases equal
    have correspondence := endpoint.context.2.2
    have finalReserved := (history.scope reserved).reserved
    have spine := TypedAnnotationSpine.ofTrExprS environmentWF correspondence.wf.toCtx
      constants uniform translated typed
    obtain ⟨peeled, peeledTranslated, equality⟩ :=
      spine.peelTypeAnnotations definitions environmentWF.ordered
    have pushed := translatedIndexContextPush (name := `t) (bi := .default)
      correspondence finalReserved peeledTranslated equality.hasType.2
    exact ⟨rawSemantic, peeled, translated, typed, peeledTranslated, equality,
      equality.hasType.2, pushed,
      newlyAllocatedBinderPositioned finalReader `t _ .default correspondence.1 finalReserved,
      Context.RecursorScopeFrame.push finalReader correspondence.1 finalReserved `t .default
        (recursorMajorDomain stats parent indices)⟩

theorem ParameterizedRecursorIndexModelEndpoint.constantInputMajorOpening
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (input : RecursorConstantInput environment universes initial.vlctx name levels originalSource)
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final input.semanticType)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (head : stats.indConsts[parent]! = .const name levels)
    (terminalSort : terminal = .sort terminalLevel)
    (mapped : VLevel.ofLevel universes terminalLevel = some level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled, RecursorMajorOpening environment universes stats parent indices
      finalReader final.vlctx rawSemantic peeled level :=
  endpoint.majorOpening environmentWF initialWF constants definitions reserved
    (head ▸ input.valueTranslated) input.valueTyped terminalSort mapped uniform

theorem ParameterizedRecursorIndexModelEndpoint.motiveDomainTranslation
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : ParameterizedRecursorIndexModelEndpoint environment universes trace initial final semantic)
    (opening : RecursorMajorOpening environment universes stats parent indices finalReader
      final.vlctx rawSemantic peeled majorLevel)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (native : initial.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ motiveSemantic motiveLevel, RecursorMotiveDomainTranslation environment universes
      stats parent indices finalReader final.vlctx peeled elimLevel motiveSemantic motiveLevel := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, history, _, _, converted, _⟩ := endpoint
  obtain ⟨motiveSemantic, motiveLevel, translated⟩ := history.motiveDomainTranslation
    (by simpa only [converted] using opening) environmentWF initial initialWF native rfl reserved mapped
  exact ⟨motiveSemantic, motiveLevel, by simpa only [converted] using translated⟩

end Lean4Lean.AddInductive
