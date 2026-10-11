import Lean4Lean.Verify.InductiveHeaderIndexApplications

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem translatedForallIndexOpening_unrestricted
    {environment : VEnv} {universes : List Name} {virtual : VLCtx} {reader : Context}
    {name : Name} {domain body : Expr} {binder : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (correspondence : TrLCtx environment universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS environment universes virtual (.forallE name domain body binder)
      (.forallE semantic bodySemantic))
    (domainTyped : environment.HasType universes.length virtual.toCtx semantic (.sort level)) :
    ∃ peeled, PeeledIndexOpening environment universes reader virtual name domain body binder
      semantic bodySemantic level peeled := by
  cases translated with
  | forallE _ _ domainTranslated bodyTranslated =>
    obtain ⟨peeled, peeledTranslated, equality, _, convertedBody⟩ :=
      domainTranslated.peeledAnonymousBodyTranslation environmentWF correspondence.wf constants definitions
        domainTyped bodyTranslated
    have nextCorrespondence := translatedIndexContextPush (name := name) (bi := binder)
      correspondence reserved peeledTranslated equality.hasType.2
    have opened : TrExpr environment universes
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
        (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) bodySemantic := by
      rw [Expr.instantiate1_eq]
      exact convertedBody.openFreshFVar environmentWF.ordered nextCorrespondence.wf
    exact ⟨peeled, peeledTranslated, equality, nextCorrespondence, opened,
      newlyAllocatedBinderPositioned reader name domain binder correspondence.1 reserved,
      Context.RecursorScopeFrame.push reader correspondence.1 reserved name binder (peelTypeAnnotations domain)⟩

theorem RecursorIndexTrace.checkedIndexModels
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (indexOnly : stats.params.size ≤ index)
    (translated : checker.TrExprS source semantic) :
    ∃ (finalChecker : TypeChecker.VContext) (finalSemantic : VExpr) (identifiers : List FVarId),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      IndexMLCtxExtension checker.mlctx identifiers finalChecker.mlctx ∧
      finalIndices.toList = indices.toList ++ identifiers.map Expr.fvar ∧
      TranslatedRecursorIndexTrace checker.venv checker.lparams trace checker.vlctx semantic
        finalChecker.vlctx finalSemantic := by
  induction trace generalizing checker semantic with
  | @stop source index indices reader notForall =>
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    exact ⟨checker, semantic, [], rfl, rfl, aligned, initialWF, .nil,
      by simp only [List.map_nil, List.append_nil],
      .stop notForall (native ▸ checker.mlctx_wf.tr) translated⟩
  | parameter parameter normalization tail induction =>
    exact False.elim (Nat.not_lt_of_ge indexOnly parameter)
  | @index name domain body binder index indices reader normalized terminal finalIndex finalIndices finalReader
      notParameter normalization tail induction =>
    have original := translated
    cases translated with
    | forallE domainIsType bodyIsType domainTranslated bodyTranslated =>
      rename_i domainSemantic bodySemantic
      obtain ⟨level, domainTyped⟩ := domainIsType
      have native : checker.mlctx.lctx = reader.lctx :=
        checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
      obtain ⟨peeled, opening⟩ := translatedForallIndexOpening_unrestricted checker.Ewf constants definitions
        (native ▸ checker.mlctx_wf.tr) reserved original domainTyped
      let nextModel := MLCtx.vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled binder checker.mlctx
      have nextModelWF : nextModel.WF checker.venv checker.lparams := by
        refine ⟨checker.mlctx_wf, ?_, opening.1, level, opening.2.1.hasType.2⟩
        rw [native]
        exact reserved.fresh (native ▸ checker.trlctx.1)
      let nextChecker := checker.withMLC nextModel (wf := ⟨nextModelWF⟩)
      have nextAligned : HeaderCheckerAligned nextChecker
          (recursorIndexContext reader name binder (peelTypeAnnotations domain)) := by
        change { checker.toContext with lctx := nextModel.lctx } = _
        rw [aligned]
        simp only [nextModel, MLCtx.lctx, native, recursorIndexContext]
      have nextReserved : ∀ identifier ∈ nextChecker.vlctx.fvars,
          ({} : TypeChecker.VState).ngen.Reserves identifier := by
        change ∀ identifier ∈ (⟨reader.ngen.curr⟩ :: checker.vlctx.fvars),
          ({} : TypeChecker.VState).ngen.Reserves identifier
        simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨?_, initialWF.ngen_wf⟩
        intro count same
        have prefixes : reader.ngen.namePrefix = ({} : TypeChecker.VState).ngen.namePrefix :=
          (Name.num.inj (FVarId.mk.inj same)).1
        exact False.elim (different prefixes.symm)
      have nextStateWF := TypeChecker.VState.WF.reset nextChecker nextReserved
      obtain ⟨normalizedSemantic, normalizedTranslated, normalizedEquality⟩ :=
        acceptedHeaderNormalization nextChecker _ nextAligned nextStateWF opening.2.2.2.1 normalization
      obtain ⟨finalChecker, finalSemantic, identifiers, sameEnvironment, sameUniverses,
        finalAligned, finalWF, extension, selected, history⟩ :=
        induction nextChecker nextAligned nextStateWF opening.2.2.2.2.2.reserved different
          constants definitions indexOnly normalizedTranslated
      refine ⟨finalChecker, finalSemantic, ⟨reader.ngen.curr⟩ :: identifiers, sameEnvironment, sameUniverses,
        finalAligned, finalWF, ?_, ?_, ?_⟩
      · exact (IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ name
          (peelTypeAnnotations domain) peeled binder).trans extension
      · simpa only [Array.toList_push, List.map_cons, List.append_assoc, List.singleton_append] using selected
      · exact .index notParameter normalization tail original opening normalizedTranslated normalizedEquality history

def HeaderRecursorIndexCheckerEndpoint
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker finalChecker : TypeChecker.VContext) (semantic resultSemantic : VExpr) : Prop :=
  finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
  HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
  HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace
    checker.mlctx finalChecker.mlctx semantic resultSemantic

theorem HeaderRecursorIndexCheckerEndpoint.model
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic) :
    HeaderRecursorIndexModelEndpoint checker.venv checker.lparams trace
      checker.mlctx finalChecker.mlctx semantic resultSemantic := endpoint.2.2.2.2

theorem HeaderRecursorIndexCheckerEndpoint.checkerContext
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic) :
    finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker :=
  ⟨endpoint.1, endpoint.2.1, endpoint.2.2.1, endpoint.2.2.2.1⟩

theorem RecursorIndexTrace.headerCheckedModels
    {stats : InductiveStats} {source headerSource terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats headerSource)
    (normalized : (monadLift (TypeChecker.whnf headerSource) : M Expr) reader = .ok source) :
    ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result := by
  obtain ⟨residual, afterIndex, parameters⟩ := trace.parameterPrefix complete
  have translated := acceptedHeaderNormalization checker reader aligned initialWF
    (input.sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalized
  obtain ⟨residualSemantic, residualTranslated, residualEquality⟩ := parameters.normalizedApplications
    checker.Ewf checker.mlctx checker.mlctx_wf (by simpa only [List.drop_zero] using input.arguments)
    translated (parameters.normalizationSupport checker aligned initialWF)
  obtain ⟨finalChecker, finalSemantic, identifiers, sameEnvironment, sameUniverses, finalAligned,
    finalStateWF, extension, selected, history⟩ :=
    (parameters.indexSuffix trace).checkedIndexModels checker aligned initialWF reserved different
      constants definitions parameters.complete residualTranslated
  have finalModelWF : finalChecker.mlctx.WF checker.venv checker.lparams := by
    simpa only [sameEnvironment, sameUniverses] using finalChecker.mlctx_wf
  have native : finalChecker.mlctx.lctx = finalReader.lctx :=
    finalChecker.lctx_eq.trans (congrArg TypeChecker.Context.lctx finalAligned)
  exact ⟨finalChecker, sameEnvironment, sameUniverses, finalAligned, finalStateWF,
    residual, afterIndex, input.values, residualSemantic, finalChecker.vlctx, finalSemantic,
    parameters, translated, input.arguments, residualTranslated, residualEquality, history,
    finalModelWF, native, rfl, identifiers, extension,
    by simpa only [Array.toList_empty, List.nil_append] using selected⟩

theorem HeaderRecursorIndexCheckerEndpoint.applicationOfPartial
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic) :
    ∃ finalValue terminalSemantic,
      finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType finalValue terminalSemantic := by
  obtain ⟨sameEnvironment, sameUniverses, _, _, model⟩ := endpoint
  obtain ⟨finalValue, terminalSemantic, translated, terminalTranslated, typed⟩ :=
    model.applicationOfPartial checker.Ewf checker.mlctx_wf translated typed
  exact ⟨finalValue, terminalSemantic,
    by simpa only [TypeChecker.VContext.TrExprS, sameEnvironment, sameUniverses] using translated,
    by simpa only [TypeChecker.VContext.TrExprS, sameEnvironment, sameUniverses] using terminalTranslated,
    by simpa only [TypeChecker.VContext.HasType, sameEnvironment, sameUniverses] using typed⟩

theorem HeaderRecursorIndexCheckerEndpoint.parentTypehoodOfPartial
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic) (sorted : terminal.isSort = true) :
    ∃ finalValue, finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.IsType finalValue := by
  obtain ⟨sameEnvironment, sameUniverses, _, _, model⟩ := endpoint
  obtain ⟨finalValue, translated, typed⟩ :=
    model.parentTypehoodOfPartial checker.Ewf checker.mlctx_wf translated typed sorted
  exact ⟨finalValue,
    by simpa only [TypeChecker.VContext.TrExprS, sameEnvironment, sameUniverses] using translated,
    by simpa only [TypeChecker.VContext.IsType, sameEnvironment, sameUniverses] using typed⟩

theorem RecursorIndexTrace.checkedHeaderBatch
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        ∃ value terminalSemantic,
          finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType value terminalSemantic := by
  obtain ⟨input, partialValue, translated, typed⟩ := batch parent bound
  obtain ⟨finalChecker, endpoint⟩ := trace.headerCheckedModels checker aligned initialWF reserved different
    constants definitions complete input normalized
  exact ⟨input, finalChecker, endpoint, endpoint.applicationOfPartial translated typed⟩

theorem mkRecInfos.loopArgs1.checkedHeaderBatchTrace {resultType : Type}
    (stats : InductiveStats) (types : Array InductiveType) (parent : Nat) (bound : parent < types.size)
    (source : Expr) (fuel : Nat) (next : Array Expr → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterFVars : stats.ParamsAreFVars)
    (arity : stats.params.size ≤ declareConstructors.arity 0 source)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (nextWF : ∀ terminal finalIndex indices current
      (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices current)
      (input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type)
      finalChecker,
      HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result →
      (∃ value terminalSemantic,
        finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
        finalChecker.TrExprS terminal terminalSemantic ∧ finalChecker.HasType value terminalSemantic) →
      (next indices current).WF post) :
    (mkRecInfos.loopArgs1 stats source 0 #[] fuel next reader).WF post := by
  have native : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  apply mkRecInfos.loopArgs1.scopedTrace stats source 0 #[] fuel next reader post (native ▸ checker.trlctx.1) reserved
  intro terminal finalIndex indices current trace frame
  have complete := trace.completeParameters parameterFVars (by simpa only [Nat.zero_add] using arity)
  obtain ⟨input, finalChecker, endpoint, application⟩ := trace.checkedHeaderBatch checker aligned initialWF
    reserved different constants definitions complete batch parent bound normalized
  exact nextWF terminal finalIndex indices current trace input finalChecker endpoint application

end Lean4Lean.AddInductive
