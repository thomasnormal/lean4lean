import Lean4Lean.Verify.InductiveRecursorSignatureInputs
import Lean4Lean.Verify.InductiveParameterPrefixTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterArguments ContextReserved)
open private selectedParameterBound absentParameterBound from Lean4Lean.Verify.InductiveConstructorDomainTrace
open private relatedMemberLeft from Lean4Lean.Verify.InductiveConstructorSemanticReceipts

inductive RecursorCtorParameterPrefix (stats : InductiveStats) :
    Expr → Nat → Expr → Nat → List Expr → Prop where
  | done (complete : stats.params.size ≤ index) :
      RecursorCtorParameterPrefix stats source index source index []
  | parameter {name : Name} {domain body parameter residual : Expr} {binder : BinderInfo}
      {index afterIndex : Nat} {arguments : List Expr}
      (selected : stats.params[index]? = some parameter)
      (remaining : RecursorCtorParameterPrefix stats (body.instantiate1 parameter)
        (index + 1) residual afterIndex arguments) :
      RecursorCtorParameterPrefix stats (.forallE name domain body binder)
        index residual afterIndex (parameter :: arguments)

theorem RecursorCtorParameterPrefix.complete
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments) :
    stats.params.size ≤ afterIndex := by
  induction parameterPrefix with
  | done complete => exact complete
  | parameter _ _ induction => exact induction

theorem RecursorCtorParameterPrefix.count
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments) :
    afterIndex = max index stats.params.size := by
  induction parameterPrefix with
  | done complete => exact (Nat.max_eq_left complete).symm
  | parameter selected _ induction =>
    have bound := selectedParameterBound selected
    omega

structure TypedCtorParameterPrefix (checker : TypeChecker.VContext) (stats : InductiveStats)
    (source : Expr) (index : Nat) (semantic : VExpr) where
  residual : Expr
  afterIndex : Nat
  nativePrefix : RecursorCtorParameterPrefix stats source index residual afterIndex (stats.params.toList.drop index)
  arguments : List VExpr
  residualSemantic : VExpr
  typedArguments : TypedParameterArguments checker.venv checker.lparams checker.mlctx
    semantic (stats.params.toList.drop index) arguments residualSemantic
  translated : checker.TrExprS residual residualSemantic

theorem AcceptedConstructorTrace.parameterPrefix
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {source terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index source finalReader finalIndex terminal)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (parameterFVars : stats.ParamsAreFVars) (distinct : stats.params.toList.Nodup)
    (absent : stats.RemainingParamsAbsent index source)
    {semantic : VExpr} (translated : checker.TrExprS source semantic) :
    Nonempty (TypedCtorParameterPrefix checker stats source index semantic) := by
  induction trace generalizing checker semantic with
  | terminal notForall valid =>
    have complete := absent.validIndAppIdx parameterFVars valid
    have empty : stats.params.toList.drop _ = [] :=
      List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using complete)
    exact ⟨{
      residual := _, afterIndex := _, nativePrefix := by rw [empty]; exact .done complete,
      arguments := [], residualSemantic := semantic, typedArguments := by rw [empty]; exact .nil,
      translated }⟩
  | @parameter index parameter reader stored domain body finalReader finalIndex terminal name binder
      selected storedCall equalCall tail induction =>
    have bound := selectedParameterBound selected
    have same : stats.params[index] = parameter := by
      simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq] using selected
    have member : parameter ∈ stats.params := same ▸ Array.getElem_mem bound
    obtain ⟨identifier, equation, present⟩ := parameters parameter member
    obtain ⟨declaration, lookup⟩ := checker.trlctx.find?_eq_some.mpr present
    have lookup : reader.lctx.find? identifier = some declaration := by
      simpa only [checker.lctx_eq, congrArg TypeChecker.Context.lctx aligned] using lookup
    obtain ⟨domainSemantic, bodySemantic, argumentSemantic, sourceShape, argumentTranslated,
      argumentTyped, opened, _⟩ := translatedReusedHeaderParameterArgument checker reader aligned initialWF
        lookup translated (by simpa only [equation] using storedCall) equalCall
    have nextAbsent := absent.consume_param parameterFVars distinct bound
    rw [same] at nextAbsent
    obtain ⟨remaining⟩ := induction checker aligned initialWF parameters
      nextAbsent (by simpa only [equation] using opened)
    have arguments : stats.params.toList.drop index = parameter :: stats.params.toList.drop (index + 1) := by
      have listed : stats.params.toList[index] = parameter :=
        (Array.getElem_toList (xs := stats.params) bound).trans same
      rw [List.drop_eq_getElem_cons (by simpa using bound), listed]
    rw [sourceShape]
    exact ⟨{
      residual := remaining.residual, afterIndex := remaining.afterIndex,
      nativePrefix := by rw [arguments]; exact .parameter selected remaining.nativePrefix,
      arguments := argumentSemantic :: remaining.arguments, residualSemantic := remaining.residualSemantic,
      typedArguments := by
        rw [arguments]
        exact .cons (by simpa only [equation] using argumentTranslated) argumentTyped remaining.typedArguments,
      translated := remaining.translated }⟩
  | field selected _ _ _ _ _ =>
    have complete := absentParameterBound selected
    have empty : stats.params.toList.drop _ = [] :=
      List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using complete)
    exact ⟨{
      residual := _, afterIndex := _, nativePrefix := by rw [empty]; exact .done complete,
      arguments := [], residualSemantic := semantic, typedArguments := by rw [empty]; exact .nil,
      translated }⟩

theorem RecursorCtorParameterPrefix.fieldSuffix
    {stats : InductiveStats} {source residual terminal : Expr} {index afterIndex finalIndex : Nat}
    {arguments : List Expr} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments)
    (trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    RecursorCtorFieldTrace stats residual afterIndex fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader := by
  induction parameterPrefix with
  | done => exact trace
  | parameter selected remaining induction =>
    cases trace with
    | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
    | parameter actual tail =>
      have equal := Option.some.inj (selected.symm.trans actual)
      cases equal
      exact induction tail
    | field missing => rw [selected] at missing; cases missing

theorem RecursorCtorParameterPrefix.annotationSuffix
    {environment : VEnv} {universes : List Name}
    {stats : InductiveStats} {source residual terminal : Expr} {index afterIndex finalIndex : Nat}
    {arguments : List Expr} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments)
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (supported : CtorFieldTraceAnnotationSupport environment universes trace) :
    CtorFieldTraceAnnotationSupport environment universes (parameterPrefix.fieldSuffix trace) := by
  induction parameterPrefix with
  | done => exact supported
  | parameter selected remaining induction =>
    cases supported with
    | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
    | parameter actual tail supportedTail =>
      have equal := Option.some.inj (selected.symm.trans actual)
      cases equal
      exact induction supportedTail
    | field missing => rw [selected] at missing; cases missing

theorem ConstructorSemanticReceipts.parameterPrefix
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (parent : Nat) (bound : parent < types.size) (source : Constructor)
    (member : source ∈ types[parent].ctors) :
    ∃ semantic, stage.model.checker.TrExprS source.type semantic ∧
      Nonempty (TypedCtorParameterPrefix stage.model.checker stats source.type 0 semantic) := by
  have sourceMember : source ∈ types.toList.flatMap (fun type => type.ctors) :=
    List.mem_flatMap.mpr ⟨types[parent], Array.mem_toList_iff.mpr (Array.getElem_mem bound), member⟩
  obtain ⟨constructor, _, translated⟩ := relatedMemberLeft receipts.translated.constructorModels sourceMember
  have closedTranslated : TrExprS stage.model.checker.venv stage.model.checker.lparams []
      source.type constructor.type := by
    simpa only [stage.semantic_eq, stage.shadowUniverses] using translated.2.2
  have free : FVarsIn (fun _ => False) source.type := by
    simpa only [VLCtx.fvars, List.filterMap_nil, List.not_mem_nil] using closedTranslated.fvarsIn
  have weakened := closedTranslated.weakFV stage.model.checker.Ewf.ordered
    (VLCtx.FVLift.from_nil stage.model.checker.mlctx.noBV) stage.model.checker.Δwf
  obtain ⟨_, _, _, _, trace, _⟩ := receipts.domains parent bound source member
  exact ⟨_, weakened, trace.parameterPrefix stage.model.checker stage.model.aligned stage.model.initialWF
    stage.model.parameterModels stage.model.paramsAreFVars stage.model.paramsNodup
    (.of_noFVars free 0) weakened⟩

theorem _root_.Lean4Lean.ElimNestedInductive.TypedParameterArguments.monoEnv
    (arguments : TypedParameterArguments environment universes model functionType
      replacements semantics resultType) (increase : environment ≤ extended) :
    TypedParameterArguments extended universes model functionType replacements semantics resultType := by
  induction arguments with
  | nil => exact .nil
  | cons translated typed _ induction => exact .cons (translated.mono increase) (typed.mono increase) induction

def ParameterizedCtorFieldModelEndpoint (environment : VEnv) (universes : List Name)
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader)
    (initial final : MLCtx) (semantic : VExpr) : Prop :=
  ∃ residual afterIndex arguments residualSemantic finalVirtual finalSemantic,
    ∃ parameterPrefix : RecursorCtorParameterPrefix stats source 0 residual afterIndex stats.params.toList,
      TrExprS environment universes initial.vlctx source semantic ∧
      TypedParameterArguments environment universes initial semantic stats.params.toList arguments residualSemantic ∧
      TrExprS environment universes initial.vlctx residual residualSemantic ∧
      TranslatedRecursorCtorFieldTrace environment universes (parameterPrefix.fieldSuffix trace)
        initial.vlctx residualSemantic finalVirtual finalSemantic ∧
      final.WF environment universes ∧ final.lctx = finalReader.lctx ∧ final.vlctx = finalVirtual ∧
      ∃ identifiers, IndexMLCtxExtension initial identifiers final ∧ fields.toList = identifiers.map Expr.fvar

theorem ConstructorConstantRegistration.parameterizedFields
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (parent : Nat) (bound : parent < types.size) (source : Constructor)
    (member : source ∈ types[parent].ctors)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (model : MLCtx) (modelWF : model.WF registration.semantic root.lparams)
    (insertion : VLCtx.FVLift' stage.model.checker.vlctx model.vlctx 0 insertionLift 0)
    {initialReader finalReader : Context} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields : Array Expr}
    (trace : RecursorCtorFieldTrace stats source.type 0 #[] #[] initialReader
      terminal finalIndex fields recursiveFields finalReader)
    (native : model.lctx = initialReader.lctx)
    (reserved : ContextReserved initialReader.lctx initialReader.ngen)
    (annotations : CtorFieldTraceAnnotationSupport registration.semantic root.lparams trace) :
    ∃ semantic finalModel,
      ParameterizedCtorFieldModelEndpoint registration.semantic root.lparams trace model finalModel semantic := by
  obtain ⟨semantic, translated, ⟨parameters⟩⟩ := receipts.parameterPrefix parent bound source member
  have parameterPrefix : RecursorCtorParameterPrefix stats source.type 0 parameters.residual
      parameters.afterIndex stats.params.toList := by
    simpa only [List.drop_zero] using parameters.nativePrefix
  have increase : stage.model.checker.venv ≤ registration.semantic :=
    stage.semantic_eq.symm ▸ registration.increase
  have translated : TrExprS registration.semantic root.lparams stage.model.checker.vlctx source.type semantic := by
    simpa only [stage.shadowUniverses] using translated.mono increase
  have arguments : TypedParameterArguments registration.semantic root.lparams stage.model.checker.mlctx
      semantic stats.params.toList parameters.arguments parameters.residualSemantic := by
    simpa only [stage.shadowUniverses, List.drop_zero] using parameters.typedArguments.monoEnv increase
  have residualTranslated : TrExprS registration.semantic root.lparams stage.model.checker.vlctx
      parameters.residual parameters.residualSemantic := by
    simpa only [stage.shadowUniverses] using parameters.translated.mono increase
  have reachedArguments := arguments.weakFV registration.semanticWF modelWF insertion
  have reachedResidual := residualTranslated.weakFV' registration.semanticWF.ordered insertion modelWF.tr.wf
  have rootIncrease := (VEnv.addInductHeaders.le receipts.registered).trans registration.increase
  obtain ⟨finalVirtual, finalSemantic, history⟩ := (parameterPrefix.fieldSuffix trace).translated
    registration.semanticWF (constants.mono rootIncrease) (definitions.mono rootIncrease)
    parameterPrefix.complete (native ▸ modelWF.tr) reserved reachedResidual
    (parameterPrefix.annotationSuffix annotations)
  obtain ⟨finalModel, identifiers, finalWF, finalNative, finalConverted, extension, selected⟩ :=
    history.mixedContext model modelWF native rfl reserved
  exact ⟨_, finalModel, parameters.residual, parameters.afterIndex, _, _, finalVirtual, finalSemantic,
    parameterPrefix, translated.weakFV' registration.semanticWF.ordered insertion modelWF.tr.wf,
    reachedArguments, reachedResidual, history, finalWF, finalNative, finalConverted,
    identifiers, extension, by simpa only [Array.toList_empty, List.nil_append] using selected⟩

theorem ParameterizedCtorFieldModelEndpoint.context
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    (endpoint : ParameterizedCtorFieldModelEndpoint environment universes trace initial final semantic) :
    final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx environment universes finalReader.lctx final.vlctx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, finalWF, native, _⟩ := endpoint
  exact ⟨finalWF, native, by simpa only [native] using finalWF.tr⟩

theorem ParameterizedCtorFieldModelEndpoint.terminalTranslation
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    (endpoint : ParameterizedCtorFieldModelEndpoint environment universes trace initial final semantic) :
    ∃ terminalSemantic, TrExprS environment universes final.vlctx terminal terminalSemantic := by
  obtain ⟨_, _, _, _, _, finalSemantic, _, _, _, _, history, _, _, converted, _⟩ := endpoint
  exact ⟨finalSemantic, by simpa only [converted] using history.finalTranslation.2⟩

theorem ParameterizedCtorFieldModelEndpoint.application
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    (endpoint : ParameterizedCtorFieldModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) {head : Expr} {headSemantic : VExpr}
    (headTranslated : TrExprS environment universes initial.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx (mkAppN (mkAppN head stats.params) fields) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  obtain ⟨_, _, semanticArguments, _, _, finalSemantic, _, _, arguments, _, history, _, _, converted, _⟩ := endpoint
  obtain ⟨appliedTranslated, appliedTyped⟩ := arguments.apply headTranslated headTyped
  have appliedTranslated : TrExprS environment universes initial.vlctx (mkAppN head stats.params)
      (ElimNestedInductive.applyParameterArguments headSemantic semanticArguments) := by
    simpa only [mkAppN, Array.foldl_toList, Expr.mkAppList_eq_foldl] using appliedTranslated
  obtain ⟨value, valueTranslated, valueTyped⟩ := history.application environmentWF appliedTranslated appliedTyped
  exact ⟨value, finalSemantic, by simpa only [converted, mkAppN, Array.foldl_empty] using valueTranslated,
    by simpa only [converted] using history.finalTranslation.2,
    by simpa only [converted] using valueTyped⟩

theorem ParameterizedCtorFieldModelEndpoint.constantInputApplication
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    (endpoint : ParameterizedCtorFieldModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (input : RecursorConstantInput environment universes initial.vlctx name levels source) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) fields) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic := by
  have endpointCopy := endpoint
  obtain ⟨_, _, _, _, _, _, _, translated, _⟩ := endpointCopy
  exact endpoint.application environmentWF input.valueTranslated
    (input.alignedType environmentWF initialWF.tr.wf translated)

end Lean4Lean.AddInductive
