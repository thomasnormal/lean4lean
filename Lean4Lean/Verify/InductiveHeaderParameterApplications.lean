import Lean4Lean.Verify.InductiveMutualHeaderTyping
import Lean4Lean.Verify.InductiveParameterPrefixTyping
import Lean4Lean.Verify.InductiveHeaderKinds

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

inductive TypedParameterApplications (environment : VEnv) (universes : List Name) (model : MLCtx) :
    VExpr → List Expr → List VExpr → VExpr → Prop where
  | nil : TypedParameterApplications environment universes model result [] [] result
  | cons (translated : TrExprS environment universes model.vlctx replacement argument)
      (typed : environment.HasType universes.length model.vlctx.toCtx argument domain)
      (remaining : TypedParameterApplications environment universes model (body.inst argument)
        replacements arguments result) :
      TypedParameterApplications environment universes model (.forallE domain body)
        (replacement :: replacements) (argument :: arguments) result
  | convertInput (equality : environment.IsDefEqU universes.length model.vlctx.toCtx source target)
      (arguments : TypedParameterApplications environment universes model target replacements values result) :
      TypedParameterApplications environment universes model source replacements values result

theorem TypedParameterApplications.ofTypedArguments
    (arguments : TypedParameterArguments environment universes model source replacements values result) :
    TypedParameterApplications environment universes model source replacements values result := by
  induction arguments with
  | nil => exact .nil
  | cons translated typed _ induction => exact .cons translated typed induction

theorem TypedParameterApplications.length
    (arguments : TypedParameterApplications environment universes model source replacements values result) :
    replacements.length = values.length := by
  induction arguments with
  | nil => rfl
  | cons _ _ _ induction => exact congrArg Nat.succ induction
  | convertInput _ _ induction => exact induction

theorem TypedParameterApplications.append
    (first : TypedParameterApplications environment universes model source replacements values middle)
    (second : TypedParameterApplications environment universes model middle more moreValues result) :
    TypedParameterApplications environment universes model source
      (replacements ++ more) (values ++ moreValues) result := by
  induction first with
  | nil => exact second
  | cons translated typed _ induction => exact .cons translated typed (induction second)
  | convertInput equality _ induction => exact .convertInput equality (induction second)

theorem TypedParameterApplications.monoEnv
    (arguments : TypedParameterApplications environment universes model source replacements values result)
    (increase : environment ≤ extended) :
    TypedParameterApplications extended universes model source replacements values result := by
  induction arguments with
  | nil => exact .nil
  | cons translated typed _ induction => exact .cons (translated.mono increase) (typed.mono increase) induction
  | convertInput equality _ induction => exact .convertInput (equality.mono increase) induction

theorem TypedParameterApplications.weakFV
    (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (targetWF : target.WF environment universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    TypedParameterApplications environment universes target (source.lift' lift) replacements
      (values.map (VExpr.lift' · lift)) (result.lift' lift) := by
  induction arguments with
  | nil => exact .nil
  | cons translated typed _ induction =>
    simp only [VExpr.lift', List.map_cons]
    refine .cons (translated.weakFV' environmentWF.ordered insertion targetWF.tr.wf)
      (typed.weak' environmentWF.ordered insertion.toCtx) ?_
    simpa only [VExpr.lift'_inst_hi] using induction
  | convertInput equality _ induction =>
    exact .convertInput (equality.weak' environmentWF.ordered insertion.toCtx) induction

theorem TypedParameterApplications.apply
    (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (translated : TrExprS environment universes model.vlctx head semantic)
    (typed : environment.HasType universes.length model.vlctx.toCtx semantic source) :
    TrExprS environment universes model.vlctx (head.mkAppList replacements)
      (applyParameterArguments semantic values) ∧
    environment.HasType universes.length model.vlctx.toCtx (applyParameterArguments semantic values) result := by
  induction arguments generalizing head semantic with
  | nil => exact ⟨translated, typed⟩
  | cons argumentTranslated argumentTyped _ induction =>
    exact induction (.app typed argumentTyped translated argumentTranslated) (typed.app argumentTyped)
  | convertInput equality _ induction =>
    exact induction translated (typed.defeqU_r environmentWF modelWF.tr.wf.toCtx equality)

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix TypedParameterApplications ContextReserved)
open private bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

theorem CheckedHeaderTrace.paramsAppend
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader) :
    ∃ more, finalStats.params.toList = stats.params.toList ++ more := by
  induction trace with
  | stop => exact ⟨[], (List.append_nil _).symm⟩
  | freshParameter _ _ _ _ induction =>
    obtain ⟨more, equation⟩ := induction
    exact ⟨_ :: more, by simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using equation⟩
  | reusedParameter _ _ _ _ _ _ induction => exact induction
  | index _ _ _ induction => exact induction

theorem CheckedHeaderTrace.paramsAfterParameters
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (complete : nparams ≤ index) : finalStats.params = stats.params := by
  induction trace with
  | stop => rfl
  | freshParameter selected => omega
  | reusedParameter selected => omega
  | index _ _ _ induction => exact induction complete

private theorem liftedSkip (expression : VExpr) (count : Nat) :
    expression.lift' (.skipN .refl count) = expression.liftN count :=
  VExpr.lift'_consN_skipN (e := expression) (n := count) (k := 0)

theorem CheckedHeaderTrace.withoutParameters
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (complete : nparams ≤ index) :
    CheckedHeaderTrace 0 stats source 0 nindices reader terminal finalStats finalIndices finalReader := by
  induction trace with
  | stop notBinder _ => exact .stop notBinder rfl
  | freshParameter selected => exact False.elim (Nat.not_lt_of_ge complete selected)
  | reusedParameter selected => exact False.elim (Nat.not_lt_of_ge complete selected)
  | index _ normalized tail induction => exact .index (Nat.not_lt_zero _) normalized (induction complete)

theorem CheckedHeaderTrace.parameterApplicationsWithKind
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal sorted : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    {semantic : VExpr} (translated : checker.TrExprS source semantic)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId)
      (values : List VExpr) (result : VExpr),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN identifiers.length) (finalStats.params.toList.drop index) values result ∧
      checker.venv.SortArity checker.lparams.length finalChecker.vlctx.toCtx (finalIndices - nindices) result := by
  induction trace generalizing checker semantic with
  | @stop stats source index nindices reader notBinder complete =>
    have bound : stats.params.size ≤ index := by rw [parameterCount]; split <;> omega
    have empty : stats.params.toList.drop index = [] :=
      List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using bound)
    exact ⟨checker, [], [], semantic, rfl, rfl, aligned, initialWF, .nil, parameters,
      by simpa only [List.length_nil, VExpr.liftN_zero, empty] using
        (TypedParameterApplications.nil (environment := checker.venv) (universes := checker.lparams)
          (model := checker.mlctx) (result := semantic)),
      by simpa only [Nat.sub_self] using acceptedHeaderSortKind checker reader aligned initialWF translated sortedCall⟩
  | @freshParameter stats name domain body binder index nindices reader normalized terminal finalStats finalIndices
      finalReader selected first normalizedCall tail induction =>
    obtain ⟨peeled, nextChecker, sameEnv, sameUniverses, nextModel, nextAligned, nextWF,
      openedSemantic, opened, openedTyped, domainSemantic, bodySemantic, level, sourceShape,
      domainTyped, domainEquality, bodyEquality⟩ := translatedHeaderOpeningWithSemantics checker reader aligned
        initialWF reserved different constants definitions translated
    obtain ⟨normalizedSemantic, normalizedTranslated, normalizedEquality⟩ :=
      acceptedHeaderNormalization nextChecker _ nextAligned nextWF
        (opened.trExpr nextChecker.Ewf.ordered nextChecker.Δwf) normalizedCall
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [nextModel]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have nextParameters := (parameters.mono head.insertion.fvars_sublist.subset).push
      ⟨reader.ngen.curr⟩ (by rw [head.fvars]; simp)
    obtain ⟨finalChecker, identifiers, values, result, finalEnv, finalUniverses, finalAligned, finalWF,
      history, finalParameters, arguments, resultKind⟩ := induction nextChecker nextAligned nextWF pushed.reserved
        different (sameEnv ▸ constants) (sameEnv ▸ definitions)
        (by simpa [first] using parameterCount) nextParameters normalizedTranslated sortedCall
    have finalModelWF : finalChecker.mlctx.WF checker.venv checker.lparams := by
      simpa only [finalEnv, finalUniverses, sameEnv, sameUniverses] using finalChecker.mlctx_wf
    have parameterTranslated : TrExprS checker.venv checker.lparams nextChecker.vlctx
        (.fvar ⟨reader.ngen.curr⟩) (.bvar 0) := by
      simp only [TypeChecker.VContext.vlctx, nextModel, MLCtx.vlctx]
      exact .fvar (A := peeled.lift) (by simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type])
    have parameterTyped : checker.venv.HasType checker.lparams.length nextChecker.vlctx.toCtx
        (.bvar 0) domainSemantic.lift := by
      rw [TypeChecker.VContext.vlctx, nextModel, MLCtx.vlctx, VLCtx.toCtx]
      exact (domainEquality.weak checker.Ewf.ordered (B := peeled)).symm.defeq (.bvar .zero)
    have resultEquality : checker.venv.IsDefEqU checker.lparams.length nextChecker.vlctx.toCtx
        normalizedSemantic bodySemantic := by
      simpa only [sameEnv, sameUniverses] using
        normalizedEquality.trans nextChecker.Ewf nextChecker.Δwf.toCtx bodyEquality
    have firstArgument : TypedParameterApplications checker.venv checker.lparams nextChecker.mlctx
        semantic.lift [.fvar ⟨reader.ngen.curr⟩] [.bvar 0] normalizedSemantic := by
      rw [sourceShape]
      refine .cons parameterTranslated parameterTyped ?_
      simpa only [VExpr.lift, VExpr.liftN, VExpr.instN_bvar0] using
        TypedParameterApplications.convertInput resultEquality.symm
          (TypedParameterApplications.nil (result := normalizedSemantic))
    have firstArgument := firstArgument.weakFV checker.Ewf finalModelWF history.insertion
    have arguments : TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (normalizedSemantic.liftN identifiers.length) (finalStats.params.toList.drop (index + 1)) values result := by
      simpa only [sameEnv, sameUniverses] using arguments
    have firstArgument : TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN (1 + identifiers.length)) [.fvar ⟨reader.ngen.curr⟩]
        ([.bvar 0].map (VExpr.lift' · (.skipN .refl identifiers.length)))
        (normalizedSemantic.liftN identifiers.length) := by
      simpa only [liftedSkip, VExpr.liftN_liftN, VExpr.lift] using firstArgument
    obtain ⟨more, appended⟩ := tail.paramsAppend
    have size : stats.params.toList.length = index := by
      simpa only [Array.length_toList, first, if_true] using parameterCount
    have drop : finalStats.params.toList.drop index = .fvar ⟨reader.ngen.curr⟩ ::
        finalStats.params.toList.drop (index + 1) := by
      rw [appended, Array.toList_push]
      simp [List.drop_append, size]
    exact ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, _, result, finalEnv.trans sameEnv,
      finalUniverses.trans sameUniverses, finalAligned, finalWF,
      by simpa only [List.singleton_append] using head.trans history, finalParameters,
      by simpa only [List.length_cons, Nat.add_comm, drop, List.singleton_append]
        using firstArgument.append arguments,
      by simpa only [sameEnv, sameUniverses] using resultKind⟩
  | @reusedParameter stats name domain body binder index nindices reader stored normalized terminal finalStats
      finalIndices finalReader selected notFirst storedCall equalCall normalizedCall tail induction =>
    have bound : index < stats.params.size := by simpa only [parameterCount, if_neg notFirst] using selected
    have member : stats.params[index]! ∈ stats.params := by
      simpa only [getElem!_pos stats.params index bound] using Array.getElem_mem bound
    obtain ⟨identifier, equation, present⟩ := parameters _ member
    obtain ⟨declaration, lookup⟩ := checker.trlctx.find?_eq_some.mpr present
    have lookup : reader.lctx.find? identifier = some declaration := by
      simpa only [checker.lctx_eq, congrArg TypeChecker.Context.lctx aligned] using lookup
    obtain ⟨domainSemantic, bodySemantic, argumentSemantic, sourceShape, argumentTranslated,
      argumentTyped, opened, openedTyped⟩ := translatedReusedHeaderParameterArgument checker reader
        aligned initialWF lookup translated (by simpa only [equation] using storedCall) equalCall
    obtain ⟨normalizedSemantic, normalizedTranslated, normalizedEquality⟩ := acceptedHeaderNormalization
      checker reader aligned initialWF (opened.trExpr checker.Ewf.ordered checker.Δwf)
      (by simpa only [equation] using normalizedCall)
    obtain ⟨finalChecker, identifiers, values, result, finalEnv, finalUniverses, finalAligned, finalWF,
      history, finalParameters, arguments, resultKind⟩ := induction checker aligned initialWF reserved different
        constants definitions (by simpa only [if_neg notFirst] using parameterCount)
        parameters normalizedTranslated sortedCall
    have finalModelWF : finalChecker.mlctx.WF checker.venv checker.lparams := by
      simpa only [finalEnv, finalUniverses] using finalChecker.mlctx_wf
    have firstArgument : TypedParameterApplications checker.venv checker.lparams checker.mlctx
        semantic [stats.params[index]!] [argumentSemantic] normalizedSemantic := by
      rw [sourceShape]
      exact .cons (by simpa only [equation] using argumentTranslated) argumentTyped
        (.convertInput normalizedEquality.symm .nil)
    have firstArgument := firstArgument.weakFV checker.Ewf finalModelWF history.insertion
    have firstArgument : TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN identifiers.length) [stats.params[index]!]
        ([argumentSemantic].map (VExpr.lift' · (.skipN .refl identifiers.length)))
        (normalizedSemantic.liftN identifiers.length) := by
      simpa only [liftedSkip] using firstArgument
    have unchanged := tail.paramsUnchanged notFirst
    have drop : finalStats.params.toList.drop index = stats.params[index]! ::
        finalStats.params.toList.drop (index + 1) := by
      rw [unchanged, List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using bound)]
      simp only [← Array.getElem_toList, getElem!_pos stats.params index bound]
    exact ⟨finalChecker, identifiers, _, result, finalEnv, finalUniverses, finalAligned, finalWF,
      history, finalParameters, by simpa only [drop, List.singleton_append] using firstArgument.append arguments, resultKind⟩
  | @index stats name domain body binder index nindices reader normalized terminal finalStats finalIndices
      finalReader notParameter normalizedCall tail induction =>
    have trace : CheckedHeaderTrace nparams stats (.forallE name domain body binder) index nindices reader
        terminal finalStats finalIndices finalReader := .index notParameter normalizedCall tail
    obtain ⟨finalChecker, identifiers, finalEnv, finalUniverses, finalAligned, finalWF, history,
      finalParameters, _⟩ := trace.checkerModels checker aligned initialWF reserved different constants definitions
        parameterCount parameters ⟨semantic, translated⟩
    have unchanged := trace.paramsAfterParameters (Nat.le_of_not_gt notParameter)
    have bound : stats.params.size ≤ index := by rw [parameterCount]; split <;> omega
    have empty : finalStats.params.toList.drop index = [] := by
      rw [unchanged]
      exact List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using bound)
    have kind := (trace.withoutParameters (Nat.le_of_not_gt notParameter)).zeroParameterKind
      checker aligned initialWF reserved different constants definitions translated sortedCall
    have lifted := kind.weakN checker.Ewf.ordered (Ctx.liftN_iff_lift'.mpr history.insertion.toCtx)
    exact ⟨finalChecker, identifiers, [], semantic.liftN identifiers.length, finalEnv, finalUniverses,
      finalAligned, finalWF, history, finalParameters, by rw [empty]; exact .nil, lifted⟩

theorem CheckedHeaderTrace.parameterApplications
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal sorted : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    {semantic : VExpr} (translated : checker.TrExprS source semantic)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId)
      (values : List VExpr) (result : VExpr),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN identifiers.length) (finalStats.params.toList.drop index) values result := by
  obtain ⟨finalChecker, identifiers, values, result, sameEnv, sameUniverses, finalAligned, finalWF,
    history, finalParameters, arguments, _⟩ := trace.parameterApplicationsWithKind checker aligned initialWF
      reserved different constants definitions parameterCount parameters translated sortedCall
  exact ⟨finalChecker, identifiers, values, result, sameEnv, sameUniverses, finalAligned, finalWF,
    history, finalParameters, arguments⟩

structure HeaderParameterApplicationInput (environment : VEnv) (universes : List Name)
    (model : MLCtx) (stats : InductiveStats) (source : Expr) where
  semantic : VExpr
  sourceTranslated : TrExprS environment universes model.vlctx source semantic
  values : List VExpr
  result : VExpr
  arguments : TypedParameterApplications environment universes model semantic stats.params.toList values result

def HeaderParameterApplicationInput.withStats
    (input : HeaderParameterApplicationInput environment universes model stats source)
    (parameters : targetStats.params = stats.params) :
    HeaderParameterApplicationInput environment universes model targetStats source :=
  ⟨input.semantic, input.sourceTranslated, input.values, input.result,
    by simpa only [parameters] using input.arguments⟩

def HeaderParameterApplicationInput.monoEnv
    (input : HeaderParameterApplicationInput environment universes model stats source)
    (increase : environment ≤ extended) :
    HeaderParameterApplicationInput extended universes model stats source :=
  ⟨input.semantic, input.sourceTranslated.mono increase, input.values, input.result,
    input.arguments.monoEnv increase⟩

def HeaderParameterApplicationInput.weakFV
    (input : HeaderParameterApplicationInput environment universes model stats source)
    (environmentWF : environment.WF) (targetWF : target.WF environment universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    HeaderParameterApplicationInput environment universes target stats source :=
  ⟨input.semantic.lift' lift,
    input.sourceTranslated.weakFV' environmentWF.ordered insertion targetWF.tr.wf,
    input.values.map (VExpr.lift' · lift), input.result.lift' lift,
    input.arguments.weakFV environmentWF targetWF insertion⟩

theorem HeaderParameterApplicationInput.application
    (input : HeaderParameterApplicationInput environment universes model stats source)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (headTranslated : TrExprS environment universes model.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length model.vlctx.toCtx headSemantic input.semantic) :
    ∃ value, TrExprS environment universes model.vlctx (mkAppN head stats.params) value ∧
      environment.HasType universes.length model.vlctx.toCtx value input.result := by
  obtain ⟨translated, typed⟩ := input.arguments.apply environmentWF modelWF headTranslated headTyped
  exact ⟨_, by simpa only [mkAppN, ← Array.foldl_toList, Expr.mkAppList_eq_foldl,
    show mkApp = Expr.app from rfl] using translated, typed⟩

structure HeaderParameterApplicationReceipt (initial : TypeChecker.VContext)
    (stats : InductiveStats) (reader : Context) (source : Expr) where
  checker : TypeChecker.VContext
  sameEnv : checker.venv = initial.venv
  sameUniverses : checker.lparams = initial.lparams
  aligned : HeaderCheckerAligned checker reader
  stateWF : ({} : TypeChecker.VState).WF checker
  identifiers : List FVarId
  history : ParameterPrefix initial.mlctx checker.mlctx identifiers
  input : HeaderParameterApplicationInput initial.venv initial.lparams checker.mlctx stats source
  indexArity : Nat
  resultKind : initial.venv.SortArity initial.lparams.length checker.vlctx.toCtx indexArity input.result

theorem HeaderParameterApplicationReceipt.modelWF
    (receipt : HeaderParameterApplicationReceipt initial stats reader source) :
    receipt.checker.mlctx.WF initial.venv initial.lparams := by
  simpa only [receipt.sameEnv, receipt.sameUniverses] using receipt.checker.mlctx_wf

theorem CheckedHeaderTrace.parameterApplicationsFromSourceWithKind
    {nparams finalIndices : Nat} {stats finalStats : InductiveStats}
    {source normalized inferred terminal sorted : Expr} {name : Name} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats normalized 0 0 reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ receipt : HeaderParameterApplicationReceipt checker finalStats finalReader source,
      receipt.indexArity = finalIndices := by
  have free := checkNoMVarNoFVar.WF reader.env name source () guarded
  obtain ⟨semantic, translated⟩ := acceptedSourceTranslation checker reader aligned initialWF
    (free.mono fun _ impossible => impossible.elim) checked
  obtain ⟨normalizedSemantic, normalizedTranslated, equality⟩ := acceptedHeaderNormalization checker reader
    aligned initialWF (translated.trExpr checker.Ewf.ordered checker.Δwf) normalization
  obtain ⟨finalChecker, identifiers, values, result, sameEnv, sameUniverses, finalAligned, stateWF,
    history, _, arguments, resultKind⟩ := trace.parameterApplicationsWithKind checker aligned initialWF reserved different
      constants definitions parameterCount parameters normalizedTranslated sortedCall
  have finalModelWF : finalChecker.mlctx.WF checker.venv checker.lparams := by
    simpa only [sameEnv, sameUniverses] using finalChecker.mlctx_wf
  have sourceTranslated := translated.weakFV' checker.Ewf.ordered history.insertion finalModelWF.tr.wf
  have sourceEquality : checker.venv.IsDefEqU checker.lparams.length finalChecker.mlctx.vlctx.toCtx
      (semantic.liftN identifiers.length) (normalizedSemantic.liftN identifiers.length) := by
    simpa only [VExpr.lift'_consN_skipN] using
      equality.symm.weak' checker.Ewf.ordered history.insertion.toCtx
  exact ⟨{
    checker := finalChecker, sameEnv, sameUniverses, aligned := finalAligned, stateWF, identifiers, history,
    input := ⟨semantic.liftN identifiers.length,
      by simpa only [VExpr.lift'_consN_skipN] using sourceTranslated,
      values, result, by
        simpa only [List.drop_zero, liftedSkip] using
          TypedParameterApplications.convertInput sourceEquality arguments⟩,
    indexArity := finalIndices, resultKind := by simpa only [Nat.sub_zero] using resultKind }, rfl⟩

theorem CheckedHeaderTrace.parameterApplicationsFromSource
    {nparams finalIndices : Nat} {stats finalStats : InductiveStats}
    {source normalized inferred terminal sorted : Expr} {name : Name} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats normalized 0 0 reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    Nonempty (HeaderParameterApplicationReceipt checker finalStats finalReader source) := by
  obtain ⟨receipt, _⟩ := trace.parameterApplicationsFromSourceWithKind checker aligned initialWF reserved different
    constants definitions parameterCount parameters guarded checked normalization sortedCall
  exact ⟨receipt⟩

theorem checkInductiveTypes.loopInd.loop.withParameterApplications {resultType : Type}
    (nparams fuel : Nat) (stats : InductiveStats) (name : Name) (source normalized inferred : Expr)
    (next : Expr → InductiveStats → Nat → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (nextWF : ∀ terminal finalStats finalIndices current,
      HeaderParameterApplicationReceipt checker finalStats current source →
      reader.RecursorScopeFrame current → (next terminal finalStats finalIndices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats normalized 0 0 fuel (fun terminal finalStats finalIndices => do
      let _ ← (monadLift (TypeChecker.ensureSort terminal) : M Expr)
      next terminal finalStats finalIndices) reader).WF post := by
  have native : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  apply checkInductiveTypes.loopInd.loop.scopedTrace nparams fuel stats normalized 0 0 _ reader post
    (native ▸ checker.trlctx.1) reserved
  intro terminal finalStats finalIndices current trace frame
  apply bindHeaderResultWF
  intro sorted sortedCall
  obtain ⟨receipt⟩ := trace.parameterApplicationsFromSource checker aligned initialWF reserved different
    constants definitions parameterCount parameters guarded checked normalization sortedCall
  exact nextWF terminal finalStats finalIndices current receipt frame

end Lean4Lean.AddInductive
