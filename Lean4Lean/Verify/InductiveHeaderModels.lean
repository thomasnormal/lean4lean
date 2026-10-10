import Lean4Lean.Verify.InductiveAnnotationDomainPeeling
import Lean4Lean.Verify.InductiveIndexContextTranslation
import Lean4Lean.Verify.InductiveHeaderTraces
import Lean4Lean.Verify.InductiveConstructorPrefixReceipts

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem ParameterPrefix.trans (first : ParameterPrefix base middle identifiers)
    (second : ParameterPrefix middle target more) :
    ParameterPrefix base target (identifiers ++ more) := by
  induction second with
  | nil => simpa only [List.append_nil] using first
  | snoc _ induction => simpa only [List.append_assoc] using ParameterPrefix.snoc induction

theorem ParameterPrefix.splitAt (parameters : ParameterPrefix base target identifiers) (count : Nat) :
    ∃ middle, ParameterPrefix base middle (identifiers.take count) ∧
      ParameterPrefix middle target (identifiers.drop count) := by
  induction parameters with
  | nil =>
    refine ⟨base, ?_, ?_⟩ <;>
      simpa only [List.take_nil, List.drop_nil] using (ParameterPrefix.nil (base := base))
  | @snoc previous identifiers identifier name nativeDomain domain binder parameters induction =>
    by_cases within : count ≤ identifiers.length
    · obtain ⟨middle, before, after⟩ := induction
      refine ⟨middle, ?_, ?_⟩
      · simpa only [List.take_append_of_le_length within] using before
      · simpa only [List.drop_append_of_le_length within] using ParameterPrefix.snoc after
    · have entire : (identifiers ++ [identifier]).length ≤ count := by
        simp only [List.length_append, List.length_singleton]
        omega
      refine ⟨MLCtx.vlam identifier name nativeDomain domain binder previous, ?_, ?_⟩
      · simpa only [List.take_of_length_le entire] using ParameterPrefix.snoc parameters
      · simpa only [List.drop_eq_nil_of_le entire] using
          (ParameterPrefix.nil (base := MLCtx.vlam identifier name nativeDomain domain binder previous))

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

theorem VState.WF.reset (checker : VContext)
    (reserved : ∀ id ∈ checker.vlctx.fvars, ({} : VState).ngen.Reserves id) :
    ({} : VState).WF checker where
  trctx := checker.trlctx
  ngen_wf := reserved
  ectx := ⟨checker.vlctx, .refl, checker.Δwf, .refl, .empty, reserved⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

end Lean4Lean.TypeChecker

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix ContextReserved)
open private readWF from Lean4Lean.Verify.InductiveStats
open private bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

def HeaderCheckerAligned (checker : TypeChecker.VContext) (reader : Context) : Prop :=
  checker.toContext =
    { env := reader.env, lctx := reader.lctx, safety := reader.safety,
      lparams := reader.lparams, fuel := reader.fuel }

def FirstHeaderCheckerModels (checker : TypeChecker.VContext) (nparams nindices : Nat)
    (params : Array Expr) (reader : Context) (terminal : Expr) : Prop :=
  ∃ (parameterModel : MLCtx) (finalChecker : TypeChecker.VContext)
    (parameters indices : List FVarId),
    finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
    HeaderCheckerAligned finalChecker reader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
    ParameterPrefix checker.mlctx parameterModel parameters ∧
    ParameterPrefix parameterModel finalChecker.mlctx indices ∧
    params.toList = parameters.map Expr.fvar ∧ parameters.length = nparams ∧ indices.length = nindices ∧
    parameterModel.WF checker.venv checker.lparams ∧
    ∃ semantic, finalChecker.TrExprS terminal semantic

theorem acceptedHeaderNormalization
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {source normalized : Expr} {semantic : VExpr}
    (translated : checker.TrExpr source semantic)
    (accepted : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized) :
    checker.TrExpr normalized semantic := by
  obtain ⟨strictSemantic, strictTranslated, equality⟩ := translated
  have nativeAccepted : (Prod.fst <$> TypeChecker.whnf source
      checker.toContext ({} : TypeChecker.VState).toState) = .ok normalized := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.whnf source
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨result, final⟩ := returned
    change Except.ok result = .ok normalized at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, normalizedSemantic, normalizedTranslated, normalizedEquality⟩ :=
      TypeChecker.whnf.WF strictTranslated initialWF normalized final checked
    exact ⟨normalizedSemantic, normalizedTranslated,
      normalizedEquality.trans checker.Ewf checker.Δwf.toCtx equality⟩

theorem translatedHeaderContext
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    {name : Name} {domain body normalized : Expr} {binder : BinderInfo} {semantic : VExpr}
    (translated : checker.TrExprS (.forallE name domain body binder) semantic)
    (accepted : (monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))) : M Expr)
      (recursorIndexContext reader name binder (peelTypeAnnotations domain)) = .ok normalized) :
    ∃ (peeled : VExpr) (nextChecker : TypeChecker.VContext),
      nextChecker.venv = checker.venv ∧ nextChecker.lparams = checker.lparams ∧
      nextChecker.mlctx = .vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled binder checker.mlctx ∧
      HeaderCheckerAligned nextChecker (recursorIndexContext reader name binder (peelTypeAnnotations domain)) ∧
      ({} : TypeChecker.VState).WF nextChecker ∧
      ∃ nextSemantic, nextChecker.TrExprS normalized nextSemantic := by
  cases translated with
  | forallE domainIsType _ domainTranslated bodyTranslated =>
    rename_i semanticDomain bodySemantic bodyIsType
    obtain ⟨level, domainTyped⟩ := domainIsType
    obtain ⟨peeled, peeledTranslated, equality, _, convertedBody⟩ :=
      domainTranslated.peeledAnonymousBodyTranslation checker.Ewf checker.Δwf constants definitions
        domainTyped bodyTranslated
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have absent : checker.mlctx.lctx.find? ⟨reader.ngen.curr⟩ = none := by
      rw [native]
      exact reserved.fresh (native ▸ checker.trlctx.1)
    let nextModel := MLCtx.vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled binder checker.mlctx
    have nextWF : nextModel.WF checker.venv checker.lparams :=
      ⟨checker.mlctx_wf, absent, peeledTranslated, level, equality.hasType.2⟩
    let nextChecker := checker.withMLC nextModel (wf := ⟨nextWF⟩)
    have nextAligned : HeaderCheckerAligned nextChecker
        (recursorIndexContext reader name binder (peelTypeAnnotations domain)) := by
      change { checker.toContext with lctx := nextModel.lctx } = _
      rw [aligned]
      simp only [nextModel, MLCtx.lctx, native, recursorIndexContext]
    have nextReserved : ∀ id ∈ nextChecker.vlctx.fvars, ({} : TypeChecker.VState).ngen.Reserves id := by
      change ∀ id ∈ (⟨reader.ngen.curr⟩ :: checker.vlctx.fvars), ({} : TypeChecker.VState).ngen.Reserves id
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨?_, initialWF.ngen_wf⟩
      intro index same
      have prefixes : reader.ngen.namePrefix = ({} : TypeChecker.VState).ngen.namePrefix :=
        (Name.num.inj (FVarId.mk.inj same)).1
      exact False.elim (different prefixes.symm)
    have nextStateWF := TypeChecker.VState.WF.reset nextChecker nextReserved
    have openedBody : nextChecker.TrExpr
        (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) bodySemantic := by
      rw [Expr.instantiate1_eq]
      exact convertedBody.openFreshFVar checker.Ewf.ordered nextWF.tr.wf
    obtain ⟨nextSemantic, nextTranslated, _⟩ :=
      acceptedHeaderNormalization nextChecker _ nextAligned nextStateWF openedBody accepted
    exact ⟨peeled, nextChecker, rfl, rfl, rfl, nextAligned, nextStateWF, nextSemantic, nextTranslated⟩

theorem CheckedHeaderTrace.firstModels
    {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (first : stats.indConsts.isEmpty = true)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (translated : ∃ semantic, checker.TrExprS type semantic) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      identifiers.length = (nparams - index) + (finalIndices - nindices) ∧
      finalStats.params.toList = stats.params.toList ++ (identifiers.take (nparams - index)).map Expr.fvar ∧
      ∃ semantic, finalChecker.TrExprS terminal semantic := by
  induction trace generalizing checker with
  | stop notBinder complete =>
    refine ⟨checker, [], rfl, rfl, aligned, initialWF, .nil, ?_, ?_, translated⟩
    · simp only [List.length_nil, complete, Nat.sub_self, Nat.add_zero]
    · simp only [List.take_nil, List.map_nil, List.append_nil]
  | @freshParameter stats name domain body binder index nindices reader normalized terminal finalStats finalIndices
      finalReader parameter firstHeader normalizedCall tail induction =>
    obtain ⟨semantic, sourceTranslated⟩ := translated
    obtain ⟨peeled, nextChecker, sameEnv, sameUniverses, nextModel, nextAligned, nextWF, nextTranslated⟩ :=
      translatedHeaderContext checker reader aligned initialWF reserved different constants definitions
        sourceTranslated normalizedCall
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    obtain ⟨finalChecker, identifiers, finalEnv, finalUniverses, finalAligned, finalWF, history,
      count, parameters, terminalTranslated⟩ := induction nextChecker nextAligned nextWF pushed.reserved
        different first (sameEnv ▸ constants) (sameEnv ▸ definitions) nextTranslated
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [nextModel]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have remaining : nparams - index = (nparams - (index + 1)) + 1 := by omega
    refine ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, finalEnv.trans sameEnv,
      finalUniverses.trans sameUniverses, finalAligned, finalWF, ?_, ?_, ?_, terminalTranslated⟩
    · simpa only [List.singleton_append] using head.trans history
    · simp only [List.length_cons]
      omega
    · rw [remaining]
      simpa only [List.take_succ_cons, List.map_cons, Array.toList_push, List.append_assoc,
        List.singleton_append] using parameters
  | reusedParameter parameter notFirst stored equal normalizedCall tail induction =>
    exact False.elim (notFirst first)
  | @index stats name domain body binder index nindices reader normalized terminal finalStats finalIndices
      finalReader notParameter normalizedCall tail induction =>
    obtain ⟨semantic, sourceTranslated⟩ := translated
    obtain ⟨peeled, nextChecker, sameEnv, sameUniverses, nextModel, nextAligned, nextWF, nextTranslated⟩ :=
      translatedHeaderContext checker reader aligned initialWF reserved different constants definitions
        sourceTranslated normalizedCall
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    obtain ⟨finalChecker, identifiers, finalEnv, finalUniverses, finalAligned, finalWF, history,
      count, parameters, terminalTranslated⟩ := induction nextChecker nextAligned nextWF pushed.reserved
        different first (sameEnv ▸ constants) (sameEnv ▸ definitions) nextTranslated
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [nextModel]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have zero : nparams - index = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt notParameter)
    have bounds := tail.countBounds
    refine ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, finalEnv.trans sameEnv,
      finalUniverses.trans sameUniverses, finalAligned, finalWF, ?_, ?_, ?_, terminalTranslated⟩
    · simpa only [List.singleton_append] using head.trans history
    · simp only [List.length_cons]
      omega
    · simpa only [zero, List.take_zero, List.map_nil, List.append_nil] using parameters

theorem CheckedHeaderTrace.firstModelFromSource
    {nparams : Nat} {stats finalStats : InductiveStats} {source inferred normalized terminal : Expr}
    {finalIndices : Nat} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats normalized 0 0 reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (first : stats.indConsts.isEmpty = true) (initialParams : stats.params = #[])
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    {declarationName : Name}
    (guarded : reader.env.checkNoMVarNoFVar declarationName source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalizedCall : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized) :
    FirstHeaderCheckerModels checker nparams finalIndices finalStats.params finalReader terminal := by
  have supported := checkNoMVarNoFVar.WF reader.env declarationName source () guarded
  obtain ⟨sourceSemantic, sourceTranslated⟩ := acceptedSourceTranslation checker reader aligned initialWF
    (supported.mono fun _ impossible => impossible.elim) checked
  obtain ⟨normalizedSemantic, normalizedTranslated, _⟩ :=
    acceptedHeaderNormalization checker reader aligned initialWF
      (sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalizedCall
  obtain ⟨finalChecker, identifiers, sameEnv, sameUniverses, finalAligned, finalWF, history,
    count, parameters, terminalTranslated⟩ := trace.firstModels checker aligned initialWF reserved different
      first constants definitions ⟨normalizedSemantic, normalizedTranslated⟩
  obtain ⟨parameterModel, parameterHistory, indexHistory⟩ := history.splitAt nparams
  have bound : nparams ≤ identifiers.length := by omega
  have parameterWF := indexHistory.baseWF finalChecker.mlctx_wf
  refine ⟨parameterModel, finalChecker, identifiers.take nparams, identifiers.drop nparams,
    sameEnv, sameUniverses, finalAligned, finalWF, parameterHistory, indexHistory, ?_, ?_, ?_, ?_,
    terminalTranslated⟩
  · simpa only [Nat.sub_zero, initialParams, Array.toList_empty, List.nil_append] using parameters
  · simp only [List.length_take, Nat.min_eq_left bound]
  · simp only [List.length_drop]
    omega
  · simpa only [sameEnv, sameUniverses] using parameterWF

theorem checkInductiveTypes.firstModels (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M ResultType) (reader : Context)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (nonempty : 0 < types.size) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∃ normalized terminal finalStats count current,
        (monadLift (TypeChecker.whnf types[0]!.type) : M Expr) reader = .ok normalized ∧
        CheckedHeaderTrace nparams { (default : InductiveStats) with levels := reader.lparams.map Level.param }
          normalized 0 0 reader terminal finalStats count current ∧
        FirstHeaderCheckerModels checker nparams count finalStats.params current terminal := by
  unfold checkInductiveTypes
  apply readWF
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i bound
    apply readWF
    apply bindHeaderResultWF
    intro checkedUnit guardCall
    cases checkedUnit
    apply bindHeaderResultWF
    intro inferred sourceCall
    apply readWF
    apply bindHeaderResultWF
    intro normalized normalizedCall
    apply checkInductiveTypes.loopInd.loop.scopedTrace
    · have native : checker.mlctx.lctx = reader.lctx :=
        checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
      exact native ▸ checker.trlctx.1
    · exact reserved
    intro terminal finalStats count current trace frame
    have guardCall : reader.env.checkNoMVarNoFVar types[0]!.name types[0]!.type = .ok () := by
      simpa only [getElem!_pos types 0 bound] using guardCall
    have sourceCall : (monadLift (TypeChecker.checkType types[0]!.type) : M Expr) reader = .ok inferred := by
      simpa only [getElem!_pos types 0 bound] using sourceCall
    have normalizedCall : (monadLift (TypeChecker.whnf types[0]!.type) : M Expr) reader = .ok normalized := by
      simpa only [getElem!_pos types 0 bound] using normalizedCall
    have models := trace.firstModelFromSource checker aligned initialWF reserved different rfl rfl
      constants definitions guardCall sourceCall normalizedCall
    exact fun _ _ => ⟨normalized, terminal, finalStats, count, current, normalizedCall, trace, models⟩
  · rename_i empty
    exact False.elim (empty nonempty)

theorem FirstHeaderCheckerModels.selectedParameterDomain
    {checker : TypeChecker.VContext} {nparams nindices : Nat} {params : Array Expr}
    {reader : Context} {terminal : Expr}
    (models : FirstHeaderCheckerModels checker nparams nindices params reader terminal)
    {index : Nat} {identifier : FVarId} (selected : params[index]? = some (.fvar identifier)) :
    ∃ (parameters : List FVarId) (smaller : MLCtx) (nativeDomain : Expr) (semanticDomain : VExpr),
      params.toList = parameters.map Expr.fvar ∧
      ParameterPrefix checker.mlctx smaller (parameters.take index) ∧
      smaller.WF checker.venv checker.lparams ∧
      TrExprS checker.venv checker.lparams smaller.vlctx nativeDomain semanticDomain ∧
      checker.venv.IsType checker.lparams.length smaller.vlctx.toCtx semanticDomain ∧
      ∃ declaration, reader.lctx.find? identifier = some declaration ∧ declaration.type = nativeDomain := by
  obtain ⟨parameterModel, finalChecker, parameters, indices, sameEnv, sameUniverses,
    finalAligned, _, parameterHistory, indexHistory, paramsEq, _, _, parameterWF, _⟩ := models
  have paramsArray : params = (parameters.map Expr.fvar).toArray :=
    Array.toList_inj.mp (by simpa only [List.toList_toArray] using paramsEq)
  rw [paramsArray] at selected
  simp only [List.getElem?_toArray, List.getElem?_map] at selected
  have selectedId : parameters[index]? = some identifier := by
    cases picked : parameters[index]? with
    | none => simp only [picked, Option.map_none, reduceCtorEq] at selected
    | some pickedId =>
      rw [picked] at selected
      have same := Expr.fvar.inj (Option.some.inj selected)
      exact congrArg some same
  obtain ⟨smaller, nativeDomain, semanticDomain, insertion, history, smallerWF, weakening,
    domainTranslated, domainTyped, declaration, lookup, domainEq⟩ :=
      parameterHistory.selectedDomain parameterWF selectedId
  have native : finalChecker.mlctx.lctx = reader.lctx :=
    finalChecker.lctx_eq.trans (congrArg TypeChecker.Context.lctx finalAligned)
  have finalWF : finalChecker.mlctx.WF checker.venv checker.lparams := by
    simpa only [sameEnv, sameUniverses] using finalChecker.mlctx_wf
  exact ⟨parameters, smaller, nativeDomain, semanticDomain, paramsEq, history, smallerWF,
    domainTranslated, domainTyped, declaration,
    native ▸ indexHistory.retainsLookup finalWF lookup, domainEq⟩

end Lean4Lean.AddInductive
