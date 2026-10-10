import Lean4Lean.Verify.InductiveHeaderTyping
import Lean4Lean.Verify.InductiveParameterPrefixTyping
import Lean4Lean.Verify.InductiveIndexDomainStrengthening

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix ContextReserved)
open private Lean4Lean.AddInductive.readWF Lean4Lean.AddInductive.bindWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

def HeaderParameterModels (stats : InductiveStats) (context : VLCtx) : Prop :=
  ∀ parameter ∈ stats.params, ∃ identifier, parameter = Expr.fvar identifier ∧ identifier ∈ context.fvars

theorem HeaderParameterModels.mono (models : HeaderParameterModels stats source)
    (support : source.fvars ⊆ target.fvars) : HeaderParameterModels stats target := by
  intro parameter member
  obtain ⟨identifier, equation, present⟩ := models parameter member
  exact ⟨identifier, equation, support present⟩

theorem HeaderParameterModels.push (models : HeaderParameterModels stats context)
    (identifier : FVarId) (present : identifier ∈ context.fvars) :
    HeaderParameterModels { stats with params := stats.params.push (.fvar identifier) } context := by
  intro parameter member
  rcases Array.mem_push.mp member with member | rfl
  · exact models parameter member
  · exact ⟨identifier, rfl, present⟩

theorem acceptedHeaderParameterEquality (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {candidate stored : Expr} {candidateSemantic storedSemantic : VExpr}
    (candidateTranslated : checker.TrExprS candidate candidateSemantic)
    (storedTranslated : checker.TrExprS stored storedSemantic)
    (accepted : (monadLift (TypeChecker.isDefEq candidate stored) : M Bool) reader = .ok true) :
    checker.IsDefEqU candidateSemantic storedSemantic := by
  have nativeAccepted : (Prod.fst <$> TypeChecker.isDefEq candidate stored
      checker.toContext ({} : TypeChecker.VState).toState) = .ok true := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.isDefEq candidate stored
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨result, final⟩ := returned
    change Except.ok result = .ok true at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, equal⟩ :=
      TypeChecker.isDefEq.WF candidateTranslated storedTranslated initialWF true final checked
    exact equal rfl

theorem translatedReusedHeaderParameter (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {identifier : FVarId} {declaration : LocalDecl} {name : Name} {domain body stored normalized : Expr}
    {binder : BinderInfo} {semantic : VExpr}
    (lookup : reader.lctx.find? identifier = some declaration)
    (translated : checker.TrExprS (.forallE name domain body binder) semantic)
    (storedCall : getType (.fvar identifier) reader = .ok stored)
    (equalCall : (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true)
    (normalizedCall : (monadLift (TypeChecker.whnf (body.instantiate1 (.fvar identifier))) : M Expr)
      reader = .ok normalized) :
    ∃ result, checker.TrExprS normalized result := by
  have inferred : TypeChecker.Inner.inferFVar checker.toContext identifier = .ok stored := by
    rw [aligned, ← getType_fvar_eq_inferFVar reader identifier declaration lookup]
    exact storedCall
  obtain ⟨parameterSemantic, storedSemantic, _, parameterTranslated, storedTranslated, parameterTyped⟩ :=
    TypeChecker.Inner.inferFVar.WF (c := checker) stored inferred
  cases translated with
  | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
    rename_i domainSemantic bodySemantic
    have equal := acceptedHeaderParameterEquality checker reader aligned initialWF
      domainTranslated storedTranslated equalCall
    have typed := parameterTyped.defeqU_r checker.Ewf checker.Δwf.toCtx equal.symm
    have opened := TrExprS.inst checker.Ewf.ordered typed bodyTranslated parameterTranslated
    have opened : checker.TrExprS (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst parameterSemantic) := by
      simpa only [Expr.instantiate1_eq] using opened
    obtain ⟨result, resultTranslated, _⟩ := acceptedHeaderNormalization checker reader aligned initialWF
      (opened.trExpr checker.Ewf.ordered checker.Δwf) normalizedCall
    exact ⟨result, resultTranslated⟩

theorem CheckedHeaderTrace.checkerModels
    {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (translated : ∃ semantic, checker.TrExprS type semantic) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      ∃ semantic, finalChecker.TrExprS terminal semantic := by
  induction trace generalizing checker with
  | stop notBinder complete =>
    exact ⟨checker, [], rfl, rfl, aligned, initialWF, .nil, parameters, translated⟩
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
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [nextModel]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have nextParameters := (parameters.mono head.insertion.fvars_sublist.subset).push
      ⟨reader.ngen.curr⟩ (by rw [head.fvars]; simp)
    obtain ⟨finalChecker, identifiers, finalEnv, finalUniverses, finalAligned, finalWF, history,
      finalParameters, terminalTranslated⟩ := induction nextChecker nextAligned nextWF pushed.reserved
        different (sameEnv ▸ constants) (sameEnv ▸ definitions)
        (by simpa [firstHeader] using parameterCount) nextParameters nextTranslated
    exact ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, finalEnv.trans sameEnv,
      finalUniverses.trans sameUniverses, finalAligned, finalWF,
      by simpa only [List.singleton_append] using head.trans history, finalParameters, terminalTranslated⟩
  | @reusedParameter stats name domain body binder index nindices reader stored normalized terminal finalStats
      finalIndices finalReader parameter notFirst storedCall equalCall normalizedCall tail induction =>
    have bound : index < stats.params.size := by
      rw [parameterCount]
      simpa only [notFirst, if_false] using parameter
    have member : stats.params[index]! ∈ stats.params := by
      rw [getElem!_pos stats.params index bound]
      exact Array.getElem_mem bound
    obtain ⟨identifier, equation, present⟩ := parameters _ member
    obtain ⟨declaration, lookup⟩ := checker.trlctx.find?_eq_some.mpr present
    have lookup : reader.lctx.find? identifier = some declaration := by
      simpa only [checker.lctx_eq, congrArg TypeChecker.Context.lctx aligned] using lookup
    obtain ⟨semantic, sourceTranslated⟩ := translated
    have opened := translatedReusedHeaderParameter checker reader aligned initialWF lookup sourceTranslated
      (by simpa only [equation] using storedCall) equalCall
      (by simpa only [equation] using normalizedCall)
    exact induction checker aligned initialWF reserved different constants definitions
      (by simpa only [notFirst, if_false] using parameterCount) parameters opened
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
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [nextModel]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    obtain ⟨finalChecker, identifiers, finalEnv, finalUniverses, finalAligned, finalWF, history,
      finalParameters, terminalTranslated⟩ := induction nextChecker nextAligned nextWF pushed.reserved
        different (sameEnv ▸ constants) (sameEnv ▸ definitions) parameterCount
        (parameters.mono head.insertion.fvars_sublist.subset) nextTranslated
    exact ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, finalEnv.trans sameEnv,
      finalUniverses.trans sameUniverses, finalAligned, finalWF,
      by simpa only [List.singleton_append] using head.trans history, finalParameters, terminalTranslated⟩

theorem CheckedHeaderTrace.generatorPrefix
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {type terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader) :
    finalReader.ngen.namePrefix = reader.ngen.namePrefix := by
  induction trace with
  | stop => rfl
  | freshParameter _ _ _ _ induction => exact induction
  | reusedParameter _ _ _ _ _ _ induction => exact induction
  | index _ _ _ induction => exact induction

theorem CheckedHeaderTrace.initialIsType
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {type terminal result : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) {semantic : VExpr}
    (translated : checker.TrExprS type semantic)
    (sorted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok result) :
    checker.IsType semantic := by
  by_cases binder : type.isForall = true
  · cases type <;> simp only [Expr.isForall, Bool.false_eq_true] at binder
    cases translated with
    | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
      exact domainTyped.forallE bodyTyped
  · cases trace <;> try exact False.elim (binder rfl)
    exact acceptedHeaderSortIsType checker reader aligned initialWF translated sorted

theorem _root_.Lean4Lean.ElimNestedInductive.ParameterPrefix.closedHeaderWF
    {root checker : TypeChecker.VContext} {identifiers : List FVarId} {source : InductiveType}
    (history : ParameterPrefix root.mlctx checker.mlctx identifiers)
    (sameEnv : checker.venv = root.venv) (sameUniverses : checker.lparams = root.lparams)
    (empty : root.mlctx = .nil) {semantic : VExpr}
    (translated : checker.TrExprS source.type semantic) (typed : checker.IsType semantic)
    (supported : source.type.FVarsIn (fun _ => False)) :
    ∃ header, TrInductiveHeader root.venv root.lparams source header ∧ header.toVConstant.WF root.venv := by
  obtain ⟨level, typed⟩ := typed
  have closed : Closed source.type 0 := checker.mlctx.noBV ▸ translated.closed
  obtain ⟨reduced, reducedTranslation, reducedType, _⟩ :=
    TrExprS.strengthenIsType checker.Ewf history.insertion (.refl checker.Ewf checker.Δwf)
      translated typed closed (supported.mono fun _ impossible => impossible.elim)
  have context : root.vlctx = [] := by
    simp only [TypeChecker.VContext.vlctx, empty, MLCtx.vlctx]
  exact ⟨{ name := source.name, uvars := root.lparams.length, type := reduced, ctors := [] },
    ⟨rfl, rfl, by simpa only [sameEnv, sameUniverses, context] using reducedTranslation⟩,
    by simpa only [VConstant.WF, sameEnv, sameUniverses, context, VLCtx.toCtx] using
      (show checker.venv.IsType checker.lparams.length root.vlctx.toCtx reduced from ⟨level, reducedType⟩)⟩

private theorem checkedHeaderTypes (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (processed : Nat) (stats : InductiveStats)
    (root checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : root.mlctx = .nil)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (sameEnv : checker.venv = root.venv) (sameUniverses : checker.lparams = root.lparams)
    (identifiers : List FVarId) (history : ParameterPrefix root.mlctx checker.mlctx identifiers)
    (indCount : stats.indConsts.size = processed)
    (parameterCount : stats.params.size = if processed = 0 then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx) :
    (checkInductiveTypes.loopInd nparams types next processed stats reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, processed ≤ parent →
        ∃ header, TrInductiveHeader root.venv root.lparams types[parent] header ∧
          header.toVConstant.WF root.venv := by
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i within
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro checkedUnit guarded
    cases checkedUnit
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro inferred checked
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro normalized normalizedCall
    have supported := checkNoMVarNoFVar.WF reader.env types[processed].name types[processed].type () guarded
    obtain ⟨sourceSemantic, sourceTranslated⟩ := acceptedSourceTranslation checker reader aligned initialWF
      (supported.mono fun _ impossible => impossible.elim) checked
    obtain ⟨normalizedSemantic, normalizedTranslated, equality⟩ :=
      acceptedHeaderNormalization checker reader aligned initialWF
        (sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalizedCall
    apply checkInductiveTypes.loopInd.loop.scopedTrace
    · have native : checker.mlctx.lctx = reader.lctx :=
        checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
      exact native ▸ checker.trlctx.1
    · exact reserved
    intro terminal finalStats count current trace frame
    obtain ⟨finalChecker, more, finalEnv, finalUniverses, finalAligned, finalWF, extension,
      finalParameters, terminalTranslated⟩ := trace.checkerModels checker aligned initialWF reserved different
        constants definitions (by simpa [Array.isEmpty, indCount] using parameterCount)
        parameters ⟨normalizedSemantic, normalizedTranslated⟩
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro sorted sortedCall
    have sourceTyped := VEnv.IsType.defeqU_l checker.Ewf checker.Δwf.toCtx equality
      (trace.initialIsType checker aligned initialWF normalizedTranslated sortedCall)
    have headerTyped := history.closedHeaderWF sameEnv sameUniverses empty sourceTranslated sourceTyped supported
    obtain ⟨indicesUnchanged, constantsUnchanged, levelsUnchanged⟩ := trace.headerFields
    have finalCount : finalStats.params.size = nparams :=
      trace.paramsCount (by simpa [Array.isEmpty, indCount] using parameterCount)
    have resume (nextStats : InductiveStats)
        (nextCount : nextStats.indConsts.size = processed + 1)
        (nextParameters : nextStats.params = finalStats.params) :
        (checkInductiveTypes.loopInd nparams types next (processed + 1) nextStats current).WF fun _ =>
          ∀ parent, ∀ bound : parent < types.size, processed ≤ parent →
            ∃ header, TrInductiveHeader root.venv root.lparams types[parent] header ∧
              header.toVConstant.WF root.venv := by
      refine (checkedHeaderTypes nparams types next (processed + 1) nextStats root finalChecker current
        finalAligned empty finalWF frame.reserved
        (by simpa only [trace.generatorPrefix] using different)
        (finalEnv ▸ constants) (finalEnv ▸ definitions) (finalEnv.trans sameEnv)
        (finalUniverses.trans sameUniverses) (identifiers ++ more) (history.trans extension)
        nextCount (by simp [nextParameters, finalCount])
        (by simpa only [HeaderParameterModels, nextParameters] using finalParameters)).mono ?_
      intro result remaining parent bound lower
      by_cases first : parent = processed
      · subst parent
        exact headerTyped
      · exact remaining parent bound (by omega)
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      apply resume
      · simp only [Array.size_push, constantsUnchanged, indCount]
      · rfl
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        apply resume
        · simp only [Array.size_push, constantsUnchanged, indCount]
        · rfl
  · exact fun _ _ parent bound lower => False.elim (by omega)
termination_by types.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.headersWF (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size,
        ∃ header, TrInductiveHeader checker.venv reader.lparams types[parent] header ∧
          header.toVConstant.WF checker.venv := by
  have initialWF := TypeChecker.VState.WF.reset checker (by
    simp [TypeChecker.VContext.vlctx, empty, MLCtx.vlctx])
  have nativeContext : reader.lctx = {} := by
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    rw [← native, empty]
    rfl
  have reserved : ContextReserved reader.lctx reader.ngen := by
    rw [nativeContext]
    exact ContextReserved.empty reader.ngen
  have universes := congrArg TypeChecker.Context.lparams aligned
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  refine (checkedHeaderTypes nparams types next 0 _ checker checker reader aligned empty initialWF reserved
    different constants definitions rfl rfl [] .nil rfl rfl ?_).mono ?_
  · intro parameter member
    change parameter ∈ (#[] : Array Expr) at member
    simp at member
  · intro result typed parent bound
    simpa only [universes] using typed parent bound (Nat.zero_le parent)

private theorem typedHeaderList (types : List InductiveType) (env : VEnv) (universes : List Name)
    (typed : ∀ type ∈ types, ∃ header, TrInductiveHeader env universes type header ∧
      header.toVConstant.WF env) :
    ∃ headers, List.Forall₂ (TrInductiveHeader env universes) types headers ∧
      ∀ header ∈ headers, header.toVConstant.WF env := by
  induction types with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons type types induction =>
    obtain ⟨header, translated, headerWF⟩ := typed type (by simp)
    obtain ⟨headers, models, headersWF⟩ := induction (fun type member => typed type (by simp [member]))
    refine ⟨header :: headers, .cons translated models, ?_⟩
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact headerWF
    · exact headersWF candidate member

theorem checkInductiveTypes.headersChecker (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (safety : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types
      (fun stats => declareInductiveTypes stats nparams types numNested isUnsafe) reader).WF fun result =>
      ∃ headers final, List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types.toList headers ∧
        (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
        checker.venv.addInductHeaders headers = some final ∧ CheckerEnv checker.safety result final := by
  intro result accepted
  have typed := checkInductiveTypes.headersWF nparams types
    (fun stats => declareInductiveTypes stats nparams types numNested isUnsafe)
    checker reader aligned empty different constants definitions result accepted
  obtain ⟨headers, models, headersWF⟩ := typedHeaderList types.toList checker.venv reader.lparams (by
    intro type member
    obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    exact typed parent bound)
  have nativeEnv : checker.env = reader.env := congrArg TypeChecker.Context.env aligned
  have initialChecker : CheckerEnv checker.safety reader.env checker.venv := by
    rw [← nativeEnv]
    exact checker.trenv.checkerEnv
  obtain ⟨final, registered, finalChecker⟩ :=
    checkInductiveTypes.refinesHeadersChecker reader nparams types numNested isUnsafe
      initialChecker safety models headersWF result accepted
  exact ⟨headers, final, models, headersWF, registered, finalChecker⟩

theorem run.headersWF (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) :
    (run nparams types numNested reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.length,
        ∃ header, TrInductiveHeader checker.venv reader.lparams types.toArray[parent] header ∧
          header.toVConstant.WF checker.venv := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.headersWF nparams types.toArray _ checker reader aligned empty
    different constants definitions

end Lean4Lean.AddInductive
