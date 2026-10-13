import Lean4Lean.Theory.SortArity
import Lean4Lean.Verify.InductiveHeaderTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)
open private bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces
open private readWF from Lean4Lean.Verify.InductiveStats

theorem acceptedHeaderSortKind (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {source result : Expr} {semantic : VExpr} (translated : checker.TrExprS source semantic)
    (accepted : (monadLift (TypeChecker.ensureSort source) : M Expr) reader = .ok result) :
    checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx 0 semantic := by
  have nativeAccepted : (Prod.fst <$> TypeChecker.ensureSort source source
      checker.toContext ({} : TypeChecker.VState).toState) = .ok result := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.ensureSort source source
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => cases nativeAccepted
  | ok returned =>
    obtain ⟨normalized, final⟩ := returned
    change Except.ok normalized = .ok result at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, ⟨normalizedSemantic, normalizedTranslated, equality⟩, level, rfl⟩ :=
      TypeChecker.ensureSort.WF translated initialWF result final checked
    cases normalizedTranslated with
    | sort translatedLevel => exact .sort (.of_ofLevel translatedLevel) equality.symm

theorem CheckedHeaderTrace.kindIndexBound
    {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader) :
    nindices ≤ finalIndices := by
  induction trace with
  | stop => exact Nat.le_refl _
  | freshParameter _ _ _ _ induction => exact induction
  | reusedParameter _ _ _ _ _ _ induction => exact induction
  | index _ _ _ induction => omega

theorem CheckedHeaderTrace.zeroParameterKind
    {stats finalStats : InductiveStats} {type terminal sorted : Expr}
    {index nindices finalIndices : Nat} {reader finalReader : Context}
    (trace : CheckedHeaderTrace 0 stats type index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    {semantic : VExpr} (translated : checker.TrExprS type semantic)
    (accepted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx (finalIndices - nindices) semantic := by
  induction trace generalizing checker semantic with
  | stop notBinder complete =>
    simpa only [Nat.sub_self] using acceptedHeaderSortKind checker _ aligned initialWF translated accepted
  | freshParameter selected => omega
  | reusedParameter selected => omega
  | @index stats name domain body binder index nindices reader normalized terminal finalStats finalIndices
      finalReader notParameter normalizedCall tail induction =>
    obtain ⟨peeled, nextChecker, environment, universes, context, nextAligned, nextWF,
      openedSemantic, opened, openedTyped, domainSemantic, bodySemantic, level, sourceShape,
      domainTyped, domainEquality, bodyEquality⟩ := translatedHeaderOpeningWithSemantics checker reader aligned
        initialWF reserved different constants definitions translated
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    obtain ⟨normalizedSemantic, normalizedTranslated, normalizedEquality⟩ :=
      acceptedHeaderNormalization nextChecker _ nextAligned nextWF
        (opened.trExpr nextChecker.Ewf.ordered nextChecker.Δwf) normalizedCall
    have normalizedKind := induction nextChecker nextAligned nextWF pushed.reserved different
      (environment ▸ constants) (environment ▸ definitions) normalizedTranslated accepted
    have openedKind := normalizedKind.defeq nextChecker.Ewf nextChecker.Δwf.toCtx
      (bodyEquality.symm.trans nextChecker.Ewf nextChecker.Δwf.toCtx normalizedEquality.symm)
    have openedKind : checker.venv.SortArity checker.lparams.length (peeled :: checker.vlctx.toCtx)
        (finalIndices - (nindices + 1)) bodySemantic := by
      simpa only [environment, universes, TypeChecker.VContext.vlctx, context, MLCtx.vlctx, VLCtx.toCtx] using openedKind
    have contexts : checker.venv.IsDefEqCtx checker.lparams.length checker.vlctx.toCtx
        (peeled :: checker.vlctx.toCtx) (domainSemantic :: checker.vlctx.toCtx) :=
      .succ .zero domainEquality.symm
    have bodyKind := openedKind.defeqCtx checker.Ewf.ordered contexts
    have domainIsType : checker.IsType domainSemantic := ⟨level, domainTyped⟩
    have bodyIsType := bodyKind.isType checker.Ewf ⟨checker.Δwf.toCtx, domainIsType⟩
    obtain ⟨sortLevel, sourceTyped⟩ := domainIsType.forallE bodyIsType
    have equality : checker.IsDefEqU semantic (.forallE domainSemantic bodySemantic) :=
      sourceShape.symm ▸ ⟨.sort sortLevel, sourceTyped⟩
    have count := tail.kindIndexBound
    have exactCount : finalIndices - nindices = (finalIndices - (nindices + 1)) + 1 := by omega
    rw [exactCount]
    exact .forallE domainIsType equality bodyKind

theorem checkInductiveTypes.firstHeaderKind (types : Array InductiveType)
    (next : InductiveStats → M resultType) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) (nonempty : 0 < types.size) :
    (checkInductiveTypes 0 types next reader).WF fun _ => ∃ semantic count,
      checker.TrExprS types[0]!.type semantic ∧
      checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count semantic := by
  unfold checkInductiveTypes
  apply readWF
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i bound
    apply readWF
    apply bindHeaderResultWF
    intro checkedUnit guarded
    cases checkedUnit
    apply bindHeaderResultWF
    intro inferred checked
    apply readWF
    apply bindHeaderResultWF
    intro normalized normalizedCall
    have guarded : reader.env.checkNoMVarNoFVar types[0]!.name types[0]!.type = .ok () := by
      simpa only [getElem!_pos types 0 bound, liftM, monadLift,
        MonadLift.monadLift, StateT.run, ReaderT.run, ExceptT.run] using guarded
    have checked : (monadLift (TypeChecker.checkType types[0]!.type) : M Expr) reader = .ok inferred := by
      simpa only [getElem!_pos types 0 bound] using checked
    have normalizedCall : (monadLift (TypeChecker.whnf types[0]!.type) : M Expr) reader = .ok normalized := by
      simpa only [getElem!_pos types 0 bound] using normalizedCall
    have free := checkNoMVarNoFVar.WF reader.env types[0]!.name types[0]!.type () guarded
    obtain ⟨sourceSemantic, sourceTranslated⟩ := acceptedSourceTranslation checker reader aligned initialWF
      (free.mono fun _ impossible => impossible.elim) checked
    obtain ⟨normalizedSemantic, normalizedTranslated, equality⟩ := acceptedHeaderNormalization checker reader
      aligned initialWF (sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalizedCall
    apply checkInductiveTypes.loopInd.loop.scopedTrace
    · have native : checker.mlctx.lctx = reader.lctx :=
        checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
      exact native ▸ checker.trlctx.1
    · exact reserved
    intro terminal finalStats count current trace scope
    apply bindHeaderResultWF
    intro sorted sortedCall
    have kind := trace.zeroParameterKind checker aligned initialWF reserved different constants definitions
      normalizedTranslated sortedCall
    have kind := kind.defeq checker.Ewf checker.Δwf.toCtx equality.symm
    exact fun _ _ => ⟨sourceSemantic, count, sourceTranslated, by simpa only [Nat.sub_zero] using kind⟩
  · rename_i impossible
    exact False.elim (impossible nonempty)

end Lean4Lean.AddInductive
