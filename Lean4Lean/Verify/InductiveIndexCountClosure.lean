import Lean4Lean.Theory.SortArityCounts
import Lean4Lean.Verify.InductiveParentCheckerClosure

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem TranslatedRecursorIndexTrace.indexBound
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx count semantic) :
    finalIndices.size - indices.size ≤ count := by
  induction history generalizing count with
  | stop => omega
  | @index name domain body normalized terminal binder index finalIndex indices finalIndices reader finalReader
      virtual finalVirtual domainSemantic bodySemantic peeled normalizedSemantic finalSemantic level
      notParameter normalization tail translated opening normalizedTranslation normalizedEquality
      history induction =>
    have virtualWF : virtual.WF environment universes.length := opening.2.2.1.wf.1
    have positive := kind.forallPositive environmentWF virtualWF.toCtx
    obtain ⟨remaining, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt positive)
    rw [countEq] at kind
    have bodyKind := kind.forallBody environmentWF virtualWF.toCtx
    have converted := bodyKind.defeqCtx environmentWF.ordered (.succ .zero opening.2.1)
    have normalizedKind := converted.defeq environmentWF opening.2.2.1.wf.toCtx normalizedEquality
    have bounded := induction (by simpa only [peeledIndexVirtualContext, VLCtx.toCtx] using normalizedKind)
    have nativeBound := tail.indexSize
    simp only [Array.size_push] at bounded nativeBound
    omega

theorem TranslatedRecursorIndexTrace.remainingKind
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx count semantic) :
    finalIndices.size - indices.size ≤ count ∧
      environment.SortArity universes.length finalVirtual.toCtx
        (count - (finalIndices.size - indices.size)) finalSemantic := by
  have bounded := history.indexBound environmentWF kind
  refine ⟨bounded, history.finalKind environmentWF ?_⟩
  simpa only [Nat.sub_add_cancel bounded] using kind

theorem TranslatedRecursorIndexTrace.exactCountOfSortKind
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx count semantic)
    (terminalKind : environment.SortArity universes.length finalVirtual.toCtx 0 finalSemantic) :
    finalIndices.size - indices.size = count := by
  obtain ⟨bounded, remaining⟩ := history.remainingKind environmentWF kind
  have exhausted := remaining.uniqueCount terminalKind environmentWF history.finalTranslation.1.wf.toCtx
  omega

theorem HeaderRecursorIndexCheckerEndpoint.indexBound
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count resultSemantic) :
    indices.size ≤ count := by
  obtain ⟨_, _, _, _, model⟩ := endpoint
  obtain ⟨_, _, _, _, _, _, _, _, _, _, equality, history, _⟩ := model
  have normalizedKind := kind.defeq checker.Ewf checker.Δwf.toCtx equality
  simpa only [Array.size_empty, Nat.sub_zero] using history.indexBound checker.Ewf normalizedKind

theorem HeaderRecursorIndexCheckerEndpoint.exactCountOfSortCheck
    {stats : InductiveStats} {source terminal sorted : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context} {checker finalChecker : TypeChecker.VContext}
    {semantic resultSemantic : VExpr}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count resultSemantic)
    (accepted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    indices.size = count := by
  obtain ⟨sameEnvironment, sameUniverses, aligned, initialWF, model⟩ := endpoint
  obtain ⟨_, _, _, _, finalVirtual, finalSemantic, _, _, _, _, equality, history, _, _, converted, _⟩ := model
  have normalizedKind := kind.defeq checker.Ewf checker.Δwf.toCtx equality
  have translated : finalChecker.TrExprS terminal finalSemantic := by
    simpa only [TypeChecker.VContext.TrExprS, sameEnvironment, sameUniverses, converted]
      using history.finalTranslation.2
  have terminalKind := acceptedHeaderSortKind finalChecker finalReader aligned initialWF translated accepted
  have terminalKind : checker.venv.SortArity checker.lparams.length
      finalVirtual.toCtx 0 finalSemantic := by
    simpa only [sameEnvironment, sameUniverses, converted] using terminalKind
  simpa only [Array.size_empty, Nat.sub_zero] using
    history.exactCountOfSortKind checker.Ewf normalizedKind terminalKind

theorem RecursorIndexTrace.checkedHeaderIndexBound
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
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        indices.size ≤ stats.nindices[parent]! := by
  obtain ⟨input, _, _, _, kind⟩ := batch parent bound
  obtain ⟨finalChecker, endpoint⟩ := trace.headerCheckedModels checker aligned initialWF reserved different
    constants definitions complete input normalized
  exact ⟨input, finalChecker, endpoint, endpoint.indexBound kind⟩

theorem RecursorIndexTrace.checkedHeaderParentOfSortCheck
    {stats : InductiveStats} {source terminal sorted : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    (accepted : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel) :
    indices.size = stats.nindices[parent]! ∧
      ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
        ∃ indexChecker finalChecker, HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
          input.semantic input.result types elimLevel parent := by
  obtain ⟨input, partialValue, translated, typed, kind⟩ := batch parent bound
  obtain ⟨indexChecker, endpoint⟩ := trace.headerCheckedModels checker aligned initialWF reserved different
    constants definitions complete input normalized
  have count := endpoint.exactCountOfSortCheck kind accepted
  obtain ⟨finalChecker, parentEndpoint⟩ := endpoint.parentCheckerOfKind reserved different constants definitions
    translated typed (count.symm ▸ kind) mapped
  exact ⟨count, input, indexChecker, finalChecker, parentEndpoint⟩

end Lean4Lean.AddInductive
