import Lean4Lean.Verify.InductiveIndexCheckerClosure

namespace Lean4Lean
open Lean hiding Environment Exception

theorem VEnv.SortArity.forallBody
    {environment : VEnv} {universes count : Nat} {context : List VExpr} {domain body : VExpr}
    (kind : environment.SortArity universes context (count + 1) (.forallE domain body))
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    environment.SortArity universes (domain :: context) count body := by
  have domainTyped := (kind.isType environmentWF contextWF).forallE_inv environmentWF.ordered
  cases kind with
  | forallE actualDomain equality tail =>
    obtain ⟨⟨_, domainEquality⟩, ⟨_, bodyEquality⟩⟩ :=
      VEnv.IsDefEqU.forallE_inv environmentWF contextWF equality
    have converted := tail.defeqCtx environmentWF.ordered (.succ .zero domainEquality.symm)
    exact converted.defeq environmentWF ⟨contextWF, domainTyped.1⟩ ⟨_, bodyEquality⟩

namespace ElimNestedInductive
open TypeChecker (MLCtx)

theorem TypedParameterApplications.resultKind
    (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (kind : environment.SortArity universes.length model.vlctx.toCtx (count + replacements.length) source) :
    environment.SortArity universes.length model.vlctx.toCtx count result := by
  induction arguments with
  | nil => simpa only [List.length_nil, Nat.add_zero] using kind
  | cons translated typed remaining induction =>
    apply induction
    exact (VEnv.SortArity.forallBody (by simpa only [List.length_cons, Nat.add_assoc] using kind)
      environmentWF modelWF.tr.wf.toCtx).instN environmentWF.ordered .zero typed
  | convertInput equality _ induction =>
    exact induction (kind.defeq environmentWF modelWF.tr.wf.toCtx equality.symm)

end ElimNestedInductive

namespace AddInductive
open TypeChecker (MLCtx)
open private originalHeaderConstantInput from Lean4Lean.Verify.InductiveHeaderApplicationBatch

theorem TranslatedRecursorIndexTrace.finalKind
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx
      (count + (finalIndices.size - indices.size)) semantic) :
    environment.SortArity universes.length finalVirtual.toCtx count finalSemantic := by
  induction history with
  | stop => simpa only [Nat.sub_self, Nat.add_zero] using kind
  | @index name domain body normalized terminal binder index finalIndex indices finalIndices reader finalReader
      virtual finalVirtual domainSemantic bodySemantic peeled normalizedSemantic finalSemantic level
      notParameter normalization tail translated opening normalizedTranslation normalizedEquality
      history induction =>
    have bound := tail.indexSize
    have countEq : count + (finalIndices.size - indices.size) =
        (count + (finalIndices.size - (indices.size + 1))) + 1 := by
      simp only [Array.size_push] at bound
      omega
    rw [countEq] at kind
    have virtualWF : virtual.WF environment universes.length := opening.2.2.1.wf.1
    have bodyKind := kind.forallBody environmentWF virtualWF.toCtx
    have converted := bodyKind.defeqCtx environmentWF.ordered (.succ .zero opening.2.1)
    have normalizedKind := converted.defeq environmentWF opening.2.2.1.wf.toCtx normalizedEquality
    exact induction (by simpa only [Array.size_push, peeledIndexVirtualContext, VLCtx.toCtx] using normalizedKind)

def HeaderParameterKindedApplicationBatch (environment : VEnv) (universes : List Name)
    (model : MLCtx) (stats : InductiveStats) (types : Array InductiveType) : Prop :=
  ∀ parent, ∀ bound : parent < types.size,
    ∃ input : HeaderParameterApplicationInput environment universes model stats types[parent].type,
      ∃ value, TrExprS environment universes model.vlctx (mkAppN stats.indConsts[parent]! stats.params) value ∧
        environment.HasType universes.length model.vlctx.toCtx value input.result ∧
        environment.SortArity universes.length model.vlctx.toCtx stats.nindices[parent]! input.result

theorem ConstructorConstantRegistration.parentParameterKindedApplications
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    HeaderParameterKindedApplicationBatch registration.semantic root.lparams
      stage.before.model.checker.mlctx stats types := by
  intro parent bound
  obtain ⟨parameters, kind⟩ := stage.before.parameterApplicationKinds parent bound
  have increase := (VEnv.addInductHeaders.le stage.registered).trans registration.increase
  have levels := stage.before.levels (by omega)
  obtain ⟨header, member, translated⟩ := stage.before.models.forall_exists_l types[parent]
    (Array.mem_toList_iff.mpr (Array.getElem_mem bound))
  have lookup := registration.increase.constants (VEnv.addInductHeaders.constants stage.registered member)
  obtain ⟨head⟩ := originalHeaderConstantInput registration.semanticWF lookup
    (translated.2.2.mono increase) translated.2.1 _ registration.parentParameterModelWF
  have head : RecursorConstantInput registration.semantic root.lparams
      stage.before.model.checker.mlctx.vlctx types[parent].name stats.levels types[parent].type := by
    simpa only [translated.1, levels] using head
  obtain ⟨value, translated, typed⟩ := head.applyHeaderParameters (parameters.monoEnv increase)
    registration.semanticWF registration.parentParameterModelWF
  exact ⟨parameters.monoEnv increase, value,
    by simpa only [stage.before.heads parent bound] using translated, typed, kind.mono increase⟩

theorem HeaderParameterKindedApplicationBatch.reindexUniverses
    (batch : HeaderParameterKindedApplicationBatch environment original model stats types)
    (extension : UniverseNameExtension original target) :
    HeaderParameterKindedApplicationBatch environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats types := by
  intro parent bound
  obtain ⟨input, value, translated, typed, kind⟩ := batch parent bound
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  exact ⟨input.reindexUniverses extension, value.instL (UniverseNameExtension.levels original target),
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using translated.reindexUniverses extension,
    by simpa only [HeaderParameterApplicationInput.reindexUniverses, TypeChecker.MLCtx.reindexLevels.vlctx,
      VLCtx.instL_toCtx] using (count.symm ▸ typed).instL extension.levelsWF,
    by simpa only [HeaderParameterApplicationInput.reindexUniverses, TypeChecker.MLCtx.reindexLevels.vlctx,
      VLCtx.instL_toCtx] using (count.symm ▸ kind).instL extension.levelsWF⟩

theorem HeaderRecursorIndexCheckerEndpoint.parentTypehoodOfKind
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx indices.size resultSemantic) :
    ∃ finalValue, finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.IsType finalValue := by
  obtain ⟨sameEnvironment, sameUniverses, _, _, model⟩ := endpoint
  obtain ⟨_, _, _, _, _, _, _, _, _, _, equality, history, _, _, converted, _⟩ := model
  have normalizedTyped := typed.defeqU_r checker.Ewf checker.Δwf.toCtx equality.symm
  obtain ⟨finalValue, translated, typed⟩ := history.application checker.Ewf
    (by simpa only [mkAppN, Array.foldl_empty] using translated) normalizedTyped
  have residualKind := kind.defeq checker.Ewf checker.Δwf.toCtx equality
  have terminalKind := history.finalKind (count := 0) checker.Ewf
    (by simpa only [Array.size_empty, Nat.sub_zero, Nat.zero_add] using residualKind)
  have typehood := terminalKind.typedIsType checker.Ewf history.finalTranslation.1.wf.toCtx typed
  exact ⟨finalValue,
    by simpa only [TypeChecker.VContext.TrExprS, sameEnvironment, sameUniverses, converted] using translated,
    by simpa only [TypeChecker.VContext.IsType, sameEnvironment, sameUniverses, converted] using typehood⟩

theorem RecursorIndexTrace.checkedHeaderBatchTypehood
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size) (counts : indices.size = stats.nindices[parent]!)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        ∃ value, finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          finalChecker.IsType value := by
  obtain ⟨input, partialValue, translated, typed, kind⟩ := batch parent bound
  obtain ⟨finalChecker, endpoint⟩ := trace.headerCheckedModels checker aligned initialWF reserved different
    constants definitions complete input normalized
  exact ⟨input, finalChecker, endpoint, endpoint.parentTypehoodOfKind translated typed (counts.symm ▸ kind)⟩

theorem run.headerParameterKindedUniverseContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          ∃ registration : ConstructorConstantRegistration receipts final, ∀ elimLevel,
            let universes := getRecLevelParams elimLevel root.lparams
            let model := stage.before.model.checker.mlctx.reindexLevels
              (UniverseNameExtension.levels root.lparams universes)
            model.WF registration.semantic universes ∧
              HeaderParameterKindedApplicationBatch registration.semantic universes model stats types.toArray := by
  refine (run.headerParameterApplicationContinuation nparams types numNested root reader aligned empty
    different constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, registration, _⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration, fun elimLevel =>
    ⟨registration.parentParameterModelWFInRecursorUniverses elimLevel,
      registration.parentParameterKindedApplications.reindexUniverses (getRecLevelParams.universeExtension elimLevel _)⟩⟩

end AddInductive
end Lean4Lean
