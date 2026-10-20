import Lean4Lean.Verify.InductiveRecursiveIndexArguments
import Lean4Lean.Verify.InductiveHeaderIndexApplications

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

private theorem mkAppList_eqv_of_getElem {left right : Expr} {xs ys : List Expr}
    (lengths : xs.length = ys.length)
    (entries : ∀ index (bound : index < xs.length),
      (xs[index] == ys[index]'(by omega)) = true)
    (heads : (left == right) = true) :
    (left.mkAppList xs == right.mkAppList ys) = true := by
  induction xs generalizing ys left right with
  | nil =>
    cases ys with
    | nil => exact heads
    | cons => simp only [List.length_nil, List.length_cons] at lengths; omega
  | cons x xs induction =>
    cases ys with
    | nil => simp at lengths
    | cons y ys =>
      apply induction (ys := ys) (left := .app left x) (right := .app right y)
        (by simpa using lengths)
        (fun index bound => by
          have leftBound : index + 1 < (x :: xs).length := Nat.succ_lt_succ bound
          have rightBound : index + 1 < (y :: ys).length := lengths ▸ leftBound
          have next := entries (index + 1) leftBound
          change ((x :: xs)[index + 1]'leftBound ==
            (y :: ys)[index + 1]'rightBound) = true at next
          rw [List.getElem_cons_succ, List.getElem_cons_succ] at next
          exact next)
      change (Expr.app left x).eqv (.app right y) = true
      rw [Expr.eqv_eq]
      have entry : (x == y) = true := entries 0 (by simp)
      simpa only [(· == ·), Expr.eqv', ← Expr.eqv_eq] using
        (show ((left == right) && (x == y)) = true by rw [heads, entry]; rfl)

/-- Accepted native family recognition relates the stored parameter application
and the actual terminal prefix by boolean expression equality. This preserves
accepted binder-name/annotation differences, without claiming native equality. -/
theorem isValidIndAppIdx.familyIndexPrefixMatches
    (accepted : isValidIndAppIdx stats terminal parent = true) :
    (mkAppN stats.indConsts[parent]! stats.params == familyIndexPrefix stats terminal) = true := by
  obtain ⟨bound, parameters⟩ := isValidIndAppIdx.parameterMatches stats terminal parent accepted
  have heads := (isValidIndAppIdx.headerMatches stats terminal parent accepted).1
  have length : stats.params.toList.length =
      (terminal.getAppArgs.toList.take stats.params.size).length := by
    simp [List.length_take, Nat.min_eq_left bound]
  have related := mkAppList_eqv_of_getElem length (fun index indexBound => by
    have paramBound : index < stats.params.size := by simpa using indexBound
    have argumentBound : index < terminal.getAppArgs.size := Nat.lt_of_lt_of_le paramBound bound
    simpa only [List.getElem_take, Array.getElem_toList, getElem!_pos stats.params index paramBound,
      getElem!_pos terminal.getAppArgs index argumentBound] using parameters index paramBound)
    (BEq.symm heads)
  have applicationConstructor : mkApp = Expr.app := rfl
  simpa only [mkAppN, applicationConstructor, Array.foldl_toList,
    Expr.mkAppList_eq_foldl, familyIndexPrefix] using related

/-- Carry the family input through successful insertion of further declarations. -/
def FamilyIndexInput.monoEnv
    (input : FamilyIndexInput env universes model stats terminal source)
    (increase : env ≤ extended) :
    FamilyIndexInput extended universes model stats terminal source :=
  ⟨input.type, input.sourceTranslated.mono increase, input.value,
    input.translated.mono increase, input.typed.mono increase⟩

/-- Reuse the checked header input in a later rule context. Only actual free
variable insertion is needed; no fresh index typing receipts are introduced. -/
def FamilyIndexInput.weakFV
    (input : FamilyIndexInput env universes model stats terminal source)
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    FamilyIndexInput env universes target stats terminal source :=
  ⟨input.type.lift' lift,
    input.sourceTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf,
    input.value.lift' lift,
    input.translated.weakFV' envWF.ordered insertion targetWF.tr.wf,
    input.typed.weak' envWF.ordered insertion.toCtx⟩

/-- The same native family input remains usable when the generated recursor
adds an elimination universe. Semantic levels are reindexed explicitly. -/
def FamilyIndexInput.reindexUniverses
    (input : FamilyIndexInput env original model stats terminal source)
    (extension : UniverseNameExtension original target) :
    FamilyIndexInput env target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats terminal source := by
  let levels := UniverseNameExtension.levels original target
  have count := UniverseNameExtension.levelsLength (original := original) (target := target)
  exact ⟨input.type.instL levels,
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using input.sourceTranslated.reindexUniverses extension,
    input.value.instL levels,
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx] using input.translated.reindexUniverses extension,
    by simpa only [TypeChecker.MLCtx.reindexLevels.vlctx, VLCtx.instL_toCtx] using
      (count.symm ▸ input.typed).instL extension.levelsWF⟩

/-- The actual checked parameter/index endpoint supplies the partial-family
input. Its residual translation and conversion discharge the expected signature;
native family recognition transports the stored prefix to the actual one. -/
theorem HeaderRecursorIndexModelEndpoint.familyIndexInput
    {trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader}
    (endpoint : HeaderRecursorIndexModelEndpoint env universes trace model indexModel semantic result)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (partialTranslated : TrExprS env universes model.vlctx
      (mkAppN stats.indConsts[parent]! stats.params) partialValue)
    (partialTyped : env.HasType universes.length model.vlctx.toCtx partialValue result)
    (accepted : isValidIndAppIdx stats terminal parent = true) :
    ∃ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex ∧
      Nonempty (FamilyIndexInput env universes model stats terminal residual) := by
  obtain ⟨residual, afterIndex, _, residualSemantic, _, _, parameters,
    _, _, translated, equality, _⟩ := endpoint
  exact ⟨residual, afterIndex, parameters, ⟨{
    type := residualSemantic
    sourceTranslated := translated
    value := partialValue
    translated := partialTranslated.eqv (isValidIndAppIdx.familyIndexPrefixMatches accepted)
    typed := partialTyped.defeqU_r envWF modelWF.tr.wf.toCtx equality.symm }⟩⟩

/-- Obtain the family input from an actual checked header batch, retaining its
residual parameter-prefix trace. No partial-family translation/typing premise
is required. General header/parameter normalization support remains explicit;
the older unrestricted checker WHNF theorem is not used. -/
theorem RecursorIndexTrace.familyIndexInputOfHeaderBatch
    {terminal : Expr}
    (trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (_normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok headerSource)
    (headerSupport : IndexNormalizationSupport checker.venv checker.lparams reader
      types[parent].type headerSource)
    (parameterSupport : ∀ residual afterIndex,
      (parameters : RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex) →
        IndexParameterNormalizationSupport checker.venv checker.lparams checker.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (accepted : isValidIndAppIdx stats terminal parent = true) :
    ∃ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex ∧
      Nonempty (FamilyIndexInput checker.venv checker.lparams checker.mlctx stats terminal residual) := by
  obtain ⟨input, partialValue, partialTranslated, partialTyped⟩ := batch parent bound
  obtain ⟨residual, afterIndex, parameters⟩ := trace.parameterPrefix complete
  have native := checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  have correspondence : TrLCtx checker.venv checker.lparams reader.lctx checker.vlctx := by
    simpa only [native] using checker.mlctx_wf.tr
  have translated := headerSupport _ _ correspondence
    (input.sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf)
  obtain ⟨indexModel, endpoint⟩ := trace.headerApplications parameters checker.Ewf
    constants definitions checker.mlctx checker.mlctx_wf
    native reserved input.arguments translated (parameterSupport residual afterIndex parameters) annotations normalizations
  exact endpoint.familyIndexInput checker.Ewf checker.mlctx_wf partialTranslated partialTyped accepted

/-- Native sort telescopes are unchanged by the actual head normalizer.
Both original-header and parameter-prefix normalization support follow from
that shape, without the older unrestricted WHNF soundness theorem. -/
theorem RecursorIndexTrace.familyIndexInputOfSortTelescope
    {terminal : Expr}
    (trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok headerSource)
    (telescope : SortTelescope types[parent].type)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (accepted : isValidIndAppIdx stats terminal parent = true) :
    ∃ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex ∧
      Nonempty (FamilyIndexInput checker.venv checker.lparams checker.mlctx stats terminal residual) := by
  have unchanged := telescope.whnf reader _ normalized
  have sourceTelescope : SortTelescope headerSource := unchanged.symm ▸ telescope
  exact trace.familyIndexInputOfHeaderBatch checker aligned constants definitions
    reserved complete batch parent bound normalized
    (fun _ _ _ translated => unchanged.symm ▸ translated)
    (fun _ _ parameters => parameters.normalizationSupport_ofSortTelescope sourceTelescope)
    annotations (trace.normalizationSupport_ofSortTelescope sourceTelescope) accepted

/-- Transport the checked header producer across the recursor environment
extension, elimination-universe extension and actual rule-context insertion.
The source remains the residual signature selected by the checked trace. -/
theorem RecursorIndexTrace.familyIndexInputInRule
    {terminal : Expr}
    (trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok headerSource)
    (headerSupport : IndexNormalizationSupport checker.venv checker.lparams reader
      types[parent].type headerSource)
    (parameterSupport : ∀ residual afterIndex,
      (parameters : RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex) →
        IndexParameterNormalizationSupport checker.venv checker.lparams checker.vlctx parameters)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (normalizations : IndexTraceNormalizationSupport checker.venv checker.lparams trace)
    (accepted : isValidIndAppIdx stats terminal parent = true)
    (increase : checker.venv ≤ env) (envWF : env.WF)
    (universes : UniverseNameExtension checker.lparams targetUniverses)
    (ruleWF : ruleModel.WF env targetUniverses)
    (insertion : VLCtx.FVLift'
      (checker.mlctx.reindexLevels (UniverseNameExtension.levels checker.lparams targetUniverses)).vlctx
      ruleModel.vlctx 0 lift 0) :
    ∃ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex ∧
      Nonempty (FamilyIndexInput env targetUniverses ruleModel stats terminal residual) := by
  obtain ⟨residual, afterIndex, parameters, ⟨input⟩⟩ := trace.familyIndexInputOfHeaderBatch
    checker aligned constants definitions reserved complete batch parent bound
    normalized headerSupport parameterSupport annotations normalizations accepted
  exact ⟨residual, afterIndex, parameters,
    ⟨((input.monoEnv increase).reindexUniverses universes).weakFV envWF ruleWF insertion⟩⟩

end Lean4Lean.AddInductive
