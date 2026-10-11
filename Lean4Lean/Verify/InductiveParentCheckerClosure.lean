import Lean4Lean.Verify.InductiveHeaderResidualKinds
import Lean4Lean.Verify.InductiveParentContextTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem RecursorIndexTrace.generatorPrefix
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader) :
    finalReader.ngen.namePrefix = reader.ngen.namePrefix := by
  induction trace with
  | stop => rfl
  | parameter _ _ _ induction => exact induction
  | index _ _ _ induction => exact induction

theorem RecursorMajorOpening.ofTypehood
    {stats : InductiveStats} {parent : Nat} {indices : Array Expr} {reader : Context}
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (translated : checker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value)
    (typehood : checker.IsType value) :
    ∃ peeled level, RecursorMajorOpening checker.venv checker.lparams stats parent indices reader
      checker.vlctx value peeled level := by
  obtain ⟨level, typed⟩ := typehood
  have native : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  have correspondence := native ▸ checker.mlctx_wf.tr
  obtain ⟨peeled, peeledTranslated, equality⟩ := translated.peeledDomain checker.Ewf
    checker.Δwf.toCtx constants definitions typed
  exact ⟨peeled, level, translated, typed, peeledTranslated, equality, equality.hasType.2,
    translatedIndexContextPush correspondence reserved peeledTranslated equality.hasType.2,
    newlyAllocatedBinderPositioned reader `t _ .default correspondence.1 reserved,
    Context.RecursorScopeFrame.push reader correspondence.1 reserved `t .default
      (recursorMajorDomain stats parent indices)⟩

theorem HeaderRecursorIndexCheckerEndpoint.parentModelStepOfKind
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context} {checker indexChecker : TypeChecker.VContext}
    {semantic resultSemantic value : VExpr} {types : Array InductiveType} {parent : Nat}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker indexChecker semantic resultSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (translated : checker.TrExprS (mkAppN stats.indConsts[parent]! stats.params) value)
    (typed : checker.HasType value resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx indices.size resultSemantic)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel) :
    ∃ finalModel allocated, RecursorParentModelStep checker.venv checker.lparams stats types elimLevel
      parent indices finalReader indexChecker.vlctx checker.mlctx finalModel allocated := by
  obtain ⟨rawSemantic, rawTranslated, rawTypehood⟩ := endpoint.parentTypehoodOfKind translated typed kind
  obtain ⟨sameEnvironment, sameUniverses, aligned, _, model⟩ := endpoint
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, history, modelWF, native, converted,
    identifiers, extension, selected⟩ := model
  have finalReserved := (history.scope reserved).reserved
  obtain ⟨peeled, level, opening⟩ := RecursorMajorOpening.ofTypehood indexChecker aligned finalReserved
    (sameEnvironment ▸ constants) (sameEnvironment ▸ definitions) rawTranslated rawTypehood
  have opening : RecursorMajorOpening checker.venv checker.lparams stats parent indices finalReader
      indexChecker.vlctx rawSemantic peeled level := by
    simpa only [sameEnvironment, sameUniverses] using opening
  exact opening.parentModelStep extension modelWF native rfl finalReserved selected checker.Ewf mapped

theorem RecursorParentModelStep.checkerContinuation
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {reader : Context} {initial finalModel : MLCtx} {identifiers : List FVarId}
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (step : RecursorParentModelStep checker.venv checker.lparams stats types elimLevel parent indices reader
      checker.vlctx initial finalModel identifiers) :
    ∃ finalChecker : TypeChecker.VContext,
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      finalChecker.mlctx = finalModel ∧
      HeaderCheckerAligned finalChecker (recursorMotiveContext stats parent indices reader elimLevel
        (recursorMotiveName types parent)) ∧ ({} : TypeChecker.VState).WF finalChecker := by
  obtain ⟨rawSemantic, peeled, majorLevel, motiveSemantic, motiveLevel, _, _, modelWF, native,
    converted, _⟩ := step
  let finalChecker := checker.withMLC finalModel (wf := ⟨modelWF⟩)
  have finalAligned : HeaderCheckerAligned finalChecker
      (recursorMotiveContext stats parent indices reader elimLevel (recursorMotiveName types parent)) := by
    change { checker.toContext with lctx := finalModel.lctx } = _
    rw [aligned]
    simp only [native, recursorMotiveContext, recursorIndexContext]
  have reserved : ∀ identifier ∈ finalChecker.vlctx.fvars,
      ({} : TypeChecker.VState).ngen.Reserves identifier := by
    intro identifier member
    change identifier ∈ finalModel.vlctx.fvars at member
    rw [converted] at member
    simp only [recursorMotiveVirtualContext, recursorMajorVirtualContext, VLCtx.fvars_cons_some,
      List.mem_cons] at member
    rcases member with rfl | rfl | member
    · intro count same
      have prefixes : reader.ngen.namePrefix = ({} : TypeChecker.VState).ngen.namePrefix :=
        (Name.num.inj (FVarId.mk.inj same)).1
      exact False.elim (different prefixes.symm)
    · intro count same
      have prefixes : reader.ngen.namePrefix = ({} : TypeChecker.VState).ngen.namePrefix :=
        (Name.num.inj (FVarId.mk.inj same)).1
      exact False.elim (different prefixes.symm)
    · exact initialWF.ngen_wf identifier member
  exact ⟨finalChecker, rfl, rfl, rfl, finalAligned, TypeChecker.VState.WF.reset finalChecker reserved⟩

def HeaderRecursorParentCheckerEndpoint
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker indexChecker finalChecker : TypeChecker.VContext) (semantic resultSemantic : VExpr)
    (types : Array InductiveType) (elimLevel : Level) (parent : Nat) : Prop :=
  HeaderRecursorIndexCheckerEndpoint trace checker indexChecker semantic resultSemantic ∧
  finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
  HeaderCheckerAligned finalChecker (recursorMotiveContext stats parent indices finalReader elimLevel
    (recursorMotiveName types parent)) ∧ ({} : TypeChecker.VState).WF finalChecker ∧
  ∃ identifiers, RecursorParentModelStep checker.venv checker.lparams stats types elimLevel parent
    indices finalReader indexChecker.vlctx checker.mlctx finalChecker.mlctx identifiers

theorem HeaderRecursorParentCheckerEndpoint.checkerContext
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker (recursorMotiveContext stats parent indices finalReader elimLevel
        (recursorMotiveName types parent)) ∧ ({} : TypeChecker.VState).WF finalChecker :=
  ⟨endpoint.2.1, endpoint.2.2.1, endpoint.2.2.2.1, endpoint.2.2.2.2.1⟩

theorem HeaderRecursorParentCheckerEndpoint.modelStep
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    ∃ identifiers, RecursorParentModelStep checker.venv checker.lparams stats types elimLevel parent
      indices finalReader indexChecker.vlctx checker.mlctx finalChecker.mlctx identifiers :=
  endpoint.2.2.2.2.2

theorem HeaderRecursorIndexCheckerEndpoint.parentCheckerOfKind
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader finalReader : Context} {checker indexChecker : TypeChecker.VContext}
    {semantic resultSemantic value : VExpr} {types : Array InductiveType} {parent : Nat}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker indexChecker semantic resultSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (translated : checker.TrExprS (mkAppN stats.indConsts[parent]! stats.params) value)
    (typed : checker.HasType value resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx indices.size resultSemantic)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel) :
    ∃ finalChecker, HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent := by
  obtain ⟨finalModel, identifiers, step⟩ := endpoint.parentModelStepOfKind reserved constants definitions
    translated typed kind mapped
  have different : ({} : TypeChecker.VState).ngen.namePrefix ≠ finalReader.ngen.namePrefix :=
    trace.generatorPrefix.symm ▸ different
  have indexStep : RecursorParentModelStep indexChecker.venv indexChecker.lparams stats types elimLevel
      parent indices finalReader indexChecker.vlctx checker.mlctx finalModel identifiers := by
    simpa only [endpoint.1, endpoint.2.1] using step
  obtain ⟨finalChecker, sameEnvironment, sameUniverses, context, aligned, finalWF⟩ :=
    indexStep.checkerContinuation indexChecker endpoint.2.2.1 endpoint.2.2.2.1 different
  exact ⟨finalChecker, endpoint, sameEnvironment.trans endpoint.1, sameUniverses.trans endpoint.2.1,
    aligned, finalWF, identifiers, context.symm ▸ step⟩

theorem RecursorIndexTrace.checkedHeaderParent
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
    (parent : Nat) (bound : parent < types.size) (counts : indices.size = stats.nindices[parent]!)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ indexChecker finalChecker, HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
        input.semantic input.result types elimLevel parent := by
  obtain ⟨input, partialValue, translated, typed, kind⟩ := batch parent bound
  obtain ⟨indexChecker, endpoint⟩ := trace.headerCheckedModels checker aligned initialWF reserved different
    constants definitions complete input normalized
  obtain ⟨finalChecker, parentEndpoint⟩ := endpoint.parentCheckerOfKind reserved different constants definitions
    translated typed (counts.symm ▸ kind) mapped
  exact ⟨input, indexChecker, finalChecker, parentEndpoint⟩

end Lean4Lean.AddInductive
