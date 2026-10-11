import Lean4Lean.Verify.InductiveParentCheckerClosure
import Lean4Lean.Verify.InductiveParentPassTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)
open private liftedSkip from Lean4Lean.Verify.InductiveHeaderParameterApplications

theorem HeaderParameterKindedApplicationBatch.weakening
    {initial final : MLCtx} {identifiers : List FVarId}
    (batch : HeaderParameterKindedApplicationBatch environment universes initial stats types)
    (environmentWF : environment.WF) (finalWF : final.WF environment universes)
    (extension : IndexMLCtxExtension initial identifiers final) :
    HeaderParameterKindedApplicationBatch environment universes final stats types := by
  intro parent bound
  obtain ⟨input, value, translated, typed, kind⟩ := batch parent bound
  let transported := input.weakFV environmentWF finalWF extension.weakening.toFVLift'
  refine ⟨transported, value.liftN identifiers.length, ?_, ?_, ?_⟩
  · exact translated.weakFV environmentWF.ordered extension.weakening finalWF.tr.wf
  · simpa only [transported, HeaderParameterApplicationInput.weakFV, liftedSkip] using
      typed.weakN environmentWF.ordered extension.weakening.toCtx
  · simpa only [transported, HeaderParameterApplicationInput.weakFV, liftedSkip] using
      kind.weakN environmentWF.ordered extension.weakening.toCtx

inductive RecursorParentPassCountAlignment
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} :
    {parent : Nat} → {infos finalInfos : Array RecInfo} → {reader finalReader : Context} →
    RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader → Prop where
  | stop {parent : Nat} {infos : Array RecInfo} {reader : Context}
      (complete : ¬ parent < types.size) :
      RecursorParentPassCountAlignment (.stop (parent := parent) (infos := infos) (reader := reader) complete)
  | step {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader indexReader : Context}
      {normalized terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
      (bound : parent < types.size)
      (normalization : (monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) reader = .ok normalized)
      (indicesTrace : RecursorIndexTrace stats normalized 0 #[] reader terminal finalIndex indices indexReader)
      (tail : RecursorParentPassTrace stats types elimLevel (parent + 1)
        (infos.push (recursorParentPassInfo stats parent indices indexReader))
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent))
        finalInfos finalReader)
      (parameters : stats.params.size ≤ finalIndex)
      (indicesCount : indices.size = stats.nindices[parent]!)
      (alignedTail : RecursorParentPassCountAlignment tail) :
      RecursorParentPassCountAlignment (.step bound normalization indicesTrace tail)

theorem RecursorParentPassTrace.checkedModels
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (trace : RecursorParentPassTrace stats types elimLevel parent infos reader finalInfos finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel checker.lparams elimLevel = some semanticElimLevel)
    (counts : RecursorParentPassCountAlignment trace) :
    ∃ finalChecker : TypeChecker.VContext,
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      HeaderParameterKindedApplicationBatch checker.venv checker.lparams finalChecker.mlctx stats types ∧
      ∃ identifiers, IndexMLCtxExtension checker.mlctx identifiers finalChecker.mlctx := by
  induction counts generalizing checker with
  | stop => exact ⟨checker, rfl, rfl, aligned, initialWF, batch, [], .nil⟩
  | @step parent infos finalInfos reader finalReader indexReader normalized terminal finalIndex indices
      bound normalization indicesTrace tail parameters indicesCount alignedTail induction =>
    obtain ⟨input, indexChecker, nextChecker, endpoint⟩ := indicesTrace.checkedHeaderParent checker aligned
      initialWF reserved different constants definitions parameters batch parent bound indicesCount
      (by simpa only [getElem!_pos types parent bound] using normalization) mapped
    obtain ⟨sameEnvironment, sameUniverses, nextAligned, nextWF⟩ := endpoint.checkerContext
    obtain ⟨identifiers, step⟩ := endpoint.modelStep
    have extension := step.extension
    obtain ⟨_, _, _, _, _, _, motive, _⟩ := step
    have nextReserved := motive.2.2.2.reserved
    have nextDifferent : ({} : TypeChecker.VState).ngen.namePrefix ≠
        (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)).ngen.namePrefix := by
      change ({} : TypeChecker.VState).ngen.namePrefix ≠ indexReader.ngen.namePrefix
      exact indicesTrace.generatorPrefix.symm ▸ different
    have nextModelWF : nextChecker.mlctx.WF checker.venv checker.lparams := by
      simpa only [sameEnvironment, sameUniverses] using nextChecker.mlctx_wf
    have nextBatch := batch.weakening checker.Ewf nextModelWF extension
    have nextBatch : HeaderParameterKindedApplicationBatch nextChecker.venv nextChecker.lparams
        nextChecker.mlctx stats types := by
      simpa only [sameEnvironment, sameUniverses] using nextBatch
    obtain ⟨finalChecker, finalEnvironment, finalUniverses, finalAligned, finalWF, finalBatch,
      more, finalExtension⟩ := induction nextChecker nextAligned nextWF nextReserved nextDifferent
        (sameEnvironment ▸ constants) (sameEnvironment ▸ definitions) nextBatch
        (sameUniverses ▸ mapped)
    refine ⟨finalChecker, finalEnvironment.trans sameEnvironment, finalUniverses.trans sameUniverses,
      finalAligned, finalWF, ?_, identifiers ++ more, extension.trans finalExtension⟩
    simpa only [sameEnvironment, sameUniverses] using finalBatch

end Lean4Lean.AddInductive
