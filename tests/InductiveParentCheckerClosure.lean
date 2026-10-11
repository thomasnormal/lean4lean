import Lean4Lean.Verify.InductiveParentPassCheckerClosure
import Lean.Util.CollectAxioms

namespace InductiveParentCheckerClosureTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    TrEnv finalChecker.safety finalChecker.env checker.venv := by
  simpa only [endpoint.checkerContext.1] using finalChecker.trenv

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    ({} : TypeChecker.VState).WF finalChecker := endpoint.checkerContext.2.2.2

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    ∃ identifiers, IndexMLCtxExtension checker.mlctx identifiers finalChecker.mlctx ∧
      ∃ rawSemantic peeled majorLevel motiveSemantic motiveLevel,
        RecursorMajorOpening checker.venv checker.lparams stats parent indices finalReader
          indexChecker.vlctx rawSemantic peeled majorLevel ∧
        RecursorMotiveOpening checker.venv checker.lparams stats parent indices finalReader
          indexChecker.vlctx peeled elimLevel (recursorMotiveName types parent) motiveSemantic motiveLevel := by
  obtain ⟨identifiers, step⟩ := endpoint.modelStep
  have extension := step.extension
  obtain ⟨rawSemantic, peeled, majorLevel, motiveSemantic, motiveLevel, major, motive, _⟩ := step
  exact ⟨identifiers, extension, rawSemantic, peeled, majorLevel, motiveSemantic, motiveLevel, major, motive⟩

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorParentCheckerEndpoint trace checker indexChecker finalChecker
      semantic resultSemantic types elimLevel parent) :
    ∃ identifiers : List FVarId, identifiers.map Expr.fvar = indices.toList ++
      [.fvar ⟨finalReader.ngen.curr⟩,
        .fvar ⟨(recursorIndexContext finalReader `t .default
          (recursorMajorDomain stats parent indices)).ngen.curr⟩] := by
  obtain ⟨identifiers, step⟩ := endpoint.modelStep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, selected⟩ := step
  exact ⟨identifiers, selected⟩

example
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
  apply RecursorIndexTrace.checkedHeaderParent <;> assumption

example {initial final : MLCtx} {identifiers : List FVarId}
    (batch : HeaderParameterKindedApplicationBatch environment universes initial stats types)
    (environmentWF : environment.WF) (finalWF : final.WF environment universes)
    (extension : IndexMLCtxExtension initial identifiers final) :
    HeaderParameterKindedApplicationBatch environment universes final stats types := by
  apply HeaderParameterKindedApplicationBatch.weakening <;> assumption

example
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
  apply RecursorParentPassTrace.checkedModels <;> assumption

example (reader : Context) (infos : Array RecInfo) (parent : Nat) (complete : ¬ parent < types.size) :
    RecursorParentPassCountAlignment (RecursorParentPassTrace.stop (stats := stats) (types := types)
      (elimLevel := elimLevel) (reader := reader) (infos := infos) complete) := .stop complete

run_meta
  let environment ← getEnv
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``HeaderRecursorIndexCheckerEndpoint.parentTypehoodOfKind,
      ``TrExprS.peeledDomain, ``RecursorMajorOpening.parentModelStep,
      ``TypeChecker.VState.WF.reset, ``TypeChecker.VContext.Δwf,
      ``RecursorIndexTrace.headerCheckedModels] do
    allowed := allowed ++ (← collectAxioms name)
  for moduleName in [`Lean4Lean.Verify.InductiveParentCheckerClosure,
      `Lean4Lean.Verify.InductiveParentPassCheckerClosure] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "parent checker closure module absent"
    let mut owned := 0
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned parent checker closure axiom {name}"
        let dependencies ← collectAxioms name
        for dependency in dependencies do
          unless allowed.contains dependency do throwError "unexpected parent checker dependency {dependency} in {name}"
        logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
        owned := owned + 1
    logInfo m!"{moduleName}: {owned} exhaustive owned parent checker closure declarations audited against unchanged earlier foundations"

end InductiveParentCheckerClosureTest
