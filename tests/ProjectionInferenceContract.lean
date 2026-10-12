import Lean4Lean.Verify.TypeChecker.InferType
import Lean.Util.CollectAxioms

namespace ProjectionInferenceContractTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private structure DependentPair where
  value : Nat
  proof : value = value

private def dependentValue : DependentPair := ⟨7, rfl⟩

theorem projectionContract {context : VContext} {state : VState}
    {parent : Name} {index : Nat} {source suppliedType : Expr} {semantic semanticType : VExpr}
    (translated : context.TrExprS source semantic)
    (typeTranslation : context.TrExprS suppliedType semanticType)
    (typed : context.HasType semantic semanticType)
    (below : context.FVarsBelow source suppliedType) :
    (Inner.inferProj parent index source suppliedType).WF context state
      (fun inferred _ => ∃ projected resultType,
        context.TrTyping (.proj parent index source) inferred projected resultType) := by
  fail_if_success
    have wrongValue : (Inner.inferProj parent index source suppliedType).WF context state
        (fun inferred _ => ∃ resultType,
          context.TrTyping (.proj parent index source) inferred semantic resultType) :=
      Inner.inferProj.WF ⟨below, translated, typeTranslation, typed⟩
  exact Inner.inferProj.WF ⟨below, translated, typeTranslation, typed⟩

theorem projectionTypeAlignment {context : VContext} {state : VState}
    {parent : Name} {index : Nat} {source suppliedType : Expr}
    {semantic actualType suppliedSemantic : VExpr}
    (translated : context.TrExprS source semantic)
    (typeTranslation : context.TrExprS suppliedType suppliedSemantic)
    (typed : context.HasType semantic actualType) (aligned : actualType = suppliedSemantic)
    (below : context.FVarsBelow source suppliedType) :
    (Inner.inferProj parent index source suppliedType).WF context state
      (fun inferred _ => ∃ projected resultType,
        context.TrTyping (.proj parent index source) inferred projected resultType) := by
  fail_if_success exact Inner.inferProj.WF ⟨below, translated, typeTranslation, typed⟩
  exact Inner.inferProj.WF ⟨below, translated, typeTranslation, aligned ▸ typed⟩

theorem closedSourceCannotIntroduceLocal (locals : VLCtx) (identifier : FVarId) {source : Expr}
    (closed : source.FVarsIn (fun _ => False)) :
    ¬ FVarsBelow locals source (.fvar identifier) := by
  intro below
  have upSet : IsFVarUpSet (fun _ => False) locals := by
    clear below
    induction locals with
    | nil => trivial
    | cons entry remaining inductionHypothesis =>
      obtain ⟨binding, declaration⟩ := entry
      cases binding
      · exact inductionHypothesis
      · exact ⟨inductionHypothesis, False.elim⟩
  exact below (fun _ => False) upSet closed

private def nativeControls : MetaM Unit := do
  let host ← getEnv
  let environment := host.toKernelEnv
  let natural := mkConst ``Nat
  let pairType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero])
    #[natural, natural, .lit (.natVal 7), .lit (.natVal 11)]
  let truth := mkConst ``True
  let conjunction := mkAppN (mkConst ``And.intro)
    #[truth, truth, mkConst ``True.intro, mkConst ``True.intro]
  let dependent := mkConst ``dependentValue
  let methods := Methods.withFuel 256
  let projections := #[(``Prod, 0, pair), (``Prod, 1, pair),
    (``DependentPair, 0, dependent), (``DependentPair, 1, dependent), (``And, 0, conjunction)]
  let mut accepted := 0
  let mut alignmentControls := 0
  let mut dependencyControls := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eagerMode in [false, true] do
      let context : Context := { env := environment, safety, eagerReduce := eagerMode }
      for (parent, index, source) in projections do
        let suppliedType ← Meta.inferType source
        let projectedType ← Meta.inferType (.proj parent index source)
        if ← Meta.isDefEq suppliedType projectedType then
          throwError "projection contract control has identical source/result types"
        let mut state : State := {}
        for _ in [:2] do
          let .ok (inferred, finalState) := Inner.inferProj parent index source suppliedType methods context state
            | throwError "projection worker rejected a well-typed contract control"
          let .ok (equal, comparedState) := Inner.isDefEq inferred projectedType methods context finalState
            | throwError "projection result-type comparison rejected"
          unless equal do throwError "projection worker returned the structure type instead of the field type"
          state := comparedState
          accepted := accepted + 1
      let identifier : FVarId := ⟨`projectionContractNatural⟩
      let locals := ({} : LocalContext).mkLocalDecl identifier `natural natural .default
      let mismatchContext : Context := { context with lctx := locals }
      let source := Expr.fvar identifier
      let .ok (inferred, _) := Inner.inferProj ``Prod 0 source pairType methods mismatchContext {}
        | throwError "trusted-type projection worker no longer demonstrates its alignment precondition"
      unless inferred == natural do throwError "trusted-type projection worker returned an unexpected type"
      if (methods.inferType (.proj ``Prod 0 source) false mismatchContext {}).isOk then
        throwError "full projection checking accepted a mismatched structure type"
      alignmentControls := alignmentControls + 1
      let aliasIdentifier : FVarId := ⟨`projectionContractTypeAlias⟩
      let aliasLocals := ({} : LocalContext).mkLetDecl aliasIdentifier `alias (.sort (.succ .zero)) natural
      let aliasContext : Context := { context with lctx := aliasLocals }
      let aliasType := mkAppN (.const ``Prod [.zero, .zero]) #[.fvar aliasIdentifier, natural]
      let .ok (aliasResult, _) := Inner.inferProj ``Prod 0 pair aliasType methods aliasContext {}
        | throwError "trusted-type projection worker rejected the definitionally equal local alias"
      unless aliasResult == Expr.fvar aliasIdentifier do
        throwError "trusted-type projection worker no longer demonstrates its native dependency precondition"
      let .ok (checkedResult, _) := methods.inferType (.proj ``Prod 0 pair) false aliasContext {}
        | throwError "full projection checking rejected the closed pair"
      unless checkedResult == natural do
        throwError "full projection checking introduced an unused local alias"
      dependencyControls := dependencyControls + 1
  let invalidDeclaration := Declaration.defnDecl {
    name := `ProjectionInferenceContractTest.invalidTrustedType
    levelParams := []
    type := .forallE `source natural natural .default
    value := .lam `source natural (.proj ``Prod 0 (.bvar 0)) .default
    hints := .opaque
    safety := .safe }
  if (host.addDeclCore 0 invalidDeclaration none).isOk then
    throwError "native kernel accepted the mismatched-type projection control"
  logInfo m!"projection semantic contract: {accepted} cold/warm ordinary/dependent/Prop controls, {alignmentControls} trusted-type alignment controls, {dependencyControls} native dependency controls, native mismatched-type rejection"

run_meta
  nativeControls

run_meta
  let admitted ← collectAxioms ``Inner.inferProj.WF
  unless admitted.contains ``sorryAx do
    throwError "projection admission baseline unexpectedly changed"
  for theoremName in #[``projectionContract, ``projectionTypeAlignment] do
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless admitted.contains dependency do
        throwError "projection contract added dependency {dependency}"
  let scopeDependencies ← collectAxioms ``closedSourceCannotIntroduceLocal
  unless scopeDependencies.isEmpty do
    throwError "native dependency counterexample uses axioms: {repr scopeDependencies}"
  logInfo m!"projection inference remains admitted: {repr admitted}; corrected contract adds no dependencies"

end ProjectionInferenceContractTest
