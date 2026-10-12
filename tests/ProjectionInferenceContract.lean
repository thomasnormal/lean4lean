import Lean4Lean.Verify.TypeChecker.ScopedInferType
import Lean.Util.CollectAxioms

namespace ProjectionInferenceContractTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private structure DependentPair where
  value : Nat
  proof : value = value

private def dependentValue : DependentPair := ⟨7, rfl⟩

private def ignoredHeader : InductiveVal := {
  name := `IgnoredProjectionHeader
  levelParams := []
  type := .sort (.succ .zero)
  numParams := 0
  numIndices := 0
  numNested := 0
  all := [`IgnoredProjectionHeader]
  ctors := []
  isRec := false
  isReflexive := false
  isUnsafe := true }

private theorem ignoredInductiveSupported :
    TrEnv' .safe (({} : ConstMap).insert ignoredHeader.name (.inductInfo ignoredHeader))
      false VEnv.empty :=
  .ignoreConst (C := {}) (ci := .inductInfo ignoredHeader)
    (by simp [SMap.find?]) (by decide) .empty

example : ({} : VEnv).constants ignoredHeader.name = none := rfl

example (valid : TrEnv safety native environment)
    (found : native.find? name = some (.inductInfo header)) : ¬environment.contains name :=
  valid.inductiveNotInModel found

example {context : VContext} {state : VState} {parent : Name} {index : Nat}
    {source suppliedType : Expr} {semanticType : VExpr}
    (translated : context.TrExprS suppliedType semanticType) :
    (Inner.inferProj parent index source suppliedType).WF context state (fun _ _ => False) :=
  Inner.inferProj.rejects translated

example {context : VContext} {state : VState} {parent : Name} {index : Nat}
    {source suppliedType : Expr} {semantic semanticType : VExpr}
    (typed : context.TrTyping source suppliedType semantic semanticType) :
    (Inner.inferProj parent index source suppliedType).ScopeWF context state
      (fun inferred _ => ∃ projected resultType,
        context.TrTyping (.proj parent index source) inferred projected resultType) :=
  Inner.inferProj.scopeWF typed

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
  let environment ← getEnv
  let baseline ← collectAxioms ``Inner.inferType'.WF
  for theoremName in #[``TrEnv'.inductiveLookupRejected, ``TrEnv.inductiveLookupRejected,
      ``TrEnv.inductiveNotInModel, ``Inner.inferProj.rejects, ``Inner.inferProj.WF,
      ``Inner.inferProj.scopeWF, ``RecM.ScopeWF.of_rejects] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "projection axiom {theoremName}"
    let some proof := information.value? | throwError "projection proof absent {theoremName}"
    if proof.hasSorry then throwError "projection proof admission {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected projection dependency {dependency} in {theoremName}"
  let some modelModule := environment.getModuleIdx? `Lean4Lean.Verify.Environment.Lemmas
    | throwError "projection environment module absent"
  for (theoremName, information) in environment.constants do
    if environment.getModuleIdxFor? theoremName == some modelModule then
      if information matches .axiomInfo _ then throwError "owned environment axiom {theoremName}"
      if let some proof := information.value? then
        if proof.hasSorry then throwError "owned environment admission {theoremName}"
  for theoremName in #[``projectionContract, ``projectionTypeAlignment] do
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "projection contract added dependency {dependency}"
  let scopeDependencies ← collectAxioms ``closedSourceCannotIntroduceLocal
  unless scopeDependencies.isEmpty do
    throwError "native dependency counterexample uses axioms: {repr scopeDependencies}"
  logInfo m!"projection inference is proved by rejection in the current TrEnv fragment; owned proof bodies have no admissions; inherited semantic/native baseline remains explicit: {repr baseline}"

end ProjectionInferenceContractTest
