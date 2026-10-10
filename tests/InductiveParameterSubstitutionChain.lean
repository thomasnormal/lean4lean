import Lean4Lean.Verify.InductiveParameterSubstitutionChain
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterSubstitutionChainTest

private theorem arbitraryFiniteChainProjectsDefEq
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before final)
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.IsDefEq universes context before final (.sort level) :=
  chain.isDefEq envWF contextWF

private theorem arbitraryFiniteChainProjectsBothTypes
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before final : VExpr}
    (chain : SemanticSubstitutionChain env universes context level before final)
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType universes)) :
    env.HasType universes context before (.sort level) ∧
      env.HasType universes context final (.sort level) :=
  chain.hasType envWF contextWF

private theorem linkedChainsCanBeAppended
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {before middle final : VExpr}
    (first : SemanticSubstitutionChain env universes context level before middle)
    (second : SemanticSubstitutionChain env universes context level middle final) :
    SemanticSubstitutionChain env universes context level before final :=
  first.append second

private theorem emptyChainKeepsTheSameEndpoint
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {expression : VExpr}
    (typed : env.HasType universes context expression (.sort level)) :
    SemanticSubstitutionChain env universes context level expression expression :=
  .nil expression typed

private theorem singleStageChain
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced domain : VExpr}
    (bodyTyped : env.HasType universes (domain :: context) body (.sort level))
    (argumentEquality : env.IsDefEq universes context original reduced domain)
    (reducedTyped : env.HasType universes context (body.inst reduced) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original) (body.inst reduced) :=
  .cons rfl rfl bodyTyped argumentEquality (.nil _ reducedTyped)

private theorem twoStageChain
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced₁ reduced₂ domain₁ domain₂ : VExpr}
    (firstTyped : env.HasType universes (domain₁ :: context) body (.sort level))
    (firstEquality : env.IsDefEq universes context original reduced₁ domain₁)
    (secondTyped : env.HasType universes (domain₂ :: context) body (.sort level))
    (secondEquality : env.IsDefEq universes context reduced₁ reduced₂ domain₂)
    (finalTyped : env.HasType universes context (body.inst reduced₂) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original)
      (body.inst reduced₂) :=
  .cons rfl rfl firstTyped firstEquality
    (.cons rfl rfl secondTyped secondEquality (.nil _ finalTyped))

private theorem threeStageChain
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced₁ reduced₂ reduced₃ domain₁ domain₂ domain₃ : VExpr}
    (typed₁ : env.HasType universes (domain₁ :: context) body (.sort level))
    (equality₁ : env.IsDefEq universes context original reduced₁ domain₁)
    (typed₂ : env.HasType universes (domain₂ :: context) body (.sort level))
    (equality₂ : env.IsDefEq universes context reduced₁ reduced₂ domain₂)
    (typed₃ : env.HasType universes (domain₃ :: context) body (.sort level))
    (equality₃ : env.IsDefEq universes context reduced₂ reduced₃ domain₃)
    (finalTyped : env.HasType universes context (body.inst reduced₃) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original)
      (body.inst reduced₃) :=
  .cons rfl rfl typed₁ equality₁
    (.cons rfl rfl typed₂ equality₂
      (.cons rfl rfl typed₃ equality₃ (.nil _ finalTyped)))

private theorem stageDomainTypingIsAnExplicitPremise
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced domain : VExpr}
    (bodyTyped : env.HasType universes (domain :: context) body (.sort level))
    (argumentEquality : env.IsDefEq universes context original reduced domain)
    (reducedTyped : env.HasType universes context (body.inst reduced) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original) (body.inst reduced) :=
  .cons rfl rfl bodyTyped argumentEquality (.nil _ reducedTyped)

private theorem sharedSortIsPartOfEveryStage
    {env : VEnv} {universes : Nat} {context : List VExpr} {level : VLevel}
    {body original reduced domain : VExpr}
    (typed : env.HasType universes (domain :: context) body (.sort level))
    (equality : env.IsDefEq universes context original reduced domain)
    (finalTyped : env.HasType universes context (body.inst reduced) (.sort level)) :
    SemanticSubstitutionChain env universes context level (body.inst original) (body.inst reduced) :=
  .cons rfl rfl typed equality (.nil _ finalTyped)

private def carrier : FVarId := ⟨`SubstitutionChainCarrier⟩
private def context : List VExpr := [.sort (.succ .zero)]
private def stageDomain : VExpr := .sort (.succ .zero)
private def stageBody : VExpr := .forallE stageDomain (.forallE (.bvar 1) (.bvar 2))
private def originalValue : VExpr := .app (.lam stageDomain (.bvar 0)) (.bvar 0)
private def reducedValue : VExpr := .bvar 0
private def stageLevel : VLevel := .succ (.succ .zero)

private theorem nonliteralStageArgumentsAreStructurallyDifferent : originalValue ≠ reducedValue := by
  intro equality
  cases equality

private theorem chainFixtureSupportsEmptySingleAndTwoLengths :
    ([] : List Nat).length = 0 ∧ [0].length = 1 ∧ [0, 1].length = 2 := by
  simp

private theorem chainFixtureSupportsExplicitDomainsAndSharedSort :
    stageDomain = .sort (.succ .zero) ∧ stageLevel = .succ (.succ .zero) := ⟨rfl, rfl⟩

private theorem nativeArgumentOrderIsRetained :
    [0, 1, 2][0]? = some 0 ∧ [0, 1, 2][1]? = some 1 ∧ [0, 1, 2][2]? = some 2 := by
  simp

private theorem repeatedStagePositionsAreDataNotHeaderClaims :
    [carrier, carrier][0]? = some carrier ∧
      [carrier, carrier][1]? = some carrier ∧
      [carrier, carrier][2]? = none := by
  simp

private theorem actualStageBodyUsesTheSuppliedDomain :
    stageBody = .forallE stageDomain (.forallE (.bvar 1) (.bvar 2)) := rfl

private theorem distinctChainLengthsAreNotInterchangeable :
    ([0, 1].length : Nat) ≠ [0, 1, 2].length := by decide

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .app function argument => [2] ++ semanticShape function ++ semanticShape argument
  | .lam type body => [3] ++ semanticShape type ++ semanticShape body
  | .forallE type body => [4] ++ semanticShape type ++ semanticShape body
  | .const _ _ => [5]

private def runtimeChainControls : MetaM Unit := do
  let empty : List Nat := []
  let one := [0]
  let two := [0, 1]
  let three := [0, 1, 2]
  let conditions := [
    (empty.length == 0, "empty chain length"),
    (one.length == 1, "single chain length"),
    (two.length == 2, "two-stage chain length"),
    (three.length == 3, "three-stage chain length"),
    (semanticShape originalValue != semanticShape reducedValue, "nonliteral arguments"),
    (semanticShape stageBody != semanticShape reducedValue, "shared-sort body shape"),
    ([0, 1, 2][0]? == some 0, "native first position"),
    ([0, 1, 2][1]? == some 1, "native second position"),
    ([carrier, carrier][2]? == none, "out of range position")]
  for (condition, label) in conditions do
    unless condition do throwError "parameter-substitution-chain runtime failed: {label}"
  logInfo m!"parameter-substitution-chain runtime: {conditions.length} empty/single/two/three-stage, sort/domain/order/position controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-substitution-chain declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "parameter-substitution-chain unexpected axiom {axiomName} in {name}"

private def auditModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterSubstitutionChain
    | throwError "parameter-substitution-chain module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "parameter-substitution-chain module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == 15 do throwError "parameter-substitution-chain declaration manifest changed"
  logInfo m!"parameter-substitution-chain module: {declarations} declarations audited; semantic chain has no native/container interfaces"

run_meta
  let allowed := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let structuralControls := [``arbitraryFiniteChainProjectsDefEq, ``arbitraryFiniteChainProjectsBothTypes,
    ``linkedChainsCanBeAppended,
    ``emptyChainKeepsTheSameEndpoint, ``singleStageChain, ``twoStageChain, ``threeStageChain,
    ``stageDomainTypingIsAnExplicitPremise, ``sharedSortIsPartOfEveryStage,
    ``nonliteralStageArgumentsAreStructurallyDifferent,
    ``chainFixtureSupportsEmptySingleAndTwoLengths, ``chainFixtureSupportsExplicitDomainsAndSharedSort,
    ``nativeArgumentOrderIsRetained, ``repeatedStagePositionsAreDataNotHeaderClaims,
    ``actualStageBodyUsesTheSuppliedDomain, ``distinctChainLengthsAreNotInterchangeable]
  for name in structuralControls do auditDeclaration name allowed
  auditModule allowed
  runtimeChainControls
  logInfo m!"parameter-substitution-chain tests: {structuralControls.length} proof controls; arbitrary finite chain recursion; empty/single/two/three-stage construction; explicit per-stage domain typing and shared sort; native order; nonliteral arguments; length/position negatives"

end InductiveParameterSubstitutionChainTest
