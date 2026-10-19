import Lean4Lean.Theory.Typing.QuotObjects
import Lean4Lean.Theory.Typing.QuotPattern
import Lean4Lean.Theory.Typing.QuotReductionAlignment

namespace Lean4Lean

theorem VEnv.quotLift_beta_of_checkedParameters {environment : VEnv}
    {locals : List VExpr} {universes : Nat}
    {levels constructorLevels : List VLevel}
    {domain relation target function respect constructorDomain constructorRelation value resultType : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (equationRegistered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value)) resultType)
    (domainEqual : environment.IsDefEqU universes locals constructorDomain domain)
    (relationEqual : environment.IsDefEqU universes locals constructorRelation relation) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value))
      (.app function value) resultType := by
  have objects := environmentWF.quotientObjects equationRegistered
  obtain ⟨sourceUniverse, targetUniverse, rfl, sourceUniverseWF, targetUniverseWF,
    domainTyped, relationTyped, targetTyped, functionTyped, respectTyped, majorTyped, resultEqual⟩ :=
      VEnv.quotLift_inv environmentWF localsWF objects.2.2.1 typed
  obtain ⟨constructorUniverse, rfl, constructorUniverseWF, constructorDomainTyped, _, valueTyped, _⟩ :=
    VEnv.quotMk_inv environmentWF localsWF objects.2.2.2.1 majorTyped
  have domains := domainEqual.of_l environmentWF localsWF constructorDomainTyped
  have universeEqual := (domainTyped.uniqU environmentWF localsWF domains.hasType.2).sort_inv
    environmentWF localsWF
  have alignedValue := domains.defeq valueTyped
  have constructorEqual := VEnv.quotMk_congr environmentWF localsWF objects.2.2.2.1
    sourceUniverseWF constructorUniverseWF universeEqual domainTyped relationTyped alignedValue
    domainEqual relationEqual alignedValue.toU
  have reduction := VEnv.quotLift_beta_of_majorEq environmentWF localsWF equationRegistered
    sourceUniverseWF targetUniverseWF domainTyped relationTyped targetTyped functionTyped
    respectTyped alignedValue constructorEqual.toU
  exact resultEqual.symm.defeqDF environmentWF localsWF reduction

theorem quotLiftPattern.sound {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {expression resultType : VExpr} {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (equationRegistered : environment.defeqs quotDefEq)
    (matched : quotLiftPattern.Matches expression levels values)
    (typed : environment.HasType universes locals expression resultType)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values) :
    environment.IsDefEq universes locals expression
      (quotLiftPatternResult.apply levels values) resultType := by
  let .app functionMatched constructorMatched := matched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .const := functionMatched
  let .var constructorMatched := constructorMatched
  let .var constructorMatched := constructorMatched
  let .var constructorMatched := constructorMatched
  let .const := constructorMatched
  simp only [quotLiftPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at checked
  exact VEnv.quotLift_beta_of_checkedParameters environmentWF localsWF equationRegistered
    typed checked.1.symm checked.2.1.symm

end Lean4Lean
