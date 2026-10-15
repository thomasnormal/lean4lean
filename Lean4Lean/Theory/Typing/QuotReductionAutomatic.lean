import Lean4Lean.Theory.Typing.QuotInjectivity

namespace Lean4Lean.VEnv

variable {environment : VEnv}

theorem quotLift_beta_of_typed
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value)) resultType) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value))
      (.app function value) resultType := by
  have objects := environmentWF.quotientObjects registered
  obtain ⟨_, _, _, _, _, _, _, _, _, _, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF objects.2.2.1 typed
  obtain ⟨_, _, _, _, _, _, quotientTypesEqual⟩ :=
    quotMk_inv environmentWF localsWF objects.2.2.2.1 majorTyped
  obtain ⟨_, domainsEqual, relationsEqual⟩ :=
    quotientTypesEqual.quot_inj environmentWF universes localsWF registered
  exact quotLift_beta_of_checkedParameters environmentWF localsWF registered typed
    domainsEqual.symm relationsEqual.symm

theorem quotInd_beta_of_typed
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
        domain) relation) motive) minor)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value)) resultType) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
        domain) relation) motive) minor)
          (.app (.app (.app (.const ``Quot.mk constructorLevels)
            constructorDomain) constructorRelation) value))
      (.app minor value) resultType := by
  have objects := environmentWF.quotientObjects registered
  obtain ⟨sourceUniverse, rfl, sourceUniverseWF, domainTyped, relationTyped,
    motiveTyped, minorTyped, majorTyped, resultEqual⟩ :=
      quotInd_inv environmentWF localsWF objects.2.1 typed
  obtain ⟨constructorUniverse, rfl, constructorUniverseWF, _, _, valueTyped, quotientTypesEqual⟩ :=
    quotMk_inv environmentWF localsWF objects.2.2.2.1 majorTyped
  obtain ⟨levelsEqual, domainsEqual, relationsEqual⟩ :=
    quotientTypesEqual.quot_inj environmentWF universes localsWF registered
  cases levelsEqual with
  | cons universeEqual _ =>
    have alignedValue := (domainsEqual.symm.of_r environmentWF localsWF domainTyped).defeq valueTyped
    have constructorEqual := quotMk_congr environmentWF localsWF objects.2.2.2.1
      sourceUniverseWF constructorUniverseWF universeEqual domainTyped relationTyped alignedValue
      domainsEqual.symm relationsEqual.symm alignedValue.toU
    have reduction := quotInd_beta_of_majorEq environmentWF localsWF objects.2.2.2.1 objects.2.1
      sourceUniverseWF domainTyped relationTyped motiveTyped minorTyped alignedValue constructorEqual.toU
    exact resultEqual.symm.defeqDF environmentWF localsWF reduction

theorem quotLift_beta_of_normalizedMajor
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect) major) resultType)
    (majorEqual : environment.IsDefEqU universes locals major
      (.app (.app (.app (.const ``Quot.mk constructorLevels)
        constructorDomain) constructorRelation) value)) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect) major)
      (.app function value) resultType := by
  obtain ⟨_, _, functionTyped, majorTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  have transported := functionTyped.appDF (majorEqual.of_l environmentWF localsWF majorTyped)
  exact typed.trans_l environmentWF localsWF (transported.trans
    (quotLift_beta_of_typed environmentWF localsWF registered transported.hasType.2))

theorem quotInd_beta_of_normalizedMajor
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
        domain) relation) motive) minor) major) resultType)
    (majorEqual : environment.IsDefEqU universes locals major
      (.app (.app (.app (.const ``Quot.mk constructorLevels)
        constructorDomain) constructorRelation) value)) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
        domain) relation) motive) minor) major)
      (.app minor value) resultType := by
  obtain ⟨_, _, functionTyped, majorTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  have transported := functionTyped.appDF (majorEqual.of_l environmentWF localsWF majorTyped)
  exact typed.trans_l environmentWF localsWF (transported.trans
    (quotInd_beta_of_typed environmentWF localsWF registered transported.hasType.2))

end Lean4Lean.VEnv
