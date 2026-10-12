import Lean4Lean.Theory.Typing.QuotReduction

namespace Lean4Lean.VEnv

private theorem instantiateLifted (expression argument : VExpr) (depth : Nat) :
    (expression.liftN (depth + 1)).inst argument depth = expression.liftN depth := by
  rw [Nat.add_comm depth 1, ← VExpr.liftN'_liftN_lo expression 1 depth, VExpr.inst_liftN]

theorem quotMk_congr {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse constructorUniverse : VLevel}
    {domain relation value constructorDomain constructorRelation constructorValue : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants ``Quot.mk = some quotMkConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (constructorUniverseWF : constructorUniverse.WF universes)
    (universeEqual : sourceUniverse ≈ constructorUniverse)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (valueTyped : environment.HasType universes locals value domain)
    (domainEqual : environment.IsDefEqU universes locals constructorDomain domain)
    (relationEqual : environment.IsDefEqU universes locals constructorRelation relation)
    (valueEqual : environment.IsDefEqU universes locals constructorValue value) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.const ``Quot.mk [constructorUniverse]) constructorDomain)
        constructorRelation) constructorValue)
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  have sourceLevelsWF : ∀ level ∈ [sourceUniverse], level.WF universes := by
    simpa using sourceUniverseWF
  have constructorLevelsWF : ∀ level ∈ [constructorUniverse], level.WF universes := by
    simpa using constructorUniverseWF
  have constructorEqual := IsDefEq.constDF registered sourceLevelsWF constructorLevelsWF
    (by rfl) (.cons universeEqual .nil) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at constructorEqual
  have constructorDomainEqual := constructorEqual.appDF
    (domainEqual.of_r environmentWF localsWF domainTyped).symm
  simp [VExpr.inst, VExpr.instVar] at constructorDomainEqual
  have constructorRelationEqual := constructorDomainEqual.appDF
    (relationEqual.of_r environmentWF localsWF relationTyped).symm
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at constructorRelationEqual
  have constructorValueEqual := constructorRelationEqual.appDF
    (valueEqual.of_r environmentWF localsWF valueTyped).symm
  simpa [VExpr.inst_lift, VExpr.inst] using constructorValueEqual.symm

private theorem applicationArgumentEqual {environment : VEnv}
    (environmentWF : environment.WF) (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (.app function canonical) resultType)
    (equal : environment.IsDefEqU universes locals actual canonical) :
    environment.IsDefEqU universes locals (.app function actual) (.app function canonical) := by
  obtain ⟨_, _, functionTyped, canonicalTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  exact (functionTyped.appDF (equal.of_r environmentWF localsWF canonicalTyped)).toU

theorem quotLift_beta_of_majorEq {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse targetUniverse : VLevel}
    {domain relation target function respect value major : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (targetUniverseWF : targetUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (targetTyped : environment.HasType universes locals target (.sort targetUniverse))
    (functionTyped : environment.HasType universes locals function (.forallE domain target.lift))
    (respectTyped : environment.HasType universes locals respect
      (.forallE domain (.forallE domain.lift
        (.forallE (.app (.app (relation.liftN 2) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const ``Eq [targetUniverse]) (target.liftN 3))
            (.app (function.liftN 3) (.bvar 2))) (.app (function.liftN 3) (.bvar 1)))))))
    (valueTyped : environment.HasType universes locals value domain)
    (majorEqual : environment.IsDefEqU universes locals major
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major)
      (.app function value) target := by
  have canonical := quotLift_beta environmentWF localsWF registered sourceUniverseWF
    targetUniverseWF domainTyped relationTyped targetTyped functionTyped respectTyped valueTyped
  have transported := applicationArgumentEqual environmentWF localsWF canonical.hasType.1 majorEqual
  exact (transported.trans environmentWF localsWF canonical.toU).of_r environmentWF localsWF
    canonical.hasType.2

theorem quotInd_beta_of_majorEq {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse : VLevel} {domain relation motive minor value major : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (constructorRegistered : environment.constants ``Quot.mk = some quotMkConst)
    (inductionRegistered : environment.constants ``Quot.ind = some quotIndConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (motiveTyped : environment.HasType universes locals motive
      (.forallE (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.sort .zero)))
    (minorTyped : environment.HasType universes locals minor
      (.forallE domain (.app motive.lift
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain.lift) relation.lift) (.bvar 0)))))
    (valueTyped : environment.HasType universes locals value domain)
    (majorEqual : environment.IsDefEqU universes locals major
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind [sourceUniverse]) domain) relation) motive) minor)
        major)
      (.app minor value) (.app motive major) := by
  have constructorTyped := quotMk_hasType constructorRegistered sourceUniverseWF
    domainTyped relationTyped valueTyped
  have canonical := quotInd_beta constructorRegistered inductionRegistered sourceUniverseWF
    domainTyped relationTyped motiveTyped minorTyped valueTyped
  have transported := applicationArgumentEqual environmentWF localsWF canonical.hasType.1 majorEqual
  have reduction := (transported.trans environmentWF localsWF canonical.toU).of_r
    environmentWF localsWF canonical.hasType.2
  exact .defeqDF (by
    simpa only [VExpr.inst] using
      (motiveTyped.appDF (majorEqual.of_r environmentWF localsWF constructorTyped)).symm) reduction

end Lean4Lean.VEnv
