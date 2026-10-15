import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean.VEnv

private theorem instantiateLifted (expression argument : VExpr) (depth : Nat) :
    (expression.liftN (depth + 1)).inst argument depth = expression.liftN depth := by
  rw [Nat.add_comm depth 1, ← VExpr.liftN'_liftN_lo expression 1 depth, VExpr.inst_liftN]

private theorem instantiateLambdaEquality {environment : VEnv}
    (environmentWF : environment.WF) (localsWF : OnCtx locals (environment.IsType universes))
    (equal : environment.IsDefEqU universes locals (.lam domain first) (.lam domain second))
    (argumentTyped : environment.HasType universes locals argument domain) :
    environment.IsDefEqU universes locals (first.inst argument) (second.inst argument) := by
  obtain ⟨_, equality⟩ := equal
  obtain ⟨⟨_, domainTyped⟩, _, firstTyped⟩ := equality.hasType.1.lam_inv environmentWF.ordered localsWF
  obtain ⟨_, _, secondTyped⟩ := equality.hasType.2.lam_inv environmentWF.ordered localsWF
  have applied := (equality.toU.of_l environmentWF localsWF (.lam domainTyped firstTyped)).appDF argumentTyped
  exact (IsDefEq.beta firstTyped argumentTyped).symm.toU.trans environmentWF localsWF applied.toU
    |>.trans environmentWF localsWF (IsDefEq.beta secondTyped argumentTyped).toU

theorem quotLift_beta {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse targetUniverse : VLevel} {domain relation target function respect value : VExpr}
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
    (valueTyped : environment.HasType universes locals value domain) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect)
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value))
      (.app function value) target := by
  have levelsWF : ∀ level ∈ [sourceUniverse, targetUniverse], level.WF universes := by
    simpa using And.intro sourceUniverseWF targetUniverseWF
  have equality := (IsDefEq.extra0 registered (environmentWF.ordered.defEqWF registered)).instL levelsWF
    |>.weak0 environmentWF.ordered (Γ := locals) |>.toU
  simp [quotDefEq, VExpr.instL, VLevel.inst] at equality
  have first := instantiateLambdaEquality environmentWF localsWF equality domainTyped
  simp [VExpr.inst, VExpr.instVar] at first
  have second := instantiateLambdaEquality environmentWF localsWF first relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at second
  have third := instantiateLambdaEquality environmentWF localsWF second targetTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at third
  have fourth := instantiateLambdaEquality environmentWF localsWF third functionTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at fourth
  have fifth := instantiateLambdaEquality environmentWF localsWF fourth respectTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at fifth
  have sixth := instantiateLambdaEquality environmentWF localsWF fifth valueTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at sixth
  apply sixth.of_r environmentWF localsWF
  simpa only [VExpr.inst_lift] using functionTyped.app valueTyped

theorem quotMk_hasType {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse : VLevel} {domain relation value : VExpr}
    (registered : environment.constants ``Quot.mk = some quotMkConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (valueTyped : environment.HasType universes locals value domain) :
    environment.HasType universes locals
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  have levelsWF : ∀ level ∈ [sourceUniverse], level.WF universes := by
    simpa using sourceUniverseWF
  have constructorTyped := HasType.const registered levelsWF (by rfl) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at constructorTyped
  have constructorDomain := constructorTyped.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at constructorDomain
  have constructorRelation := constructorDomain.app relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at constructorRelation
  simpa [VExpr.inst_lift, VExpr.inst] using constructorRelation.app valueTyped

private theorem applicationArgumentTyped {environment : VEnv}
    (environmentWF : environment.WF) (localsWF : OnCtx locals (environment.IsType universes))
    (applicationTyped : environment.HasType universes locals (.app function argument) resultType)
    (functionTyped : environment.HasType universes locals function (.forallE domain codomain)) :
    environment.HasType universes locals argument domain := by
  obtain ⟨_, _, actualFunctionTyped, argumentTyped⟩ :=
    applicationTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨⟨_, domainEqual⟩, _⟩ :=
    (actualFunctionTyped.uniqU environmentWF localsWF functionTyped).forallE_inv
      environmentWF localsWF
  exact domainEqual.defeq argumentTyped

theorem quotMk_inv {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {levels : List VLevel} {domain relation value resultType : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants ``Quot.mk = some quotMkConst)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.const ``Quot.mk levels) domain) relation) value) resultType) :
    ∃ sourceUniverse, levels = [sourceUniverse] ∧ sourceUniverse.WF universes ∧
      environment.HasType universes locals domain (.sort sourceUniverse) ∧
      environment.HasType universes locals relation
        (.forallE domain (.forallE domain.lift (.sort .zero))) ∧
      environment.HasType universes locals value domain ∧
      environment.IsDefEqU universes locals resultType
        (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  obtain ⟨_, _, functionTyped, _⟩ := typed.app_inv environmentWF.ordered localsWF
  obtain ⟨_, _, partialTyped, _⟩ := functionTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨_, _, headTyped, _⟩ := partialTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨constant, lookup, levelsWF, arity⟩ :=
    headTyped.const_inv environmentWF.ordered localsWF
  rw [registered] at lookup
  cases lookup
  obtain ⟨sourceUniverse, rfl⟩ := List.length_eq_one_iff.mp arity
  have sourceUniverseWF : sourceUniverse.WF universes := levelsWF _ (by simp)
  have constructorTyped := HasType.const registered levelsWF (by rfl) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at constructorTyped
  have domainTyped := applicationArgumentTyped environmentWF localsWF partialTyped constructorTyped
  have constructorDomain := constructorTyped.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at constructorDomain
  have relationTyped := applicationArgumentTyped environmentWF localsWF functionTyped constructorDomain
  have constructorRelation := constructorDomain.app relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at constructorRelation
  have valueTyped := applicationArgumentTyped environmentWF localsWF typed constructorRelation
  exact ⟨sourceUniverse, rfl, sourceUniverseWF, domainTyped, relationTyped, valueTyped,
    typed.uniqU environmentWF localsWF
      (quotMk_hasType registered sourceUniverseWF domainTyped relationTyped valueTyped)⟩

theorem quotInd_beta {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse : VLevel} {domain relation motive minor value : VExpr}
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
    (valueTyped : environment.HasType universes locals value domain) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.const ``Quot.ind [sourceUniverse]) domain) relation) motive) minor)
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value))
      (.app minor value)
      (.app motive (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)) := by
  have levelsWF : ∀ level ∈ [sourceUniverse], level.WF universes := by
    simpa using sourceUniverseWF
  have constructorValue := quotMk_hasType constructorRegistered sourceUniverseWF
    domainTyped relationTyped valueTyped
  have inductionTyped := HasType.const inductionRegistered levelsWF (by rfl) (Γ := locals)
  simp [quotIndConst, VExpr.instL, VLevel.inst] at inductionTyped
  have inductionDomain := inductionTyped.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at inductionDomain
  have inductionRelation := inductionDomain.app relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at inductionRelation
  have inductionMotive := inductionRelation.app motiveTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at inductionMotive
  have inductionMinor := inductionMotive.app minorTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at inductionMinor
  have inductionValue := inductionMinor.app constructorValue
  simp [VExpr.inst_lift, VExpr.inst, VExpr.instVar] at inductionValue
  have minorValue := minorTyped.app valueTyped
  simp [VExpr.inst_lift, VExpr.inst, VExpr.instVar] at minorValue
  exact .proofIrrel (by simpa only [VExpr.inst] using motiveTyped.app constructorValue)
    inductionValue minorValue

end Lean4Lean.VEnv
