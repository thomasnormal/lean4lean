import Lean4Lean.Theory.Typing.QuotHereditaryExtra
import Lean4Lean.Theory.Typing.QuotInjectivity

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private proofSpineType from Lean4Lean.Theory.Typing.QuotHereditaryExtra

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

include environmentWF in
/-- The source universes of definitionally equal quotient types agree. This
uses their actual sort typings and uniqueness, without quotient injectivity
or confluence. It does not assert injectivity of the two term parameters. -/
theorem quot_source_eq
    (registered : environment.constants ``Quot = some quotConst)
    (localsWF : OnCtx locals (environment.IsType universes))
    (equal : environment.IsDefEqU universes locals
      (.app (.app (.const ``Quot [leftUniverse]) leftDomain) leftRelation)
      (.app (.app (.const ``Quot [rightUniverse]) rightDomain) rightRelation)) :
    leftUniverse ≈ rightUniverse := by
  obtain ⟨_, equality⟩ := equal
  obtain ⟨_, levelsLeft, _, _, _, leftTyped⟩ :=
    quot_inv environmentWF localsWF registered equality.hasType.1
  obtain ⟨_, levelsRight, _, _, _, rightTyped⟩ :=
    quot_inv environmentWF localsWF registered equality.hasType.2
  cases List.cons.inj levelsLeft |>.1
  cases List.cons.inj levelsRight |>.1
  exact (((equality.toU.of_l environmentWF localsWF leftTyped).hasType.2).uniqU
    environmentWF localsWF rightTyped).sort_inv environmentWF localsWF

include environmentWF in
/-- Any proof inhabiting a quotient forces its source universe to be zero.
The quotient inhabitant may be neutral; no constructor shape is needed. -/
theorem quot_proof_source
    (registered : environment.constants ``Quot = some quotConst)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals major
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation))
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (proofTyped : environment.HasType universes locals major proposition) :
    zeroLike sourceUniverse = true := by
  have quotientProp := propositionTyped.defeqU_l environmentWF localsWF
    (proofTyped.uniqU environmentWF localsWF typed)
  obtain ⟨_, levels, _, _, _, quotientTyped⟩ :=
    quot_inv environmentWF localsWF registered quotientProp
  cases List.cons.inj levels |>.1
  exact (zeroLike_iff sourceUniverse).mpr
    ((quotientTyped.uniqU environmentWF localsWF quotientProp).sort_inv environmentWF localsWF)

include environmentWF in
/-- Recover the source universe of a constructor from its actual quotient
result type, even when the two parameter pairs differ syntactically. -/
theorem quotMk_source_eq
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (.app (.app (.app (.const ``Quot.mk [constructorUniverse]) constructorDomain)
        constructorRelation) value)
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation)) :
    sourceUniverse ≈ constructorUniverse := by
  obtain ⟨_, _, _, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  obtain ⟨_, levels, _, _, _, _, equal⟩ :=
    quotMk_inv environmentWF localsWF constructorRegistered typed
  cases List.cons.inj levels |>.1
  exact quot_source_eq (environmentWF := environmentWF) quotientRegistered localsWF equal

/-- Expose a major at a nonzero quotient source. The constructor alternative
contains the actual original-core path and all three normal capture relations.
The other alternative isolates the remaining semantic obligation: an actual
eta path would equate this quotient type with a Pi type. No separation theorem
or caller-supplied exposure certificate is assumed. -/
theorem normal_quot_major_expose
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (nonzero : zeroLike sourceUniverse = false)
    (typed : environment.HasType universes locals left
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation))
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left
      (.app (.app (.app (.const ``Quot.mk [constructorUniverse]) constructorDomain)
        constructorRelation) value)) :
    (∃ leftUniverse leftDomain leftRelation leftValue,
      @ParRedS (environmentWF.reductionParams universes) locals left
        (.app (.app (.app (.const ``Quot.mk [leftUniverse]) leftDomain) leftRelation) leftValue) ∧
      leftUniverse ≈ constructorUniverse ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftDomain constructorDomain ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftRelation constructorRelation ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftValue value ∧
      environment.HasType universes locals
        (.app (.app (.app (.const ``Quot.mk [leftUniverse]) leftDomain) leftRelation) leftValue)
        (.app (.app (.const ``Quot [sourceUniverse]) domain) relation)) ∨
    (∃ binder body codomain,
      @ParRedS (environmentWF.reductionParams universes) locals left (.lam binder body) ∧
      @NormalEq (environmentWF.reductionParams universes) locals (.lam binder body)
        (.app (.app (.app (.const ``Quot.mk [constructorUniverse]) constructorDomain)
          constructorRelation) value) ∧
      environment.HasType universes locals (.lam binder body)
        (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) ∧
      environment.IsDefEqU universes locals
        (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.forallE binder codomain)) := by
  letI := environmentWF.reductionParams universes
  have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
  obtain ⟨result, path, exposed⟩ := normal_spine_expose
    (arguments := [constructorDomain, constructorRelation, value]) localsWF normal
  have resultTyped := path.hasType localsWF typed
  cases exposed with
  | proof propositionTyped leftTyped rightTyped =>
    have zero := quot_proof_source (environmentWF := environmentWF) quotientRegistered localsWF resultTyped propositionTyped leftTyped
    simp only [nonzero, Bool.false_eq_true] at zero
  | @spine leftLevels leftArguments type arguments locals spineTyped heads argumentsNormal =>
    cases argumentsNormal with
    | cons domainNormal rest =>
      cases rest with
      | cons relationNormal rest =>
        cases rest with
        | cons valueNormal rest =>
          cases rest
          have levels : List.Forall₂ (· ≈ ·) leftLevels [constructorUniverse] := by
            cases heads with
            | refl => exact .cons rfl .nil
            | constDF _ _ _ _ equal => exact equal
            | proofIrrel propositionTyped leftProof rightProof =>
              have resultProp := proofSpineType (environmentWF := environmentWF) localsWF
                propositionTyped leftProof resultTyped
              have zero := quot_proof_source (environmentWF := environmentWF) quotientRegistered localsWF resultTyped
                resultProp resultTyped
              simp only [nonzero, Bool.false_eq_true] at zero
          cases levels with
          | cons levelEqual rest =>
            cases rest
            exact .inl ⟨_, _, _, _, path, levelEqual, domainNormal, relationNormal, valueNormal, resultTyped⟩
  | @lam arguments binder codomain body locals functionTyped bodyExposed =>
    have exposedNormal := (RigidSpine.lam functionTyped bodyExposed).normalEq localsWF
    have rightTyped := ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2
    exact .inr ⟨binder, body, codomain, path, exposedNormal, resultTyped,
      rightTyped.uniqU environmentWF localsWF functionTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
