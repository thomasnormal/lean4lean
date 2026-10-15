import Lean4Lean.Theory.Typing.ConcreteReduction

namespace Lean4Lean.VEnv

variable {environment : VEnv}

private def sortTelescope : VExpr → Prop
  | .sort _ => True
  | .forallE _ body => sortTelescope body
  | _ => False

private theorem sortTelescopeNotProp (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (shape : sortTelescope expression)
    (typed : environment.HasType universes locals expression (.sort .zero)) : False := by
  induction expression generalizing locals with
  | sort level =>
    have levelWF := typed.sort_inv environmentWF.ordered
    have equal := (typed.uniqU environmentWF localsWF (HasType.sort levelWF)).sort_inv
      environmentWF localsWF
    have evaluated := VLevel.equiv_def.mp equal []
    exact Nat.noConfusion evaluated
  | forallE domain body domainIH bodyIH =>
    obtain ⟨⟨domainUniverse, domainTyped⟩, bodyUniverse, bodyTyped⟩ :=
      typed.forallE_inv environmentWF.ordered
    have equal := (typed.uniqU environmentWF localsWF (HasType.forallE domainTyped bodyTyped)).sort_inv
      environmentWF localsWF
    have bodyZero : bodyUniverse ≈ .zero := VLevel.equiv_def.mpr fun values => by
      change bodyUniverse.eval values = 0
      have evaluated := VLevel.equiv_def.mp equal values
      change 0 = Nat.imax (domainUniverse.eval values) (bodyUniverse.eval values) at evaluated
      cases bodyValue : bodyUniverse.eval values with
      | zero => rfl
      | succ value =>
        simp only [Nat.imax, bodyValue, Nat.succ_ne_zero, if_false] at evaluated
        have bound := Nat.le_max_right (domainUniverse.eval values) (value + 1)
        exact Nat.le_zero.mp (Nat.le_trans bound (Nat.le_of_eq evaluated.symm))
    have extendedWF : OnCtx (domain :: locals) (environment.IsType universes) :=
      ⟨localsWF, _, domainTyped⟩
    obtain ⟨_, bodySortTyped⟩ := bodyTyped.isType environmentWF.ordered extendedWF
    have bodyUniverseWF := bodySortTyped.sort_inv environmentWF.ordered
    exact bodyIH extendedWF shape (.defeqDF (.sortDF bodyUniverseWF (by trivial) bodyZero) bodyTyped)
  | _ => cases shape

private theorem notProofOfSortTelescope (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (shape : sortTelescope type)
    (typed : environment.HasType universes locals expression type)
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (proofTyped : environment.HasType universes locals expression proposition) : False := by
  have equal := proofTyped.uniqU environmentWF localsWF typed
  exact sortTelescopeNotProp environmentWF localsWF shape
    (propositionTyped.defeqU_l environmentWF localsWF equal)

private theorem applicationArgumentTyped (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (applicationTyped : environment.HasType universes locals (.app function argument) resultType)
    (functionTyped : environment.HasType universes locals function (.forallE domain codomain)) :
    environment.HasType universes locals argument domain := by
  obtain ⟨_, _, actualFunctionTyped, argumentTyped⟩ :=
    applicationTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨⟨_, domainEqual⟩, _⟩ :=
    (actualFunctionTyped.uniqU environmentWF localsWF functionTyped).forallE_inv
      environmentWF localsWF
  exact domainEqual.defeq argumentTyped

private theorem quotDomainTyping (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants ``Quot = some quotConst)
    (typed : environment.HasType universes locals (.app (.const ``Quot levels) domain) resultType) :
    ∃ sourceUniverse, levels = [sourceUniverse] ∧ sourceUniverse.WF universes ∧
      environment.HasType universes locals domain (.sort sourceUniverse) ∧
      environment.HasType universes locals (.app (.const ``Quot levels) domain)
        (.forallE (.forallE domain (.forallE domain.lift (.sort .zero))) (.sort sourceUniverse)) := by
  obtain ⟨_, _, headTyped, _⟩ := typed.app_inv environmentWF.ordered localsWF
  obtain ⟨constant, lookup, levelsWF, arity⟩ := headTyped.const_inv environmentWF.ordered localsWF
  rw [registered] at lookup
  cases lookup
  obtain ⟨sourceUniverse, rfl⟩ := List.length_eq_one_iff.mp arity
  have canonical := HasType.const registered levelsWF (by rfl) (Γ := locals)
  simp [quotConst, VExpr.instL, VLevel.inst] at canonical
  have domainTyped := applicationArgumentTyped environmentWF localsWF typed canonical
  refine ⟨sourceUniverse, rfl, levelsWF _ (by simp), domainTyped, ?_⟩
  simpa [VExpr.inst, VExpr.instVar] using canonical.app domainTyped

theorem quot_inv (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants ``Quot = some quotConst)
    (typed : environment.HasType universes locals
      (.app (.app (.const ``Quot levels) domain) relation) resultType) :
    ∃ sourceUniverse, levels = [sourceUniverse] ∧ sourceUniverse.WF universes ∧
      environment.HasType universes locals domain (.sort sourceUniverse) ∧
      environment.HasType universes locals relation
        (.forallE domain (.forallE domain.lift (.sort .zero))) ∧
      environment.HasType universes locals
        (.app (.app (.const ``Quot levels) domain) relation) (.sort sourceUniverse) := by
  obtain ⟨_, _, partialTyped, _⟩ := typed.app_inv environmentWF.ordered localsWF
  obtain ⟨sourceUniverse, levelsEqual, sourceUniverseWF, domainTyped, canonical⟩ :=
    quotDomainTyping environmentWF localsWF registered partialTyped
  have relationTyped := applicationArgumentTyped environmentWF localsWF typed canonical
  exact ⟨sourceUniverse, levelsEqual, sourceUniverseWF, domainTyped, relationTyped,
    by simpa [VExpr.inst] using canonical.app relationTyped⟩

private theorem quotHeadNotMatched (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (rule : RewriteRule environment pattern result)
    (matched : pattern.Matches (.const ``Quot levels) levelValues expressionValues) : False := by
  cases rule with
  | delta closed definitionRegistered =>
    change (Pattern.const _).Matches _ _ _ at matched
    generalize nameEqual : VConstVal.name _ = name at matched
    cases matched
    exact environmentWF.rewriteMetadata.quotientNames definitionRegistered registered
      ``Quot (by simp) nameEqual
  | quot => cases matched

private theorem quotDomainNotMatched
    (rule : RewriteRule environment pattern result)
    (matched : pattern.Matches (.app (.const ``Quot levels) domain)
      levelValues expressionValues) : False := by
  cases rule with
  | delta => cases matched
  | quot =>
    cases matched with
    | app functionMatched _ => cases functionMatched

private theorem quotTypeNotMatched
    (rule : RewriteRule environment pattern result)
    (matched : pattern.Matches (.app (.app (.const ``Quot levels) domain) relation)
      levelValues expressionValues) : False := by
  cases rule with
  | delta => cases matched
  | quot =>
    cases matched with
    | app functionMatched _ =>
      cases functionMatched with
      | var previous => cases previous

section
variable {environment : VEnv} (environmentWF : environment.WF) (universes : Nat)

theorem ParRed.quot_head (registered : environment.defeqs quotDefEq)
    (reduced : @ParRed (environmentWF.reductionParams universes) locals
      (.const ``Quot levels) result) : result = .const ``Quot levels := by
  letI := environmentWF.reductionParams universes
  cases reduced with
  | const => rfl
  | extra rule matched => exact False.elim (quotHeadNotMatched environmentWF registered rule matched)

theorem ParRed.quot_domain (registered : environment.defeqs quotDefEq)
    (reduced : @ParRed (environmentWF.reductionParams universes) locals
      (.app (.const ``Quot levels) domain) result) :
    ∃ domain', result = .app (.const ``Quot levels) domain' ∧
      @ParRed (environmentWF.reductionParams universes) locals domain domain' := by
  letI := environmentWF.reductionParams universes
  cases reduced with
  | app functionReduced domainReduced =>
    cases functionReduced.quot_head environmentWF universes registered
    exact ⟨_, rfl, domainReduced⟩
  | extra rule matched => exact False.elim (quotDomainNotMatched rule matched)

theorem ParRed.quot_type (registered : environment.defeqs quotDefEq)
    (reduced : @ParRed (environmentWF.reductionParams universes) locals
      (.app (.app (.const ``Quot levels) domain) relation) result) :
    ∃ domain' relation', result = .app (.app (.const ``Quot levels) domain') relation' ∧
      @ParRed (environmentWF.reductionParams universes) locals domain domain' ∧
      @ParRed (environmentWF.reductionParams universes) locals relation relation' := by
  letI := environmentWF.reductionParams universes
  cases reduced with
  | app functionReduced relationReduced =>
    obtain ⟨domain', rfl, domainReduced⟩ :=
      functionReduced.quot_domain environmentWF universes registered
    exact ⟨domain', _, rfl, domainReduced, relationReduced⟩
  | extra rule matched => exact False.elim (quotTypeNotMatched rule matched)

theorem ParRedS.quot_type (registered : environment.defeqs quotDefEq)
    (reduced : @ParRedS (environmentWF.reductionParams universes) locals
      (.app (.app (.const ``Quot levels) domain) relation) result) :
    ∃ domain' relation', result = .app (.app (.const ``Quot levels) domain') relation' ∧
      @ParRedS (environmentWF.reductionParams universes) locals domain domain' ∧
      @ParRedS (environmentWF.reductionParams universes) locals relation relation' := by
  letI := environmentWF.reductionParams universes
  induction reduced with
  | rfl => exact ⟨domain, relation, rfl, .rfl, .rfl⟩
  | tail previous step inductionHypothesis =>
    obtain ⟨previousDomain, previousRelation, rfl, domainReduced, relationReduced⟩ := inductionHypothesis
    obtain ⟨domain', relation', rfl, domainStep, relationStep⟩ :=
      step.quot_type environmentWF universes registered
    exact ⟨domain', relation', rfl, .tail domainReduced domainStep, .tail relationReduced relationStep⟩

theorem NormalEq.quot_head
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (equal : @NormalEq (environmentWF.reductionParams universes) locals
      (.const ``Quot leftLevels) (.const ``Quot rightLevels)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels := by
  letI := environmentWF.reductionParams universes
  cases equal with
  | refl => exact .rfl fun _ _ => rfl
  | constDF _ _ _ _ levelsEqual => exact levelsEqual
  | proofIrrel propositionTyped proofTyped _ =>
    obtain ⟨constant, lookup, levelsWF, arity⟩ := proofTyped.const_inv environmentWF.ordered localsWF
    have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
    rw [quotientRegistered] at lookup
    cases lookup
    exact False.elim (notProofOfSortTelescope environmentWF localsWF
      (by trivial) (HasType.const quotientRegistered levelsWF arity) propositionTyped proofTyped)

theorem NormalEq.quot_domain
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (equal : @NormalEq (environmentWF.reductionParams universes) locals
      (.app (.const ``Quot leftLevels) leftDomain)
      (.app (.const ``Quot rightLevels) rightDomain)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftDomain rightDomain := by
  letI := environmentWF.reductionParams universes
  have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
  cases equal with
  | refl typed =>
    obtain ⟨_, _, _, domainTyped, _⟩ := quotDomainTyping environmentWF localsWF quotientRegistered typed
    exact ⟨.rfl fun _ _ => rfl, .refl domainTyped⟩
  | appDF _ _ _ _ functionEqual domainEqual =>
    exact ⟨functionEqual.quot_head environmentWF universes localsWF registered, domainEqual⟩
  | proofIrrel propositionTyped proofTyped _ =>
    obtain ⟨_, _, _, _, canonical⟩ := quotDomainTyping environmentWF localsWF quotientRegistered proofTyped
    exact False.elim (notProofOfSortTelescope environmentWF localsWF (by trivial)
      canonical propositionTyped proofTyped)

theorem NormalEq.quot_type
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (equal : @NormalEq (environmentWF.reductionParams universes) locals
      (.app (.app (.const ``Quot leftLevels) leftDomain) leftRelation)
      (.app (.app (.const ``Quot rightLevels) rightDomain) rightRelation)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftDomain rightDomain ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftRelation rightRelation := by
  letI := environmentWF.reductionParams universes
  have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
  cases equal with
  | refl typed =>
    obtain ⟨_, _, _, domainTyped, relationTyped, _⟩ := quot_inv environmentWF localsWF quotientRegistered typed
    exact ⟨.rfl fun _ _ => rfl, .refl domainTyped, .refl relationTyped⟩
  | appDF _ _ _ _ functionEqual relationEqual =>
    obtain ⟨levelsEqual, domainEqual⟩ := functionEqual.quot_domain environmentWF universes localsWF registered
    exact ⟨levelsEqual, domainEqual, relationEqual⟩
  | proofIrrel propositionTyped proofTyped _ =>
    obtain ⟨_, _, _, _, _, canonical⟩ := quot_inv environmentWF localsWF quotientRegistered proofTyped
    exact False.elim (notProofOfSortTelescope environmentWF localsWF (by trivial)
      canonical propositionTyped proofTyped)

include environmentWF in
theorem IsDefEqU.quot_inj
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (equal : environment.IsDefEqU universes locals
      (.app (.app (.const ``Quot leftLevels) leftDomain) leftRelation)
      (.app (.app (.const ``Quot rightLevels) rightDomain) rightRelation)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      environment.IsDefEqU universes locals leftDomain rightDomain ∧
      environment.IsDefEqU universes locals leftRelation rightRelation := by
  letI := environmentWF.reductionParams universes
  obtain ⟨_, equality⟩ := equal
  have quotientRegistered := (environmentWF.quotientObjects registered).2.2.2.2.1
  obtain ⟨_, _, _, leftDomainTyped, leftRelationTyped, _⟩ :=
    quot_inv environmentWF localsWF quotientRegistered equality.hasType.1
  obtain ⟨_, _, _, rightDomainTyped, rightRelationTyped, _⟩ :=
    quot_inv environmentWF localsWF quotientRegistered equality.hasType.2
  obtain ⟨_, _, _, _, leftReduced, rightReduced, normalEqual⟩ := equality.church_rosser localsWF
  obtain ⟨_, _, rfl, leftDomainReduced, leftRelationReduced⟩ :=
    leftReduced.quot_type environmentWF universes registered
  obtain ⟨_, _, rfl, rightDomainReduced, rightRelationReduced⟩ :=
    rightReduced.quot_type environmentWF universes registered
  obtain ⟨levelsEqual, domainsEqual, relationsEqual⟩ :=
    normalEqual.quot_type environmentWF universes localsWF registered
  exact ⟨levelsEqual,
    (leftDomainReduced.defeq localsWF leftDomainTyped).toU.trans environmentWF localsWF
      ((domainsEqual.defeq localsWF).trans environmentWF localsWF
        (rightDomainReduced.defeq localsWF rightDomainTyped).symm.toU),
    (leftRelationReduced.defeq localsWF leftRelationTyped).toU.trans environmentWF localsWF
      ((relationsEqual.defeq localsWF).trans environmentWF localsWF
        (rightRelationReduced.defeq localsWF rightRelationTyped).symm.toU)⟩

end
end Lean4Lean.VEnv
