import Lean4Lean.Theory.Typing.RewriteRules
import Lean4Lean.Theory.Typing.ChurchRosser

namespace Lean4Lean.VEnv

variable {environment : VEnv}

private theorem spineSubpattern (subpattern : Subpattern pattern (.varN (.const name) count)) :
    ∃ subcount, subcount ≤ count ∧ pattern = .varN (.const name) subcount := by
  induction count with
  | zero => cases subpattern; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ count inductionHypothesis =>
    cases subpattern with
    | refl => exact ⟨count + 1, Nat.le_refl _, rfl⟩
    | varL previous =>
      obtain ⟨subcount, bound, equal⟩ := inductionHypothesis previous
      exact ⟨subcount, by omega, equal⟩

private theorem spineIntersection (first second : Lean.Name) (left right : Nat) :
    (Pattern.varN (.const first) left).inter (.varN (.const second) right) =
      if first = second ∧ left = right then some (.varN (.const first) left) else none := by
  induction left generalizing right with
  | zero =>
    cases right with
    | zero => simp only [Pattern.varN, Pattern.inter, eq_self, and_true]
    | succ right =>
      rw [if_neg (by intro equal; cases equal.2)]
      rfl
  | succ left inductionHypothesis =>
    cases right with
    | zero =>
      rw [if_neg (by intro equal; cases equal.2)]
      rfl
    | succ right =>
      simp only [Pattern.varN, Pattern.inter, inductionHypothesis]
      cases Decidable.em (first = second) with
      | inl namesEqual =>
        subst second
        cases Decidable.em (left = right) with
        | inl countsEqual =>
          subst right
          rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
          rfl
        | inr countsDifferent =>
          rw [if_neg (by intro equal; exact countsDifferent equal.2),
            if_neg (by intro equal; exact countsDifferent (Nat.succ.inj equal.2))]
          rfl
      | inr namesDifferent =>
        rw [if_neg (by intro equal; exact namesDifferent equal.1),
          if_neg (by intro equal; exact namesDifferent equal.1)]
        rfl

private theorem noAppSpine (subpattern : Subpattern (.app function argument) (.varN (.const name) count)) :
    False := by
  obtain ⟨subcount, _, equal⟩ := spineSubpattern subpattern
  cases subcount <;> cases equal

private theorem quotientSubpattern (subpattern : Subpattern pattern quotLiftPattern) :
    pattern = quotLiftPattern ∨
      (∃ subcount, subcount ≤ 5 ∧ pattern = .varN (.const ``Quot.lift) subcount) ∨
      ∃ subcount, subcount ≤ 3 ∧ pattern = .varN (.const ``Quot.mk) subcount := by
  cases subpattern with
  | refl => exact .inl rfl
  | appL previous => exact .inr (.inl (spineSubpattern previous))
  | appR previous => exact .inr (.inr (spineSubpattern previous))

private theorem quotientSpineIntersection (name : Lean.Name) (count : Nat) (small : count ≤ 5) :
    quotLiftPattern.inter (.varN (.const name) count) = none := by
  cases count with
  | zero => rfl
  | succ count =>
    change (do
      let function ← (Pattern.varN (.const ``Quot.lift) 5).inter (.varN (.const name) count)
      pure (Pattern.app function (.varN (.const ``Quot.mk) 3))) = none
    rw [spineIntersection]
    simp [show 5 ≠ count by omega]

private theorem quotientAppSubpattern
    (subpattern : Subpattern (.app function argument) quotLiftPattern) :
    function = .varN (.const ``Quot.lift) 5 ∧ argument = .varN (.const ``Quot.mk) 3 := by
  cases subpattern with
  | refl => exact ⟨rfl, rfl⟩
  | appL previous | appR previous => exact False.elim (noAppSpine previous)

private theorem RewriteRule.appSubpattern (rule : RewriteRule environment pattern result)
    (subpattern : Subpattern (.app function argument) pattern) :
    pattern = quotLiftPattern ∧ function = .varN (.const ``Quot.lift) 5 ∧
      argument = .varN (.const ``Quot.mk) 3 := by
  cases rule with
  | delta => cases subpattern
  | quot => exact ⟨rfl, quotientAppSubpattern subpattern⟩

theorem RewriteRule.unique (environmentWF : environment.WF)
    (first : RewriteRule environment firstPattern firstResult)
    (second : RewriteRule environment secondPattern secondResult)
    (subpattern : Subpattern shared firstPattern)
    (intersection : secondPattern.inter shared = some overlap) :
    firstPattern = secondPattern ∧ secondPattern = shared ∧ HEq firstResult secondResult := by
  cases first with
  | @delta firstDefinition firstClosed firstRegistered =>
    cases subpattern
    cases second with
    | @delta secondDefinition secondClosed secondRegistered =>
      simp only [Pattern.inter] at intersection
      split at intersection
      · rename_i namesEqual
        cases environmentWF.rewriteMetadata.unique firstRegistered secondRegistered namesEqual.symm
        exact ⟨rfl, rfl, HEq.rfl⟩
      · cases intersection
    | quot => cases intersection
  | quot firstRegistered =>
    cases second with
    | @delta definition closed registered =>
      have protectedNames := environmentWF.rewriteMetadata.quotientNames registered firstRegistered
      rcases quotientSubpattern subpattern with rfl | ⟨count, _, rfl⟩ | ⟨count, _, rfl⟩
      · cases intersection
      · have disjoint : (Pattern.const definition.name).inter (.varN (.const ``Quot.lift) count) = none := by
          change (Pattern.varN (.const definition.name) 0).inter _ = none
          rw [spineIntersection]
          simp [protectedNames ``Quot.lift (by simp)]
        rw [disjoint] at intersection
        cases intersection
      · have disjoint : (Pattern.const definition.name).inter (.varN (.const ``Quot.mk) count) = none := by
          change (Pattern.varN (.const definition.name) 0).inter _ = none
          rw [spineIntersection]
          simp [protectedNames ``Quot.mk (by simp)]
        rw [disjoint] at intersection
        cases intersection
    | quot =>
      rcases quotientSubpattern subpattern with rfl | ⟨count, bound, rfl⟩ | ⟨count, bound, rfl⟩
      · exact ⟨rfl, rfl, HEq.rfl⟩
      · rw [quotientSpineIntersection _ _ bound] at intersection
        cases intersection
      · rw [quotientSpineIntersection _ _ (by omega)] at intersection
        cases intersection

theorem RewriteRule.noNestedApplication (rule : RewriteRule environment pattern result)
    (subpattern : Subpattern (.app function argument) pattern) :
    ¬Subpattern (.app nestedFunction nestedArgument) function := by
  obtain ⟨_, rfl, _⟩ := rule.appSubpattern subpattern
  exact noAppSpine

theorem RewriteRule.majorHeadDisjoint
    (first : RewriteRule environment firstPattern firstResult)
    (second : RewriteRule environment secondPattern secondResult)
    (firstSubpattern : Subpattern (.app firstFunction firstArgument) firstPattern)
    (secondSubpattern : Subpattern (.app secondFunction secondArgument) secondPattern)
    (variableSubpattern : Subpattern (.var shared) firstFunction) :
    secondFunction.inter shared = none := by
  obtain ⟨_, rfl, _⟩ := first.appSubpattern firstSubpattern
  obtain ⟨_, rfl, _⟩ := second.appSubpattern secondSubpattern
  obtain ⟨count, bound, equal⟩ := spineSubpattern variableSubpattern
  cases count with
  | zero => cases equal
  | succ count =>
    cases equal
    rw [spineIntersection]
    simp [show 5 ≠ count by omega]

theorem RewriteRule.majorArgumentDisjoint
    (first : RewriteRule environment firstPattern firstResult)
    (second : RewriteRule environment secondPattern secondResult)
    (firstSubpattern : Subpattern (.app firstFunction firstArgument) firstPattern)
    (secondSubpattern : Subpattern (.app secondFunction secondArgument) secondPattern)
    (functionSubpattern : Subpattern left firstFunction)
    (argumentSubpattern : Subpattern right secondArgument) :
    left.inter right = none := by
  obtain ⟨_, rfl, _⟩ := first.appSubpattern firstSubpattern
  obtain ⟨_, _, rfl⟩ := second.appSubpattern secondSubpattern
  obtain ⟨leftCount, _, rfl⟩ := spineSubpattern functionSubpattern
  obtain ⟨rightCount, _, rfl⟩ := spineSubpattern argumentSubpattern
  rw [spineIntersection]
  simp

abbrev WF.reductionParams (environmentWF : environment.WF) (universes : Nat) : Params where
  env := environment
  henv := environmentWF
  univs := universes
  Pat := RewriteRule environment
  pat_simple := RewriteRule.simple
  pat_uniq := RewriteRule.unique environmentWF
  pat_wf := RewriteRule.sound environmentWF
  pat_app_l := RewriteRule.noNestedApplication
  pat_app_l_uniq := RewriteRule.majorHeadDisjoint
  pat_app_uniq := RewriteRule.majorArgumentDisjoint
  extra_pat registered _ arity := RewriteRule.equation environmentWF registered arity

end Lean4Lean.VEnv
