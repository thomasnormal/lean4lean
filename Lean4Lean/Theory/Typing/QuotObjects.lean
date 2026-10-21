import Lean4Lean.Theory.Typing.EnvLemmas

/-! Quotient objects recovered from their actual declaration history. -/

namespace Lean4Lean

theorem VEnv.addConsts_defeqs {environment extended : VEnv} :
    ∀ {definitions}, environment.addConsts definitions = some extended →
      extended.defeqs = environment.defeqs
  | [], added => by cases added; rfl
  | _ :: _, added => by
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp added
    exact (addConsts_defeqs rest).trans (addConst.defeqs_eq first)

theorem VEnv.addDefEqs_defeqs (environment : VEnv) (definitions : List VDefVal)
    (equation : VDefEq) :
    (environment.addDefEqs definitions).defeqs equation ↔
      (∃ definition ∈ definitions, equation = definition.toDefEq) ∨ environment.defeqs equation := by
  induction definitions generalizing environment with
  | nil => simp [addDefEqs]
  | cons definition definitions induction =>
    change ((environment.addDefEq definition.toDefEq).addDefEqs definitions).defeqs equation ↔ _
    rw [induction]
    simp only [addDefEq, List.mem_cons]
    constructor
    · rintro (⟨previous, member, equal⟩ | equal | old)
      · exact .inl ⟨previous, .inr member, equal⟩
      · exact .inl ⟨definition, .inl rfl, equal⟩
      · exact .inr old
    · rintro (⟨previous, rfl | member, equal⟩ | old)
      · exact .inr (.inl equal)
      · exact .inl ⟨previous, member, equal⟩
      · exact .inr (.inr old)

theorem VEnv.addDefEqs_constants (environment : VEnv) (definitions : List VDefVal) :
    (environment.addDefEqs definitions).constants = environment.constants := by
  induction definitions generalizing environment with
  | nil => rfl
  | cons definition definitions induction => exact induction (environment.addDefEq definition.toDefEq)

theorem VEnv.addDefEqs_extension (environment : VEnv) (definitions : List VDefVal) :
    environment ≤ environment.addDefEqs definitions := by
  refine ⟨?_, ?_⟩
  · intro name constant found
    rwa [addDefEqs_constants]
  · intro equation registered
    exact (addDefEqs_defeqs ..).mpr (.inr registered)


theorem VEnv.WF.quotientObjects {environment : VEnv}
    (environmentWF : environment.WF) (registered : environment.defeqs quotDefEq) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] := by
  obtain ⟨declarations, wellFormed⟩ := environmentWF
  induction wellFormed with
  | empty => cases registered
  | decl declaration _ inductionHypothesis =>
    cases declaration with
    | «axiom» _ added | «opaque» _ added =>
      rw [VEnv.addConst.defeqs_eq added] at registered
      exact (inductionHypothesis registered).mono (VEnv.addConst_le added)
    | «def» _ added =>
      rcases registered with newEquation | oldEquation
      · cases congrArg VDefEq.lhs newEquation
      · rw [VEnv.addConst.defeqs_eq added] at oldEquation
        exact (inductionHypothesis oldEquation).mono
          ((VEnv.addConst_le added).trans VEnv.addDefEq_le)
    | mutualDef _ added _ =>
      rcases (VEnv.addDefEqs_defeqs ..).mp registered with ⟨definition, _, impossible⟩ | old
      · cases congrArg VDefEq.lhs impossible
      · rw [VEnv.addConsts_defeqs added] at old
        exact (inductionHypothesis old).mono
          ((VEnv.addConsts_le added).trans (VEnv.addDefEqs_extension ..))
    | «example» _ => exact inductionHypothesis registered
    | quot _ added => exact VEnv.addQuot_objs added
    | induct _ added =>
      rw [VEnv.addInduct.defeqs_eq added] at registered
      exact (inductionHypothesis registered).mono (VEnv.addInduct.le added)

end Lean4Lean
