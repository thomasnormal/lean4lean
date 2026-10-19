import Lean4Lean.Theory.Typing.EnvLemmas

/-! Quotient objects recovered from their actual declaration history. -/

namespace Lean4Lean

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
    | «example» _ => exact inductionHypothesis registered
    | quot _ added => exact VEnv.addQuot_objs added
    | induct _ added =>
      rw [VEnv.addInduct.defeqs_eq added] at registered
      exact (inductionHypothesis registered).mono (VEnv.addInduct.le added)

end Lean4Lean
