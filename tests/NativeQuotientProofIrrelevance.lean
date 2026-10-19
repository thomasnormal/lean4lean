import Lean

namespace NativeQuotientProofIrrelevance

variable (proposition : Prop) (relation : proposition → proposition → Prop)
  (function : proposition → Prop)
  (respect : ∀ first second, relation first second → function first = function second)
  (value : proposition) (major : Quot relation)

example : major = Quot.mk relation value := rfl

example : Quot.lift function respect (Quot.mk relation value) = function value := rfl

example : Quot.lift function respect major = Quot.lift function respect (Quot.mk relation value) := by
  fail_if_success rfl
  exact congrArg (Quot.lift function respect) (show major = Quot.mk relation value from rfl)

example : Quot.lift function respect major = function value := by
  fail_if_success rfl
  have first : Quot.lift function respect major = Quot.lift function respect (Quot.mk relation value) :=
    congrArg (Quot.lift function respect) (show major = Quot.mk relation value from rfl)
  exact first.trans (show Quot.lift function respect (Quot.mk relation value) = function value from rfl)

end NativeQuotientProofIrrelevance
