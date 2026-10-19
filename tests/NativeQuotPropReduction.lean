import Lean

namespace NativeQuotPropReduction

theorem selector (proposition : Prop) (relation : proposition → proposition → Prop)
    (major : Quot relation) : proposition :=
  Quot.ind (β := fun _ => proposition) (fun value => value) major

example (major : Quot (α := False) fun _ _ => True) : False := selector False _ major

variable (proposition : Prop) (relation : proposition → proposition → Prop)
  (function : proposition → Prop)
  (respect : ∀ first second, relation first second → function first = function second)
  (value : proposition) (major : Quot relation)

example : selector proposition relation (Quot.mk relation value) = value := rfl

example : Quot.lift function respect major = function (selector proposition relation major) := by
  fail_if_success rfl
  have reconstructed : major = Quot.mk relation (selector proposition relation major) := rfl
  exact (congrArg (Quot.lift function respect) reconstructed).trans (by rfl)

example : function (selector proposition relation major) = function value := rfl

example {target : Sort level} (mapping : proposition → target)
    (compatible : ∀ first second, relation first second → mapping first = mapping second) :
    Quot.lift mapping compatible major = mapping (selector proposition relation major) := by
  have reconstructed : major = Quot.mk relation (selector proposition relation major) := rfl
  exact (congrArg (Quot.lift mapping compatible) reconstructed).trans (by rfl)

end NativeQuotPropReduction
