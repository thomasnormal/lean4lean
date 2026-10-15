import Lean

namespace NativeQuotPrefixReduction

theorem selector (proposition : Prop) (relation : proposition → proposition → Prop)
    (major : Quot relation) : proposition :=
  Quot.ind (β := fun _ => proposition) (fun value => value) major

theorem unfolding (proposition : Prop) (relation : proposition → proposition → Prop)
    {target : Sort level} (function : proposition → target)
    (respect : ∀ first second, relation first second → function first = function second)
    (major : Quot relation) :
    Quot.lift function respect major = function (selector proposition relation major) := by
  have reconstructed : major = Quot.mk relation (selector proposition relation major) := rfl
  exact (congrArg (Quot.lift function respect) reconstructed).trans (by rfl)

theorem expandedPrefix (proposition : Prop) (relation : proposition → proposition → Prop)
    {target : Sort level} (function : proposition → target)
    (respect : ∀ first second, relation first second → function first = function second) :
    Quot.lift function respect = fun major => function (selector proposition relation major) := by
  funext major
  exact unfolding proposition relation function respect major

theorem expandedConstant :
    (fun (proposition : Prop) (relation : proposition → proposition → Prop) (target : Sort level)
      (function : proposition → target)
      (respect : ∀ first second, relation first second → function first = function second) =>
        Quot.lift function respect) =
    (fun proposition relation _target function _respect major =>
      function (selector proposition relation major) :
        ∀ (proposition : Prop) (relation : proposition → proposition → Prop) (target : Sort level)
          (function : proposition → target),
          (∀ first second, relation first second → function first = function second) → Quot relation → target) := by
  funext proposition relation target function respect major
  exact unfolding proposition relation function respect major

#print axioms selector
#print axioms unfolding
#print axioms expandedPrefix
#print axioms expandedConstant

end NativeQuotPrefixReduction
