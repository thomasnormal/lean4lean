import Lean4Lean.Verify.InductiveBinderDomains

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem OpenedTelescope.samePrefixAndNextDomain {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal) (count : Nat)
    (hvalues : (left.take count).map BinderStep.value = (right.take count).map BinderStep.value)
    (hroles : (left.take count).map BinderStep.role = (right.take count).map BinderStep.role) :
    left.take count = right.take count ∧
      ((left.drop count).head?).map BinderStep.domain =
        ((right.drop count).head?).map BinderStep.domain := by
  induction count generalizing type left right leftTerminal rightTerminal with
  | zero =>
    cases leftOpened with
    | sort level => cases rightOpened; exact ⟨rfl, rfl⟩
    | bind role name domain bi value tail =>
      cases rightOpened with
      | bind rightRole _ _ _ rightValue rightTail => exact ⟨rfl, rfl⟩
  | succ count ih =>
    cases leftOpened with
    | sort level => cases rightOpened; exact ⟨rfl, rfl⟩
    | @bind role name domain bi value body terminal steps tail =>
      cases rightOpened with
      | bind rightRole _ _ _ rightValue rightTail =>
        simp only [List.take_succ_cons, List.map_cons, List.cons.injEq] at hvalues hroles
        obtain ⟨hvalue, hvalues⟩ := hvalues
        obtain ⟨hrole, hroles⟩ := hroles
        subst rightValue rightRole
        obtain ⟨hprefix, hdomain⟩ := ih tail rightTail hvalues hroles
        refine ⟨?_, ?_⟩
        · exact congrArg ({ role, name, domain, bi, value } :: ·) hprefix
        · simpa only [List.drop_succ_cons] using hdomain

theorem OpenedTelescope.samePrefix {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal) (count : Nat)
    (hvalues : (left.take count).map BinderStep.value = (right.take count).map BinderStep.value)
    (hroles : (left.take count).map BinderStep.role = (right.take count).map BinderStep.role) :
    left.take count = right.take count :=
  (leftOpened.samePrefixAndNextDomain rightOpened count hvalues hroles).1

theorem OpenedTelescope.sameNextLocalDomain {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal) (count : Nat)
    (hvalues : (left.take count).map BinderStep.value = (right.take count).map BinderStep.value)
    (hroles : (left.take count).map BinderStep.role = (right.take count).map BinderStep.role) :
    ((left.drop count).head?).map BinderStep.localDomain =
      ((right.drop count).head?).map BinderStep.localDomain := by
  have hdomains := (leftOpened.samePrefixAndNextDomain rightOpened count hvalues hroles).2
  have hconsumed := congrArg (Option.map Expr.consumeTypeAnnotations) hdomains
  simpa only [Option.map_map, Function.comp_def, BinderStep.localDomain] using hconsumed

end Lean4Lean.AddInductive
