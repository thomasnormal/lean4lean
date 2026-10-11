import Lean4Lean.Theory.SortArity

namespace Lean4Lean.VEnv.SortArity

theorem uniqueCount
    {environment : VEnv} {universes first second : Nat} {context : List VExpr} {type : VExpr}
    (left : environment.SortArity universes context first type)
    (right : environment.SortArity universes context second type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    first = second := by
  induction left generalizing second with
  | sort levelWF equality =>
    cases right with
    | sort => rfl
    | forallE domainTyped other tail =>
      exact False.elim (IsDefEqU.sort_forallE_inv environmentWF contextWF
        (equality.symm.trans environmentWF contextWF other))
  | forallE domainTyped equality tail induction =>
    cases right with
    | sort levelWF other =>
      exact False.elim (IsDefEqU.sort_forallE_inv environmentWF contextWF
        (other.symm.trans environmentWF contextWF equality))
    | forallE actualDomainTyped other actualTail =>
      obtain ⟨⟨_, domainEquality⟩, ⟨_, bodyEquality⟩⟩ :=
        IsDefEqU.forallE_inv environmentWF contextWF (equality.symm.trans environmentWF contextWF other)
      have adjusted := actualTail.defeqCtx environmentWF.ordered (.succ .zero domainEquality.symm)
      have adjusted := adjusted.defeq environmentWF ⟨contextWF, domainTyped⟩ ⟨_, bodyEquality⟩
      exact congrArg Nat.succ (induction adjusted ⟨contextWF, domainTyped⟩)

theorem forallPositive
    {environment : VEnv} {universes count : Nat} {context : List VExpr} {domain body : VExpr}
    (kind : environment.SortArity universes context count (.forallE domain body))
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    0 < count := by
  cases kind with
  | sort levelWF equality =>
    exact False.elim (IsDefEqU.sort_forallE_inv environmentWF contextWF equality.symm)
  | forallE => omega

end Lean4Lean.VEnv.SortArity
