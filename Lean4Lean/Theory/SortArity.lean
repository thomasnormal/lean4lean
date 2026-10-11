import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean

inductive VEnv.SortArity (environment : VEnv) (universes : Nat) : List VExpr → Nat → VExpr → Prop where
  | sort (levelWF : level.WF universes)
      (equality : environment.IsDefEqU universes context type (.sort level)) :
      environment.SortArity universes context 0 type
  | forallE (domainTyped : environment.IsType universes context domain)
      (equality : environment.IsDefEqU universes context type (.forallE domain body))
      (tail : environment.SortArity universes (domain :: context) count body) :
      environment.SortArity universes context (count + 1) type

namespace VEnv.SortArity

variable {environment extended : VEnv} {universes count amount position : Nat}
  {context source target base original : List VExpr} {type other argument domain : VExpr}

theorem isType (kind : environment.SortArity universes context count type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    environment.IsType universes context type := by
  induction kind with
  | sort levelWF equality =>
    exact IsType.defeqU_l environmentWF contextWF equality.symm ⟨_, .sort levelWF⟩
  | forallE domainTyped equality tail induction =>
    exact IsType.defeqU_l environmentWF contextWF equality.symm
      (domainTyped.forallE (induction ⟨contextWF, domainTyped⟩))

theorem defeq (kind : environment.SortArity universes context count type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes))
    (equal : environment.IsDefEqU universes context other type) :
    environment.SortArity universes context count other := by
  cases kind with
  | sort levelWF equality => exact .sort levelWF (equal.trans environmentWF contextWF equality)
  | forallE domainTyped equality tail =>
    exact .forallE domainTyped (equal.trans environmentWF contextWF equality) tail

theorem defeqCtx (kind : environment.SortArity universes source count type)
    (ordered : environment.Ordered) (equal : environment.IsDefEqCtx universes base source target) :
    environment.SortArity universes target count type := by
  induction kind generalizing target with
  | sort levelWF equality => exact .sort levelWF (equality.defeqDFC ordered equal)
  | forallE domainTyped equality tail induction =>
    obtain ⟨level, typed⟩ := domainTyped
    exact .forallE ⟨level, typed.defeqDFC ordered equal⟩ (equality.defeqDFC ordered equal)
      (induction (.succ equal typed))

theorem weakN (kind : environment.SortArity universes source count type)
    (ordered : environment.Ordered) (insertion : Ctx.LiftN amount position source target) :
    environment.SortArity universes target count (type.liftN amount position) := by
  induction kind generalizing position target with
  | sort levelWF equality =>
    exact .sort levelWF (by simpa only [VExpr.liftN] using equality.weakN ordered insertion)
  | forallE domainTyped equality tail induction =>
    exact .forallE (domainTyped.weakN ordered insertion)
      (by simpa only [VExpr.liftN] using equality.weakN ordered insertion) (induction insertion.succ)

theorem mono (kind : environment.SortArity universes context count type) (increase : environment ≤ extended) :
    extended.SortArity universes context count type := by
  induction kind with
  | sort levelWF equality => exact .sort levelWF (equality.mono increase)
  | forallE domainTyped equality tail induction =>
    exact .forallE (domainTyped.mono increase) (equality.mono increase) induction

theorem instN (kind : environment.SortArity universes source count type)
    (ordered : environment.Ordered) (substitution : Ctx.InstN original argument domain position source target)
    (typed : environment.HasType universes original argument domain) :
    environment.SortArity universes target count (type.inst argument position) := by
  induction kind generalizing position target with
  | sort levelWF equality =>
    exact .sort levelWF (by simpa only [VExpr.inst] using equality.instN ordered substitution typed)
  | forallE domainTyped equality tail induction =>
    exact .forallE (domainTyped.instN ordered substitution typed)
      (by simpa only [VExpr.inst] using equality.instN ordered substitution typed) (induction substitution.succ)

theorem apply {function functionType argument domain body : VExpr}
    (kind : environment.SortArity universes context (count + 1) functionType)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes))
    (functionTyped : environment.HasType universes context function functionType)
    (applicationTyped : environment.HasType universes context function (.forallE domain body))
    (argumentTyped : environment.HasType universes context argument domain) :
    environment.SortArity universes context count (body.inst argument) := by
  have equality := applicationTyped.uniqU environmentWF contextWF functionTyped
  have adjusted := kind.defeq environmentWF contextWF equality
  cases adjusted with
  | forallE domainTyped equality tail =>
    obtain ⟨⟨_, domainEquality⟩, ⟨_, bodyEquality⟩⟩ :=
      IsDefEqU.forallE_inv environmentWF contextWF equality
    have bodyKind := tail.defeqCtx environmentWF.ordered (.succ .zero domainEquality.symm)
    have domainIsType := applicationTyped.isType environmentWF contextWF
    have domainIsType := (domainIsType.forallE_inv environmentWF.ordered).1
    have bodyKind := bodyKind.defeq environmentWF ⟨contextWF, domainIsType⟩ ⟨_, bodyEquality⟩
    exact bodyKind.instN environmentWF.ordered .zero argumentTyped

theorem typedIsType {semantic : VExpr}
    (kind : environment.SortArity universes context 0 type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes))
    (typed : environment.HasType universes context semantic type) :
    environment.IsType universes context semantic := by
  cases kind with
  | sort levelWF equality =>
    exact ⟨_, equality.defeqDF environmentWF contextWF typed⟩

theorem instL {levels : List VLevel} {specializedUniverses : Nat}
    (kind : environment.SortArity universes context count type)
    (levelsWF : ∀ level ∈ levels, level.WF specializedUniverses) :
    environment.SortArity specializedUniverses (context.map (VExpr.instL levels)) count
      (type.instL levels) := by
  induction kind with
  | sort levelWF equality =>
    exact .sort (VLevel.WF.inst levelsWF) (by simpa only [VExpr.instL] using equality.instL levelsWF)
  | forallE domainTyped equality tail induction =>
    exact .forallE (domainTyped.instL levelsWF)
      (by simpa only [VExpr.instL] using equality.instL levelsWF) induction

theorem weak0 (kind : environment.SortArity universes [] count type)
    (environmentWF : environment.WF) : environment.SortArity universes context count type := by
  obtain ⟨_, typed⟩ := kind.isType environmentWF trivial
  have closed := typed.closedN environmentWF.ordered trivial
  simpa only [List.append_nil, closed.liftN_eq (Nat.zero_le _)] using
    kind.weakN environmentWF.ordered (.zero context)

end VEnv.SortArity
end Lean4Lean
