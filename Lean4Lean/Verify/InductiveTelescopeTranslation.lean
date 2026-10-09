import Lean4Lean.Verify.InductiveBinderDomains
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

inductive FreshBinderValues : List FVarId → List BinderStep → Prop where
  | nil {existing : List FVarId} : FreshBinderValues existing []
  | cons {existing : List FVarId} {step : BinderStep} {steps : List BinderStep} {id : FVarId}
      (value : step.value = .fvar id) (fresh : id ∉ existing)
      (tail : FreshBinderValues (id :: existing) steps) :
      FreshBinderValues existing (step :: steps)

inductive TranslatedBinderHistory (env : VEnv) (universeNames : List Name) :
    VLCtx → List BinderStep → Prop where
  | nil {context : VLCtx} (contextWF : context.WF env universeNames.length) :
      TranslatedBinderHistory env universeNames context []
  | cons {context : VLCtx} {step : BinderStep} {steps : List BinderStep}
      {id : FVarId} {semanticDomain : VExpr} {level : VLevel}
      (contextWF : context.WF env universeNames.length)
      (value : step.value = .fvar id) (fresh : id ∉ context.fvars)
      (domainTranslated : TrExprS env universeNames context step.domain semanticDomain)
      (domainTyped : env.HasType universeNames.length context.toCtx semanticDomain (.sort level))
      (tail : TranslatedBinderHistory env universeNames
        ((some (id, []), .vlam semanticDomain) :: context) steps) :
      TranslatedBinderHistory env universeNames context (step :: steps)

theorem translatedForallDomain {env : VEnv} {universeNames : List Name} {context : VLCtx}
    {name : Name} {domain body : Expr} {bi : BinderInfo} {semantic : VExpr}
    (translated : TrExprS env universeNames context (.forallE name domain body bi) semantic) :
    ∃ semanticDomain semanticBody level,
      semantic = .forallE semanticDomain semanticBody ∧
      TrExprS env universeNames context domain semanticDomain ∧
      env.HasType universeNames.length context.toCtx semanticDomain (.sort level) ∧
      TrExprS env universeNames ((none, .vlam semanticDomain) :: context) body semanticBody := by
  cases translated with
  | forallE domainIsType _ domainTranslated bodyTranslated =>
    obtain ⟨level, domainTyped⟩ := domainIsType
    exact ⟨_, _, level, rfl, domainTranslated, domainTyped, bodyTranslated⟩

theorem OpenedTelescope.translatedHistory {env : VEnv} {universeNames : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr}
    (opened : OpenedTelescope type steps terminal)
    (translated : TrExprS env universeNames context type semantic)
    (ordered : env.Ordered) (contextWF : context.WF env universeNames.length)
    (freshValues : FreshBinderValues context.fvars steps) :
    TranslatedBinderHistory env universeNames context steps := by
  induction opened generalizing context semantic with
  | sort level => exact .nil contextWF
  | @bind role name domain bi value body terminal steps tail ih =>
    cases freshValues with
    | @cons _ _ _ id valueEq fresh tailFresh =>
      obtain ⟨semanticDomain, semanticBody, level, semanticEq, domainTranslated,
        domainTyped, bodyTranslated⟩ := translatedForallDomain translated
      have nextWF : VLCtx.WF env universeNames.length
          ((some (id, []), .vlam semanticDomain) :: context) := by
        refine ⟨contextWF, ?_, level, domainTyped⟩
        intro otherId dependencies equal
        cases equal
        exact ⟨fresh, List.nil_subset _⟩
      have openedBody : TrExprS env universeNames
          ((some (id, []), .vlam semanticDomain) :: context)
          (body.instantiate1 value) semanticBody := by
        change value = .fvar id at valueEq
        rw [valueEq, Expr.instantiate1_eq]
        exact bodyTranslated.inst_fvar ordered nextWF
      have translatedTail := ih openedBody nextWF
        (by simpa only [VLCtx.fvars_cons_some] using tailFresh)
      exact .cons contextWF valueEq fresh domainTranslated domainTyped translatedTail

theorem TranslatedBinderHistory.domains {env : VEnv} {universeNames : List Name}
    {context : VLCtx} {steps : List BinderStep}
    (history : TranslatedBinderHistory env universeNames context steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧
      (∀ position, (contexts position).WF env universeNames.length) ∧
      ∀ position step, steps[position]? = some step → ∃ semantic,
        TrExprS env universeNames (contexts position) step.domain semantic ∧
        env.HasType universeNames.length (contexts position).toCtx semantic (.sort (levels position)) := by
  induction history with
  | nil contextWF =>
    exact ⟨fun _ => _, fun _ => .zero, rfl, fun _ => contextWF,
      fun _ _ selected => by cases selected⟩
  | @cons context step steps id semanticDomain level contextWF value fresh
      domainTranslated domainTyped tail ih =>
    obtain ⟨tailContexts, tailLevels, tailInitial, tailWF, tailDomains⟩ := ih
    refine ⟨(fun position => match position with | 0 => context | position + 1 => tailContexts position),
      (fun position => match position with | 0 => level | position + 1 => tailLevels position),
      rfl, ?_, ?_⟩
    · intro position
      cases position with
      | zero => exact contextWF
      | succ position => exact tailWF position
    · intro position selectedStep selected
      cases position with
      | zero =>
        have sameStep : step = selectedStep := Option.some.inj selected
        subst selectedStep
        exact ⟨semanticDomain, domainTranslated, domainTyped⟩
      | succ position => exact tailDomains position selectedStep selected

theorem OpenedTelescope.translatedDomains {env : VEnv} {universeNames : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr}
    (opened : OpenedTelescope type steps terminal)
    (translated : TrExprS env universeNames context type semantic)
    (ordered : env.Ordered) (contextWF : context.WF env universeNames.length)
    (freshValues : FreshBinderValues context.fvars steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧
      (∀ position, (contexts position).WF env universeNames.length) ∧
      ∀ position step, steps[position]? = some step → ∃ semanticDomain,
        TrExprS env universeNames (contexts position) step.domain semanticDomain ∧
        env.HasType universeNames.length (contexts position).toCtx semanticDomain
          (.sort (levels position)) :=
  (opened.translatedHistory translated ordered contextWF freshValues).domains

end Lean4Lean.AddInductive
