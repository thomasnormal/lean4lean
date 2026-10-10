import Lean4Lean.Verify.InductiveNestedRebinding
import Lean4Lean.Verify.InductiveIndexSubstitutionStageBinding

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel
open TypeChecker (MLCtx)

theorem replaceParams.singleton_eq (identifier : FVarId) (body replacement : Expr)
    (nativeEnv : Environment) (state : State) (scope : body.looseBVarRange' = 0) :
    replaceParams #[replacement] body #[.fvar identifier] nativeEnv state =
      .ok ((body.abstract1 identifier).instantiate1' replacement, state) := by
  rw [replaceParams.eq_ok #[replacement] body #[.fvar identifier] nativeEnv state rfl]
  have abstraction : body.abstract #[.fvar identifier] = body.abstract1 identifier := by
    simpa only [Expr.abstractList] using
      Expr.abstract_eq_of_scope (ids := [identifier]) scope (by simp)
  rw [abstraction, Expr.instantiateRev_eq, Expr.instantiate_eq, Array.toList_reverse]
  change Except.ok ((body.abstract1 identifier).instantiateMany [replacement], state) = _
  rw [Expr.instantiateMany_singleton]

theorem replaceParams.singleton_typed
    {env : VEnv} {universes : List Name} {base : MLCtx}
    {identifier : FVarId} {name : Name} {nativeDomain : Expr} {domain : VExpr} {binder : BinderInfo}
    (envWF : env.WF)
    (sourceWF : (MLCtx.vlam identifier name nativeDomain domain binder base).WF env universes)
    {body replacement : Expr} {semantic argument : VExpr} {level : VLevel}
    (translated : TrExprS env universes (MLCtx.vlam identifier name nativeDomain domain binder base).vlctx body semantic)
    (typed : env.HasType universes.length (domain :: base.vlctx.toCtx) semantic (.sort level))
    (replacementTranslated : TrExprS env universes base.vlctx replacement argument)
    (replacementTyped : env.HasType universes.length base.vlctx.toCtx argument domain)
    (nativeEnv : Environment) (state : State) :
    (replaceParams #[replacement] body #[.fvar identifier] nativeEnv state).WF fun returned =>
      returned.2 = state ∧ returned.1 = (body.abstract1 identifier).instantiate1' replacement ∧
      TrExprS env universes base.vlctx returned.1 (semantic.inst argument) ∧
      env.HasType universes.length base.vlctx.toCtx (semantic.inst argument) (.sort level) ∧
      Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
      returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧ identifier ∉ base.vlctx.fvars := by
  have bodyClosed : Closed body 0 :=
    (MLCtx.vlam identifier name nativeDomain domain binder base).noBV ▸ translated.closed
  rw [replaceParams.singleton_eq identifier body replacement nativeEnv state bodyClosed.looseBVarRange_zero]
  have abstracted : TrExprS env universes ((none, .vlam domain) :: base.vlctx)
      (body.abstract1 identifier) semantic := translated.abstract .zero
  have instantiated := abstracted.inst envWF.ordered replacementTyped replacementTranslated
  have instantiatedTyped : env.HasType universes.length base.vlctx.toCtx (semantic.inst argument) (.sort level) := by
    simpa only [VExpr.inst] using typed.instN envWF.ordered .zero replacementTyped
  have closed : Closed ((body.abstract1 identifier).instantiate1' replacement) 0 :=
    base.noBV ▸ instantiated.closed
  exact Except.WF.pure ⟨rfl, rfl, instantiated, instantiatedTyped, closed, closed.looseBVarRange_zero,
    instantiated.fvarsIn, sourceWF.1.tr.find?_eq_none.mp sourceWF.2.1⟩

theorem replaceParams.singleton_typedRebased
    {env : VEnv} {universes : List Name} {base target : MLCtx} {insertionLift : Lift}
    {identifier : FVarId} {name : Name} {nativeDomain : Expr} {domain : VExpr} {binder : BinderInfo}
    (envWF : env.WF)
    (sourceWF : (MLCtx.vlam identifier name nativeDomain domain binder base).WF env universes)
    {body replacement : Expr} {semantic argument : VExpr} {level : VLevel}
    (translated : TrExprS env universes (MLCtx.vlam identifier name nativeDomain domain binder base).vlctx body semantic)
    (typed : env.HasType universes.length (domain :: base.vlctx.toCtx) semantic (.sort level))
    (replacementTranslated : TrExprS env universes base.vlctx replacement argument)
    (replacementTyped : env.HasType universes.length base.vlctx.toCtx argument domain)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0)
    (nativeEnv : Environment) (state : State) :
    (replaceParams #[replacement] body #[.fvar identifier] nativeEnv state).WF fun returned =>
      returned.2 = state ∧ returned.1 = (body.abstract1 identifier).instantiate1' replacement ∧
      TrExprS env universes base.vlctx returned.1 (semantic.inst argument) ∧
      env.HasType universes.length base.vlctx.toCtx (semantic.inst argument) (.sort level) ∧
      Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
      returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧ identifier ∉ base.vlctx.fvars ∧
      TrExprS env universes target.vlctx returned.1 ((semantic.inst argument).lift' insertionLift) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((semantic.inst argument).lift' insertionLift) (.sort level) := by
  exact (replaceParams.singleton_typed envWF sourceWF translated typed replacementTranslated replacementTyped
    nativeEnv state).mono fun returned receipts => by
      obtain ⟨unchanged, equation, translatedResult, typedResult, closed, scope, support, fresh⟩ := receipts
      exact ⟨unchanged, equation, translatedResult, typedResult, closed, scope, support, fresh,
        translatedResult.weakFV' envWF.ordered insertion targetWF.tr.wf,
        typedResult.weak' envWF.ordered insertion.toCtx⟩

end Lean4Lean.ElimNestedInductive
