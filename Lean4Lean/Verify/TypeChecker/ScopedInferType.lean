import Lean4Lean.Verify.TypeChecker.ScopedWHNF
import Lean4Lean.Verify.TypeChecker.InferType

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open TypeChecker

namespace TypeChecker.Inner

theorem ensureSortCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (ensureSortCore expression expected).ScopeWF context state fun result _ =>
      (∃ level, result = .sort level) ∧ context.TrExpr result semantic ∧
        context.FVarsBelow expression result := by
  simp [ensureSortCore]
  split
  · let .sort level := expression
    exact RecM.ScopeWF.pure ⟨⟨level, rfl⟩, translated.trExpr context.Ewf context.Δwf, .rfl⟩
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨below, normalizedTranslation, _⟩ := normalizedResult
  split
  · let .sort level := normalized
    exact RecM.ScopeWF.pure ⟨⟨level, rfl⟩, normalizedTranslation, below⟩
  exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw

theorem ensureForallCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (ensureForallCore expression expected).ScopeWF context state fun result _ =>
      context.FVarsBelow expression result ∧ context.TrExpr result semantic ∧
        ∃ name domain body binder, result = .forallE name domain body binder := by
  simp [ensureForallCore]
  split
  · let .forallE name domain body binder := expression
    exact RecM.ScopeWF.pure ⟨.rfl, translated.trExpr context.Ewf context.Δwf,
      _, _, _, _, rfl⟩
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨below, normalizedTranslation, _⟩ := normalizedResult
  split
  · let .forallE name domain body binder := normalized
    exact RecM.ScopeWF.pure ⟨below, normalizedTranslation, _, _, _, _, rfl⟩
  exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw

theorem inferFVar.scopeWF {context : VContext} {state : VState} {name : FVarId} :
    RecM.ScopeWF context state (readThe Context >>= fun context => liftM (inferFVar context name))
      (fun type _ =>
        ∃ expression semanticType, context.TrTyping (.fvar name) type expression semanticType) :=
  by
    apply RecM.ScopeWF.readThe
    change RecM.ScopeWF context state (liftM (inferFVar context.toContext name)) _
    exact RecM.ScopeWF.liftExcept inferFVar.WF

end TypeChecker.Inner
end Lean4Lean
