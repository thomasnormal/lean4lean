import Lean4Lean.Verify.TypeChecker.ScopedWHNF
import Lean4Lean.Verify.TypeChecker.InferType

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open TypeChecker

theorem TypeChecker.VState.WF.next {context : VContext} {state : VState}
    (valid : state.WF context) : state.next.WF context := by
  constructor
  · exact valid.trctx
  · intro freeVariable member
    exact (valid.ngen_wf freeVariable member).mono .next
  · obtain ⟨levels, count, levelsWF, contextLift, managerWF, reserved⟩ := valid.ectx
    exact ⟨levels, count, levelsWF, contextLift, managerWF,
      fun freeVariable member => (reserved freeVariable member).mono .next⟩
  · intro expression type found
    exact (valid.inferTypeI_wf found).mono .next
  · intro expression type found
    exact (valid.inferTypeC_wf found).mono .next
  · intro expression value found
    exact (valid.whnfCore_wf found).mono .next
  · intro expression value found
    exact (valid.whnf_wf found).mono .next
  · exact valid.unfold_wf

theorem TypeChecker.HeadScopeCacheWF.next {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) :
    HeadScopeCacheWF locals { state with ngen := state.ngen.next } := by
  exact stable

theorem TypeChecker.RecM.ScopeWF.withFreshId {context : VContext} {state : VState}
    {continuation : Name → RecM Result} {post : Result → VState → Prop}
    (valid : ∀ name,
      (continuation name).ScopeWF context state.next post) :
    (withFreshId continuation).ScopeWF context state post := by
  intro methods callbacks caches wellFormed result finalState accepted
  change continuation state.ngen.curr methods context.toContext state.next.toState =
    .ok (result, finalState) at accepted
  have final := valid state.ngen.curr methods callbacks
    (by simpa [VState.next] using caches.next)
    (wellFormed.next) result finalState accepted
  obtain ⟨updated, equal, increasing, wellFormed', scopedPost⟩ := final
  exact ⟨updated, equal, NameGenerator.LE.next.trans increasing, wellFormed', scopedPost⟩

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

theorem checkLevel.scopeWF {context : VContext} {state : VState} {level : Level}
    (valid : level.hasMVar' = false) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context => liftM (checkLevel context level))
      (fun _ _ => ∃ level', VLevel.ofLevel context.lparams level = some level') := by
  apply RecM.ScopeWF.readThe
  change RecM.ScopeWF context state (liftM (checkLevel context.toContext level)) _
  exact RecM.ScopeWF.liftExcept (checkLevel.WF valid)

theorem envGet.scopeWF {context : VContext} {state : VState} {name : Name} :
    RecM.ScopeWF context state
      ((liftM TypeChecker.getEnv : RecM Environment) >>= fun environment =>
        liftM (environment.get name))
      (fun info _ => context.env.find? name = some info) := by
  apply RecM.ScopeWF.getEnv
  exact RecM.ScopeWF.liftExcept envGet.WF

theorem inferConstant.scopeWF {context : VContext} {state : VState}
    {name : Name} {levels : List Level} {inferOnly : Bool}
    (validLevels : ∀ level ∈ levels, level.hasMVar' = false)
    (validInference : inferOnly = true → ∃ expression,
      context.TrExprS (.const name levels) expression) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context =>
        liftM (inferConstant context name levels inferOnly))
      (fun type _ => ∃ expression semanticType,
        context.TrTyping (.const name levels) type expression semanticType) := by
  apply RecM.ScopeWF.readThe
  change RecM.ScopeWF context state
    (liftM (inferConstant context.toContext name levels inferOnly)) _
  exact RecM.ScopeWF.liftExcept (inferConstant.WF validLevels validInference)

end TypeChecker.Inner
end Lean4Lean
