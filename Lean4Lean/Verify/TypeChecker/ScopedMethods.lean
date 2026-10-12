import Lean4Lean.Verify.TypeChecker.ScopedDelta
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

private theorem comparisonDispatcherFrame {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqCore' first second).ScopeWF context state (fun _ _ => True) := by
  unfold isDefEqCore'
  extract_lets falseResult ordinaryComparison readerComparison
  refine (quickIsDefEq.scopeWF firstTranslation secondTranslation).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| RecM.ScopeWF.readThe ?_
  suffices ∀ {state}, (ordinaryComparison ⟨⟩).ScopeWF context state (fun _ _ => True) by
    split <;> [skip; exact this]
    refine (whnf.scopeWF firstTranslation).bind fun _ _ _ _ => ?_
    split <;> [exact RecM.ScopeWF.pure trivial; exact this]
  intro state
  unfold ordinaryComparison
  refine (whnfCore.scopeWF firstTranslation).bind
    fun _ _ _ ⟨_, ⟨_, firstStructural, _⟩, _⟩ => ?_
  refine (whnfCore.scopeWF secondTranslation).bind
    fun _ _ _ ⟨_, ⟨_, secondStructural, _⟩, _⟩ => ?_
  extract_lets normalizedQuick remainingComparison
  suffices ∀ {state}, (remainingComparison ⟨⟩).ScopeWF context state (fun _ _ => True) by
    split <;> [skip; exact this]
    refine (quickIsDefEq.scopeWF firstStructural secondStructural).bind fun _ _ _ _ => ?_
    split <;> [exact RecM.ScopeWF.pure trivial; exact this]
  intro state
  unfold remainingComparison
  refine (isDefEqProofIrrel.scopeWF firstStructural secondStructural).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| (lazyDeltaReduction.scopeWF firstStructural secondStructural).bind
    fun _ _ _ reduction => ?_
  split
  · cases reduction.1
  · exact RecM.ScopeWF.pure trivial
  obtain ⟨⟨_, firstReduced, _⟩, ⟨_, secondReduced, _⟩⟩ := reduction
  extract_lets unitComparison stringComparison structComparison etaComparison
    applicationComparison finalComparison
  suffices ∀ {state}, (finalComparison ⟨⟩).ScopeWF context state (fun _ _ => True) by
    split
    · split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · split <;> [skip; exact this]
      let .proj firstBody _ := firstReduced
      let .proj secondBody _ := secondReduced
      refine (isDefEq.scopeWF firstBody secondBody).bind fun _ _ _ _ => ?_
      split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · exact this
  intro state
  unfold finalComparison
  refine (whnfCore.scopeWF firstReduced).bind
    fun _ _ _ ⟨_, ⟨_, firstNormalized, _⟩, _⟩ => ?_
  refine (whnfCore.scopeWF secondReduced).bind
    fun _ _ _ ⟨_, ⟨_, secondNormalized, _⟩, _⟩ => ?_
  split
  · exact (isDefEqCore.scopeWF firstNormalized secondNormalized).bind
      fun _ _ _ _ => RecM.ScopeWF.pure trivial
  refine RecM.ScopeWF.pureBind <| (isDefEqApp.scopeWF firstReduced secondReduced).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| (tryEtaExpansion.scopeWF firstReduced secondReduced).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| (tryEtaStruct.scopeWF firstReduced secondReduced).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| (tryStringLitExpansion.scopeWF firstReduced secondReduced).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| (isDefEqUnitLike.scopeWF firstReduced secondReduced).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  exact RecM.ScopeWF.pureBind (RecM.ScopeWF.pure trivial)

theorem isDefEqCore'.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqCore' first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) := by
  exact ((comparisonDispatcherFrame firstTranslation secondTranslation).andWF
    (isDefEqCore'.WF firstTranslation secondTranslation)).mono fun _ _ _ result => result.2

end Lean4Lean.TypeChecker.Inner

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

theorem Methods.withFuel.scopeWF : ∀ {depth}, (withFuel depth).ScopeWF
  | 0 => withFuel.zero_scopeWF
  | depth + 1 =>
    have callbacks := withFuel.scopeWF (depth := depth)
    { base := withFuel.WF
      whnfCore translated := Inner.whnfCore'.scopeWF translated _ callbacks
      whnf translated := Inner.whnf'.scopeWF translated _ callbacks
      inferType freeVariables translated := Inner.inferType'.scopeWF freeVariables translated _ callbacks
      isDefEqCore firstTranslation secondTranslation :=
        Inner.isDefEqCore'.scopeWF firstTranslation secondTranslation _ callbacks }

theorem RecM.ScopeWF.run {context : VContext} {state : VState} {action : RecM Result} {post}
    (valid : action.ScopeWF context state post) : (RecM.run action).ScopeWF context state post :=
  valid _ Methods.withFuel.scopeWF

theorem M.ScopeWF.run {environment : Kernel.Environment} {environments : Lean4Lean.VEnvs}
    (wellFormed : environments.WF environment) {action : M Result} {post : Result → Prop}
    (valid : action.ScopeWF (VContext.mk' wellFormed safety levels fuel) {}
      (fun result _ => post result)) :
    (M.run environment safety {} levels fuel action).WF post := by
  exact M.WF.run wellFormed <| (valid (HeadScopeCacheWF.empty _)).mono
    fun _ _ _ result => result.2

theorem whnfCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (whnfCore expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized :=
  (Inner.whnfCore.scopeWF translated).run

theorem whnf.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (whnf expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized :=
  (Inner.whnf.scopeWF translated).run

theorem inferType.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (inferType expression).ScopeWF context state fun type _ =>
      ∃ semanticType, context.TrTyping expression type semantic semanticType :=
  (Inner.inferType.scopeWF_of_translation translated).run

theorem checkType.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (checkType expression).ScopeWF context state fun type _ =>
      ∃ semantic semanticType, context.TrTyping expression type semantic semanticType :=
  (Inner.checkType.scopeWF freeVariables).run

theorem isDefEq.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEq first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  (Inner.isDefEq.scopeWF firstTranslation secondTranslation).run

end Lean4Lean.TypeChecker
