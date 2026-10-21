import Lean4Lean.Verify.TypeChecker.ScopedDelta
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

private theorem reduceProjCore_scopeFrame {context : VContext} {state : VState}
    {expression : Expr} {semantic : VExpr} (translated : context.TrExprS expression semantic) (index : Nat) :
    (reduceProjCore index expression).ScopeWF context state (fun _ _ => True) := by
  have finish {state : VState} (value : Expr) :
      (value.withApp fun head arguments => do
        let .const name _ := head | return none
        let environment ← TypeChecker.getEnv
        let .ctorInfo information ← environment.get name | return none
        return arguments[information.numParams + index]? : RecM (Option Expr)).ScopeWF
        context state (fun _ _ => True) := by
    rw [Expr.withApp_eq]
    cases value.getAppFn <;> dsimp only [Bind.bind, ReaderT.bind]
    any_goals exact RecM.ScopeWF.pure trivial
    apply RecM.ScopeWF.getEnv
    refine (RecM.ScopeWF.liftExcept (action := context.env.get _) (post := fun _ => True)
      (fun _ _ => trivial)).bind ?_
    intro information finalState increasing valid
    cases information <;> exact RecM.ScopeWF.pure trivial
  unfold reduceProjCore
  dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
  cases expression with
  | lit literal =>
    cases literal with
    | natVal value => exact finish _
    | strVal text =>
      let .lit contains constructor := translated
      exact (whnf.scopeWF constructor).bind fun expanded _ _ _ => finish expanded
  | _ => exact finish _

private theorem reduceProjCore_scopeWF {context : VContext} {state : VState}
    {n : Name} {i : Nat} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS (.proj n i expression) semantic) :
    (reduceProjCore i expression).ScopeWF context state fun result _ =>
      ∀ normalized, result = some normalized →
        context.FVarsBelow (.proj n i expression) normalized ∧
          context.TrExpr normalized semantic := by
  let .proj sourceTranslation _ := translated
  exact ((reduceProjCore_scopeFrame sourceTranslation i).andWF
    (reduceProjCore.WF translated)).mono fun _ _ _ result => result.2

private theorem lazyDeltaProjReduction_finish_scopeWF {context : VContext} {state : VState}
    {n₁ n₂ : Name} {i : Nat} {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (firstTranslation : context.TrExprS (.proj n₁ i e₁) e₁')
    (secondTranslation : context.TrExprS (.proj n₂ i e₂) e₂') :
    (lazyDeltaProjReduction.finish i e₁ e₂).ScopeWF context state (fun _ _ => True) := by
  unfold lazyDeltaProjReduction.finish
  let .proj firstSource _ := firstTranslation
  let .proj secondSource _ := secondTranslation
  refine (reduceProjCore_scopeWF firstTranslation).bind fun _ _ _ firstResult => ?_
  split
  · obtain ⟨_, _, firstBodySource, _⟩ := firstResult _ rfl
    refine (reduceProjCore_scopeWF secondTranslation).bind fun _ _ _ secondResult => ?_
    split
    · obtain ⟨_, _, secondBodySource, _⟩ := secondResult _ rfl
      exact (isDefEqCore.scopeWF firstBodySource secondBodySource).mono
        fun _ _ _ _ => trivial
    · exact (isDefEqCore.scopeWF firstSource secondSource).mono fun _ _ _ _ => trivial
  · exact (isDefEqCore.scopeWF firstSource secondSource).mono fun _ _ _ _ => trivial

private theorem lazyDeltaProjReduction_loop_scopeWF {context : VContext} {state : VState}
    {n₁ n₂ : Name} {i : Nat} {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (firstTranslation : context.TrExprS (.proj n₁ i e₁) e₁')
    (secondTranslation : context.TrExprS (.proj n₂ i e₂) e₂') (fuel : Nat) :
    (lazyDeltaProjReduction.loop i e₁ e₂ fuel).ScopeWF context state (fun _ _ => True) := by
  induction fuel generalizing state e₁ e₂ e₁' e₂' with
  | zero => exact RecM.ScopeWF.throw
  | succ fuel inductionHypothesis =>
    let .proj firstSource firstProjection := firstTranslation
    let .proj secondSource secondProjection := secondTranslation
    rw [lazyDeltaProjReduction.loop.eq_2]
    dsimp only [Bind.bind, ReaderT.bind]
    refine (lazyDeltaReductionStep.scopeWF firstSource secondSource).bind
      fun status _ _ reduction => ?_
    cases status with
    | «continue» nextFirst nextSecond =>
      obtain ⟨_, ⟨_, nextFirstTranslation, firstEquality⟩,
        ⟨_, nextSecondTranslation, secondEquality⟩⟩ := reduction
      obtain ⟨_, nextFirstProjection⟩ := firstProjection.defeqDFC context.Ewf
        (.refl context.Δwf.toCtx) firstEquality.symm
      obtain ⟨_, nextSecondProjection⟩ := secondProjection.defeqDFC context.Ewf
        (.refl context.Δwf.toCtx) secondEquality.symm
      change (lazyDeltaProjReduction.loop i nextFirst nextSecond fuel).ScopeWF context _ _
      exact inductionHypothesis (.proj nextFirstTranslation nextFirstProjection)
        (.proj nextSecondTranslation nextSecondProjection)
    | «true» =>
      change (pure true : RecM Bool).ScopeWF context _ _
      exact RecM.ScopeWF.pure trivial
    | «unknown» nextFirst nextSecond
    | «false» nextFirst nextSecond =>
      change (lazyDeltaProjReduction.finish i nextFirst nextSecond).ScopeWF context _ _
      obtain ⟨⟨_, nextFirstTranslation, firstEquality⟩,
        ⟨_, nextSecondTranslation, secondEquality⟩⟩ := reduction
      obtain ⟨_, nextFirstProjection⟩ := firstProjection.defeqDFC context.Ewf
        (.refl context.Δwf.toCtx) firstEquality.symm
      obtain ⟨_, nextSecondProjection⟩ := secondProjection.defeqDFC context.Ewf
        (.refl context.Δwf.toCtx) secondEquality.symm
      exact lazyDeltaProjReduction_finish_scopeWF
        (.proj nextFirstTranslation nextFirstProjection)
        (.proj nextSecondTranslation nextSecondProjection)

private theorem lazyDeltaProjReduction_scopeWF {context : VContext} {state : VState}
    {n₁ n₂ : Name} {i : Nat} {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (firstTranslation : context.TrExprS (.proj n₁ i e₁) e₁')
    (secondTranslation : context.TrExprS (.proj n₂ i e₂) e₂') :
    (lazyDeltaProjReduction e₁ e₂ i).ScopeWF context state (fun _ _ => True) := by
  unfold lazyDeltaProjReduction
  exact RecM.ScopeWF.readThe (lazyDeltaProjReduction_loop_scopeWF firstTranslation secondTranslation _)

private theorem comparisonDispatcherFrame {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqCore' first second).ScopeWF context state (fun _ _ => True) := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.scopeWF firstTranslation secondTranslation).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine RecM.ScopeWF.pureBind <| RecM.ScopeWF.readThe ?_
  suffices ∀ {state}, (F1 ⟨⟩).ScopeWF context state (fun _ _ => True) by
    by_cases special : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true) = true
    · have hcondition : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true) = true := special
      cases h : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true)
      · simp_all [h]
      · simp_all [h]
        refine (whnf.scopeWF firstTranslation).bind fun _ _ _ _ => ?_
        split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · have nonspecial : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true) = false := by
        cases h : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true) <;> simp_all
      cases h : ((!first.hasFVar || context.eagerReduce) && second.isConstOf ``true)
      · simp_all [h]
        exact this
      · simp_all [h]
  intro state
  unfold F1
  refine (whnfCore.scopeWF firstTranslation).bind
    fun _ _ _ ⟨_, ⟨_, firstStructural, _⟩, _⟩ => ?_
  refine (whnfCore.scopeWF secondTranslation).bind
    fun _ _ _ ⟨_, ⟨_, secondStructural, _⟩, _⟩ => ?_
  extract_lets F2
  suffices ∀ {state}, (F2 ⟨⟩).ScopeWF context state (fun _ _ => True) by
    split <;> [skip; exact this]
    refine (quickIsDefEq.scopeWF firstStructural secondStructural).bind fun _ _ _ _ => ?_
    split <;> [exact RecM.ScopeWF.pure trivial; exact this]
  intro state
  unfold F2
  refine (isDefEqProofIrrel.scopeWF firstStructural secondStructural).bind fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine (lazyDeltaReduction.scopeWF firstStructural secondStructural).bind
    fun _ _ _ reduction => ?_
  split
  · cases reduction.1
  all_goals try exact RecM.ScopeWF.pure trivial
  obtain ⟨⟨_, firstReduced, _⟩, ⟨_, secondReduced, _⟩⟩ := reduction
  extract_lets unitComparison
  suffices ∀ {state}, (unitComparison ⟨⟩).ScopeWF context state (fun _ _ => True) by
    split
    · split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · split <;> [skip; exact this]
      let .proj firstBody firstProjection := firstReduced
      let .proj secondBody secondProjection := secondReduced
      simp_all
      refine (lazyDeltaProjReduction_scopeWF firstReduced secondReduced).bind
        fun _ _ _ _ => ?_
      split <;> [exact RecM.ScopeWF.pure trivial; exact this]
    · exact this
  intro state
  unfold unitComparison
  simp only [Bind.bind, ReaderT.bind]
  refine (whnfCore.scopeWF firstReduced).bind
    fun _ _ _ ⟨_, ⟨_, firstNormalized, _⟩, _⟩ => ?_
  refine (whnfCore.scopeWF secondReduced).bind
    fun _ _ _ ⟨_, ⟨_, secondNormalized, _⟩, _⟩ => ?_
  split
  · exact (isDefEqCore.scopeWF firstNormalized secondNormalized).mono fun _ _ _ _ => trivial
  refine (isDefEqApp.scopeWF firstReduced secondReduced).bind
    fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine (tryEtaExpansion.scopeWF firstReduced secondReduced).bind
    fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine (tryEtaStruct.scopeWF firstReduced secondReduced).bind
    fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine (tryStringLitExpansion.scopeWF firstReduced secondReduced).bind
    fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  refine (isDefEqUnitLike.scopeWF firstReduced secondReduced).bind
    fun _ _ _ _ => ?_
  split <;> [exact RecM.ScopeWF.pure trivial; skip]
  exact RecM.ScopeWF.pure trivial

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
