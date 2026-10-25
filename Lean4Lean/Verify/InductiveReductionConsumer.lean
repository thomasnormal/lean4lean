import Lean4Lean.Verify.InductiveGeneratedRuleResult
import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

/- Consume a successful native reduction at the generated-rule boundary.  The
   executable reducer and generated replacement list are deliberately connected
   by the explicit `outputShape` premise; this keeps the remaining native branch
   proof separate from the semantic transport proved here. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRec
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {rule : RecursorRule}
    {target : MLCtx} {_count : Nat} {arguments : List VExpr} {_resultType : VExpr}
    {insertionLift : Lift} {replacements : List Expr} {rhsSemantic : VExpr}
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (reduction : inductiveReduceRec environment expression normalize infer compare =
      pure (some reduced))
    (outputShape : reduced = rule.rhs.mkAppList replacements)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare = pure (some reduced) ∧
      TrExpr env universes target.vlctx reduced
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) := by
  exact ⟨reduction, outputShape ▸ translated.trExpr envWF.ordered targetWF.tr.wf⟩

end Lean4Lean.AddInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

/- Keep the target typing and sort-arity witnesses alongside the reducer
   transport.  This is the small endpoint used after a generated target-iota
   package has been destructured; it avoids reopening the target translation
   merely to attach the terminal typing facts. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecWithType
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {rule : RecursorRule}
    {target : MLCtx} {_count : Nat} {arguments : List VExpr} {_resultType : VExpr}
    {insertionLift : Lift} {replacements : List Expr} {rhsSemantic : VExpr}
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (reduction : inductiveReduceRec environment expression normalize infer compare =
      pure (some reduced))
    (outputShape : reduced = rule.rhs.mkAppList replacements)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare = pure (some reduced) ∧
      TrExpr env universes target.vlctx reduced
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  obtain ⟨reduction, ordinary⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRec
      (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
      (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
      (rule := rule) (target := target) (_count := _count) (arguments := arguments)
      (_resultType := _resultType) (insertionLift := insertionLift)
      (replacements := replacements) (rhsSemantic := rhsSemantic)
      (translated := translated) (reduction := reduction) (outputShape := outputShape)
      (envWF := envWF) (targetWF := targetWF)
  exact ⟨reduction, ordinary, typed, sortArity⟩

end Lean4Lean.AddInductive
