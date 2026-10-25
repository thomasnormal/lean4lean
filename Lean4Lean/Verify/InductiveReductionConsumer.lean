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
