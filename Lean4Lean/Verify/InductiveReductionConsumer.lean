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

/- A reducer consumer needs the generated target witnesses and the native
   output-shape equation at the same existential boundary.  Keep those facts
   paired so the ordinary checker transport cannot accidentally mix witnesses
   from different generated rules. -/
abbrev GeneratedRecursorRuleIotaTargetReduction
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule} : Prop :=
  ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
    (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count
      (resultType.lift' insertionLift) ∧
    inductiveReduceRec environment expression normalize infer compare =
      pure (some reduced) ∧
    reduced = rule.rhs.mkAppList replacements

theorem GeneratedRecursorRuleIotaTargetReduction.toOrdinary
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (package : GeneratedRecursorRuleIotaTargetReduction
      (environment := environment) (expression := expression) (reduced := reduced)
      (normalize := normalize) (infer := infer) (compare := compare)
      (env := env) (universes := universes) (stats := stats) (motives := motives)
      (minors := minors) (ctx := ctx) (constructor := constructor) (minor := minor)
      (rule := rule))
    (envWF : env.WF) (targetWF : ∀ target : MLCtx, target.WF env universes) :
    ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      inductiveReduceRec environment expression normalize infer compare = pure (some reduced) ∧
      TrExpr env universes target.vlctx reduced
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  rcases package with ⟨target, count, arguments, resultType, insertionLift,
    replacements, rhsSemantic, translated, typed, sortArity, reduction, outputShape⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecWithType
      (env := env) (universes := universes) (_stats := stats) (_motives := motives)
      (_minors := minors) (_ctx := ctx) (_constructor := constructor) (_minor := minor)
      (rule := rule) (target := target) (_count := count) (arguments := arguments)
      (_resultType := resultType) (insertionLift := insertionLift)
      (replacements := replacements) (rhsSemantic := rhsSemantic)
      (translated := translated) (typed := typed) (sortArity := sortArity)
      (reduction := reduction) (outputShape := outputShape) envWF (targetWF target)⟩

/- The complete generated-rule result already contains the target endpoint.
   This eliminator lets a native reducer callback attach its success and shape
   equations to that exact endpoint without reopening the constructor package. -/
theorem GeneratedConstructorRuleRhsResult.iotaTargetReductionOf
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule)
    (reduction : ∀ (target : MLCtx) (count : Nat) (arguments : List VExpr)
      (resultType : VExpr) (insertionLift : Lift) (replacements : List Expr)
      (rhsSemantic : VExpr),
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) →
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) →
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) →
      inductiveReduceRec environment expression normalize infer compare = pure (some reduced) ∧
      reduced = rule.rhs.mkAppList replacements) :
    GeneratedRecursorRuleIotaTargetReduction
      (environment := environment) (expression := expression) (reduced := reduced)
      (normalize := normalize) (infer := infer) (compare := compare)
      (env := env) (universes := universes) (stats := stats) (motives := motives)
      (minors := minors) (ctx := ctx) (constructor := constructor) (minor := minor)
      (rule := rule) := by
  obtain ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    translated, typed, sortArity⟩ := result.iotaKind.targetResult
  obtain ⟨reduction, outputShape⟩ := reduction target count arguments resultType insertionLift
    replacements rhsSemantic translated typed sortArity
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    translated, typed, sortArity, reduction, outputShape⟩

/- The executable reducer callback can state its exact generated RHS result in
   one equation.  This relation omits the redundant arbitrary `reduced` and
   shape fields, so the callback cannot accidentally pair a rule with another
   reducer output. -/
abbrev GeneratedRecursorRuleIotaTargetReductionExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule} : Prop :=
  ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
    (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count
      (resultType.lift' insertionLift) ∧
    inductiveReduceRec environment expression normalize infer compare =
      pure (some (rule.rhs.mkAppList replacements))

theorem GeneratedConstructorRuleRhsResult.iotaTargetReductionOfExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule)
    (reduction : ∀ (target : MLCtx) (count : Nat) (arguments : List VExpr)
      (resultType : VExpr) (insertionLift : Lift) (replacements : List Expr)
      (rhsSemantic : VExpr),
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) →
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) →
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) →
      inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements))) :
    GeneratedRecursorRuleIotaTargetReductionExact
      (environment := environment) (expression := expression)
      (normalize := normalize) (infer := infer) (compare := compare)
      (env := env) (universes := universes) (stats := stats) (motives := motives)
      (minors := minors) (ctx := ctx) (constructor := constructor) (minor := minor)
      (rule := rule) := by
  obtain ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    translated, typed, sortArity⟩ := result.iotaKind.targetResult
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    translated, typed, sortArity,
    reduction target count arguments resultType insertionLift replacements rhsSemantic
      translated typed sortArity⟩

theorem GeneratedRecursorRuleIotaTargetReductionExact.toOrdinary
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (package : GeneratedRecursorRuleIotaTargetReductionExact
      (environment := environment) (expression := expression)
      (normalize := normalize) (infer := infer) (compare := compare)
      (env := env) (universes := universes) (stats := stats) (motives := motives)
      (minors := minors) (ctx := ctx) (constructor := constructor) (minor := minor)
      (rule := rule))
    (envWF : env.WF) (targetWF : ∀ target : MLCtx, target.WF env universes) :
    ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  rcases package with ⟨target, count, arguments, resultType, insertionLift,
    replacements, rhsSemantic, translated, typed, sortArity, reduction⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    reduction, translated.trExpr envWF.ordered (targetWF target).tr.wf, typed, sortArity⟩

end Lean4Lean.AddInductive
