import Lean4Lean.Verify.InductiveGeneratedRuleResult
import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

/- Unfold the concrete non-K application branch of the native dispatcher.  The
   hypotheses mirror the branch decisions, so the resulting equation is the
   exact RHS assembled by `inductiveReduceRec`, including its trailing-argument
   conditional.  The lawful-monad premise is used only to expose the supplied
   successful normalization and structure-adaptation callbacks. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_normalizedApplication
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedFn normalizedArg : Expr} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.app normalizedFn normalizedArg))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [notK, Bool.false_eq_true, ↓reduceIte]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [adapted]
  simp only [pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- The same dispatcher equation for a normalized nullary constructor.  Keeping
   this branch separate makes the constructor expression visible to the rule
   lookup instead of hiding it behind an application decomposition. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_normalizedConstant
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.const normalizedName normalizedLevels))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [notK, Bool.false_eq_true, ↓reduceIte]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [adapted]
  simp only [pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- Nat literals are converted to their canonical constructor before the rule
   lookup.  This records that conversion and the exact output equation in one
   theorem, without treating the literal as an arbitrary reducer result. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_normalizedNatLiteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr} {value : Nat} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.natVal value)))
    (ruleLookup : getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (fieldCount : rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
            (Expr.natLitToConstructor value).getAppArgs.size (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
          (Expr.natLitToConstructor value).getAppArgs.size (Expr.natLitToConstructor value).getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [notK, Bool.false_eq_true, ↓reduceIte]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- String literals first normalize their constructor expansion.  The second
   callback and rule lookup are therefore explicit premises of this branch
   equation. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_normalizedStringLiteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {text : String} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [notK, Bool.false_eq_true, ↓reduceIte]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [expanded]
  simp only [pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- K-like recursors first adapt their major through `toCtorWhenK`, then follow
   the same normalization and constructor-adaptation path.  This equation
   keeps that extra callback explicit while preserving the exact RHS assembly. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_kNormalizedApplication
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedFn normalizedArg : Expr}
    {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.app normalizedFn normalizedArg))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [isK, if_true]
  rw [kAdapted]
  simp only [Bind.bind, pure_bind]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [adaptedStruct]
  simp only [pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- K-like recursors can still reach the literal branches after their major has
   been adapted.  Nat literals then use their canonical constructor directly
   for rule lookup and field extraction. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_kNormalizedNatLiteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted : Expr} {value : Nat} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.natVal value)))
    (ruleLookup : getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (fieldCount : rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
            (Expr.natLitToConstructor value).getAppArgs.size
              (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
          (Expr.natLitToConstructor value).getAppArgs.size
            (Expr.natLitToConstructor value).getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [isK, if_true]
  rw [kAdapted]
  simp only [Bind.bind, pure_bind]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- The corresponding K String branch expands the literal before looking up the
   generated constructor rule. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_kNormalizedStringLiteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {text : String} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [isK, if_true]
  rw [kAdapted]
  simp only [Bind.bind, pure_bind]
  rw [normalized]
  simp only [Bind.bind, pure_bind]
  rw [expanded]
  simp only [pure_bind]
  rw [ruleLookup]
  dsimp only
  simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- Every nonliteral normalization result follows the structure-adaptation
   default branch.  The two literal exclusions make that branch decision
   explicit while leaving the adapted constructor and exact RHS visible. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_normalizedStructure
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major normalized constructor : Expr} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalizedEq : normalize major = pure normalized)
    (notNat : ∀ value, normalized ≠ .lit (.natVal value))
    (notString : ∀ text, normalized ≠ .lit (.strVal text))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
      pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [notK, Bool.false_eq_true, ↓reduceIte]
  rw [normalizedEq]
  simp only [Bind.bind, pure_bind]
  cases normalized
  case lit literal =>
    cases literal
    case natVal value => exact (notNat value rfl).elim
    case strVal text => exact (notString text rfl).elim
  all_goals
    rw [adapted]
    simp only [pure_bind]
    rw [ruleLookup]
    dsimp only
    simp [Nat.not_lt_of_ge fieldCount, levelCount]

/- The K path has the same nonliteral default branch after its preliminary
   `toCtorWhenK` conversion. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_kNormalizedStructure
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted normalized constructor : Expr} {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalizedEq : normalize adapted = pure normalized)
    (notNat : ∀ value, normalized ≠ .lit (.natVal value))
    (notString : ∀ text, normalized ≠ .lit (.strVal text))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
      pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length) :
    inductiveReduceRec environment expression normalize infer compare =
      if info.getMajorIdx + 1 < expression.getAppArgs.size then
        pure (some <| mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
      else
        pure (some <| mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) := by
  unfold inductiveReduceRec
  rw [head]
  simp only [lookup]
  rw [selected]
  simp only [isK, if_true]
  rw [kAdapted]
  simp only [Bind.bind, pure_bind]
  rw [normalizedEq]
  simp only [Bind.bind, pure_bind]
  cases normalized
  case lit literal =>
    cases literal
    case natVal value => exact (notNat value rfl).elim
    case strVal text => exact (notString text rfl).elim
  all_goals
    rw [adaptedStruct]
    simp only [pure_bind]
    rw [ruleLookup]
    dsimp only
    simp [Nat.not_lt_of_ge fieldCount, levelCount]

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

/- The generated replacement list is the exact endpoint expected by the
   dispatcher characterization.  Keep that equation in the target package so
   consumers do not have to introduce an arbitrary intermediate `reduced` and
   then separately recover its shape. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
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
      pure (some (rule.rhs.mkAppList replacements)))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  exact ⟨reduction, translated.trExpr envWF.ordered targetWF.tr.wf, typed, sortArity⟩

/- A dispatcher equation with a conditional assembled RHS can be converted to
   the exact generated replacement-list equation once its conditional shape is
   supplied. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {rule : RecursorRule} {target : MLCtx} {_count : Nat}
    {arguments : List VExpr} {_resultType : VExpr} {insertionLift : Lift}
    {replacements : List Expr} {rhsSemantic : VExpr} {condition : Prop} [Decidable condition]
    {withTrailing withoutTrailing : Expr}
    (dispatch : inductiveReduceRec environment expression normalize infer compare =
      if condition then pure (some withTrailing) else pure (some withoutTrailing))
    (outputShape : (if condition then withTrailing else withoutTrailing) =
      rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have exactReduction : inductiveReduceRec environment expression normalize infer compare =
      pure (some (rule.rhs.mkAppList replacements)) := by
    rw [dispatch]
    by_cases h : condition
    · simp only [h, if_true] at outputShape ⊢
      rw [outputShape]
    · simp only [h, if_false] at outputShape ⊢
      rw [outputShape]
  exact GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    translated typed sortArity exactReduction envWF targetWF

theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr} {value : Nat} {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.natVal value)))
    (ruleLookup : getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (fieldCount : rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length)
    (outputShape :
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
            (Expr.natLitToConstructor value).getAppArgs.size
              (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
          (Expr.natLitToConstructor value).getAppArgs.size
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have dispatch := inductiveReduceRec.eq_some_of_normalizedNatLiteral
    (environment := environment) expression normalize infer compare head lookup selected notK
    normalized ruleLookup fieldCount levelCount
  exact GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    (condition := info.getMajorIdx + 1 < expression.getAppArgs.size)
    (withTrailing := mkAppRange
      (mkAppRange
        (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
          0 info.getFirstIndexIdx expression.getAppArgs)
        ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
        (Expr.natLitToConstructor value).getAppArgs.size
          (Expr.natLitToConstructor value).getAppArgs)
      (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
    (withoutTrailing := mkAppRange
      (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
        0 info.getFirstIndexIdx expression.getAppArgs)
      ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
      (Expr.natLitToConstructor value).getAppArgs.size
        (Expr.natLitToConstructor value).getAppArgs)
    dispatch outputShape translated typed sortArity envWF targetWF

theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {text : String} {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length)
    (outputShape :
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) = rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have dispatch := inductiveReduceRec.eq_some_of_normalizedStringLiteral
    (environment := environment) expression normalize infer compare head lookup selected notK
    normalized expanded ruleLookup fieldCount levelCount
  exact GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    (condition := info.getMajorIdx + 1 < expression.getAppArgs.size)
    (withTrailing := mkAppRange
      (mkAppRange
        (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
          0 info.getFirstIndexIdx expression.getAppArgs)
        (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
          constructor.getAppArgs)
      (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
    (withoutTrailing := mkAppRange
      (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
        0 info.getFirstIndexIdx expression.getAppArgs)
      (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
        constructor.getAppArgs)
    dispatch outputShape translated typed sortArity envWF targetWF

/- Consume the characterized K application branch at the generated target
   endpoint.  The only remaining native-to-generated obligation is the
   explicit equality between the assembled conditional RHS and the generated
   replacement list. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedFn normalizedArg : Expr}
    {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.app normalizedFn normalizedArg))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length)
    (outputShape :
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) = rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have dispatch := inductiveReduceRec.eq_some_of_kNormalizedApplication
    (environment := environment) expression normalize infer compare head lookup selected isK
    kAdapted normalized adaptedStruct ruleLookup fieldCount levelCount
  exact GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    (condition := info.getMajorIdx + 1 < expression.getAppArgs.size)
    (withTrailing := mkAppRange
      (mkAppRange
        (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
          0 info.getFirstIndexIdx expression.getAppArgs)
        (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
          constructor.getAppArgs)
      (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
    (withoutTrailing := mkAppRange
      (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
        0 info.getFirstIndexIdx expression.getAppArgs)
      (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
        constructor.getAppArgs)
    dispatch outputShape translated typed sortArity envWF targetWF

theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted : Expr} {value : Nat} {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.natVal value)))
    (ruleLookup : getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (fieldCount : rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length)
    (outputShape :
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
            (Expr.natLitToConstructor value).getAppArgs.size
              (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
          (Expr.natLitToConstructor value).getAppArgs.size
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have dispatch := inductiveReduceRec.eq_some_of_kNormalizedNatLiteral
    (environment := environment) expression normalize infer compare head lookup selected isK
    kAdapted normalized ruleLookup fieldCount levelCount
  exact GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    (condition := info.getMajorIdx + 1 < expression.getAppArgs.size)
    (withTrailing := mkAppRange
      (mkAppRange
        (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
          0 info.getFirstIndexIdx expression.getAppArgs)
        ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
        (Expr.natLitToConstructor value).getAppArgs.size
          (Expr.natLitToConstructor value).getAppArgs)
      (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
    (withoutTrailing := mkAppRange
      (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
        0 info.getFirstIndexIdx expression.getAppArgs)
      ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields)
      (Expr.natLitToConstructor value).getAppArgs.size
        (Expr.natLitToConstructor value).getAppArgs)
    dispatch outputShape translated typed sortArity envWF targetWF

theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {text : String} {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (ruleLookup : getRecRuleFor info constructor = some rule)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelCount : levels.length = info.levelParams.length)
    (outputShape :
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
              constructor.getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
            constructor.getAppArgs) = rule.rhs.mkAppList replacements)
    (translated : TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))))
    (typed : env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (_resultType.lift' insertionLift))
    (sortArity : env.SortArity universes.length target.vlctx.toCtx _count
      (_resultType.lift' insertionLift))
    (envWF : env.WF) (targetWF : target.WF env universes) :
    inductiveReduceRec environment expression normalize infer compare =
        pure (some (rule.rhs.mkAppList replacements)) ∧
      TrExpr env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift) := by
  have dispatch := inductiveReduceRec.eq_some_of_kNormalizedStringLiteral
    (environment := environment) expression normalize infer compare head lookup selected isK
    kAdapted normalized expanded ruleLookup fieldCount levelCount
  exact GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
    (env := env) (universes := universes) (_stats := _stats) (_motives := _motives)
    (_minors := _minors) (_ctx := _ctx) (_constructor := _constructor) (_minor := _minor)
    (rule := rule) (target := target) (_count := _count) (arguments := arguments)
    (_resultType := _resultType) (insertionLift := insertionLift)
    (replacements := replacements) (rhsSemantic := rhsSemantic)
    (condition := info.getMajorIdx + 1 < expression.getAppArgs.size)
    (withTrailing := mkAppRange
      (mkAppRange
        (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
          0 info.getFirstIndexIdx expression.getAppArgs)
        (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
          constructor.getAppArgs)
      (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs)
    (withoutTrailing := mkAppRange
      (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
        0 info.getFirstIndexIdx expression.getAppArgs)
      (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
        constructor.getAppArgs)
    dispatch outputShape translated typed sortArity envWF targetWF

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
