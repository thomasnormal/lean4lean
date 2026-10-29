import Lean4Lean.Verify.InductiveGeneratedRuleResult
import Lean4Lean.Verify.InductiveHeaderComparisonHelperTransport
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

/- K-like recursors also reach the ordinary constant branch after their major
   has been adapted.  Keep that adaptation and the nullary constructor result
   explicit before the rule lookup, matching the non-K constant equation. -/
theorem _root_.Lean4Lean.inductiveReduceRec.eq_some_of_kNormalizedConstant
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (environment : Kernel.Environment) (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    {rule : RecursorRule}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.const normalizedName normalizedLevels))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
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

/- The native reducer assembles its result from three slices: the recursor
   prefix, the constructor fields, and any trailing arguments.  This helper
   turns explicit list decompositions for those slices into the single
   generated replacement-list shape used by the target consumer. -/
theorem dispatcherConditionalShapeOfReplacementDecomposition
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor : Expr} {rule : RecursorRule}
    {headArgs omitted trailing ctorPrefix fields replacements : List Expr}
    (argsShape : expression.getAppArgs.toList = headArgs ++ omitted ++ trailing)
    (argsPrefixLength : headArgs.length = info.getFirstIndexIdx)
    (argsMajorEnd : (headArgs ++ omitted).length = info.getMajorIdx + 1)
    (argsEnd : (headArgs ++ omitted ++ trailing).length = expression.getAppArgs.size)
    (ctorShape : constructor.getAppArgs.toList = ctorPrefix ++ fields)
    (ctorPrefixLength : ctorPrefix.length = constructor.getAppArgs.size - rule.nfields)
    (ctorEnd : (ctorPrefix ++ fields).length = constructor.getAppArgs.size)
    (levelShape : rule.rhs.instantiateLevelParams info.levelParams levels = rule.rhs)
    (replacementShape : replacements = headArgs ++ fields ++ trailing) :
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
          constructor.getAppArgs) = rule.rhs.mkAppList replacements := by
  rw [levelShape]
  have prefixSlice :
      mkAppRange rule.rhs 0 info.getFirstIndexIdx expression.getAppArgs =
        rule.rhs.mkAppList headArgs := by
    apply Expr.mkAppRange_eq (e := rule.rhs) (args := expression.getAppArgs)
      (l₁ := []) (l₂ := headArgs) (l₃ := omitted ++ trailing)
    · simpa [argsShape, List.append_assoc]
    · simp
    · simpa [argsPrefixLength]
  have fieldSlice :
      mkAppRange (rule.rhs.mkAppList headArgs)
        (constructor.getAppArgs.size - rule.nfields) constructor.getAppArgs.size
        constructor.getAppArgs =
        (rule.rhs.mkAppList headArgs).mkAppList fields := by
    apply Expr.mkAppRange_eq (e := rule.rhs.mkAppList headArgs)
      (args := constructor.getAppArgs) (l₁ := ctorPrefix) (l₂ := fields) (l₃ := [])
    · simpa [ctorShape]
    · exact ctorPrefixLength
    · exact ctorEnd
  by_cases hTrailing : info.getMajorIdx + 1 < expression.getAppArgs.size
  · simp only [hTrailing, if_true]
    have trailingSlice :
        mkAppRange ((rule.rhs.mkAppList headArgs).mkAppList fields)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs =
          ((rule.rhs.mkAppList headArgs).mkAppList fields).mkAppList trailing := by
      apply Expr.mkAppRange_eq
        (e := (rule.rhs.mkAppList headArgs).mkAppList fields)
        (args := expression.getAppArgs) (l₁ := headArgs ++ omitted) (l₂ := trailing) (l₃ := [])
      · simpa [argsShape, List.append_assoc]
      · exact argsMajorEnd
      · exact argsEnd
    rw [prefixSlice, fieldSlice, trailingSlice]
    simp [Expr.mkAppList_append, replacementShape, List.append_assoc]
  · simp only [hTrailing, if_false]
    have trailingNil : trailing = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hSize : info.getMajorIdx + 1 ≥ expression.getAppArgs.size := by omega
      have hCombined : (headArgs ++ omitted).length + trailing.length =
          expression.getAppArgs.size := by
        simpa [List.length_append, Nat.add_assoc] using argsEnd
      omega
    rw [prefixSlice, fieldSlice]
    simp [Expr.mkAppList_append, replacementShape, trailingNil, List.append_assoc]

/- The selected major premise determines canonical list slices for the
   recursor application.  This is the list-level metadata bridge used by the
   generated-rule consumer: the prefix ends at `getFirstIndexIdx`, the middle
   slice ends immediately after the major, and the final slice contains any
   trailing application arguments. -/
theorem dispatcherArgumentSliceDecomposition
    {expression : Expr} {info : RecursorVal} {major : Expr}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major) :
    ∃ (headArgs omitted trailing : List Expr),
      expression.getAppArgs.toList = headArgs ++ omitted ++ trailing ∧
      headArgs.length = info.getFirstIndexIdx ∧
      (headArgs ++ omitted).length = info.getMajorIdx + 1 ∧
      (headArgs ++ omitted ++ trailing).length = expression.getAppArgs.size := by
  let args := expression.getAppArgs.toList
  let headArgs := args.take info.getFirstIndexIdx
  let omitted := (args.drop info.getFirstIndexIdx).take (info.numIndices + 1)
  let trailing := args.drop (info.getMajorIdx + 1)
  have hmajorArray : info.getMajorIdx < expression.getAppArgs.size := by
    by_contra hbound
    have hnone : expression.getAppArgs[info.getMajorIdx]? = none :=
      Array.getElem?_eq_none (show expression.getAppArgs.size ≤ info.getMajorIdx by omega)
    rw [hnone] at selected
    cases selected
  have hmajor : info.getMajorIdx < args.length := by
    simpa [args] using hmajorArray
  have hfirst : info.getFirstIndexIdx ≤ args.length := by
    dsimp [RecursorVal.getMajorIdx, RecursorVal.getFirstIndexIdx] at hmajor ⊢
    omega
  have hmiddle : info.numIndices + 1 ≤ args.length - info.getFirstIndexIdx := by
    dsimp [RecursorVal.getMajorIdx, RecursorVal.getFirstIndexIdx] at hmajor ⊢
    omega
  have hargsSize : args.length = expression.getAppArgs.size := by simp [args]
  have hdrop : (args.drop info.getFirstIndexIdx).drop (info.numIndices + 1) =
      args.drop (info.getMajorIdx + 1) := by
    rw [List.drop_drop]
    dsimp [RecursorVal.getMajorIdx, RecursorVal.getFirstIndexIdx]
    congr 1
  have hmajorIndex : info.getMajorIdx = info.getFirstIndexIdx + info.numIndices := by
    simp [RecursorVal.getMajorIdx, RecursorVal.getFirstIndexIdx, Nat.add_assoc]
  refine ⟨headArgs, omitted, trailing, ?_, ?_, ?_, ?_⟩
  · dsimp [headArgs, omitted, trailing]
    change args = args.take info.getFirstIndexIdx ++
      (args.drop info.getFirstIndexIdx).take (info.numIndices + 1) ++
      args.drop (info.getMajorIdx + 1)
    calc
      args = args.take info.getFirstIndexIdx ++ args.drop info.getFirstIndexIdx :=
        (List.take_append_drop _ _).symm
      _ = args.take info.getFirstIndexIdx ++
          ((args.drop info.getFirstIndexIdx).take (info.numIndices + 1) ++
            (args.drop info.getFirstIndexIdx).drop (info.numIndices + 1)) := by
        exact congrArg (fun xs => args.take info.getFirstIndexIdx ++ xs)
          (List.take_append_drop (info.numIndices + 1) (args.drop info.getFirstIndexIdx)).symm
      _ = args.take info.getFirstIndexIdx ++
          ((args.drop info.getFirstIndexIdx).take (info.numIndices + 1) ++
            args.drop (info.getMajorIdx + 1)) := by
        exact congrArg (fun xs => args.take info.getFirstIndexIdx ++
          ((args.drop info.getFirstIndexIdx).take (info.numIndices + 1) ++ xs)) hdrop
      _ = args.take info.getFirstIndexIdx ++
          (args.drop info.getFirstIndexIdx).take (info.numIndices + 1) ++
            args.drop (info.getMajorIdx + 1) :=
        (List.append_assoc (args.take info.getFirstIndexIdx)
          ((args.drop info.getFirstIndexIdx).take (info.numIndices + 1))
          (args.drop (info.getMajorIdx + 1))).symm
  · dsimp [headArgs]
    rw [List.length_take]
    exact Nat.min_eq_left hfirst
  · dsimp [headArgs, omitted]
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left hfirst, Nat.min_eq_left hmiddle, hmajorIndex]
    omega
  · dsimp [headArgs, omitted, trailing]
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left hfirst, Nat.min_eq_left hmiddle, hmajorIndex]
    omega

/- The rule field count determines canonical prefix and field slices for the
   constructor application. -/
theorem dispatcherConstructorSliceDecomposition
    {constructor : Expr} {rule : RecursorRule}
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size) :
    ∃ (ctorPrefix fields : List Expr),
      constructor.getAppArgs.toList = ctorPrefix ++ fields ∧
      ctorPrefix.length = constructor.getAppArgs.size - rule.nfields ∧
      (ctorPrefix ++ fields).length = constructor.getAppArgs.size := by
  let args := constructor.getAppArgs.toList
  let ctorPrefix := args.take (constructor.getAppArgs.size - rule.nfields)
  let fields := args.drop (constructor.getAppArgs.size - rule.nfields)
  have hsize : args.length = constructor.getAppArgs.size := by simp [args]
  have hprefix : constructor.getAppArgs.size - rule.nfields ≤ args.length := by
    simpa [hsize] using Nat.sub_le _ _
  refine ⟨ctorPrefix, fields, ?_, ?_, ?_⟩
  · dsimp [ctorPrefix, fields]
    exact (List.take_append_drop _ _).symm
  · dsimp [ctorPrefix]
    rw [List.length_take]
    exact Nat.min_eq_left hprefix
  · dsimp [ctorPrefix, fields]
    rw [List.length_append, List.length_take, List.length_drop]
    simp [hsize]

/- Combine the two canonical decompositions and choose the generated
   replacement list.  The remaining level-instantiation relation is kept as an
   explicit premise because stored recursor RHS metadata can still contain
   level parameters in the general frontend contract. -/
theorem dispatcherConditionalShapeOfCanonicalDecomposition
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr} {rule : RecursorRule}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (levelShape : rule.rhs.instantiateLevelParams info.levelParams levels = rule.rhs) :
    ∃ (headArgs omitted trailing ctorPrefix fields replacements : List Expr),
      expression.getAppArgs.toList = headArgs ++ omitted ++ trailing ∧
      headArgs.length = info.getFirstIndexIdx ∧
      (headArgs ++ omitted).length = info.getMajorIdx + 1 ∧
      (headArgs ++ omitted ++ trailing).length = expression.getAppArgs.size ∧
      constructor.getAppArgs.toList = ctorPrefix ++ fields ∧
      ctorPrefix.length = constructor.getAppArgs.size - rule.nfields ∧
      (ctorPrefix ++ fields).length = constructor.getAppArgs.size ∧
      replacements = headArgs ++ fields ++ trailing ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements := by
  obtain ⟨headArgs, omitted, trailing, hargs, hprefix, hmajor, hend⟩ :=
    dispatcherArgumentSliceDecomposition (expression := expression) (info := info)
      (major := major) selected
  obtain ⟨ctorPrefix, fields, hctor, hctorPrefix, hctorEnd⟩ :=
    dispatcherConstructorSliceDecomposition (constructor := constructor) (rule := rule) fieldCount
  let replacements := headArgs ++ fields ++ trailing
  refine ⟨headArgs, omitted, trailing, ctorPrefix, fields, replacements, hargs, hprefix,
    hmajor, hend, hctor, hctorPrefix, hctorEnd, rfl, ?_⟩
  exact dispatcherConditionalShapeOfReplacementDecomposition hargs hprefix hmajor hend
    hctor hctorPrefix hctorEnd levelShape rfl

/- A caller that has the generated RHS no-level-parameter receipt only needs
   the final replacement-list equation.  Hide the intermediate list slices
   while retaining the native field-count obligation. -/
theorem dispatcherConditionalShapeOfCanonicalOutput
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr} {rule : RecursorRule}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (fieldCount : rule.nfields ≤ constructor.getAppArgs.size)
    (noLevelParam : rule.rhs.hasLevelParam' = false) :
    ∃ replacements : List Expr,
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements := by
  have levelShape : rule.rhs.instantiateLevelParams info.levelParams levels = rule.rhs := by
    rw [Expr.instantiateLevelParams_eq]
    exact Expr.instantiateLevelParamsCore_eq_self noLevelParam
  obtain ⟨headArgs, omitted, trailing, ctorPrefix, fields, replacements,
    hargs, hprefix, hmajor, hend, hctor, hctorPrefix, hctorEnd, hreplacement, houtput⟩ :=
    dispatcherConditionalShapeOfCanonicalDecomposition selected fieldCount levelShape
  exact ⟨replacements, houtput⟩

/- Project the stored constructor metadata to the field-count premise consumed
   by the native reducer.  The caller supplies the native constructor-argument
   bound for the looked-up `ConstructorVal`; the metadata then aligns that
   value with the corresponding recursor rule. -/
theorem dispatcherFieldCountOfConstructorMetadata
    {types : Array InductiveType} {environment : Kernel.Environment}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (constructor : Expr)
    (constructorFieldBound : ∀ info : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo info) →
      info.numFields ≤ constructor.getAppArgs.size) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo info) ∧
      rule.nfields ≤ constructor.getAppArgs.size := by
  obtain ⟨recursor, recursorLookup, entries⟩ := metadata parent parentBound
  obtain ⟨rule, info, ruleAt, constructorLookup, ruleName, ruleFields⟩ :=
    entries index constructorEntry constructorEntryAt
  refine ⟨recursor, rule, info, recursorLookup, ruleAt, constructorLookup, ?_⟩
  rw [ruleFields]
  exact constructorFieldBound info constructorLookup

/- The native structure-normalization receipt records its constructor arity
   with `getAppNumArgs`; the reducer slices the `getAppArgs` array.  Keep that
   small representation bridge explicit while deriving the field bound from the
   receipt's checked arity. -/
theorem dispatcherConstructorFieldBoundOfNativeEtaStructEntryReceipt
    {context : TypeChecker.Context} {constructor : Expr} {info : ConstructorVal}
    (receipt : NativeEtaStructEntryReceipt context constructor info)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size) :
    info.numFields ≤ constructor.getAppArgs.size := by
  have harity : constructor.getAppNumArgs = info.numParams + info.numFields :=
    beq_iff_eq.mp receipt.arity
  omega

/- Combine the stored constructor/rule alignment with the canonical output
   projection.  This is the first metadata-driven endpoint that returns an
   exact generated replacement-list equation for a registered rule. -/
theorem dispatcherConditionalShapeOfMetadataOutput
    {types : Array InductiveType} {environment : Kernel.Environment}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (constructor : Expr)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements := by
  obtain ⟨recursor, rule, ctorInfo, hrecursor, hrule, hconstructor, hfieldCount⟩ :=
    dispatcherFieldCountOfConstructorMetadata metadata parent parentBound index
      constructorEntry constructorEntryAt constructor constructorFieldBound
  have hnoLevelParam := noLevelParam recursor rule hrule
  obtain ⟨replacements, hshape⟩ :=
    dispatcherConditionalShapeOfCanonicalOutput selected hfieldCount hnoLevelParam
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor, hshape⟩

/- Consume the native structure-normalization receipt at the metadata-driven
   output boundary.  The constructor head and context/environment equality
   identify the receipt's constructor value with the metadata lookup; the
   explicit `getAppNumArgs = getAppArgs.size` bridge then supplies the field
   bound required by the reducer slice theorem. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceipt
    {types : Array InductiveType} {environment : Kernel.Environment}
    {context : TypeChecker.Context} {constructorEntry : Constructor}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr} {ctorInfo : ConstructorVal}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (receipt : NativeEtaStructEntryReceipt context constructor ctorInfo)
    (contextEnvEq : context.env = environment)
    (constructorHead : constructor.getAppFn = .const constructorEntry.name levels)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements := by
  obtain ⟨receiptName, receiptLevels, receiptHead, receiptLookup⟩ := receipt.lookup
  have hhead : Expr.const receiptName receiptLevels =
      Expr.const constructorEntry.name levels := receiptHead.symm.trans constructorHead
  have hname : receiptName = constructorEntry.name := by
    injection hhead
  subst receiptName
  rw [contextEnvEq] at receiptLookup
  have constructorFieldBound : ∀ metadataInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
        metadataInfo.numFields ≤ constructor.getAppArgs.size := by
    intro metadataInfo metadataLookup
    have hlookup : some (ConstantInfo.ctorInfo metadataInfo) =
        some (ConstantInfo.ctorInfo ctorInfo) :=
      metadataLookup.symm.trans receiptLookup
    have hconst : ConstantInfo.ctorInfo metadataInfo = ConstantInfo.ctorInfo ctorInfo :=
      Option.some.inj hlookup
    have hinfo : metadataInfo = ctorInfo := ConstantInfo.ctorInfo.inj hconst
    subst metadataInfo
    exact dispatcherConstructorFieldBoundOfNativeEtaStructEntryReceipt receipt appNumArgsEq
  obtain ⟨recursor, rule, metadataInfo, hrecursor, hrule, hconstructor, hfieldCount⟩ :=
    dispatcherFieldCountOfConstructorMetadata metadata parent parentBound index
      constructorEntry constructorEntryAt constructor constructorFieldBound
  have hnoLevelParam := noLevelParam recursor rule hrule
  obtain ⟨replacements, hshape⟩ :=
    dispatcherConditionalShapeOfCanonicalOutput selected hfieldCount hnoLevelParam
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape⟩

/- Carry the executable rule lookup alongside the metadata-derived output
   shape.  The lookup callback is intentionally explicit: metadata alignment
   identifies the stored rule, while proving that `getRecRuleFor` selects that
   same rule remains a separate frontend obligation. -/
theorem dispatcherConditionalShapeOfMetadataOutputWithRuleLookup
    {types : Array InductiveType} {environment : Kernel.Environment}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor, hshape⟩ :=
    dispatcherConditionalShapeOfMetadataOutput (types := types) (environment := environment)
      (expression := expression) (levels := levels) (info := info) (constructor := constructor)
      (major := major) metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructor constructorFieldBound noLevelParam
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor, hshape,
    ruleLookup recursor rule ctorInfo hrule hconstructor⟩

/- Keep the metadata-derived field bound in the same existential package as
   the output shape and executable rule lookup.  This avoids asking each
   generated-target wrapper to repeat the rule-field alignment proof. -/
theorem dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
    {types : Array InductiveType} {environment : Kernel.Environment}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule := by
  obtain ⟨recursor, hrecursor, entries⟩ := metadata parent parentBound
  obtain ⟨rule, ctorInfo, hrule, hconstructor, _ruleName, hfields⟩ :=
    entries index constructorEntry constructorEntryAt
  have hfieldCount : rule.nfields ≤ constructor.getAppArgs.size := by
    rw [hfields]
    exact constructorFieldBound ctorInfo hconstructor
  have hnoLevelParam := noLevelParam recursor rule hrule
  obtain ⟨replacements, hshape⟩ :=
    dispatcherConditionalShapeOfCanonicalOutput selected hfieldCount hnoLevelParam
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, ruleLookup recursor rule ctorInfo hrule hconstructor⟩

/- The receipt-backed form packages the native structure constructor with the
   same executable rule lookup.  This is the boundary consumed by a generated
   target theorem: native normalization supplies the constructor metadata,
   while rule selection remains an explicit callback. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookup
    {types : Array InductiveType} {environment : Kernel.Environment}
    {context : TypeChecker.Context} {constructorEntry : Constructor}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr} {ctorInfo : ConstructorVal}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (receipt : NativeEtaStructEntryReceipt context constructor ctorInfo)
    (contextEnvEq : context.env = environment)
    (constructorHead : constructor.getAppFn = .const constructorEntry.name levels)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule := by
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceipt metadata
      parent parentBound index constructorEntryAt selected receipt contextEnvEq constructorHead
      appNumArgsEq noLevelParam
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, ruleLookup recursor rule metadataInfo hrule hconstructor⟩

/- Pair the structure-adaptation callback with the receipt-backed metadata
   package.  Both ordinary and K-normalized structure consumers use the same
   `toCtorWhenStruct` result after their branch-specific normalization. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookupAndAdaptation
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {context : TypeChecker.Context} {constructorEntry : Constructor}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major normalized : Expr} {ctorInfo : ConstructorVal}
    (normalize infer : Expr → m Expr)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
      pure constructor)
    (receipt : NativeEtaStructEntryReceipt context constructor ctorInfo)
    (contextEnvEq : context.env = environment)
    (constructorHead : constructor.getAppFn = .const constructorEntry.name levels)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
        pure constructor := by
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookup
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor) (major := major)
      metadata parent parentBound index constructorEntryAt selected receipt contextEnvEq
      constructorHead appNumArgsEq noLevelParam ruleLookup
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, adapted⟩

/- Literal branches use a canonical constructor expression produced by the
   reducer itself.  Specialize the metadata package to that expression while
   keeping constructor-value bounds and executable rule selection explicit. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfNormalizedNatLiteral
    {types : Array InductiveType} {environment : Kernel.Environment}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major : Expr} {value : Nat}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
      rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size ∧
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
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule := by
  exact dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
    (types := types) (environment := environment) (expression := expression)
    (levels := levels) (info := info) (constructor := Expr.natLitToConstructor value)
    metadata parent parentBound index constructorEntry constructorEntryAt selected
    constructorFieldBound noLevelParam ruleLookup

/- Pair ordinary normalized-constant adaptation with the metadata-driven
   output package.  The constructor expression is supplied by the adaptation
   receipt, while metadata still derives the registered rule field bound and
   exact replacement-list shape.
-/
theorem dispatcherConditionalShapeOfMetadataOutputOfNormalizedConstant
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    (normalize infer : Expr → m Expr)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenStruct environment normalize infer info.getMajorInduct
        (.const normalizedName normalizedLevels) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, adapted⟩

/- Pair ordinary normalized-application adaptation with the metadata-driven
   output package, keeping the normalized application and constructor result
   explicit alongside the registered-rule witnesses. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfNormalizedApplication
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedFn normalizedArg : Expr}
    (normalize infer : Expr → m Expr)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenStruct environment normalize infer info.getMajorInduct
        (.app normalizedFn normalizedArg) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, adapted⟩

/- Pair the K-normalized application adaptations with the same metadata-driven
   output package.  Both the preliminary K conversion and the subsequent
   structure conversion remain visible at the package boundary. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfKNormalizedApplication
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedFn normalizedArg : Expr}
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenK environment normalize infer compare info major = pure adapted ∧
      toCtorWhenStruct environment normalize infer info.getMajorInduct
        (.app normalizedFn normalizedArg) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNormalizedApplication
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      (normalizedFn := normalizedFn) (normalizedArg := normalizedArg)
      normalize infer metadata parent parentBound index constructorEntry constructorEntryAt
      selected adaptedStruct constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, kAdapted, hadapted⟩

/- Pair the K-normalized constant adaptations with the metadata-driven output
   package, retaining both the preliminary K conversion and the constant's
   structure adaptation at the registered-rule boundary. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfKNormalizedConstant
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenK environment normalize infer compare info major = pure adapted ∧
      toCtorWhenStruct environment normalize infer info.getMajorInduct
        (.const normalizedName normalizedLevels) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, kAdapted, adaptedStruct⟩

/- Pair the K conversion with String-literal expansion at the metadata-driven
   output boundary, so both callbacks and the registered-rule witnesses share
   one constructor package. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfKNormalizedStringLiteralExpansion
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {text : String}
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      toCtorWhenK environment normalize infer compare info major = pure adapted ∧
      normalize (.strLitToConstructor text) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, kAdapted, expanded⟩

/- Pair the K conversion with the canonical Nat constructor at the metadata
   boundary, retaining the same field bound and rule-selection witnesses. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfKNormalizedNatLiteral
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {major adapted : Expr} {value : Nat}
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ (Expr.natLitToConstructor value).getAppArgs.size ∧
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
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule ∧
      toCtorWhenK environment normalize infer compare info major = pure adapted := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info)
      (constructor := Expr.natLitToConstructor value)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, kAdapted⟩

/- Pair String-literal expansion with the metadata-driven output package.  The
   expansion callback remains explicit, but downstream target consumers can no
   longer accidentally combine it with a shape or rule lookup from another
   constructor package. -/
theorem dispatcherConditionalShapeOfMetadataOutputOfStringLiteralExpansion
    {m : Type → Type} [Monad m]
    {types : Array InductiveType} {environment : Kernel.Environment}
    (normalize : Expr → m Expr)
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntry : Constructor)
    (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    {expression : Expr} {levels : List Level} {info : RecursorVal}
    {constructor major : Expr} {text : String}
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (ctorInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      getRecRuleFor info constructor = some rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (ctorInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) ∧
      rule.nfields ≤ constructor.getAppArgs.size ∧
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements ∧
      getRecRuleFor info constructor = some rule ∧
      normalize (.strLitToConstructor text) = pure constructor := by
  obtain ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt selected
      constructorFieldBound noLevelParam ruleLookup
  exact ⟨recursor, rule, ctorInfo, replacements, hrecursor, hrule, hconstructor,
    hfieldCount, hshape, hruleLookup, expanded⟩

theorem instantiateLevelParams_eq_self_of_noLevelParam
    {expression : Expr} {parameters : List Name} {levels : List Level}
    (noLevelParam : expression.hasLevelParam' = false) :
    expression.instantiateLevelParams parameters levels = expression := by
  rw [Expr.instantiateLevelParams_eq]
  exact Expr.instantiateLevelParamsCore_eq_self noLevelParam

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

theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major normalized constructor : Expr} {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
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
  have dispatch := inductiveReduceRec.eq_some_of_normalizedStructure
    (environment := environment) expression normalize infer compare head lookup selected notK
    normalizedEq notNat notString adapted ruleLookup fieldCount levelCount
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

/- Combine the receipt-backed metadata package with the generated target
   endpoint for the ordinary structure branch.  The generated translation,
   typing, and sort-arity facts are supplied as a dependent witness family so
   this theorem does not hide any target-side obligation behind an existential
   choice of rule or replacement list. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major normalized constructor : Expr}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType} {context : TypeChecker.Context}
    {constructorEntry : Constructor} {ctorInfo : ConstructorVal}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalizedEq : normalize major = pure normalized)
    (notNat : ∀ value, normalized ≠ .lit (.natVal value))
    (notString : ∀ text, normalized ≠ .lit (.strVal text))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
      pure constructor)
    (receipt : NativeEtaStructEntryReceipt context constructor ctorInfo)
    (contextEnvEq : context.env = environment)
    (constructorHead : constructor.getAppFn = .const constructorEntry.name levels)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookupAndAdaptation
      normalize infer metadata parent parentBound index constructorEntryAt selected adapted receipt
      contextEnvEq constructorHead appNumArgsEq noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected notK
      normalizedEq notNat notString hadapted hruleLookup hfieldCount levelCount hshape
      translated typed sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩

/- Connect the Nat-literal metadata package to the generated target result. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr} {value : Nat}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.natVal value)))
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields) (Expr.natLitToConstructor value).getAppArgs.size
              (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields) (Expr.natLitToConstructor value).getAppArgs.size
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNormalizedNatLiteral
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (value := value)
      metadata parent parentBound index constructorEntry constructorEntryAt
      selected constructorFieldBound noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected notK
      normalized hruleLookup hfieldCount levelCount hshape translated typed sortArity
      envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩


/- Connect the ordinary normalized-constant metadata package to the generated target result. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.const normalizedName normalizedLevels))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
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
  have dispatch := inductiveReduceRec.eq_some_of_normalizedConstant
    (environment := environment) expression normalize infer compare head lookup selected notK
    normalized adapted ruleLookup fieldCount levelCount
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

theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.const normalizedName normalizedLevels))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNormalizedConstant
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      (normalizedName := normalizedName) (normalizedLevels := normalizedLevels)
      normalize infer metadata parent parentBound index constructorEntry constructorEntryAt
      selected adapted constructorFieldBound noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected notK
      normalized hadapted hruleLookup hfieldCount levelCount hshape translated typed
      sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩


/- Consume the characterized K-normalized constant branch at the generated
   target endpoint, retaining the explicit K and structure adaptations. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
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
    (normalized : normalize adapted = pure (.const normalizedName normalizedLevels))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
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
  have dispatch := inductiveReduceRec.eq_some_of_kNormalizedConstant
    (environment := environment) expression normalize infer compare head lookup selected isK
    kAdapted normalized adapted ruleLookup fieldCount levelCount
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


/- Connect the K-normalized constant metadata package to the generated target result. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedName : Name} {normalizedLevels : List Level}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.const normalizedName normalizedLevels))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.const normalizedName normalizedLevels) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hkAdapted, hadaptedStruct⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfKNormalizedConstant
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      (normalizedName := normalizedName) (normalizedLevels := normalizedLevels)
      normalize infer compare metadata parent parentBound index constructorEntry
      constructorEntryAt selected kAdapted adaptedStruct constructorFieldBound noLevelParam
      ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected isK
      hkAdapted normalized hadaptedStruct hruleLookup hfieldCount levelCount hshape translated
      typed sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩


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


/- Connect the K-normalized Nat-literal metadata package to the generated target result. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr} {value : Nat}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.natVal value)))
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ (Expr.natLitToConstructor value).getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info (Expr.natLitToConstructor value) = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      (if info.getMajorIdx + 1 < expression.getAppArgs.size then
        mkAppRange
          (mkAppRange
            (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
              0 info.getFirstIndexIdx expression.getAppArgs)
            ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields) (Expr.natLitToConstructor value).getAppArgs.size
              (Expr.natLitToConstructor value).getAppArgs)
          (info.getMajorIdx + 1) expression.getAppArgs.size expression.getAppArgs
       else
        mkAppRange
          (mkAppRange (rule.rhs.instantiateLevelParams info.levelParams levels)
            0 info.getFirstIndexIdx expression.getAppArgs)
          ((Expr.natLitToConstructor value).getAppArgs.size - rule.nfields) (Expr.natLitToConstructor value).getAppArgs.size
            (Expr.natLitToConstructor value).getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hkAdapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfKNormalizedNatLiteral
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (value := value)
      normalize infer compare metadata parent parentBound index constructorEntry
      constructorEntryAt selected kAdapted constructorFieldBound noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected isK
      hkAdapted normalized hruleLookup hfieldCount levelCount hshape translated
      typed sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩



/- Connect the String-literal metadata package to the generated target result. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {text : String}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hexpanded⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfStringLiteralExpansion
      (types := types) (environment := environment) (expression := expression)
      (normalize := normalize)
      (levels := levels) (info := info)
      (constructor := constructor)
      metadata parent parentBound index constructorEntry constructorEntryAt
      selected expanded constructorFieldBound noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected notK
      normalized hexpanded hruleLookup hfieldCount levelCount hshape translated typed
      sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩



/- Connect the K-normalized String-literal metadata package to the generated target result. -/
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


theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {text : String}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.lit (.strVal text)))
    (expanded : normalize (.strLitToConstructor text) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hkAdapted, hexpanded⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfKNormalizedStringLiteralExpansion
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info)
      (constructor := constructor)
      normalize infer compare metadata parent parentBound index constructorEntry
      constructorEntryAt selected kAdapted expanded constructorFieldBound noLevelParam
      ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected isK
      hkAdapted normalized hexpanded hruleLookup hfieldCount levelCount hshape translated
      typed sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩




/- Combine the receipt-backed metadata package with the generated target endpoint for the K-normalized structure branch. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted normalized constructor : Expr} {rule : RecursorRule}
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
    (normalizedEq : normalize adapted = pure normalized)
    (notNat : ∀ value, normalized ≠ .lit (.natVal value))
    (notString : ∀ text, normalized ≠ .lit (.strVal text))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct normalized =
      pure constructor)
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
  have dispatch := inductiveReduceRec.eq_some_of_kNormalizedStructure
    (environment := environment) expression normalize infer compare head lookup selected isK
    kAdapted normalizedEq notNat notString adaptedStruct ruleLookup fieldCount levelCount
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

theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major normalized constructor : Expr}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType} {context : TypeChecker.Context}
    {constructorEntry : Constructor} {ctorInfo : ConstructorVal}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
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
    (receipt : NativeEtaStructEntryReceipt context constructor ctorInfo)
    (contextEnvEq : context.env = environment)
    (constructorHead : constructor.getAppFn = .const constructorEntry.name levels)
    (appNumArgsEq : constructor.getAppNumArgs = constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookupAndAdaptation
      normalize infer metadata parent parentBound index constructorEntryAt selected adaptedStruct receipt
      contextEnvEq constructorHead appNumArgsEq noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, typed, sortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected isK
      kAdapted normalizedEq notNat notString hadapted hruleLookup hfieldCount levelCount
      hshape translated typed sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, typed, sortArity⟩

/- Consume the characterized ordinary application branch at the generated
   target endpoint.  The normalized application and structure adaptation stay
   explicit, as do the rule lookup, field bound, and generated output shape.
   This is the ordinary counterpart of the K-normalized application endpoint
   below.
-/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedFn normalizedArg : Expr}
    {rule : RecursorRule}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic : VExpr}
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.app normalizedFn normalizedArg))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
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
  have dispatch := inductiveReduceRec.eq_some_of_normalizedApplication
    (environment := environment) expression normalize infer compare head lookup selected notK
    normalized adapted ruleLookup fieldCount levelCount
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

/- Connect the ordinary normalized-application metadata package to the
   generated target result.  The metadata package supplies the registered rule
   and replacement shape; the existing ordinary application consumer then
   carries the dispatcher result through the target witnesses. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major constructor : Expr} {normalizedFn normalizedArg : Expr}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (notK : info.k = false)
    (normalized : normalize major = pure (.app normalizedFn normalizedArg))
    (adapted : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfNormalizedApplication
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      (normalizedFn := normalizedFn) (normalizedArg := normalizedArg)
      normalize infer metadata parent parentBound index constructorEntry constructorEntryAt
      selected adapted constructorFieldBound noLevelParam ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, targetTyped, targetSortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected notK
      normalized hadapted hruleLookup hfieldCount levelCount hshape translated typed sortArity
      envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, targetTyped, targetSortArity⟩

/- Consume the characterized ordinary nullary-constant branch at the generated
   target endpoint.  The normalized constant and structure adaptation remain
   explicit, together with the same rule, shape, and target witnesses as the
   application branch.
-/
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

/- Connect the K-normalized application metadata package to the generated
   target result.  Both K and structure adaptations stay explicit while the
   existing K application consumer supplies the dispatcher transport. -/
theorem GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationMetadataExact
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {environment : Kernel.Environment} (expression : Expr)
    (normalize infer : Expr → m Expr) (compare : Expr → Expr → m Bool)
    {recursorName : Name} {levels : List Level} {info : RecursorVal}
    {major adapted constructor : Expr} {normalizedFn normalizedArg : Expr}
    {env : VEnv} {universes : List Name} {_stats : InductiveStats}
    {_motives _minors : Array Expr} {_ctx : Context} {_constructor : Constructor}
    {_minor : Expr} {target : MLCtx} {_count : Nat} {arguments : List VExpr}
    {_resultType : VExpr} {insertionLift : Lift} {rhsSemantic : VExpr}
    {types : Array InductiveType}
    {constructorEntry : Constructor}
    (metadata : RuleConstructorFieldMetadata types environment)
    (parent : Nat) (parentBound : parent < types.size)
    (index : Nat) (constructorEntryAt : types[parent]!.ctors[index]? = some constructorEntry)
    (head : expression.getAppFn = .const recursorName levels)
    (lookup : environment.find? recursorName = some (.recInfo info))
    (selected : expression.getAppArgs[info.getMajorIdx]? = some major)
    (isK : info.k = true)
    (kAdapted : toCtorWhenK environment normalize infer compare info major = pure adapted)
    (normalized : normalize adapted = pure (.app normalizedFn normalizedArg))
    (adaptedStruct : toCtorWhenStruct environment normalize infer info.getMajorInduct
      (.app normalizedFn normalizedArg) = pure constructor)
    (constructorFieldBound : ∀ ctorInfo : ConstructorVal,
      environment.find? constructorEntry.name = some (.ctorInfo ctorInfo) →
      ctorInfo.numFields ≤ constructor.getAppArgs.size)
    (noLevelParam : ∀ (recursor : RecursorVal) (rule : RecursorRule),
      recursor.rules[index]? = some rule → rule.rhs.hasLevelParam' = false)
    (ruleLookup : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal),
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
      getRecRuleFor info constructor = some rule)
    (generated : ∀ (recursor : RecursorVal) (rule : RecursorRule)
      (metadataInfo : ConstructorVal) (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) →
      recursor.rules[index]? = some rule →
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) →
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
            constructor.getAppArgs) = rule.rhs.mkAppList replacements →
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (_resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx _count
        (_resultType.lift' insertionLift))
    (levelCount : levels.length = info.levelParams.length)
    (envWF : env.WF) (targetWF : target.WF env universes) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (metadataInfo : ConstructorVal)
      (replacements : List Expr),
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      recursor.rules[index]? = some rule ∧
      environment.find? constructorEntry.name = some (.ctorInfo metadataInfo) ∧
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
  obtain ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
      hfieldCount, hshape, hruleLookup, hkAdapted, hadapted⟩ :=
    dispatcherConditionalShapeOfMetadataOutputOfKNormalizedApplication
      (types := types) (environment := environment) (expression := expression)
      (levels := levels) (info := info) (constructor := constructor)
      (normalizedFn := normalizedFn) (normalizedArg := normalizedArg)
      normalize infer compare metadata parent parentBound index constructorEntry
      constructorEntryAt selected kAdapted adaptedStruct constructorFieldBound noLevelParam
      ruleLookup
  obtain ⟨translated, typed, sortArity⟩ := generated recursor rule metadataInfo replacements
    hrecursor hrule hconstructor hshape
  obtain ⟨reduction, ordinary, targetTyped, targetSortArity⟩ :=
    GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationExact
      (environment := environment) (env := env) (universes := universes) (_stats := _stats)
      (_motives := _motives) (_minors := _minors) (_ctx := _ctx)
      (_constructor := _constructor) (_minor := _minor) (target := target)
      (_count := _count) (arguments := arguments) (_resultType := _resultType)
      (insertionLift := insertionLift) (replacements := replacements)
      (rhsSemantic := rhsSemantic) expression normalize infer compare head lookup selected isK
      hkAdapted normalized hadapted hruleLookup hfieldCount levelCount hshape translated typed
      sortArity envWF targetWF
  exact ⟨recursor, rule, metadataInfo, replacements, hrecursor, hrule, hconstructor,
    reduction, ordinary, targetTyped, targetSortArity⟩

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

/- The target-result spelling denotes the same exact endpoint.  Keep the
   reducer equation in this relation: an ``exact`` target result must retain
   the native result/RHS link rather than merely repeat the translated target
   witnesses. -/
abbrev GeneratedRecursorRuleIotaTargetResultExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule} : Prop :=
  GeneratedRecursorRuleIotaTargetReductionExact
    (environment := environment) (expression := expression)
    (normalize := normalize) (infer := infer) (compare := compare)
    (env := env) (universes := universes) (stats := stats)
    (motives := motives) (minors := minors) (ctx := ctx)
    (constructor := constructor) (minor := minor) (rule := rule)

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

/- Consume the complete indexed generated-rule producer at the stored-rule
   reducer boundary.  Ordered recursor metadata recovers the constructor,
   minor, and source index for each stored rule; the native reduction callback
   then supplies the exact stored-RHS equation required by the target package. -/
theorem LocalRecursorRuleRhsScope.completeRuleResultSemanticsAndIotaTargetReductionExact
    {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression : Expr}
    {normalize infer : Expr → m Expr}
    {compare : Expr → Expr → m Bool}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : VEnv} {universes : List Name}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx environment)
    (ordered : OrderedRecursorRules types environment)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule))
    (reduction : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      ∀ (target : MLCtx) (count : Nat) (arguments : List VExpr)
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
    ∀ parent, parent < types.size → ∃ recursor,
      environment.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ rule ∈ recursor.rules, ∃ (index : Nat) (ctor : Constructor) (minor : Expr)
        (semantic : VExpr),
        types[parent]!.ctors[index]? = some ctor ∧
        infos[parent]!.minors[index]? = some minor ∧
        recursor.rules[index]? = some rule ∧
        TrExprS env universes [] rule.rhs semantic ∧
        GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule ∧
        GeneratedRecursorRuleIotaTargetReductionExact
          (environment := environment) (expression := expression)
          (normalize := normalize) (infer := infer) (compare := compare)
          (env := env) (universes := universes) (stats := stats)
          (motives := infos.map (·.motive)) (minors := infos.flatMap (·.minors))
          (ctx := ctx) (constructor := ctor) (minor := minor) (rule := rule) := by
  intro parent hparent
  obtain ⟨recursor, lookup, entries⟩ :=
    hscope.completeRuleResultSemanticsAndIotaBaseAndTargetResults ordered head parent hparent
  refine ⟨recursor, lookup, ?_⟩
  intro rule hmem
  obtain ⟨index, ctor, minor, semantic, ctorLookup, minorLookup, ruleLookup,
    semanticResult, generated, _baseTarget⟩ := entries rule hmem
  refine ⟨index, ctor, minor, semantic, ctorLookup,
    minorLookup, ruleLookup, semanticResult, generated, ?_⟩
  · exact GeneratedConstructorRuleRhsResult.iotaTargetReductionOfExact generated
      (fun target count arguments resultType insertionLift replacements rhsSemantic translated
        typed sortArity => reduction parent recursor index ctor rule minor target count arguments resultType insertionLift
        replacements rhsSemantic translated typed sortArity)

end Lean4Lean.AddInductive
