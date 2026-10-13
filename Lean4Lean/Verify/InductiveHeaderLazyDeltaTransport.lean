import Lean4Lean.Verify.InductiveHeaderComparisonHelperTransport

namespace Lean4Lean
open Lean hiding Environment Exception

inductive NativeDeltaSide where
  | first
  | second

def NativeDeltaSide.select : NativeDeltaSide → Expr → Expr → Expr
  | .first, firstExpression, _ => firstExpression
  | .second, _, secondExpression => secondExpression

def NativeDeltaSide.replace : NativeDeltaSide → Expr → Expr → Expr → Expr × Expr
  | .first, _, secondExpression, normalized => (normalized, secondExpression)
  | .second, firstExpression, _, normalized => (firstExpression, normalized)

def NativeDeltaSide.other : NativeDeltaSide → NativeDeltaSide
  | .first => .second
  | .second => .first

inductive NativeLazyDeltaPlan where
  | unknown
  | projection (side : NativeDeltaSide)
  | unfold (side : NativeDeltaSide)
  | both (arguments : Bool)

def nativeLazyDeltaPlan (environment : Kernel.Environment) (state : TypeChecker.State)
    (first second : Expr) : NativeLazyDeltaPlan :=
  match TypeChecker.Inner.isDelta environment first, TypeChecker.Inner.isDelta environment second with
  | none, none => .unknown
  | some _, none => .projection .second
  | none, some _ => .projection .first
  | some firstDefinition, some secondDefinition =>
    if firstDefinition.hints.lt' secondDefinition.hints then .unfold .second
    else if secondDefinition.hints.lt' firstDefinition.hints then .unfold .first
    else .both (first.isApp && second.isApp && ptrEqConstantInfo firstDefinition secondDefinition
      && firstDefinition.hints.isRegular && !TypeChecker.Inner.failedBefore state.failure first second)

theorem nativeLazyDeltaPlan.headerShadow_eq
    (agreement : HeaderAxiomLookupAgreement changed actual shadow)
    (state : TypeChecker.State) (first second : Expr) :
    nativeLazyDeltaPlan actual state first second = nativeLazyDeltaPlan shadow state first second := by
  unfold nativeLazyDeltaPlan
  rw [agreement.delta first, agreement.delta second]

def TypeChecker.Inner.nativeDeltaUnfold (expression : Expr) : TypeChecker.RecM Expr := do
  whnfCore (← unfoldDefinition expression).get! (cheapProj := true)

def TypeChecker.Inner.nativeDeltaContinue (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  return match ← quickIsDefEq first second with
  | .undef => .continue first second
  | .true => .true
  | .false => .false first second

def TypeChecker.Inner.nativeDeltaSingle (side : NativeDeltaSide) (first second : Expr) :
    TypeChecker.RecM TypeChecker.ReductionStatus := do
  let normalized ← nativeDeltaUnfold (side.select first second)
  let pair := side.replace first second normalized
  nativeDeltaContinue pair.1 pair.2

def TypeChecker.Inner.nativeDeltaPair (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  let normalizedFirst ← nativeDeltaUnfold first
  let normalizedSecond ← nativeDeltaUnfold second
  nativeDeltaContinue normalizedFirst normalizedSecond

def TypeChecker.Inner.nativeDeltaArguments (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  if Level.isEquivList first.getAppFn.constLevels! second.getAppFn.constLevels! then
    if ← isDefEqArgs first second then return .true
  cacheFailure first second
  nativeDeltaPair first second

def TypeChecker.Inner.nativeLazyDeltaRun (plan : NativeLazyDeltaPlan) (first second : Expr) :
    TypeChecker.RecM TypeChecker.ReductionStatus := do
  match plan with
  | .unknown => return .unknown first second
  | .projection side =>
    if let some normalized ← tryUnfoldProjApp (side.select first second) then
      let pair := side.replace first second normalized
      nativeDeltaContinue pair.1 pair.2
    else nativeDeltaSingle side.other first second
  | .unfold side => nativeDeltaSingle side first second
  | .both arguments =>
    if arguments then nativeDeltaArguments first second else nativeDeltaPair first second

theorem TypeChecker.Inner.lazyDeltaReductionStep.entry_eq (first second : Expr) :
    lazyDeltaReductionStep first second = (do
      let environment ← getEnv
      let state ← get
      nativeLazyDeltaRun (nativeLazyDeltaPlan environment state first second) first second) := by
  funext methods context state
  dsimp only [lazyDeltaReductionStep, nativeLazyDeltaPlan, TypeChecker.getEnv, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read,
    ReaderT.read, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.bind, Except.pure]
  cases TypeChecker.Inner.isDelta context.env first <;> cases TypeChecker.Inner.isDelta context.env second
  all_goals dsimp only [nativeLazyDeltaRun, NativeDeltaSide.select, NativeDeltaSide.replace,
    NativeDeltaSide.other, nativeDeltaSingle, nativeDeltaPair, nativeDeltaArguments, nativeDeltaUnfold,
    nativeDeltaContinue, Bind.bind, ReaderT.bind, ReaderT.pure, Pure.pure]
  all_goals try rfl
  split <;> try rfl
  split <;> try rfl

def NativeDeltaUnfoldCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop :=
  ∀ unfolded nextState,
    TypeChecker.Inner.unfoldDefinition expression actualMethods actualContext state = .ok (unfolded, nextState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore unfolded.get! true)
      (shadowMethods.whnfCore unfolded.get! true) actualContext shadowContext nextState

def NativeDeltaQuickCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  ∀ nextState, TypeChecker.Inner.nativeQuickProbe first second false actualContext state = .ok (false, nextState) →
    NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second

structure NativeDeltaSingleCallbacks (side : NativeDeltaSide) (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  unfolding : NativeDeltaUnfoldCallbacks actualMethods shadowMethods actualContext shadowContext state (side.select first second)
  continuation : ∀ normalized nextState,
    TypeChecker.Inner.nativeDeltaUnfold (side.select first second) actualMethods actualContext state = .ok (normalized, nextState) →
    NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext nextState
      (side.replace first second normalized).1 (side.replace first second normalized).2

structure NativeDeltaPairCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstUnfolding : NativeDeltaUnfoldCallbacks actualMethods shadowMethods actualContext shadowContext state first
  secondUnfolding : ∀ normalizedFirst firstState,
    TypeChecker.Inner.nativeDeltaUnfold first actualMethods actualContext state = .ok (normalizedFirst, firstState) →
    NativeDeltaUnfoldCallbacks actualMethods shadowMethods actualContext shadowContext firstState second
  continuation : ∀ normalizedFirst firstState normalizedSecond secondState,
    TypeChecker.Inner.nativeDeltaUnfold first actualMethods actualContext state = .ok (normalizedFirst, firstState) →
    TypeChecker.Inner.nativeDeltaUnfold second actualMethods actualContext firstState = .ok (normalizedSecond, secondState) →
    NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext secondState normalizedFirst normalizedSecond

def NativeDeltaArgumentCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  ∀ currentState firstFunction firstArgument secondFunction secondArgument,
    NativeArgumentComparisonReachable actualMethods actualContext state first second currentState
      (.app firstFunction firstArgument) (.app secondFunction secondArgument) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstArgument secondArgument)
      (shadowMethods.isDefEqCore firstArgument secondArgument) actualContext shadowContext currentState

structure NativeDeltaArgumentsCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  arguments : Level.isEquivList first.getAppFn.constLevels! second.getAppFn.constLevels! = true →
    NativeDeltaArgumentCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  differentLevels : Level.isEquivList first.getAppFn.constLevels! second.getAppFn.constLevels! = false →
    ∀ cachedState, TypeChecker.Inner.cacheFailure first second actualContext state = .ok ((), cachedState) →
    NativeDeltaPairCallbacks actualMethods shadowMethods actualContext shadowContext cachedState first second
  rejectedArguments : ∀ argumentState cachedState,
    Level.isEquivList first.getAppFn.constLevels! second.getAppFn.constLevels! = true →
    TypeChecker.Inner.isDefEqArgs first second actualMethods actualContext state = .ok (false, argumentState) →
    TypeChecker.Inner.cacheFailure first second actualContext argumentState = .ok ((), cachedState) →
    NativeDeltaPairCallbacks actualMethods shadowMethods actualContext shadowContext cachedState first second

structure NativeDeltaProjectionCallbacks (side : NativeDeltaSide) (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  normalization : (side.select first second).getAppFn.isProj = true →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore (side.select first second) false)
      (shadowMethods.whnfCore (side.select first second) false) actualContext shadowContext state
  continuation : ∀ normalized nextState,
    TypeChecker.Inner.tryUnfoldProjApp (side.select first second) actualMethods actualContext state = .ok (some normalized, nextState) →
    NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext nextState
      (side.replace first second normalized).1 (side.replace first second normalized).2
  fallback : ∀ nextState,
    TypeChecker.Inner.tryUnfoldProjApp (side.select first second) actualMethods actualContext state = .ok (none, nextState) →
    NativeDeltaSingleCallbacks side.other actualMethods shadowMethods actualContext shadowContext nextState first second

def NativeLazyDeltaStepCallbacks (plan : NativeLazyDeltaPlan) (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  match plan with
  | .unknown => True
  | .projection side => NativeDeltaProjectionCallbacks side actualMethods shadowMethods actualContext shadowContext state first second
  | .unfold side => NativeDeltaSingleCallbacks side actualMethods shadowMethods actualContext shadowContext state first second
  | .both true => NativeDeltaArgumentsCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  | .both false => NativeDeltaPairCallbacks actualMethods shadowMethods actualContext shadowContext state first second

theorem TypeChecker.Inner.nativeDeltaUnfold.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (expression : Expr)
    (callbacks : NativeDeltaUnfoldCallbacks actualMethods shadowMethods actualContext shadowContext state expression) :
    TypeChecker.M.SuccessTransport (nativeDeltaUnfold expression actualMethods) (nativeDeltaUnfold expression shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDeltaUnfold, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (by
      intro result accepted
      rw [unfoldDefinition.headerShadowTransport actualMethods shadowMethods actualContext shadowContext agreement] at accepted
      exact accepted)
  intro unfolded nextState accepted
  exact callbacks unfolded nextState accepted

theorem TypeChecker.Inner.nativeDeltaContinue.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDeltaContinue first second actualMethods) (nativeDeltaContinue first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDeltaContinue, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (quickIsDefEq.transport _ _ _ _ _ _ _ false callbacks)
  intro comparison nextState _
  exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.nativeDeltaSingle.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (side : NativeDeltaSide) (first second : Expr)
    (callbacks : NativeDeltaSingleCallbacks side actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDeltaSingle side first second actualMethods) (nativeDeltaSingle side first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDeltaSingle, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (nativeDeltaUnfold.transport _ _ _ _ agreement _ _ callbacks.unfolding)
  intro normalized nextState accepted
  exact nativeDeltaContinue.transport _ _ _ _ _ _ _ (callbacks.continuation _ _ accepted)

theorem TypeChecker.Inner.nativeDeltaPair.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaPairCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDeltaPair first second actualMethods) (nativeDeltaPair first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDeltaPair, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (nativeDeltaUnfold.transport _ _ _ _ agreement _ _ callbacks.firstUnfolding)
  intro normalizedFirst firstState firstAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (nativeDeltaUnfold.transport _ _ _ _ agreement _ _ (callbacks.secondUnfolding _ _ firstAccepted))
  intro normalizedSecond secondState secondAccepted
  exact nativeDeltaContinue.transport _ _ _ _ _ _ _ (callbacks.continuation _ _ _ _ firstAccepted secondAccepted)

theorem TypeChecker.Inner.tryUnfoldProjApp.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr)
    (callback : expression.getAppFn.isProj = true →
      TypeChecker.M.SuccessTransport (actualMethods.whnfCore expression false)
        (shadowMethods.whnfCore expression false) actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (tryUnfoldProjApp expression actualMethods) (tryUnfoldProjApp expression shadowMethods)
      actualContext shadowContext state := by
  unfold tryUnfoldProjApp
  cases matching : expression.getAppFn.isProj with
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    simp only [Bool.not, Bool.false_eq_true, ↓reduceIte, pure_bind]
    dsimp only [Bind.bind, ReaderT.bind, whnfCore]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callback matching)
    intro normalized nextState _
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.nativeDeltaArguments.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaArgumentsCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDeltaArguments first second actualMethods) (nativeDeltaArguments first second shadowMethods)
      actualContext shadowContext state := by
  unfold nativeDeltaArguments
  cases matching : Level.isEquivList first.getAppFn.constLevels! second.getAppFn.constLevels! with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    dsimp only [Bind.bind, ReaderT.bind, liftM, MonadLift.monadLift, MonadLiftT.monadLift]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (by intro result accepted; exact accepted)
    intro ignored cachedState accepted
    cases ignored
    exact nativeDeltaPair.transport _ _ _ _ agreement _ _ _ (callbacks.differentLevels matching _ accepted)
  | true =>
    simp only [↓reduceIte]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (isDefEqArgs.transport _ _ _ _ _ _ _ (callbacks.arguments matching))
    intro equal argumentState accepted
    cases equal with
    | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      change TypeChecker.M.SuccessTransport
        ((pure PUnit.unit : TypeChecker.M PUnit) >>= fun _ => cacheFailure first second >>= fun _ => nativeDeltaPair first second actualMethods)
        ((pure PUnit.unit : TypeChecker.M PUnit) >>= fun _ => cacheFailure first second >>= fun _ => nativeDeltaPair first second shadowMethods)
        actualContext shadowContext argumentState
      simp only [pure_bind]
      dsimp only [Bind.bind, ReaderT.bind, liftM, MonadLift.monadLift, MonadLiftT.monadLift]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (by intro result accepted; exact accepted)
      intro ignored cachedState cached
      cases ignored
      exact nativeDeltaPair.transport _ _ _ _ agreement _ _ _ (callbacks.rejectedArguments _ _ matching accepted cached)

theorem TypeChecker.Inner.nativeLazyDeltaRun.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (plan : NativeLazyDeltaPlan) (first second : Expr)
    (callbacks : NativeLazyDeltaStepCallbacks plan actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeLazyDeltaRun plan first second actualMethods) (nativeLazyDeltaRun plan first second shadowMethods)
      actualContext shadowContext state := by
  cases plan with
  | unknown => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | unfold side => exact nativeDeltaSingle.transport _ _ _ _ agreement _ _ _ _ callbacks
  | both arguments =>
    cases arguments with
    | true => exact nativeDeltaArguments.transport _ _ _ _ agreement _ _ _ callbacks
    | false => exact nativeDeltaPair.transport _ _ _ _ agreement _ _ _ callbacks
  | projection side =>
    dsimp only [nativeLazyDeltaRun, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (tryUnfoldProjApp.transport _ _ _ _ _ _ callbacks.normalization)
    intro normalized nextState accepted
    cases normalized with
    | none => exact nativeDeltaSingle.transport _ _ _ _ agreement _ _ _ _ (callbacks.fallback _ accepted)
    | some normalized => exact nativeDeltaContinue.transport _ _ _ _ _ _ _ (callbacks.continuation _ _ accepted)

theorem TypeChecker.Inner.lazyDeltaReductionStep.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeLazyDeltaStepCallbacks (nativeLazyDeltaPlan actualContext.env state first second)
      actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (lazyDeltaReductionStep first second actualMethods) (lazyDeltaReductionStep first second shadowMethods)
      actualContext shadowContext state := by
  rw [lazyDeltaReductionStep.entry_eq]
  change TypeChecker.M.SuccessTransport
    (nativeLazyDeltaRun (nativeLazyDeltaPlan actualContext.env state first second) first second actualMethods)
    (nativeLazyDeltaRun (nativeLazyDeltaPlan shadowContext.env state first second) first second shadowMethods)
    actualContext shadowContext state
  rw [← nativeLazyDeltaPlan.headerShadow_eq agreement]
  exact nativeLazyDeltaRun.transport _ _ _ _ agreement _ _ _ _ callbacks

structure NativeDeltaNatCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop where
  successor : expression.getAppNumArgs = 1 → (expression.appFn! == .const ``Nat.succ []) = true →
    TypeChecker.M.SuccessTransport (actualMethods.whnf expression.appArg!) (shadowMethods.whnf expression.appArg!)
      actualContext shadowContext state
  binary : ∀ name levels first second, expression = .app (.app (.const name levels) first) second →
    name ∈ nativeBinaryNatOperations → NativeNatOperands actualMethods shadowMethods actualContext shadowContext state first second

def TypeChecker.Inner.nativeLazyDeltaTail (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  let environment ← getEnv
  if let some normalized ← reduceNative environment first then
    return .bool normalized second (← isDefEqCore normalized second)
  else if let some normalized ← reduceNative environment second then
    return .bool first normalized (← isDefEqCore first normalized)
  lazyDeltaReductionStep first second

def TypeChecker.Inner.nativeLazyDeltaNaturalTail (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  if let some normalized ← reduceNat first then
    return .bool normalized second (← isDefEqCore normalized second)
  else if let some normalized ← reduceNat second then
    return .bool first normalized (← isDefEqCore first normalized)
  nativeLazyDeltaTail first second

def nativeLazyDeltaNaturalGate (context : TypeChecker.Context) (first second : Expr) : Bool :=
  !first.hasFVar && !second.hasFVar || context.eagerReduce

def TypeChecker.Inner.nativeLazyDeltaRound (first second : Expr) : TypeChecker.RecM TypeChecker.ReductionStatus := do
  let offset ← isDefEqOffset first second
  if offset != .undef then return .bool first second (offset == .true)
  if nativeLazyDeltaNaturalGate (← readThe TypeChecker.Context) first second then
    nativeLazyDeltaNaturalTail first second
  else nativeLazyDeltaTail first second

private theorem nativeDeltaBindCongr {resultType : Type} (action : TypeChecker.RecM resultType)
    (first second : resultType → TypeChecker.RecM TypeChecker.ReductionStatus)
    (agreement : ∀ result, first result = second result) :
    (action >>= first) = (action >>= second) := by
  exact congrArg (fun continuation => action >>= continuation) (funext agreement)

private theorem nativeDeltaBoolContinuation (first second : Expr) (fuel : Nat)
    (action : TypeChecker.RecM Bool) :
    (TypeChecker.ReductionStatus.bool first second <$> action) = (do
      let result ← TypeChecker.ReductionStatus.bool first second <$> action
      match result with
      | .continue nextFirst nextSecond => TypeChecker.Inner.lazyDeltaReduction.loop nextFirst nextSecond fuel
      | result => pure result) := by
  funext methods context
  dsimp only [Functor.map, ReaderT.instFunctorOfMonad, Bind.bind, ReaderT.bind, ReaderT.pure]
  funext state
  dsimp only [StateT.map, StateT.bind, Except.bind, Except.pure]
  cases h : action methods context state with
  | error error =>
    change Except.error error = Except.bind (Except.error error) _
    rfl
  | ok value => cases value with
    | mk result nextState => cases result <;> rfl

set_option maxHeartbeats 800000 in
theorem TypeChecker.Inner.lazyDeltaReduction.loop_round_eq (first second : Expr) (fuel : Nat) :
    lazyDeltaReduction.loop first second (fuel + 1) = (do
      match ← nativeLazyDeltaRound first second with
      | .continue nextFirst nextSecond => lazyDeltaReduction.loop nextFirst nextSecond fuel
      | result => pure result) := by
  simp only [lazyDeltaReduction.loop, nativeLazyDeltaRound, nativeLazyDeltaNaturalTail,
    nativeLazyDeltaTail, nativeLazyDeltaNaturalGate, bind_assoc]
  apply congrArg (fun continuation : LBool → TypeChecker.RecM TypeChecker.ReductionStatus =>
    isDefEqOffset first second >>= continuation)
  funext offset
  cases offset <;> simp only [show (LBool.undef != LBool.undef) = false from rfl,
    show (LBool.true != LBool.undef) = true from rfl,
    show (LBool.false != LBool.undef) = true from rfl, Bool.false_eq_true, if_false, if_true, pure_bind, bind_assoc]
  repeat' first | rfl | (simp only [bind_assoc, pure_bind]) |
    (exact nativeDeltaBoolContinuation _ _ _ _) |
    (apply nativeDeltaBindCongr; intro result) | split
  all_goals simp_all
  all_goals repeat' first | rfl | (simp only [bind_assoc, pure_bind]) |
    (exact nativeDeltaBoolContinuation _ _ _ _) |
    (apply nativeDeltaBindCongr; intro result) | split
  all_goals
    rename_i gate natural
    have secondTrue : second.hasFVar = true := gate.1 natural.1
    have secondFalse : second.hasFVar = false := natural.2
    simp_all

structure NativeDeltaTailCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstComparison : ∀ normalized, TypeChecker.Inner.reduceNative actualContext.env first = .ok (some normalized) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore normalized second) (shadowMethods.isDefEqCore normalized second)
      actualContext shadowContext state
  secondComparison : ∀ normalized, TypeChecker.Inner.reduceNative actualContext.env first = .ok none →
    TypeChecker.Inner.reduceNative actualContext.env second = .ok (some normalized) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore first normalized) (shadowMethods.isDefEqCore first normalized)
      actualContext shadowContext state
  step : TypeChecker.Inner.reduceNative actualContext.env first = .ok none →
    TypeChecker.Inner.reduceNative actualContext.env second = .ok none →
    NativeLazyDeltaStepCallbacks (nativeLazyDeltaPlan actualContext.env state first second)
      actualMethods shadowMethods actualContext shadowContext state first second

structure NativeDeltaNaturalTailCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstNormalization : NativeDeltaNatCallbacks actualMethods shadowMethods actualContext shadowContext state first
  secondNormalization : ∀ firstState,
    TypeChecker.Inner.reduceNat first actualMethods actualContext state = .ok (none, firstState) →
    NativeDeltaNatCallbacks actualMethods shadowMethods actualContext shadowContext firstState second
  firstComparison : ∀ normalized firstState,
    TypeChecker.Inner.reduceNat first actualMethods actualContext state = .ok (some normalized, firstState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore normalized second) (shadowMethods.isDefEqCore normalized second)
      actualContext shadowContext firstState
  secondComparison : ∀ firstState normalized secondState,
    TypeChecker.Inner.reduceNat first actualMethods actualContext state = .ok (none, firstState) →
    TypeChecker.Inner.reduceNat second actualMethods actualContext firstState = .ok (some normalized, secondState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore first normalized) (shadowMethods.isDefEqCore first normalized)
      actualContext shadowContext secondState
  tail : ∀ firstState secondState,
    TypeChecker.Inner.reduceNat first actualMethods actualContext state = .ok (none, firstState) →
    TypeChecker.Inner.reduceNat second actualMethods actualContext firstState = .ok (none, secondState) →
    NativeDeltaTailCallbacks actualMethods shadowMethods actualContext shadowContext secondState first second

structure NativeDeltaRoundCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  offset : NativeOffsetCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  naturals : ∀ offsetState,
    TypeChecker.Inner.isDefEqOffset first second actualMethods actualContext state = .ok (.undef, offsetState) →
    nativeLazyDeltaNaturalGate actualContext first second = true →
    NativeDeltaNaturalTailCallbacks actualMethods shadowMethods actualContext shadowContext offsetState first second
  tail : ∀ offsetState,
    TypeChecker.Inner.isDefEqOffset first second actualMethods actualContext state = .ok (.undef, offsetState) →
    nativeLazyDeltaNaturalGate actualContext first second = false →
    NativeDeltaTailCallbacks actualMethods shadowMethods actualContext shadowContext offsetState first second

theorem TypeChecker.Inner.nativeLazyDeltaTail.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaTailCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeLazyDeltaTail first second actualMethods) (nativeLazyDeltaTail first second shadowMethods)
      actualContext shadowContext state := by
  intro result accepted
  dsimp only [nativeLazyDeltaTail, TypeChecker.getEnv, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, StateT.lift,
    Except.bind, Except.pure] at accepted ⊢
  rw [← reduceNative.environmentIndependent actualContext.env shadowContext.env first,
    ← reduceNative.environmentIndependent actualContext.env shadowContext.env second]
  cases firstResult : reduceNative actualContext.env first with
  | error error => rw [firstResult] at accepted; contradiction
  | ok firstNormalized =>
    rw [firstResult] at accepted
    cases firstNormalized with
    | some normalized =>
      dsimp only [Except.bind] at accepted ⊢
      exact (TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.firstComparison _ firstResult)
        (fun _ _ _ => TypeChecker.M.SuccessTransport.pure _ _ _ _)) result accepted
    | none =>
      dsimp only [Except.bind] at accepted ⊢
      cases secondResult : reduceNative actualContext.env second with
      | error error => rw [secondResult] at accepted; contradiction
      | ok secondNormalized =>
        rw [secondResult] at accepted
        cases secondNormalized with
        | some normalized =>
          try dsimp only [Except.bind] at accepted ⊢
          exact (TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.secondComparison _ firstResult secondResult)
            (fun _ _ _ => TypeChecker.M.SuccessTransport.pure _ _ _ _)) result accepted
        | none =>
          try dsimp only [Except.bind] at accepted ⊢
          exact lazyDeltaReductionStep.headerAxiomTransport _ _ _ _ agreement _ _ _
            (callbacks.step firstResult secondResult) result accepted

theorem TypeChecker.Inner.nativeLazyDeltaNaturalTail.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaNaturalTailCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeLazyDeltaNaturalTail first second actualMethods)
      (nativeLazyDeltaNaturalTail first second shadowMethods) actualContext shadowContext state := by
  dsimp only [nativeLazyDeltaNaturalTail, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (reduceNat.transport _ _ _ _ _ _ callbacks.firstNormalization.successor callbacks.firstNormalization.binary)
  intro normalized firstState firstAccepted
  cases normalized with
  | some normalized =>
    dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.firstComparison _ _ firstAccepted)
    intro _ _ _
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | none =>
    dsimp only [Bind.bind, ReaderT.bind]
    have secondCallbacks := callbacks.secondNormalization _ firstAccepted
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (reduceNat.transport _ _ _ _ _ _ secondCallbacks.successor secondCallbacks.binary)
    intro normalized secondState secondAccepted
    cases normalized with
    | some normalized =>
      dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.secondComparison _ _ _ firstAccepted secondAccepted)
      intro _ _ _
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | none =>
      exact nativeLazyDeltaTail.transport _ _ _ _ agreement _ _ _ (callbacks.tail _ _ firstAccepted secondAccepted)

theorem TypeChecker.Inner.nativeLazyDeltaRound.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDeltaRoundCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeLazyDeltaRound first second actualMethods) (nativeLazyDeltaRound first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeLazyDeltaRound, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (isDefEqOffset.transport _ _ _ _ _ _ _ callbacks.offset)
  intro offset offsetState accepted
  cases offset with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | undef =>
    simp only [show (LBool.undef != LBool.undef) = false from rfl, Bool.false_eq_true, if_false]
    intro result completed
    dsimp only [Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
      Except.bind, Except.pure, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read] at completed ⊢
    have gate : nativeLazyDeltaNaturalGate actualContext first second = nativeLazyDeltaNaturalGate shadowContext first second := by
      simp only [nativeLazyDeltaNaturalGate, policy]
    rw [← gate]
    cases matching : nativeLazyDeltaNaturalGate actualContext first second with
    | true =>
      rw [matching] at completed
      exact nativeLazyDeltaNaturalTail.transport _ _ _ _ agreement _ _ _ (callbacks.naturals _ accepted matching) result completed
    | false =>
      rw [matching] at completed
      exact nativeLazyDeltaTail.transport _ _ _ _ agreement _ _ _ (callbacks.tail _ accepted matching) result completed

inductive NativeLazyDeltaReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) : Expr → Expr → TypeChecker.State → Nat → Prop
  | initial : NativeLazyDeltaReachable methods context state first second first second state context.fuel.lazyDelta
  | continued {currentFirst currentSecond currentState remaining nextFirst nextSecond nextState} :
    NativeLazyDeltaReachable methods context state first second currentFirst currentSecond currentState (remaining + 1) →
    TypeChecker.Inner.nativeLazyDeltaRound currentFirst currentSecond methods context currentState = .ok (.continue nextFirst nextSecond, nextState) →
    NativeLazyDeltaReachable methods context state first second nextFirst nextSecond nextState remaining

def NativeLazyDeltaCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  ∀ currentFirst currentSecond currentState remaining,
    NativeLazyDeltaReachable actualMethods actualContext state first second currentFirst currentSecond currentState (remaining + 1) →
    NativeDeltaRoundCallbacks actualMethods shadowMethods actualContext shadowContext currentState currentFirst currentSecond

theorem TypeChecker.Inner.lazyDeltaReduction.loop_headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeLazyDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second)
    (currentFirst currentSecond : Expr) (currentState : TypeChecker.State) (remaining shadowRemaining : Nat)
    (reached : NativeLazyDeltaReachable actualMethods actualContext state first second currentFirst currentSecond currentState remaining)
    (budget : remaining ≤ shadowRemaining) :
    TypeChecker.M.SuccessTransport (lazyDeltaReduction.loop currentFirst currentSecond remaining actualMethods)
      (lazyDeltaReduction.loop currentFirst currentSecond shadowRemaining shadowMethods) actualContext shadowContext currentState := by
  induction remaining generalizing currentFirst currentSecond currentState shadowRemaining with
  | zero =>
    intro result accepted
    change Except.error Kernel.Exception.deterministicTimeout = Except.ok result at accepted
    contradiction
  | succ remaining inductionHypothesis =>
    cases shadowRemaining with
    | zero => omega
    | succ shadowRemaining =>
      rw [lazyDeltaReduction.loop_round_eq, lazyDeltaReduction.loop_round_eq]
      dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (nativeLazyDeltaRound.transport _ _ _ _ agreement policy _ _ _ (callbacks _ _ _ _ reached))
      intro result nextState accepted
      cases result with
      | «continue» nextFirst nextSecond =>
        exact inductionHypothesis _ _ _ _ (.continued reached accepted) (by omega)
      | «true» => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | «false» nextFirst nextSecond => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | unknown nextFirst nextSecond => exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.lazyDeltaReduction.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeLazyDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (lazyDeltaReduction first second actualMethods) (lazyDeltaReduction first second shadowMethods)
      actualContext shadowContext state := by
  change TypeChecker.M.SuccessTransport
    (lazyDeltaReduction.loop first second actualContext.fuel.lazyDelta actualMethods)
    (lazyDeltaReduction.loop first second shadowContext.fuel.lazyDelta shadowMethods) actualContext shadowContext state
  exact lazyDeltaReduction.loop_headerAxiomTransport _ _ _ _ agreement policy _ _ _ callbacks _ _ _ _ _ .initial budget

end Lean4Lean
