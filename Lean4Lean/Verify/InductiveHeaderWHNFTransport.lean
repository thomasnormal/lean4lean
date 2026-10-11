import Lean4Lean.Verify.InductiveHeaderWHNFCoreTransport

namespace Lean4Lean
open Lean hiding Environment Exception

structure NativeNatOperands (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  initial : TypeChecker.M.SuccessTransport (actualMethods.whnf first) (shadowMethods.whnf first)
    actualContext shadowContext state
  continuation : ∀ normalized finalState value,
    actualMethods.whnf first actualContext state = .ok (normalized, finalState) →
    TypeChecker.Inner.rawNatLitExt? normalized = some value →
    TypeChecker.M.SuccessTransport (actualMethods.whnf second) (shadowMethods.whnf second)
      actualContext shadowContext finalState

theorem TypeChecker.Inner.reduceBinNatOp.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (operation : Nat → Nat → Nat) (first second : Expr)
    (operands : NativeNatOperands actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (reduceBinNatOp operation first second actualMethods)
      (reduceBinNatOp operation first second shadowMethods) actualContext shadowContext state := by
  dsimp only [reduceBinNatOp, Bind.bind, ReaderT.bind, whnf]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ operands.initial
  intro normalized finalState accepted
  cases found : rawNatLitExt? normalized with
  | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | some firstValue =>
    dsimp only [Bind.bind, ReaderT.bind, whnf]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (operands.continuation normalized finalState firstValue accepted found)
    intro secondNormalized secondState _
    cases rawNatLitExt? secondNormalized <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.reduceBinNatPred.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (operation : Nat → Nat → Bool) (first second : Expr)
    (operands : NativeNatOperands actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (reduceBinNatPred operation first second actualMethods)
      (reduceBinNatPred operation first second shadowMethods) actualContext shadowContext state := by
  dsimp only [reduceBinNatPred, Bind.bind, ReaderT.bind, whnf]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ operands.initial
  intro normalized finalState accepted
  cases found : rawNatLitExt? normalized with
  | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | some firstValue =>
    dsimp only [Bind.bind, ReaderT.bind, whnf]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (operands.continuation normalized finalState firstValue accepted found)
    intro secondNormalized secondState _
    cases rawNatLitExt? secondNormalized <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.reducePow.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (operands : NativeNatOperands actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (reducePow first second actualMethods)
      (reducePow first second shadowMethods) actualContext shadowContext state := by
  dsimp only [reducePow, Bind.bind, ReaderT.bind, whnf]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ operands.initial
  intro normalized finalState accepted
  cases found : rawNatLitExt? normalized with
  | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | some firstValue =>
    dsimp only [Bind.bind, ReaderT.bind, whnf]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (operands.continuation normalized finalState firstValue accepted found)
    intro secondNormalized secondState _
    cases rawNatLitExt? secondNormalized with
    | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | some secondValue =>
      dsimp only
      split <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _

def nativeBinaryNatOperations : List Name :=
  [``Nat.add, ``Nat.mul, ``Nat.pow, ``Nat.sub, ``Nat.beq, ``Nat.ble,
    ``Nat.shiftLeft, ``Nat.div, ``Nat.shiftRight, ``Nat.mod]

set_option maxHeartbeats 800000 in
theorem TypeChecker.Inner.reduceNat.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr)
    (successor : expression.getAppNumArgs = 1 → (expression.appFn! == .const ``Nat.succ []) = true →
      TypeChecker.M.SuccessTransport (actualMethods.whnf expression.appArg!) (shadowMethods.whnf expression.appArg!)
        actualContext shadowContext state)
    (binary : ∀ name levels first second, expression = .app (.app (.const name levels) first) second →
      name ∈ nativeBinaryNatOperations →
      NativeNatOperands actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (reduceNat expression actualMethods) (reduceNat expression shadowMethods)
      actualContext shadowContext state := by
  unfold reduceNat
  by_cases unary : (expression.getAppNumArgs == 1) = true
  · rw [if_pos unary]
    split
    · rename_i matching
      dsimp only [Bind.bind, ReaderT.bind, whnf]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (successor (by simpa using unary) matching)
      intro normalized finalState _
      cases rawNatLitExt? normalized <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    · exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  · rw [if_neg unary]
    by_cases two : (expression.getAppNumArgs == 2) = true
    · rw [if_pos two]
      cases expression <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      rename_i function second
      cases function <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      rename_i head first
      cases head <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      rename_i name levels
      dsimp only [ReaderT.bind, ReaderT.pure]
      simp only [bind_pure]
      have operandReceipt (selected : name ∈ nativeBinaryNatOperations) := binary name levels first second rfl selected
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.add _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.mul _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reducePow.transport _ _ _ _ _ _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.sub _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatPred.transport _ _ _ _ _ Nat.beq _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatPred.transport _ _ _ _ _ Nat.ble _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.shiftLeft _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.div _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.shiftRight _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      split
      · rename_i selected
        exact reduceBinNatOp.transport _ _ _ _ _ Nat.mod _ _ (operandReceipt (by simp only [beq_iff_eq] at selected; simp [nativeBinaryNatOperations, selected]))
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    · rw [if_neg two]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.unfoldDefinitionCore.headerShadowTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (expression : Expr) :
    unfoldDefinitionCore expression actualMethods actualContext state =
      unfoldDefinitionCore expression shadowMethods shadowContext state := by
  cases expression <;> try rfl
  rename_i name levels
  dsimp only [unfoldDefinitionCore, TypeChecker.getEnv, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  rw [agreement.delta]
  cases selected : isDelta shadowContext.env (.const name levels) <;> dsimp only
  · rfl
  · split <;> try rfl
    split <;> try rfl
    dsimp only [Bind.bind, Pure.pure, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
      Except.pure, Except.bind, MonadState.get, getThe, MonadStateOf.get, StateT.get,
      liftM, MonadLift.monadLift, MonadLiftT.monadLift]
    cases cached : state.unfold[Expr.const name levels]? <;> rfl

theorem TypeChecker.Inner.unfoldDefinition.headerShadowTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (expression : Expr) :
    unfoldDefinition expression actualMethods actualContext state =
      unfoldDefinition expression shadowMethods shadowContext state := by
  simp only [unfoldDefinition]
  split
  · dsimp only [Bind.bind, ReaderT.bind, StateT.bind]
    rw [unfoldDefinitionCore.headerShadowTransport actualMethods shadowMethods actualContext shadowContext agreement]
    cases selected : unfoldDefinitionCore expression.getAppFn shadowMethods shadowContext state with
    | error error => rfl
    | ok returned =>
      rcases returned with ⟨value, finalState⟩
      cases value <;> rfl
  · exact unfoldDefinitionCore.headerShadowTransport actualMethods shadowMethods actualContext shadowContext agreement state expression

theorem TypeChecker.Inner.reduceNative.environmentIndependent
    (actual shadow : Kernel.Environment) (expression : Expr) :
    reduceNative actual expression = reduceNative shadow expression := rfl

theorem TypeChecker.Inner.reduceNative.transport
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (liftM (reduceNative actualContext.env expression))
      (liftM (reduceNative shadowContext.env expression)) actualContext shadowContext state := by
  intro result accepted
  exact accepted

def TypeChecker.Context.whnfBudget (context : TypeChecker.Context) : Nat :=
  if context.eagerReduce then context.fuel.whnfEager else context.fuel.whnf

def TypeChecker.Inner.whnfCacheEligible (locals : LocalContext) : Expr → Bool
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => true
  | .fvar name => isLetFVar locals name
  | _ => false

structure NativeWhnfEntryReceipt (context : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop where
  eligible : TypeChecker.Inner.whnfCacheEligible context.lctx expression = true
  cacheMiss : state.whnfCache[expression]? = none

inductive NativeWhnfReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) : Expr → TypeChecker.State → Nat → Prop
  | initial : NativeWhnfEntryReceipt context state expression →
      NativeWhnfReachable methods context state expression expression state context.whnfBudget
  | unfolded {current currentState remaining normalized normalizedState naturalState unfolded unfoldedState} :
      NativeWhnfReachable methods context state expression current currentState (remaining + 1) →
      TypeChecker.Inner.whnfCore' current false false methods context currentState = .ok (normalized, normalizedState) →
      TypeChecker.Inner.reduceNative context.env normalized = .ok none →
      TypeChecker.Inner.reduceNat normalized methods context normalizedState = .ok (none, naturalState) →
      TypeChecker.Inner.unfoldDefinition normalized methods context naturalState = .ok (some unfolded, unfoldedState) →
      NativeWhnfReachable methods context state expression unfolded unfoldedState remaining

structure NativeWhnfCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop where
  cores : ∀ current currentState remaining,
    NativeWhnfReachable actualMethods actualContext state expression current currentState (remaining + 1) →
    NativeCoreCallbacks actualMethods shadowMethods actualContext shadowContext currentState current.consumeMData false false
  naturals : ∀ current currentState remaining normalized normalizedState,
    NativeWhnfReachable actualMethods actualContext state expression current currentState (remaining + 1) →
    TypeChecker.Inner.whnfCore' current false false actualMethods actualContext currentState = .ok (normalized, normalizedState) →
    TypeChecker.Inner.reduceNative actualContext.env normalized = .ok none →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceNat normalized actualMethods)
      (TypeChecker.Inner.reduceNat normalized shadowMethods) actualContext shadowContext normalizedState

theorem TypeChecker.Inner.whnf'.loop_headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx)
    (state : TypeChecker.State) (expression : Expr)
    (callbacks : NativeWhnfCallbacks actualMethods shadowMethods actualContext shadowContext state expression)
    (current : Expr) (currentState : TypeChecker.State) (remaining shadowRemaining : Nat)
    (reached : NativeWhnfReachable actualMethods actualContext state expression current currentState remaining)
    (budget : remaining ≤ shadowRemaining) :
    TypeChecker.M.SuccessTransport (whnf'.loop current remaining actualMethods)
      (whnf'.loop current shadowRemaining shadowMethods) actualContext shadowContext currentState := by
  induction remaining generalizing current currentState shadowRemaining with
  | zero =>
    intro result accepted
    change Except.error Kernel.Exception.deterministicTimeout = Except.ok result at accepted
    contradiction
  | succ remaining inductionHypothesis =>
    cases shadowRemaining with
    | zero => omega
    | succ shadowRemaining =>
      intro result accepted
      rw [whnf'.loop] at accepted ⊢
      dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
        MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
        ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.pure, Except.bind,
        TypeChecker.M.SuccessTransport, Except.SuccessTransport, Except.WF] at accepted ⊢
      cases coreResult : whnfCore' current false false actualMethods actualContext currentState with
      | error error =>
        rw [coreResult] at accepted
        contradiction
      | ok corePair =>
        rcases corePair with ⟨normalized, normalizedState⟩
        have coreTransport := whnfCore'.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext
          currentState current false false locals (callbacks.cores current currentState remaining reached)
          (normalized, normalizedState) coreResult
        rw [coreResult] at accepted
        rw [coreTransport]
        dsimp only [StateT.lift, Except.bind] at accepted ⊢
        rw [← reduceNative.environmentIndependent actualContext.env shadowContext.env normalized]
        cases nativeResult : reduceNative actualContext.env normalized with
        | error error =>
          rw [nativeResult] at accepted
          contradiction
        | ok native =>
          rw [nativeResult] at accepted
          cases native with
          | some reduced => exact accepted
          | none =>
            dsimp only [Except.bind, Bind.bind, Pure.pure, ReaderT.bind, ReaderT.pure,
              StateT.bind, StateT.pure, Except.pure] at accepted ⊢
            cases naturalResult : reduceNat normalized actualMethods actualContext normalizedState with
            | error error =>
              rw [naturalResult] at accepted
              contradiction
            | ok naturalPair =>
              rcases naturalPair with ⟨natural, naturalState⟩
              have naturalTransport := callbacks.naturals current currentState remaining normalized normalizedState
                reached coreResult nativeResult (natural, naturalState) naturalResult
              rw [naturalResult] at accepted
              rw [naturalTransport]
              cases natural with
              | some reduced => exact accepted
              | none =>
                dsimp only [Except.bind, Bind.bind, Pure.pure, ReaderT.bind, ReaderT.pure,
                  StateT.bind, StateT.pure, Except.pure] at accepted ⊢
                rw [← unfoldDefinition.headerShadowTransport actualMethods shadowMethods actualContext shadowContext agreement]
                cases unfoldResult : unfoldDefinition normalized actualMethods actualContext naturalState with
                | error error =>
                  rw [unfoldResult] at accepted
                  contradiction
                | ok unfoldPair =>
                  rcases unfoldPair with ⟨unfolded, unfoldedState⟩
                  rw [unfoldResult] at accepted
                  cases unfolded with
                  | none => exact accepted
                  | some unfolded =>
                    exact inductionHypothesis unfolded unfoldedState shadowRemaining
                      (.unfolded reached coreResult nativeResult naturalResult unfoldResult) (by omega) result accepted

theorem TypeChecker.Inner.whnf'.consumeMData (expression : Expr) :
    whnf' expression = whnf' expression.consumeMData := by
  induction expression with
  | mdata data expression inductionHypothesis =>
    simp only [whnf', Expr.consumeMData, bind_pure]
    exact inductionHypothesis
  | _ => rfl

def TypeChecker.Inner.whnfCacheProgram (expression : Expr) : TypeChecker.RecM Expr := do
  if let some cached := (← get).whnfCache[expression]? then return cached
  let context ← readThe TypeChecker.Context
  let normalized ← whnf'.loop expression context.whnfBudget
  modify fun state => { state with whnfCache := state.whnfCache.insert expression normalized }
  return normalized

theorem TypeChecker.Inner.whnf'.cache_eq (methods : TypeChecker.Methods)
    (context : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr)
    (noMetadata : expression.isMData = false) (eligible : whnfCacheEligible context.lctx expression = true) :
    whnf' expression methods context state = whnfCacheProgram expression methods context state := by
  cases expression <;> try rfl
  all_goals try simp only [whnfCacheEligible, Bool.false_eq_true] at eligible
  case fvar name =>
    simp only [whnf']
    dsimp only [getLCtx, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
      ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.pure, Except.bind]
    simp only [eligible, Bool.not_true, Bool.false_eq_true, if_false]
    rfl

theorem TypeChecker.Inner.whnf'.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (expression : Expr)
    (callbacks : NativeWhnfCallbacks actualMethods shadowMethods actualContext shadowContext state expression.consumeMData)
    (budget : NativeWhnfEntryReceipt actualContext state expression.consumeMData →
      actualContext.whnfBudget ≤ shadowContext.whnfBudget) :
    TypeChecker.M.SuccessTransport (whnf' expression actualMethods) (whnf' expression shadowMethods)
      actualContext shadowContext state := by
  have noMetadata := whnfCore'.input_not_isMData expression
  rw [whnf'.consumeMData expression]
  generalize inputEq : expression.consumeMData = input at callbacks budget noMetadata ⊢
  by_cases eligible : whnfCacheEligible actualContext.lctx input = true
  · have shadowEligible : whnfCacheEligible shadowContext.lctx input = true := by simpa only [← locals] using eligible
    intro result accepted
    rw [whnf'.cache_eq actualMethods actualContext state input noMetadata eligible] at accepted
    rw [whnf'.cache_eq shadowMethods shadowContext state input noMetadata shadowEligible]
    dsimp only [whnfCacheProgram, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadState.get, getThe, MonadStateOf.get, StateT.get, MonadReader.read, readThe,
      MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure,
      StateT.bind, StateT.pure, Except.pure, Except.bind] at accepted ⊢
    cases cached : state.whnfCache[input]? with
    | some value => simpa only [cached] using accepted
    | none =>
      have entry : NativeWhnfEntryReceipt actualContext state input := ⟨eligible, cached⟩
      have loopTransport := whnf'.loop_headerAxiomTransport actualMethods shadowMethods actualContext shadowContext
        agreement locals state input callbacks input state actualContext.whnfBudget shadowContext.whnfBudget
        (.initial entry) (budget entry)
      simp only [cached] at accepted ⊢
      dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.bind, StateT.pure,
        Except.bind, Except.pure] at accepted ⊢
      cases loopResult : whnf'.loop input actualContext.whnfBudget actualMethods actualContext state with
      | error error =>
        rw [loopResult] at accepted
        contradiction
      | ok loopPair =>
        have shadowResult := loopTransport loopPair loopResult
        rw [loopResult] at accepted
        rw [shadowResult]
        exact accepted
  · cases input with
    | bvar index => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | sort level => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | mvar name => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | forallE name domain body binder => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | lit literal => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | mdata data expression => cases noMetadata
    | fvar name =>
      intro result accepted
      have shadowEligible : whnfCacheEligible shadowContext.lctx (.fvar name) ≠ true := by simpa only [← locals] using eligible
      dsimp only [whnf', getLCtx, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
        MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
        ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.pure, Except.bind] at accepted ⊢
      simp only [whnfCacheEligible] at eligible shadowEligible
      have actualFalse : isLetFVar actualContext.lctx name = false := Bool.eq_false_iff.mpr eligible
      have shadowFalse : isLetFVar shadowContext.lctx name = false := Bool.eq_false_iff.mpr shadowEligible
      simpa only [actualFalse, shadowFalse, Bool.not_false, if_true] using accepted
    | _ => simp [whnfCacheEligible] at eligible

end Lean4Lean
