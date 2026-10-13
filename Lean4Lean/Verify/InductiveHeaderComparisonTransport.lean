import Lean4Lean.Verify.InductiveHeaderProjectionTransport

namespace Lean4Lean
open Lean hiding Environment Exception

inductive NativeBinderKind where
  | lambda
  | forall

def NativeBinderKind.node (kind : NativeBinderKind) (name : Name) (domain body : Expr) (binder : BinderInfo) : Expr :=
  match kind with
  | .lambda => .lam name domain body binder
  | .forall => .forallE name domain body binder

def NativeBinderKind.matches (kind : NativeBinderKind) (first second : Expr) : Bool :=
  match kind, first, second with
  | .lambda, .lam .., .lam .. | .forall, .forallE .., .forallE .. => true
  | _, _, _ => false

def TypeChecker.Inner.nativeBinderContinuation (name : Name) (binder : BinderInfo)
    (domain firstBody secondBody : Expr) (substitution : Array Expr)
    (next : Array Expr → TypeChecker.RecM Bool) : TypeChecker.RecM Bool :=
  if firstBody.hasLooseBVars || secondBody.hasLooseBVars then
    withLocalDecl name binder (domain.instantiateRev substitution) fun fresh =>
      next (substitution.push fresh)
  else next (substitution.push default)

def TypeChecker.Inner.nativeBinderComparisonStep (name : Name) (binder : BinderInfo)
    (firstDomain secondDomain firstBody secondBody : Expr) (substitution : Array Expr)
    (next : Array Expr → TypeChecker.RecM Bool) : TypeChecker.RecM Bool := do
  if firstDomain == secondDomain then
    nativeBinderContinuation name binder secondDomain firstBody secondBody substitution next
  else
    if !(← isDefEq (firstDomain.instantiateRev substitution) (secondDomain.instantiateRev substitution)) then
      return false
    nativeBinderContinuation name binder secondDomain firstBody secondBody substitution next

theorem TypeChecker.Inner.isDefEqLambda.lam_eq (firstName secondName : Name)
    (firstDomain secondDomain firstBody secondBody : Expr) (firstBinder secondBinder : BinderInfo)
    (substitution : Array Expr) :
    isDefEqLambda (.lam firstName firstDomain firstBody firstBinder)
      (.lam secondName secondDomain secondBody secondBinder) substitution =
      nativeBinderComparisonStep secondName secondBinder firstDomain secondDomain firstBody secondBody
        substitution (fun next => isDefEqLambda firstBody secondBody next) := by
  rw [isDefEqLambda]
  unfold nativeBinderComparisonStep nativeBinderContinuation
  split <;> simp only [pure_bind, Option.getD_none, Option.getD_some]

theorem TypeChecker.Inner.isDefEqForall.forall_eq (firstName secondName : Name)
    (firstDomain secondDomain firstBody secondBody : Expr) (firstBinder secondBinder : BinderInfo)
    (substitution : Array Expr) :
    isDefEqForall (.forallE firstName firstDomain firstBody firstBinder)
      (.forallE secondName secondDomain secondBody secondBinder) substitution =
      nativeBinderComparisonStep secondName secondBinder firstDomain secondDomain firstBody secondBody
        substitution (fun next => isDefEqForall firstBody secondBody next) := by
  rw [isDefEqForall]
  unfold nativeBinderComparisonStep nativeBinderContinuation
  split <;> simp only [pure_bind, Option.getD_none, Option.getD_some]

inductive NativeBinderDomainAccepted (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (firstDomain secondDomain : Expr) (substitution : Array Expr) : TypeChecker.State → Prop
  | same : (firstDomain == secondDomain) = true →
      NativeBinderDomainAccepted methods context state firstDomain secondDomain substitution state
  | checked {nextState} : (firstDomain == secondDomain) = false →
      TypeChecker.Inner.isDefEq (firstDomain.instantiateRev substitution) (secondDomain.instantiateRev substitution)
        methods context state = .ok (true, nextState) →
      NativeBinderDomainAccepted methods context state firstDomain secondDomain substitution nextState

inductive NativeBinderComparisonReachable (kind : NativeBinderKind) (methods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (first second : Expr) (substitution : Array Expr) :
    TypeChecker.Context → TypeChecker.Context → TypeChecker.State → Expr → Expr → Array Expr → Prop
  | initial : NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
      actualContext shadowContext state first second substitution
  | opened {actual shadow currentState firstName secondName firstDomain secondDomain firstBody secondBody firstBinder secondBinder current nextState} :
      NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
        actual shadow currentState (kind.node firstName firstDomain firstBody firstBinder)
        (kind.node secondName secondDomain secondBody secondBinder) current →
      NativeBinderDomainAccepted methods actual currentState firstDomain secondDomain current nextState →
      (firstBody.hasLooseBVars || secondBody.hasLooseBVars) = true →
      NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
        (actual.openLocal nextState secondName secondBinder (secondDomain.instantiateRev current))
        (shadow.openLocal nextState secondName secondBinder (secondDomain.instantiateRev current))
        nextState.allocateLocal firstBody secondBody (current.push (.fvar ⟨nextState.ngen.curr⟩))
  | closed {actual shadow currentState firstName secondName firstDomain secondDomain firstBody secondBody firstBinder secondBinder current nextState} :
      NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
        actual shadow currentState (kind.node firstName firstDomain firstBody firstBinder)
        (kind.node secondName secondDomain secondBody secondBinder) current →
      NativeBinderDomainAccepted methods actual currentState firstDomain secondDomain current nextState →
      (firstBody.hasLooseBVars || secondBody.hasLooseBVars) = false →
      NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
        actual shadow nextState firstBody secondBody (current.push default)

structure NativeBinderComparisonCallbacks (kind : NativeBinderKind) (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (first second : Expr) (substitution : Array Expr) : Prop where
  domains : ∀ actual shadow currentState firstName secondName firstDomain secondDomain firstBody secondBody firstBinder secondBinder current,
    NativeBinderComparisonReachable kind actualMethods actualContext shadowContext state first second substitution
      actual shadow currentState (kind.node firstName firstDomain firstBody firstBinder)
      (kind.node secondName secondDomain secondBody secondBinder) current →
    (firstDomain == secondDomain) = false →
    TypeChecker.M.SuccessTransport
      (actualMethods.isDefEqCore (firstDomain.instantiateRev current) (secondDomain.instantiateRev current))
      (shadowMethods.isDefEqCore (firstDomain.instantiateRev current) (secondDomain.instantiateRev current))
      actual shadow currentState
  terminals : ∀ actual shadow currentState currentFirst currentSecond current,
    NativeBinderComparisonReachable kind actualMethods actualContext shadowContext state first second substitution
      actual shadow currentState currentFirst currentSecond current →
    kind.matches currentFirst currentSecond = false →
    TypeChecker.M.SuccessTransport
      (actualMethods.isDefEqCore (currentFirst.instantiateRev current) (currentSecond.instantiateRev current))
      (shadowMethods.isDefEqCore (currentFirst.instantiateRev current) (currentSecond.instantiateRev current))
      actual shadow currentState

theorem TypeChecker.Inner.nativeBinderComparisonStep.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (name : Name) (binder : BinderInfo)
    (firstDomain secondDomain firstBody secondBody : Expr) (substitution : Array Expr)
    (actualNext shadowNext : Array Expr → TypeChecker.RecM Bool)
    (comparison : (firstDomain == secondDomain) = false →
      TypeChecker.M.SuccessTransport
        (actualMethods.isDefEqCore (firstDomain.instantiateRev substitution) (secondDomain.instantiateRev substitution))
        (shadowMethods.isDefEqCore (firstDomain.instantiateRev substitution) (secondDomain.instantiateRev substitution))
        actualContext shadowContext state)
    (opened : ∀ nextState, NativeBinderDomainAccepted actualMethods actualContext state firstDomain secondDomain substitution nextState →
      (firstBody.hasLooseBVars || secondBody.hasLooseBVars) = true →
      TypeChecker.M.SuccessTransport (actualNext (substitution.push (.fvar ⟨nextState.ngen.curr⟩)) actualMethods)
        (shadowNext (substitution.push (.fvar ⟨nextState.ngen.curr⟩)) shadowMethods)
        (actualContext.openLocal nextState name binder (secondDomain.instantiateRev substitution))
        (shadowContext.openLocal nextState name binder (secondDomain.instantiateRev substitution)) nextState.allocateLocal)
    (closed : ∀ nextState, NativeBinderDomainAccepted actualMethods actualContext state firstDomain secondDomain substitution nextState →
      (firstBody.hasLooseBVars || secondBody.hasLooseBVars) = false →
      TypeChecker.M.SuccessTransport (actualNext (substitution.push default) actualMethods)
        (shadowNext (substitution.push default) shadowMethods) actualContext shadowContext nextState) :
    TypeChecker.M.SuccessTransport
      (nativeBinderComparisonStep name binder firstDomain secondDomain firstBody secondBody substitution actualNext actualMethods)
      (nativeBinderComparisonStep name binder firstDomain secondDomain firstBody secondBody substitution shadowNext shadowMethods)
      actualContext shadowContext state := by
  have continuation : ∀ nextState, NativeBinderDomainAccepted actualMethods actualContext state firstDomain secondDomain substitution nextState →
      TypeChecker.M.SuccessTransport
        (nativeBinderContinuation name binder secondDomain firstBody secondBody substitution actualNext actualMethods)
        (nativeBinderContinuation name binder secondDomain firstBody secondBody substitution shadowNext shadowMethods)
        actualContext shadowContext nextState := by
    intro nextState reached
    unfold nativeBinderContinuation
    cases loose : firstBody.hasLooseBVars || secondBody.hasLooseBVars with
    | true =>
      simp only [if_true]
      exact TypeChecker.withLocalDecl_transport actualMethods shadowMethods actualContext shadowContext nextState name binder
        (secondDomain.instantiateRev substitution) _ _ (opened _ reached loose)
    | false => simp only [Bool.false_eq_true, if_false]; exact closed _ reached loose
  unfold nativeBinderComparisonStep
  cases same : firstDomain == secondDomain with
  | true => simp only [if_true]; exact continuation _ (.same same)
  | false =>
    simp only [Bool.false_eq_true, if_false]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (isDefEq.transport _ _ _ _ _ _ _ (comparison same))
    intro equal nextState accepted
    cases equal with
    | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | true => exact continuation _ (.checked same accepted)

theorem TypeChecker.Inner.isDefEqLambda.reachable_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .lambda actualMethods shadowMethods actualContext shadowContext state first second substitution)
    (actual shadow : TypeChecker.Context) (currentState : TypeChecker.State) (currentFirst currentSecond : Expr) (current : Array Expr)
    (reached : NativeBinderComparisonReachable .lambda actualMethods actualContext shadowContext state first second substitution
      actual shadow currentState currentFirst currentSecond current) :
    TypeChecker.M.SuccessTransport (isDefEqLambda currentFirst currentSecond current actualMethods)
      (isDefEqLambda currentFirst currentSecond current shadowMethods) actual shadow currentState := by
  induction currentFirst generalizing actual shadow currentState currentSecond current with
  | lam firstName firstDomain firstBody firstBinder domainIH bodyIH =>
    cases currentSecond with
    | lam secondName secondDomain secondBody secondBinder =>
      rw [lam_eq]
      apply nativeBinderComparisonStep.transport
      · exact callbacks.domains _ _ _ _ _ _ _ _ _ _ _ _ reached
      · intro nextState accepted loose
        exact bodyIH _ _ _ _ _ (.opened reached accepted loose)
      · intro nextState accepted loose
        exact bodyIH _ _ _ _ _ (.closed reached accepted loose)
    | _ =>
      simp only [isDefEqLambda.eq_def]
      exact isDefEq.transport _ _ _ _ _ _ _ (callbacks.terminals _ _ _ _ _ _ reached rfl)
  | _ =>
    simp only [isDefEqLambda.eq_def]
    exact isDefEq.transport _ _ _ _ _ _ _ (callbacks.terminals _ _ _ _ _ _ reached rfl)

theorem TypeChecker.Inner.isDefEqLambda.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .lambda actualMethods shadowMethods actualContext shadowContext state first second substitution) :
    TypeChecker.M.SuccessTransport (isDefEqLambda first second substitution actualMethods)
      (isDefEqLambda first second substitution shadowMethods) actualContext shadowContext state :=
  reachable_transport _ _ _ _ _ _ _ _ callbacks _ _ _ _ _ _ .initial

theorem TypeChecker.Inner.isDefEqForall.reachable_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .forall actualMethods shadowMethods actualContext shadowContext state first second substitution)
    (actual shadow : TypeChecker.Context) (currentState : TypeChecker.State) (currentFirst currentSecond : Expr) (current : Array Expr)
    (reached : NativeBinderComparisonReachable .forall actualMethods actualContext shadowContext state first second substitution
      actual shadow currentState currentFirst currentSecond current) :
    TypeChecker.M.SuccessTransport (isDefEqForall currentFirst currentSecond current actualMethods)
      (isDefEqForall currentFirst currentSecond current shadowMethods) actual shadow currentState := by
  induction currentFirst generalizing actual shadow currentState currentSecond current with
  | forallE firstName firstDomain firstBody firstBinder domainIH bodyIH =>
    cases currentSecond with
    | forallE secondName secondDomain secondBody secondBinder =>
      rw [forall_eq]
      apply nativeBinderComparisonStep.transport
      · exact callbacks.domains _ _ _ _ _ _ _ _ _ _ _ _ reached
      · intro nextState accepted loose
        exact bodyIH _ _ _ _ _ (.opened reached accepted loose)
      · intro nextState accepted loose
        exact bodyIH _ _ _ _ _ (.closed reached accepted loose)
    | _ =>
      simp only [isDefEqForall.eq_def]
      exact isDefEq.transport _ _ _ _ _ _ _ (callbacks.terminals _ _ _ _ _ _ reached rfl)
  | _ =>
    simp only [isDefEqForall.eq_def]
    exact isDefEq.transport _ _ _ _ _ _ _ (callbacks.terminals _ _ _ _ _ _ reached rfl)

theorem TypeChecker.Inner.isDefEqForall.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr)
    (callbacks : NativeBinderComparisonCallbacks .forall actualMethods shadowMethods actualContext shadowContext state first second substitution) :
    TypeChecker.M.SuccessTransport (isDefEqForall first second substitution actualMethods)
      (isDefEqForall first second substitution shadowMethods) actualContext shadowContext state :=
  reachable_transport _ _ _ _ _ _ _ _ callbacks _ _ _ _ _ _ .initial

theorem TypeChecker.RecM.toLBoolM_transport (actualMethods shadowMethods : Methods)
    (actualContext shadowContext : Context) (state : State) (actual shadow : RecM Bool)
    (comparison : M.SuccessTransport (actual actualMethods) (shadow shadowMethods) actualContext shadowContext state) :
    M.SuccessTransport (toLBoolM actual actualMethods) (toLBoolM shadow shadowMethods) actualContext shadowContext state := by
  dsimp only [toLBoolM, Bind.bind, ReaderT.bind]
  apply M.SuccessTransport.bind _ _ _ _ _ _ _ comparison
  intro equal finalState accepted
  exact M.SuccessTransport.pure _ _ _ _

def TypeChecker.Inner.nativeQuickProbe (first second : Expr) (useHash : Bool) : TypeChecker.M Bool :=
  modifyGet fun (.mk generator inferenceOnly checkedInference coreCache normalizationCache failures unfolds (eqvManager := manager)) =>
    let (equal, manager) := manager.isEquiv useHash first second
    (equal, .mk generator inferenceOnly checkedInference coreCache normalizationCache failures unfolds (eqvManager := manager))

def TypeChecker.Inner.nativeQuickBody (first second : Expr) : TypeChecker.RecM LBool :=
  match first, second with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda first second
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall first second
  | .sort firstLevel, .sort secondLevel => pure (firstLevel.isEquiv secondLevel).toLBool
  | .mdata _ firstBody, .mdata _ secondBody => toLBoolM <| isDefEq firstBody secondBody
  | .mvar .., .mvar .. => panicWithPosWithDecl "Lean4Lean.TypeChecker" "Lean4Lean.TypeChecker.Inner.quickIsDefEq" 491 26
      "unreachable code has been reached"
  | .lit firstLiteral, .lit secondLiteral => pure (firstLiteral == secondLiteral).toLBool
  | _, _ => pure .undef

private theorem nativeQuickProbe_lift (f : TypeChecker.State → Prod Bool TypeChecker.State) :
    (modifyGet f : TypeChecker.RecM Bool) = liftM (modifyGet f : TypeChecker.M Bool) := by
  rfl

theorem TypeChecker.Inner.quickIsDefEq.entry_eq (first second : Expr) (useHash : Bool) :
    quickIsDefEq first second useHash = (do
      if ← nativeQuickProbe first second useHash then return .true
      nativeQuickBody first second) := by
  funext methods context state
  cases state
  simp only [quickIsDefEq, nativeQuickProbe, nativeQuickBody, pure_bind]
  rw [nativeQuickProbe_lift]
  cases first <;> cases second <;> simp only [nativeQuickBody] <;> rfl


def NativeQuickBodyCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  match first, second with
  | .lam .., .lam .. =>
    NativeBinderComparisonCallbacks .lambda actualMethods shadowMethods actualContext shadowContext state first second #[]
  | .forallE .., .forallE .. =>
    NativeBinderComparisonCallbacks .forall actualMethods shadowMethods actualContext shadowContext state first second #[]
  | .mdata _ firstBody, .mdata _ secondBody =>
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstBody secondBody)
      (shadowMethods.isDefEqCore firstBody secondBody) actualContext shadowContext state
  | _, _ => True

theorem TypeChecker.Inner.nativeQuickBody.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeQuickBody first second actualMethods)
      (nativeQuickBody first second shadowMethods) actualContext shadowContext state := by
  cases first <;> cases second
  all_goals dsimp only [nativeQuickBody, NativeQuickBodyCallbacks] at callbacks ⊢
  case lam.lam => exact TypeChecker.RecM.toLBoolM_transport _ _ _ _ _ _ _ (isDefEqLambda.transport _ _ _ _ _ _ _ _ callbacks)
  case forallE.forallE => exact TypeChecker.RecM.toLBoolM_transport _ _ _ _ _ _ _ (isDefEqForall.transport _ _ _ _ _ _ _ _ callbacks)
  case mdata.mdata => exact TypeChecker.RecM.toLBoolM_transport _ _ _ _ _ _ _ (isDefEq.transport _ _ _ _ _ _ _ callbacks)
  all_goals intro result accepted; exact accepted

theorem TypeChecker.Inner.quickIsDefEq.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (useHash : Bool)
    (callbacks : ∀ nextState, nativeQuickProbe first second useHash actualContext state = .ok (false, nextState) →
      NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second) :
    TypeChecker.M.SuccessTransport (quickIsDefEq first second useHash actualMethods)
      (quickIsDefEq first second useHash shadowMethods) actualContext shadowContext state := by
  rw [entry_eq]
  dsimp only [Bind.bind, ReaderT.bind, liftM, MonadLift.monadLift, MonadLiftT.monadLift]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (Except.SuccessTransport.refl _)
  intro equal nextState accepted
  cases equal with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact nativeQuickBody.transport _ _ _ _ _ _ _ (callbacks _ accepted)

inductive NativeArgumentComparisonReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) : TypeChecker.State → Expr → Expr → Prop
  | initial : NativeArgumentComparisonReachable methods context state first second state first second
  | compared {currentState nextState firstFunction firstArgument secondFunction secondArgument} :
      NativeArgumentComparisonReachable methods context state first second currentState
        (.app firstFunction firstArgument) (.app secondFunction secondArgument) →
      TypeChecker.Inner.isDefEq firstArgument secondArgument methods context currentState = .ok (true, nextState) →
      NativeArgumentComparisonReachable methods context state first second nextState firstFunction secondFunction

theorem TypeChecker.Inner.isDefEqArgs.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : ∀ currentState firstFunction firstArgument secondFunction secondArgument,
      NativeArgumentComparisonReachable actualMethods actualContext state first second currentState
        (.app firstFunction firstArgument) (.app secondFunction secondArgument) →
      TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstArgument secondArgument)
        (shadowMethods.isDefEqCore firstArgument secondArgument) actualContext shadowContext currentState) :
    TypeChecker.M.SuccessTransport (isDefEqArgs first second actualMethods)
      (isDefEqArgs first second shadowMethods) actualContext shadowContext state := by
  have auxiliary : ∀ currentFirst currentSecond currentState,
      NativeArgumentComparisonReachable actualMethods actualContext state first second currentState currentFirst currentSecond →
      TypeChecker.M.SuccessTransport (isDefEqArgs currentFirst currentSecond actualMethods)
        (isDefEqArgs currentFirst currentSecond shadowMethods) actualContext shadowContext currentState := by
    intro currentFirst
    induction currentFirst with
    | app firstFunction firstArgument functionIH argumentIH =>
      intro currentSecond currentState reached
      cases currentSecond with
      | app secondFunction secondArgument =>
        rw [isDefEqArgs]
        dsimp only [Bind.bind, ReaderT.bind]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (isDefEq.transport _ _ _ _ _ _ _ (callbacks _ _ _ _ _ reached))
        intro equal nextState accepted
        cases equal with
        | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
        | true => exact functionIH _ _ (.compared reached accepted)
      | _ => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | _ =>
      intro currentSecond currentState reached
      cases currentSecond <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  exact auxiliary _ _ _ .initial

inductive NativeAppComparisonReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (firstArguments secondArguments : Array Expr) (sameSize : firstArguments.size = secondArguments.size)
    (initialIndex : Nat) : Nat → TypeChecker.State → Prop
  | initial : NativeAppComparisonReachable methods context state firstArguments secondArguments sameSize initialIndex initialIndex state
  | compared {index currentState nextState} (inBounds : index < firstArguments.size) :
      NativeAppComparisonReachable methods context state firstArguments secondArguments sameSize initialIndex index currentState →
      TypeChecker.Inner.isDefEq firstArguments[index] secondArguments[index] methods context currentState = .ok (true, nextState) →
      NativeAppComparisonReachable methods context state firstArguments secondArguments sameSize initialIndex (index + 1) nextState

theorem TypeChecker.Inner.isDefEqApp.loop_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (firstArguments secondArguments : Array Expr) (sameSize : firstArguments.size = secondArguments.size)
    (initialIndex : Nat)
    (callbacks : ∀ index currentState (inBounds : index < firstArguments.size),
      NativeAppComparisonReachable actualMethods actualContext state firstArguments secondArguments sameSize initialIndex index currentState →
      TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstArguments[index] secondArguments[index])
        (shadowMethods.isDefEqCore firstArguments[index] secondArguments[index]) actualContext shadowContext currentState) :
    TypeChecker.M.SuccessTransport (isDefEqApp.loop firstArguments secondArguments sameSize initialIndex actualMethods)
      (isDefEqApp.loop firstArguments secondArguments sameSize initialIndex shadowMethods) actualContext shadowContext state := by
  have auxiliary : ∀ remaining index currentState, firstArguments.size - index ≤ remaining →
      NativeAppComparisonReachable actualMethods actualContext state firstArguments secondArguments sameSize initialIndex index currentState →
      TypeChecker.M.SuccessTransport (isDefEqApp.loop firstArguments secondArguments sameSize index actualMethods)
        (isDefEqApp.loop firstArguments secondArguments sameSize index shadowMethods) actualContext shadowContext currentState := by
    intro remaining
    induction remaining with
    | zero =>
      intro index currentState bound reached
      have exhausted : ¬index < firstArguments.size := by omega
      rw [isDefEqApp.loop.eq_def]
      simp only [exhausted, dite_false]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | succ remaining inductionHypothesis =>
      intro index currentState bound reached
      rw [isDefEqApp.loop.eq_def]
      by_cases inBounds : index < firstArguments.size
      · simp only [inBounds, dite_true, pure_bind]
        dsimp only [Bind.bind, ReaderT.bind]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (isDefEq.transport _ _ _ _ _ _ _ (callbacks _ _ inBounds reached))
        intro equal nextState accepted
        cases equal with
        | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
        | true => exact inductionHypothesis _ _ (by omega) (.compared inBounds reached accepted)
      · simp only [inBounds, dite_false]
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  exact auxiliary (firstArguments.size - initialIndex) _ _ (Nat.le_refl _) .initial

structure NativeAppComparisonCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  heads : (first.isApp && second.isApp) = true →
    (nativeProjectionView first).2.size = (nativeProjectionView second).2.size →
    TypeChecker.M.SuccessTransport
      (actualMethods.isDefEqCore (nativeProjectionView first).1 (nativeProjectionView second).1)
      (shadowMethods.isDefEqCore (nativeProjectionView first).1 (nativeProjectionView second).1) actualContext shadowContext state
  arguments : ∀ sameSize nextState,
    (first.isApp && second.isApp) = true →
    TypeChecker.Inner.isDefEq (nativeProjectionView first).1 (nativeProjectionView second).1 actualMethods actualContext state = .ok (true, nextState) →
    ∀ index currentState (inBounds : index < (nativeProjectionView first).2.size),
    NativeAppComparisonReachable actualMethods actualContext nextState (nativeProjectionView first).2 (nativeProjectionView second).2 sameSize 0 index currentState →
    TypeChecker.M.SuccessTransport
      (actualMethods.isDefEqCore (nativeProjectionView first).2[index] (nativeProjectionView second).2[index])
      (shadowMethods.isDefEqCore (nativeProjectionView first).2[index] (nativeProjectionView second).2[index]) actualContext shadowContext currentState

theorem TypeChecker.Inner.isDefEqApp.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeAppComparisonCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (isDefEqApp first second actualMethods)
      (isDefEqApp first second shadowMethods) actualContext shadowContext state := by
  unfold isDefEqApp
  cases applications : first.isApp && second.isApp with
  | false => simp only [Bool.false_eq_true, if_false]; exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    simp only [if_true, pure_bind]
    rw [Expr.withApp_projectionView, Expr.withApp_projectionView]
    by_cases sameSize : (nativeProjectionView first).2.size = (nativeProjectionView second).2.size
    · simp only [sameSize, dite_true]
      dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (isDefEq.transport _ _ _ _ _ _ _ (callbacks.heads applications sameSize))
      intro equal nextState accepted
      cases equal with
      | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | true => exact loop_transport _ _ _ _ _ _ _ _ _ (callbacks.arguments sameSize _ applications accepted)
    · simp only [sameSize, dite_false]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _

end Lean4Lean
