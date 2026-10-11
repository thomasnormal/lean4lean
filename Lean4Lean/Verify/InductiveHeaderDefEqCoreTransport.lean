import Lean4Lean.Verify.InductiveHeaderLazyDeltaTransport

namespace Lean4Lean
open Lean hiding Environment Exception

def TypeChecker.Inner.nativeDefEqFallback (first second : Expr) : TypeChecker.RecM Bool := do
  if ← isDefEqApp first second then return true
  else if ← tryEtaExpansion first second then return true
  else if ← tryEtaStruct first second then return true
  else
    let string ← tryStringLitExpansion first second
    if string != .undef then return string == .true
    else if ← isDefEqUnitLike first second then return true
    else return false

def TypeChecker.Inner.nativeDefEqRenormalize (first second : Expr) : TypeChecker.RecM Bool := do
  let normalizedFirst ← whnfCore first
  let normalizedSecond ← whnfCore second
  if !(ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) then
    isDefEqCore normalizedFirst normalizedSecond
  else nativeDefEqFallback first second

def TypeChecker.Inner.nativeDefEqSimple (first second : Expr) : TypeChecker.RecM Bool :=
  match first, second with
  | .const firstName firstLevels, .const secondName secondLevels =>
    pure (firstName == secondName && Level.isEquivList firstLevels secondLevels)
  | .fvar firstName, .fvar secondName => pure (firstName == secondName)
  | .proj _ firstIndex firstBody, .proj _ secondIndex secondBody =>
    if firstIndex == secondIndex then isDefEq firstBody secondBody else pure false
  | _, _ => pure false

def TypeChecker.Inner.nativeDefEqUnknown (first second : Expr) : TypeChecker.RecM Bool := do
  match first, second with
  | .const firstName firstLevels, .const secondName secondLevels =>
    if firstName == secondName && Level.isEquivList firstLevels secondLevels then return true
  | .fvar firstName, .fvar secondName => if firstName == secondName then return true
  | .proj _ firstIndex firstBody, .proj _ secondIndex secondBody =>
    if firstIndex == secondIndex then if ← isDefEq firstBody secondBody then return true
  | _, _ => pure ()
  nativeDefEqRenormalize first second

def TypeChecker.Inner.nativeDefEqDelta (first second : Expr) : TypeChecker.RecM Bool := do
  match ← lazyDeltaReduction first second with
  | .continue .. => panicWithPosWithDecl "Lean4Lean.TypeChecker" "Lean4Lean.TypeChecker.Inner.isDefEqCore'" 676 20 "unreachable code has been reached"
  | .bool equal => pure equal
  | .unknown normalizedFirst normalizedSecond => nativeDefEqUnknown normalizedFirst normalizedSecond

def TypeChecker.Inner.nativeDefEqProof (first second : Expr) : TypeChecker.RecM Bool := do
  let proof ← isDefEqProofIrrel first second
  if proof != .undef then return proof == .true
  else nativeDefEqDelta first second

def TypeChecker.Inner.nativeDefEqRecheck (first second normalizedFirst normalizedSecond : Expr) : TypeChecker.RecM LBool :=
  if !(ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) then
    quickIsDefEq normalizedFirst normalizedSecond
  else pure .undef

def TypeChecker.Inner.nativeDefEqNormalized (first second normalizedFirst normalizedSecond : Expr) : TypeChecker.RecM Bool := do
  if !(ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) then
    let rechecked ← quickIsDefEq normalizedFirst normalizedSecond
    if rechecked != .undef then return rechecked == .true
  nativeDefEqProof normalizedFirst normalizedSecond

def TypeChecker.Inner.nativeDefEqCheap (first second : Expr) : TypeChecker.RecM Bool := do
  let normalizedFirst ← whnfCore first (cheapProj := true)
  let normalizedSecond ← whnfCore second (cheapProj := true)
  nativeDefEqNormalized first second normalizedFirst normalizedSecond

def nativeDefEqBoolGate (context : TypeChecker.Context) (first second : Expr) : Bool :=
  (!first.hasFVar || context.eagerReduce) && second.isConstOf ``true

def TypeChecker.Inner.nativeDefEqBoolShortcut (first second : Expr) : TypeChecker.RecM Bool := do
  if nativeDefEqBoolGate (← readThe TypeChecker.Context) first second then
    return (← whnf first).isConstOf ``true
  else return false

def TypeChecker.Inner.nativeDefEqShort (first second : Expr) : TypeChecker.RecM Bool := do
  if nativeDefEqBoolGate (← readThe TypeChecker.Context) first second then
    if (← whnf first).isConstOf ``true then return true
  nativeDefEqCheap first second

def TypeChecker.Inner.nativeDefEqEntry (first second : Expr) : TypeChecker.RecM Bool := do
  let quick ← quickIsDefEq first second (useHash := true)
  if quick != .undef then return quick == .true
  else nativeDefEqShort first second

private theorem nativeDefEqBindCongr {resultType : Type} (action : TypeChecker.RecM resultType)
    (first second : resultType → TypeChecker.RecM Bool) (agreement : ∀ result, first result = second result) :
    (action >>= first) = (action >>= second) :=
  congrArg (fun continuation => action >>= continuation) (funext agreement)

set_option maxHeartbeats 1600000 in
theorem TypeChecker.Inner.isDefEqCore'.entry_eq (first second : Expr) :
    isDefEqCore' first second = nativeDefEqEntry first second := by
  simp only [isDefEqCore', nativeDefEqEntry, nativeDefEqShort, nativeDefEqBoolGate,
    nativeDefEqCheap, nativeDefEqNormalized, nativeDefEqProof, nativeDefEqDelta,
    nativeDefEqUnknown, nativeDefEqRenormalize, nativeDefEqFallback, pure_bind, bind_pure]
  rfl

theorem TypeChecker.Inner.nativeDefEqShort.entry_eq (first second : Expr) :
    nativeDefEqShort first second = (do
      if ← nativeDefEqBoolShortcut first second then return true
      else nativeDefEqCheap first second) := by
  simp only [nativeDefEqShort, nativeDefEqBoolShortcut, bind_assoc, pure_bind]
  apply nativeDefEqBindCongr
  intro context
  cases matching : nativeDefEqBoolGate context first second with
  | false => simp only [Bool.false_eq_true, if_false, pure_bind]
  | true =>
    simp only [if_true, bind_assoc, pure_bind]

theorem TypeChecker.Inner.nativeDefEqNormalized.entry_eq (first second normalizedFirst normalizedSecond : Expr) :
    nativeDefEqNormalized first second normalizedFirst normalizedSecond = (do
      let rechecked ← nativeDefEqRecheck first second normalizedFirst normalizedSecond
      if rechecked != .undef then return rechecked == .true
      else nativeDefEqProof normalizedFirst normalizedSecond) := by
  simp only [nativeDefEqNormalized, nativeDefEqRecheck, pure_bind]
  cases matching : ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second with
  | false => simp only [Bool.not_false, if_true]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind,
      show (LBool.undef != LBool.undef) = false from rfl]

theorem TypeChecker.Inner.nativeDefEqUnknown.entry_eq (first second : Expr) :
    nativeDefEqUnknown first second = (do
      if ← nativeDefEqSimple first second then return true
      else nativeDefEqRenormalize first second) := by
  cases first <;> cases second
  all_goals simp only [nativeDefEqUnknown, nativeDefEqSimple, pure_bind]
  all_goals try rfl
  rename_i firstParent firstIndex firstBody secondParent secondIndex secondBody
  cases matching : firstIndex == secondIndex with
  | false => simp only [Bool.false_eq_true, if_false, pure_bind]
  | true =>
    simp only [if_true]

inductive NativeDefEqFallbackStage where
  | application
  | eta
  | etaStruct
  | string
  | unit

inductive NativeDefEqFallbackReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) : NativeDefEqFallbackStage → TypeChecker.State → Prop
  | initial : NativeDefEqFallbackReachable methods context state first second .application state
  | application {currentState nextState} :
    NativeDefEqFallbackReachable methods context state first second .application currentState →
    TypeChecker.Inner.isDefEqApp first second methods context currentState = .ok (false, nextState) →
    NativeDefEqFallbackReachable methods context state first second .eta nextState
  | eta {currentState nextState} :
    NativeDefEqFallbackReachable methods context state first second .eta currentState →
    TypeChecker.Inner.tryEtaExpansion first second methods context currentState = .ok (false, nextState) →
    NativeDefEqFallbackReachable methods context state first second .etaStruct nextState
  | etaStruct {currentState nextState} :
    NativeDefEqFallbackReachable methods context state first second .etaStruct currentState →
    TypeChecker.Inner.tryEtaStruct first second methods context currentState = .ok (false, nextState) →
    NativeDefEqFallbackReachable methods context state first second .string nextState
  | string {currentState nextState} :
    NativeDefEqFallbackReachable methods context state first second .string currentState →
    TypeChecker.Inner.tryStringLitExpansion first second methods context currentState = .ok (.undef, nextState) →
    NativeDefEqFallbackReachable methods context state first second .unit nextState

structure NativeDefEqEtaCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  forward : NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  backward : ∀ nextState, TypeChecker.Inner.tryEtaExpansionCore first second actualMethods actualContext state = .ok (false, nextState) →
    NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first

structure NativeDefEqStructCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  forward : NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  backward : ∀ nextState, TypeChecker.Inner.tryEtaStructCore first second actualMethods actualContext state = .ok (false, nextState) →
    NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first

structure NativeDefEqStringCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  forward : NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  backward : ∀ nextState, TypeChecker.Inner.tryStringLitExpansionCore first second actualMethods actualContext state = .ok (.undef, nextState) →
    NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first

structure NativeDefEqFallbackCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  applications : ∀ currentState, NativeDefEqFallbackReachable actualMethods actualContext state first second .application currentState →
    NativeAppComparisonCallbacks actualMethods shadowMethods actualContext shadowContext currentState first second
  functions : ∀ currentState, NativeDefEqFallbackReachable actualMethods actualContext state first second .eta currentState →
    NativeDefEqEtaCallbacks actualMethods shadowMethods actualContext shadowContext currentState first second
  structures : ∀ currentState, NativeDefEqFallbackReachable actualMethods actualContext state first second .etaStruct currentState →
    NativeDefEqStructCallbacks actualMethods shadowMethods actualContext shadowContext currentState first second
  strings : ∀ currentState, NativeDefEqFallbackReachable actualMethods actualContext state first second .string currentState →
    NativeDefEqStringCallbacks actualMethods shadowMethods actualContext shadowContext currentState first second
  units : ∀ currentState, NativeDefEqFallbackReachable actualMethods actualContext state first second .unit currentState →
    NativeUnitLikeCallbacks actualMethods shadowMethods actualContext shadowContext currentState first second

structure NativeDefEqRenormalizeCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstNormalization : TypeChecker.M.SuccessTransport (actualMethods.whnfCore first false false)
    (shadowMethods.whnfCore first false false) actualContext shadowContext state
  secondNormalization : ∀ normalizedFirst firstState, actualMethods.whnfCore first false false actualContext state = .ok (normalizedFirst, firstState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore second false false) (shadowMethods.whnfCore second false false)
      actualContext shadowContext firstState
  changed : ∀ normalizedFirst firstState normalizedSecond secondState,
    actualMethods.whnfCore first false false actualContext state = .ok (normalizedFirst, firstState) →
    actualMethods.whnfCore second false false actualContext firstState = .ok (normalizedSecond, secondState) →
    (ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) = false →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore normalizedFirst normalizedSecond)
      (shadowMethods.isDefEqCore normalizedFirst normalizedSecond) actualContext shadowContext secondState
  unchanged : ∀ normalizedFirst firstState normalizedSecond secondState,
    actualMethods.whnfCore first false false actualContext state = .ok (normalizedFirst, firstState) →
    actualMethods.whnfCore second false false actualContext firstState = .ok (normalizedSecond, secondState) →
    (ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) = true →
    NativeDefEqFallbackCallbacks actualMethods shadowMethods actualContext shadowContext secondState first second

def NativeDefEqSimpleCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop :=
  ∀ firstParent firstIndex firstBody secondParent secondIndex secondBody,
    first = .proj firstParent firstIndex firstBody → second = .proj secondParent secondIndex secondBody →
    (firstIndex == secondIndex) = true →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstBody secondBody)
      (shadowMethods.isDefEqCore firstBody secondBody) actualContext shadowContext state

structure NativeDefEqUnknownCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  simple : NativeDefEqSimpleCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  continuation : ∀ nextState, TypeChecker.Inner.nativeDefEqSimple first second actualMethods actualContext state = .ok (false, nextState) →
    NativeDefEqRenormalizeCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second

structure NativeDefEqDeltaCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  reduction : NativeLazyDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  unknown : ∀ normalizedFirst normalizedSecond nextState,
    TypeChecker.Inner.lazyDeltaReduction first second actualMethods actualContext state = .ok (.unknown normalizedFirst normalizedSecond, nextState) →
    NativeDefEqUnknownCallbacks actualMethods shadowMethods actualContext shadowContext nextState normalizedFirst normalizedSecond

structure NativeDefEqProofCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  proofIrrelevance : NativeProofIrrelCallbacks actualMethods shadowMethods actualContext shadowContext state first second
  continuation : ∀ nextState, TypeChecker.Inner.isDefEqProofIrrel first second actualMethods actualContext state = .ok (.undef, nextState) →
    NativeDefEqDeltaCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second

structure NativeDefEqNormalizedCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second normalizedFirst normalizedSecond : Expr) : Prop where
  recheck : (ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second) = false →
    NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext state normalizedFirst normalizedSecond
  continuation : ∀ nextState,
    TypeChecker.Inner.nativeDefEqRecheck first second normalizedFirst normalizedSecond actualMethods actualContext state = .ok (.undef, nextState) →
    NativeDefEqProofCallbacks actualMethods shadowMethods actualContext shadowContext nextState normalizedFirst normalizedSecond

structure NativeDefEqCheapCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstNormalization : TypeChecker.M.SuccessTransport (actualMethods.whnfCore first false true)
    (shadowMethods.whnfCore first false true) actualContext shadowContext state
  secondNormalization : ∀ normalizedFirst firstState, actualMethods.whnfCore first false true actualContext state = .ok (normalizedFirst, firstState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore second false true) (shadowMethods.whnfCore second false true)
      actualContext shadowContext firstState
  continuation : ∀ normalizedFirst firstState normalizedSecond secondState,
    actualMethods.whnfCore first false true actualContext state = .ok (normalizedFirst, firstState) →
    actualMethods.whnfCore second false true actualContext firstState = .ok (normalizedSecond, secondState) →
    NativeDefEqNormalizedCallbacks actualMethods shadowMethods actualContext shadowContext secondState first second normalizedFirst normalizedSecond

structure NativeDefEqShortCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  normalization : nativeDefEqBoolGate actualContext first second = true →
    TypeChecker.M.SuccessTransport (actualMethods.whnf first) (shadowMethods.whnf first) actualContext shadowContext state
  continuation : ∀ nextState, TypeChecker.Inner.nativeDefEqBoolShortcut first second actualMethods actualContext state = .ok (false, nextState) →
    NativeDefEqCheapCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second

structure NativeDefEqCoreCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  quick : ∀ nextState, TypeChecker.Inner.nativeQuickProbe first second true actualContext state = .ok (false, nextState) →
    NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second
  continuation : ∀ nextState, TypeChecker.Inner.quickIsDefEq first second true actualMethods actualContext state = .ok (.undef, nextState) →
    NativeDefEqShortCallbacks actualMethods shadowMethods actualContext shadowContext nextState first second

theorem TypeChecker.Inner.nativeDefEqFallback.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqFallbackCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqFallback first second actualMethods) (nativeDefEqFallback first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDefEqFallback, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (isDefEqApp.transport _ _ _ _ _ _ _ (callbacks.applications _ .initial))
  intro applicationResult applicationState applicationAccepted
  cases applicationResult with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false =>
    simp only [Bool.false_eq_true, if_false]
    dsimp only [Bind.bind, ReaderT.bind]
    have etaReached := NativeDefEqFallbackReachable.application .initial applicationAccepted
    have etaCallbacks := callbacks.functions _ etaReached
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (tryEtaExpansion.transport _ _ _ _ _ _ _ etaCallbacks.forward etaCallbacks.backward)
    intro etaResult etaState etaAccepted
    cases etaResult with
    | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | false =>
      simp only [Bool.false_eq_true, if_false]
      dsimp only [Bind.bind, ReaderT.bind]
      have structReached := NativeDefEqFallbackReachable.eta etaReached etaAccepted
      have structCallbacks := callbacks.structures _ structReached
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (tryEtaStruct.transport _ _ _ _ agreement _ _ _ structCallbacks.forward structCallbacks.backward)
      intro structResult structState structAccepted
      cases structResult with
      | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | false =>
        simp only [Bool.false_eq_true, if_false]
        dsimp only [Bind.bind, ReaderT.bind]
        have stringReached := NativeDefEqFallbackReachable.etaStruct structReached structAccepted
        have stringCallbacks := callbacks.strings _ stringReached
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (tryStringLitExpansion.transport _ _ _ _ _ _ _ stringCallbacks.forward stringCallbacks.backward)
        intro stringResult stringState stringAccepted
        cases stringResult with
        | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
        | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
        | undef =>
          simp only [show (LBool.undef != LBool.undef) = false from rfl, Bool.false_eq_true, if_false]
          dsimp only [Bind.bind, ReaderT.bind]
          have unitReached := NativeDefEqFallbackReachable.string stringReached stringAccepted
          apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
            (isDefEqUnitLike.transport _ _ _ _ agreement _ _ _ (callbacks.units _ unitReached))
          intro unitResult unitState _
          cases unitResult <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.nativeDefEqRenormalize.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqRenormalizeCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqRenormalize first second actualMethods) (nativeDefEqRenormalize first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDefEqRenormalize, whnfCore, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.firstNormalization
  intro normalizedFirst firstState firstAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.secondNormalization _ _ firstAccepted)
  intro normalizedSecond secondState secondAccepted
  cases matching : ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second with
  | false => exact callbacks.changed _ _ _ _ firstAccepted secondAccepted matching
  | true => exact nativeDefEqFallback.transport _ _ _ _ agreement _ _ _ (callbacks.unchanged _ _ _ _ firstAccepted secondAccepted matching)

theorem TypeChecker.Inner.nativeDefEqSimple.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqSimpleCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqSimple first second actualMethods) (nativeDefEqSimple first second shadowMethods)
      actualContext shadowContext state := by
  cases first <;> cases second <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  rename_i firstParent firstIndex firstBody secondParent secondIndex secondBody
  dsimp only [nativeDefEqSimple]
  cases matching : firstIndex == secondIndex with
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true => exact isDefEq.transport _ _ _ _ _ _ _ (callbacks _ _ _ _ _ _ rfl rfl matching)

theorem TypeChecker.Inner.nativeDefEqUnknown.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqUnknownCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqUnknown first second actualMethods) (nativeDefEqUnknown first second shadowMethods)
      actualContext shadowContext state := by
  rw [nativeDefEqUnknown.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (nativeDefEqSimple.transport _ _ _ _ _ _ _ callbacks.simple)
  intro simpleResult nextState accepted
  cases simpleResult with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact nativeDefEqRenormalize.transport _ _ _ _ agreement _ _ _ (callbacks.continuation _ accepted)

theorem TypeChecker.Inner.nativeDefEqDelta.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqDelta first second actualMethods) (nativeDefEqDelta first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDefEqDelta, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (lazyDeltaReduction.headerAxiomTransport _ _ _ _ agreement policy budget _ _ _ callbacks.reduction)
  intro reduction nextState accepted
  cases reduction with
  | «continue» nextFirst nextSecond => intro result completed; exact completed
  | bool equal => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | unknown normalizedFirst normalizedSecond =>
    exact nativeDefEqUnknown.transport _ _ _ _ agreement _ _ _ (callbacks.unknown _ _ _ accepted)

theorem TypeChecker.Inner.nativeDefEqProof.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqProofCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqProof first second actualMethods) (nativeDefEqProof first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDefEqProof, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (isDefEqProofIrrel.transport _ _ _ _ _ _ _ callbacks.proofIrrelevance)
  intro proof nextState accepted
  cases proof with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | undef => exact nativeDefEqDelta.transport _ _ _ _ agreement policy budget _ _ _ (callbacks.continuation _ accepted)

theorem TypeChecker.Inner.nativeDefEqNormalized.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second normalizedFirst normalizedSecond : Expr)
    (callbacks : NativeDefEqNormalizedCallbacks actualMethods shadowMethods actualContext shadowContext state first second normalizedFirst normalizedSecond) :
    TypeChecker.M.SuccessTransport (nativeDefEqNormalized first second normalizedFirst normalizedSecond actualMethods)
      (nativeDefEqNormalized first second normalizedFirst normalizedSecond shadowMethods) actualContext shadowContext state := by
  rw [nativeDefEqNormalized.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (by
      unfold nativeDefEqRecheck
      cases matching : ptrEqExpr normalizedFirst first && ptrEqExpr normalizedSecond second with
      | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | false => exact quickIsDefEq.transport _ _ _ _ _ _ _ false (callbacks.recheck matching))
  intro rechecked nextState accepted
  cases rechecked with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | undef => exact nativeDefEqProof.transport _ _ _ _ agreement policy budget _ _ _ (callbacks.continuation _ accepted)

theorem TypeChecker.Inner.nativeDefEqCheap.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqCheapCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqCheap first second actualMethods) (nativeDefEqCheap first second shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeDefEqCheap, whnfCore, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.firstNormalization
  intro normalizedFirst firstState firstAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.secondNormalization _ _ firstAccepted)
  intro normalizedSecond secondState secondAccepted
  exact nativeDefEqNormalized.transport _ _ _ _ agreement policy budget _ _ _ _ _ (callbacks.continuation _ _ _ _ firstAccepted secondAccepted)

theorem TypeChecker.Inner.nativeDefEqBoolShortcut.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (state : TypeChecker.State) (first second : Expr)
    (callback : nativeDefEqBoolGate actualContext first second = true →
      TypeChecker.M.SuccessTransport (actualMethods.whnf first) (shadowMethods.whnf first) actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (nativeDefEqBoolShortcut first second actualMethods) (nativeDefEqBoolShortcut first second shadowMethods)
      actualContext shadowContext state := by
  intro result accepted
  dsimp only [nativeDefEqBoolShortcut, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
    ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.bind, Except.pure] at accepted ⊢
  have gate : nativeDefEqBoolGate actualContext first second = nativeDefEqBoolGate shadowContext first second := by
    simp only [nativeDefEqBoolGate, policy]
  rw [← gate]
  cases matching : nativeDefEqBoolGate actualContext first second with
  | false => rw [matching] at accepted; exact accepted
  | true =>
    rw [matching] at accepted
    simp only [if_true] at accepted ⊢
    dsimp only [whnf, Bind.bind, ReaderT.bind] at accepted ⊢
    exact (TypeChecker.M.SuccessTransport.bind (actualMethods.whnf first) (shadowMethods.whnf first)
      (fun normalized => pure (normalized.isConstOf ``true)) (fun normalized => pure (normalized.isConstOf ``true))
      actualContext shadowContext state (callback matching)
      (fun _ _ _ => TypeChecker.M.SuccessTransport.pure _ _ _ _)) result accepted

theorem TypeChecker.Inner.nativeDefEqShort.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqShortCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeDefEqShort first second actualMethods) (nativeDefEqShort first second shadowMethods)
      actualContext shadowContext state := by
  rw [nativeDefEqShort.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (nativeDefEqBoolShortcut.transport _ _ _ _ policy _ _ _ callbacks.normalization)
  intro equal nextState accepted
  cases equal with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact nativeDefEqCheap.transport _ _ _ _ agreement policy budget _ _ _ (callbacks.continuation _ accepted)

theorem TypeChecker.Inner.isDefEqCore'.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (policy : actualContext.eagerReduce = shadowContext.eagerReduce)
    (budget : actualContext.fuel.lazyDelta ≤ shadowContext.fuel.lazyDelta)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeDefEqCoreCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (isDefEqCore' first second actualMethods) (isDefEqCore' first second shadowMethods)
      actualContext shadowContext state := by
  rw [isDefEqCore'.entry_eq]
  dsimp only [nativeDefEqEntry, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (quickIsDefEq.transport _ _ _ _ _ _ _ true callbacks.quick)
  intro quick nextState accepted
  cases quick with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | undef => exact nativeDefEqShort.transport _ _ _ _ agreement policy budget _ _ _ (callbacks.continuation _ accepted)

end Lean4Lean
