import Lean4Lean.Verify.InductiveHeaderWHNFTransport

namespace Lean4Lean
open Lean hiding Environment Exception

inductive NativeAppReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (arguments : Array Expr) (initialType : Expr) :
    Expr → Nat → Nat → TypeChecker.State → Prop
  | initial : NativeAppReachable methods context state source arguments initialType initialType 0 0 state
  | direct {name domain body binder pending index currentState} :
      NativeAppReachable methods context state source arguments initialType (.forallE name domain body binder) pending index currentState →
      index < arguments.size →
      NativeAppReachable methods context state source arguments initialType body pending (index + 1) currentState
  | normalized {current pending index currentState normalized normalizedState} :
      NativeAppReachable methods context state source arguments initialType current pending index currentState →
      index < arguments.size → current.isForall = false →
      TypeChecker.Inner.ensureForallCore (current.instantiateRevRange pending index arguments) source methods context currentState =
        .ok (normalized, normalizedState) →
      NativeAppReachable methods context state source arguments initialType normalized.bindingBody! index (index + 1) normalizedState

structure NativeAppCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (source : Expr) (arguments : Array Expr) (initialType : Expr) : Prop where
  normalizations : ∀ current pending index currentState,
    NativeAppReachable actualMethods actualContext state source arguments initialType current pending index currentState →
    index < arguments.size → current.isForall = false →
    ¬(current.instantiateRevRange pending index arguments).isForall = true →
    TypeChecker.M.SuccessTransport (actualMethods.whnf (current.instantiateRevRange pending index arguments))
      (shadowMethods.whnf (current.instantiateRevRange pending index arguments)) actualContext shadowContext currentState

theorem TypeChecker.Inner.inferApp.loop_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (arguments : Array Expr) (initialType : Expr)
    (callbacks : NativeAppCallbacks actualMethods shadowMethods actualContext shadowContext state source arguments initialType)
    (current : Expr) (pending index : Nat) (currentState : TypeChecker.State)
    (reached : NativeAppReachable actualMethods actualContext state source arguments initialType current pending index currentState) :
    TypeChecker.M.SuccessTransport (inferApp.loop source arguments current pending index actualMethods)
      (inferApp.loop source arguments current pending index shadowMethods) actualContext shadowContext currentState := by
  generalize distanceEq : arguments.size - index = distance
  induction distance using Nat.strongRecOn generalizing current pending index currentState with
  | ind distance inductionHypothesis =>
    rw [inferApp.loop.eq_def]
    by_cases inRange : index < arguments.size
    · rw [if_pos inRange]
      have closer : arguments.size - (index + 1) < distance := by omega
      cases current with
      | forallE name domain body binder =>
        exact inductionHypothesis _ closer body pending (index + 1) currentState (.direct reached inRange) rfl
      | _ =>
        dsimp only [Bind.bind, ReaderT.bind]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (ensureForallCore.transport actualMethods shadowMethods actualContext shadowContext currentState _ source
            (callbacks.normalizations _ pending index currentState reached inRange rfl))
        intro normalized normalizedState accepted
        exact inductionHypothesis _ closer normalized.bindingBody! index (index + 1) normalizedState
          (.normalized reached inRange rfl accepted) rfl
    · rw [if_neg inRange]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _

structure NativeInferAppCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop where
  head : TypeChecker.M.SuccessTransport (actualMethods.inferType expression.getAppFn true)
    (shadowMethods.inferType expression.getAppFn true) actualContext shadowContext state
  continuation : ∀ normalized normalizedState,
    actualMethods.inferType expression.getAppFn true actualContext state = .ok (normalized, normalizedState) →
    NativeAppCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState expression expression.getAppArgs normalized

theorem TypeChecker.Inner.inferApp.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr)
    (callbacks : NativeInferAppCallbacks actualMethods shadowMethods actualContext shadowContext state expression) :
    TypeChecker.M.SuccessTransport (inferApp expression actualMethods) (inferApp expression shadowMethods)
      actualContext shadowContext state := by
  rw [inferApp, Expr.withApp_eq]
  dsimp only [Bind.bind, ReaderT.bind, inferType]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.head
  intro normalized normalizedState accepted
  exact inferApp.loop_transport actualMethods shadowMethods actualContext shadowContext normalizedState expression
    expression.getAppArgs normalized (callbacks.continuation normalized normalizedState accepted) normalized 0 0 normalizedState .initial

theorem TypeChecker.Inner.inferConstant.headerShadowTransport
    (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (safety : actualContext.safety = shadowContext.safety) (parameters : actualContext.lparams = shadowContext.lparams)
    (name : Name) (levels : List Level) (inferOnly : Bool) :
    Except.SuccessTransport (inferConstant actualContext name levels inferOnly)
      (inferConstant shadowContext name levels inferOnly) := by
  have contextEquality : inferConstant { actualContext with env := shadowContext.env } name levels inferOnly =
      inferConstant shadowContext name levels inferOnly := by
    simp only [inferConstant, checkLevel, safety, parameters]
  intro result accepted
  rw [← contextEquality]
  exact inferConstant.headerAxiomTransport actualContext shadowContext.env agreement name levels inferOnly result accepted

def TypeChecker.State.inferenceCache (state : TypeChecker.State) (inferOnly : Bool) : InferCache :=
  cond inferOnly state.inferTypeI state.inferTypeC

structure NativeInferEntryReceipt (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool) : Prop where
  closed : expression.hasLooseBVars = false
  cacheMiss : (state.inferenceCache inferOnly)[expression]? = none

def TypeChecker.Inner.nativeInferBody (expression : Expr) (inferOnly : Bool) : TypeChecker.RecM Expr :=
  match expression with
  | .lit literal => do
    if !inferOnly then
      match literal with
      | .natVal _ => _ ← (← TypeChecker.getEnv).get ``Nat
      | .strVal _ => _ ← (← TypeChecker.getEnv).get ``Char.ofNat; _ ← (← TypeChecker.getEnv).get ``String.ofList
    pure (mkConst literal.typeName)
  | .mdata _ inner => inferType' inner inferOnly
  | .proj parent index source => do inferProj parent index source (← inferType' source inferOnly)
  | .fvar name => do inferFVar (← readThe TypeChecker.Context) name
  | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
  | .bvar _ => panicWithPosWithDecl "Lean4Lean.TypeChecker" "Lean4Lean.TypeChecker.Inner.inferType'" 242 17
      "unreachable code has been reached"
  | .sort level => do
    if !inferOnly then checkLevel (← readThe TypeChecker.Context) level
    pure <| .sort (.succ level)
  | .const name levels => do inferConstant (← readThe TypeChecker.Context) name levels inferOnly
  | .lam .. => inferLambda expression inferOnly
  | .forallE .. => inferForall expression inferOnly
  | .app function argument => do
    if inferOnly then inferApp expression
    else
      let functionType ← ensureForallCore (← inferType' function inferOnly) expression
      let argumentType ← inferType' argument inferOnly
      let domain := functionType.bindingDomain!
      let equal ← if argument.isAppOfArity ``eagerReduce 2 then
        withTheReader TypeChecker.Context (fun context => { context with eagerReduce := true }) <| isDefEq domain argumentType
      else isDefEq domain argumentType
      if !equal then throw <| .appTypeMismatch (← TypeChecker.getEnv) (← getLCtx) expression functionType argumentType
      pure <| functionType.bindingBody!.instantiate1 argument
  | .letE .. => inferLet expression inferOnly

theorem TypeChecker.Inner.bindIte (condition : Prop) [Decidable condition]
    (positive negative : TypeChecker.RecM firstType) (continuation : firstType → TypeChecker.RecM resultType) :
    ((if condition then positive else negative) >>= continuation) =
      if condition then positive >>= continuation else negative >>= continuation := by
  by_cases selected : condition <;> simp only [selected, if_true, if_false]

theorem TypeChecker.Inner.inferType'.entry_eq (expression : Expr) (inferOnly : Bool) :
    inferType' expression inferOnly = (do
      if expression.hasLooseBVars then
        throw <| .other "type checker does not support loose bound variables, replace them with free variables before invoking it"
      let state ← get
      if let some cached := (state.inferenceCache inferOnly)[expression]? then return cached
      let result ← nativeInferBody expression inferOnly
      modify fun state => cond inferOnly
        { state with inferTypeI := state.inferTypeI.insert expression result }
        { state with inferTypeC := state.inferTypeC.insert expression result }
      return result) := by
  cases expression <;> rw [inferType']
  all_goals simp only [nativeInferBody, TypeChecker.State.inferenceCache, bind_assoc, pure_bind, bindIte]
  case lit literal =>
    cases literal <;> cases inferOnly <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false,
      Bool.false_eq_true, bind_assoc, pure_bind] <;> rfl
  all_goals try rfl

theorem TypeChecker.Inner.inferType'.entry_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (body : NativeInferEntryReceipt state expression inferOnly →
      TypeChecker.M.SuccessTransport (nativeInferBody expression inferOnly actualMethods)
        (nativeInferBody expression inferOnly shadowMethods) actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (inferType' expression inferOnly actualMethods)
      (inferType' expression inferOnly shadowMethods) actualContext shadowContext state := by
  intro result accepted
  rw [inferType'.entry_eq] at accepted ⊢
  by_cases loose : expression.hasLooseBVars = true
  · simp only [loose, if_true] at accepted
    change Except.error _ = Except.ok result at accepted
    contradiction
  · have closed : expression.hasLooseBVars = false := Bool.eq_false_iff.mpr loose
    simp only [loose, Bool.false_eq_true, if_false] at accepted ⊢
    dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, MonadState.get, getThe,
      MonadStateOf.get, StateT.get, Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure,
      StateT.bind, StateT.pure, Except.pure, Except.bind] at accepted ⊢
    cases cached : (state.inferenceCache inferOnly)[expression]? with
    | some value => simpa only [cached] using accepted
    | none =>
      have entry : NativeInferEntryReceipt state expression inferOnly := ⟨closed, cached⟩
      simp only [cached] at accepted ⊢
      dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at accepted ⊢
      cases found : nativeInferBody expression inferOnly actualMethods actualContext state with
      | error error => rw [found] at accepted; contradiction
      | ok returned =>
        have transported := body entry returned found
        rw [found] at accepted
        rw [transported]
        exact accepted

def TypeChecker.Context.inferComparisonContext (context : TypeChecker.Context) (argument : Expr) : TypeChecker.Context :=
  if argument.isAppOfArity `eagerReduce 2 then { context with eagerReduce := true } else context

inductive NativeInferReachable (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (root : Expr) (inferOnly : Bool) : Expr → TypeChecker.State → Prop
  | initial : NativeInferEntryReceipt state root inferOnly → NativeInferReachable methods context state root inferOnly root state
  | metadata {data inner currentState} :
      NativeInferReachable methods context state root inferOnly (.mdata data inner) currentState →
      NativeInferEntryReceipt currentState inner inferOnly → NativeInferReachable methods context state root inferOnly inner currentState
  | projection {parent index source currentState} :
      NativeInferReachable methods context state root inferOnly (.proj parent index source) currentState →
      NativeInferEntryReceipt currentState source inferOnly → NativeInferReachable methods context state root inferOnly source currentState
  | function {function argument currentState} :
      NativeInferReachable methods context state root inferOnly (.app function argument) currentState → inferOnly = false →
      NativeInferEntryReceipt currentState function inferOnly → NativeInferReachable methods context state root inferOnly function currentState
  | argument {function argument currentState functionType functionState normalized normalizedState} :
      NativeInferReachable methods context state root inferOnly (.app function argument) currentState → inferOnly = false →
      TypeChecker.Inner.inferType' function inferOnly methods context currentState = .ok (functionType, functionState) →
      TypeChecker.Inner.ensureForallCore functionType (.app function argument) methods context functionState = .ok (normalized, normalizedState) →
      NativeInferEntryReceipt normalizedState argument inferOnly → NativeInferReachable methods context state root inferOnly argument normalizedState

structure NativeInferCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (root : Expr) (inferOnly : Bool) : Prop where
  applications : ∀ function argument currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.app function argument) currentState → inferOnly = true →
    NativeInferAppCallbacks actualMethods shadowMethods actualContext shadowContext currentState (.app function argument)
  lambdas : ∀ name domain body binder currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.lam name domain body binder) currentState →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferLambda (.lam name domain body binder) inferOnly actualMethods)
      (TypeChecker.Inner.inferLambda (.lam name domain body binder) inferOnly shadowMethods) actualContext shadowContext currentState
  foralls : ∀ name domain body binder currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.forallE name domain body binder) currentState →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferForall (.forallE name domain body binder) inferOnly actualMethods)
      (TypeChecker.Inner.inferForall (.forallE name domain body binder) inferOnly shadowMethods) actualContext shadowContext currentState
  lets : ∀ name domain value body nondependent currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.letE name domain value body nondependent) currentState →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferLet (.letE name domain value body nondependent) inferOnly actualMethods)
      (TypeChecker.Inner.inferLet (.letE name domain value body nondependent) inferOnly shadowMethods) actualContext shadowContext currentState
  projections : ∀ parent index source currentState sourceType sourceState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.proj parent index source) currentState →
    TypeChecker.Inner.inferType' source inferOnly actualMethods actualContext currentState = .ok (sourceType, sourceState) →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferProj parent index source sourceType actualMethods)
      (TypeChecker.Inner.inferProj parent index source sourceType shadowMethods) actualContext shadowContext sourceState
  casts : ∀ function argument currentState functionType functionState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.app function argument) currentState → inferOnly = false →
    TypeChecker.Inner.inferType' function inferOnly actualMethods actualContext currentState = .ok (functionType, functionState) →
    ¬functionType.isForall = true → TypeChecker.M.SuccessTransport (actualMethods.whnf functionType)
      (shadowMethods.whnf functionType) actualContext shadowContext functionState
  equalities : ∀ function argument currentState functionType functionState normalized normalizedState argumentType argumentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.app function argument) currentState → inferOnly = false →
    TypeChecker.Inner.inferType' function inferOnly actualMethods actualContext currentState = .ok (functionType, functionState) →
    TypeChecker.Inner.ensureForallCore functionType (.app function argument) actualMethods actualContext functionState = .ok (normalized, normalizedState) →
    TypeChecker.Inner.inferType' argument inferOnly actualMethods actualContext normalizedState = .ok (argumentType, argumentState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore normalized.bindingDomain! argumentType)
      (shadowMethods.isDefEqCore normalized.bindingDomain! argumentType)
      (actualContext.inferComparisonContext argument) (shadowContext.inferComparisonContext argument) argumentState

theorem HeaderAxiomLookupAgreement.present
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) (info : ConstantInfo)
    (found : actual.find? name = some info) : ∃ shadowInfo, shadow.find? name = some shadowInfo := by
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · exact ⟨info, same.symm.trans found⟩
  · exact ⟨_, shadowLookup⟩

theorem TypeChecker.Inner.nativeInferBody.literal_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (literal : Literal) (inferOnly : Bool) :
    TypeChecker.M.SuccessTransport (nativeInferBody (.lit literal) inferOnly actualMethods)
      (nativeInferBody (.lit literal) inferOnly shadowMethods) actualContext shadowContext state := by
  intro result accepted
  cases inferOnly
  case true => exact accepted
  case false =>
    cases literal
    all_goals
      simp only [nativeInferBody, Bool.not_false, if_true] at accepted ⊢
      dsimp only [nativeInferBody, TypeChecker.getEnv, getLCtx, liftM, MonadLift.monadLift,
        MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
        Pure.pure, Bind.bind, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.bind,
        Except.pure, StateT.lift] at accepted ⊢
    case natVal value =>
      cases found : actualContext.env.find? ``Nat with
      | none => simp [Kernel.Environment.get, found] at accepted
      | some info =>
        obtain ⟨shadowInfo, shadowFound⟩ := agreement.present ``Nat info found
        simpa only [Kernel.Environment.get, found, shadowFound, Except.bind, Except.pure] using accepted
    case strVal text =>
      cases charFound : actualContext.env.find? ``Char.ofNat with
      | none => simp [Kernel.Environment.get, charFound] at accepted
      | some charInfo =>
        obtain ⟨shadowChar, shadowCharFound⟩ := agreement.present ``Char.ofNat charInfo charFound
        cases stringFound : actualContext.env.find? ``String.ofList with
        | none => simp [Kernel.Environment.get, charFound, stringFound, Pure.pure, Except.pure] at accepted
        | some stringInfo =>
          obtain ⟨shadowString, shadowStringFound⟩ := agreement.present ``String.ofList stringInfo stringFound
          simpa only [Kernel.Environment.get, charFound, shadowCharFound, stringFound, shadowStringFound,
            Except.bind, Except.pure] using accepted

theorem TypeChecker.M.SuccessTransport.liftExcept
    (actual shadow : Except Kernel.Exception resultType) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (transport : Except.SuccessTransport actual shadow) :
    TypeChecker.M.SuccessTransport (liftM actual) (liftM shadow) actualContext shadowContext state := by
  intro result accepted
  dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift,
    Bind.bind, Pure.pure, Except.bind, Except.pure] at accepted ⊢
  cases found : actual with
  | error error => rw [found] at accepted; contradiction
  | ok value =>
    have transported := transport value found
    rw [found] at accepted
    rw [transported]
    exact accepted

theorem TypeChecker.Inner.isDefEq.argument_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (argument domain argumentType : Expr)
    (comparison : TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore domain argumentType)
      (shadowMethods.isDefEqCore domain argumentType)
      (actualContext.inferComparisonContext argument) (shadowContext.inferComparisonContext argument) state) :
    TypeChecker.M.SuccessTransport
      ((if argument.isAppOfArity ``eagerReduce 2 then
          withTheReader TypeChecker.Context (fun context => { context with eagerReduce := true }) (isDefEq domain argumentType)
        else isDefEq domain argumentType) actualMethods)
      ((if argument.isAppOfArity ``eagerReduce 2 then
          withTheReader TypeChecker.Context (fun context => { context with eagerReduce := true }) (isDefEq domain argumentType)
        else isDefEq domain argumentType) shadowMethods) actualContext shadowContext state := by
  have transported := isDefEq.transport actualMethods shadowMethods
    (actualContext.inferComparisonContext argument) (shadowContext.inferComparisonContext argument) state domain argumentType comparison
  by_cases eager : argument.isAppOfArity ``eagerReduce 2 = true
  · simpa only [TypeChecker.Context.inferComparisonContext, eager, if_true] using transported
  · simpa only [TypeChecker.Context.inferComparisonContext, eager, Bool.false_eq_true, if_false] using transported

theorem TypeChecker.Inner.inferType'.reachable_headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams)
    (state : TypeChecker.State) (root : Expr) (inferOnly : Bool)
    (callbacks : NativeInferCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly)
    (current : Expr) (currentState : TypeChecker.State)
    (reaches : NativeInferEntryReceipt currentState current inferOnly →
      NativeInferReachable actualMethods actualContext state root inferOnly current currentState) :
    TypeChecker.M.SuccessTransport (inferType' current inferOnly actualMethods) (inferType' current inferOnly shadowMethods)
      actualContext shadowContext currentState := by
  induction current generalizing currentState with
  | bvar index =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _ result accepted
    exact accepted
  | mvar name =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _ result accepted
    exact accepted
  | fvar name =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _ result accepted
    dsimp only [nativeInferBody, inferFVar, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
      ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.bind, Except.pure, StateT.lift] at accepted ⊢
    simpa only [locals] using accepted
  | sort level =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _ result accepted
    cases inferOnly <;> simp only [nativeInferBody, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false] at accepted ⊢
    all_goals dsimp only [checkLevel, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
      MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
      ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.bind, Except.pure, StateT.lift] at accepted ⊢
    all_goals simpa only [parameters] using accepted
  | const name levels =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _
    exact TypeChecker.M.SuccessTransport.liftExcept _ _ actualContext shadowContext currentState
      (inferConstant.headerShadowTransport actualContext shadowContext agreement safety parameters name levels inferOnly)
  | lam name domain body binder domainIH bodyIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    exact callbacks.lambdas name domain body binder currentState (reaches entry)
  | forallE name domain body binder domainIH bodyIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    exact callbacks.foralls name domain body binder currentState (reaches entry)
  | letE name domain value body nondependent domainIH valueIH bodyIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    exact callbacks.lets name domain value body nondependent currentState (reaches entry)
  | lit literal =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro _
    exact nativeInferBody.literal_transport actualMethods shadowMethods actualContext shadowContext agreement currentState literal inferOnly
  | mdata data inner innerIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    exact innerIH currentState (fun childEntry => .metadata (reaches entry) childEntry)
  | proj parent index source sourceIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    dsimp only [nativeInferBody, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (sourceIH currentState (fun childEntry => .projection (reaches entry) childEntry))
    intro sourceType sourceState accepted
    exact callbacks.projections parent index source currentState sourceType sourceState (reaches entry) accepted
  | app function argument functionIH argumentIH =>
    apply inferType'.entry_transport actualMethods shadowMethods actualContext shadowContext currentState _ inferOnly
    intro entry
    have reached := reaches entry
    cases inferOnly with
    | true =>
      exact inferApp.transport actualMethods shadowMethods actualContext shadowContext currentState _
        (callbacks.applications function argument currentState reached rfl)
    | false =>
      simp only [nativeInferBody, Bool.false_eq_true, if_false]
      dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (functionIH currentState (fun childEntry => .function reached rfl childEntry))
      intro functionType functionState functionAccepted
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (ensureForallCore.transport actualMethods shadowMethods actualContext shadowContext functionState functionType _
          (callbacks.casts function argument currentState functionType functionState reached rfl functionAccepted))
      intro normalized normalizedState normalizedAccepted
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (argumentIH normalizedState (fun childEntry => .argument reached rfl functionAccepted normalizedAccepted childEntry))
      intro argumentType argumentState argumentAccepted
      have comparison := isDefEq.argument_transport actualMethods shadowMethods actualContext shadowContext argumentState argument normalized.bindingDomain! argumentType
        (callbacks.equalities function argument currentState functionType functionState normalized normalizedState argumentType argumentState
          reached rfl functionAccepted normalizedAccepted argumentAccepted)
      by_cases eager : argument.isAppOfArity ``eagerReduce 2 = true
      all_goals
        simp only [eager, if_true, Bool.false_eq_true, if_false] at comparison ⊢
        dsimp only [ReaderT.bind]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ comparison
        intro equal equalityState _
        cases equal with
        | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
        | false =>
          intro result accepted
          change Except.error _ = Except.ok result at accepted
          contradiction

theorem TypeChecker.Inner.inferType'.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeInferCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferType' expression inferOnly actualMethods) (inferType' expression inferOnly shadowMethods)
      actualContext shadowContext state :=
  inferType'.reachable_headerAxiomTransport actualMethods shadowMethods actualContext shadowContext agreement locals safety parameters
    state expression inferOnly callbacks expression state .initial

end Lean4Lean
