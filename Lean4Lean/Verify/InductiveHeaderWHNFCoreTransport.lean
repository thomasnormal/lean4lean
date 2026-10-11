import Lean4Lean.Verify.InductiveHeaderReductionTransport

namespace Lean4Lean
open Lean hiding Environment Exception

def TypeChecker.Inner.whnfCoreBetaInput (arguments : Array Expr) (consumed : Nat) (body : Expr) : Expr :=
  match body with
  | .lam _ _ next _ =>
    if consumed < arguments.size then whnfCoreBetaInput arguments (consumed + 1) next
    else (body.instantiateRange (arguments.size - consumed) arguments.size arguments).mkAppRevRange 0
      (arguments.size - consumed) arguments
  | _ => (body.instantiateRange (arguments.size - consumed) arguments.size arguments).mkAppRevRange 0
      (arguments.size - consumed) arguments
termination_by structural body

theorem TypeChecker.Inner.whnfCore'.loop_eq (expression : Expr) (cheapRec cheapProj : Bool)
    (arguments : Array Expr) (consumed : Nat) (body : Expr) :
    whnfCore'.loop expression cheapRec cheapProj arguments consumed body = (do
      let normalized ← whnfCore (whnfCoreBetaInput arguments consumed body) cheapRec cheapProj
      whnfCore'.save expression cheapRec cheapProj normalized) := by
  induction body generalizing consumed with
  | lam name domain body binder domainIH bodyIH =>
    simp only [whnfCore'.loop, whnfCoreBetaInput]
    split
    · exact bodyIH _
    · rfl
  | _ => rfl

theorem TypeChecker.Inner.whnfCore'.save_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression normalized : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport (whnfCore'.save expression cheapRec cheapProj normalized actualMethods)
      (whnfCore'.save expression cheapRec cheapProj normalized shadowMethods) actualContext shadowContext state := by
  cases cheapRec <;> cases cheapProj <;> intro result accepted <;> exact accepted

theorem TypeChecker.Inner.whnfCore'.consumeMData (expression : Expr) (cheapRec cheapProj : Bool) :
    whnfCore' expression cheapRec cheapProj = whnfCore' expression.consumeMData cheapRec cheapProj := by
  induction expression with
  | mdata data expression inductionHypothesis =>
    simp only [whnfCore', Expr.consumeMData, bind_pure]
    exact inductionHypothesis
  | _ => rfl

structure NativeCoreHeadReceipt (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool) (normalized : Expr)
    (normalizedState : TypeChecker.State) : Prop where
  application : expression.isApp = true
  cacheMiss : state.whnfCoreCache[expression]? = none
  normalization : methods.whnfCore expression.getAppFn cheapRec cheapProj context state = .ok (normalized, normalizedState)

structure NativeCoreCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (cheapRec cheapProj : Bool) : Prop where
  fvars : expression.isFVar = true → state.whnfCoreCache[expression]? = none → ∀ declaration value,
    actualContext.lctx.find? expression.fvarId! = some declaration → declaration.value? true = some value →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore value cheapRec cheapProj)
      (shadowMethods.whnfCore value cheapRec cheapProj) actualContext shadowContext state
  lets : ∀ name domain value body nondependent, expression = .letE name domain value body nondependent →
    state.whnfCoreCache[expression]? = none →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore (body.instantiate1 value) cheapRec cheapProj)
      (shadowMethods.whnfCore (body.instantiate1 value) cheapRec cheapProj) actualContext shadowContext state
  heads : expression.isApp = true → state.whnfCoreCache[expression]? = none →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore expression.getAppFn cheapRec cheapProj)
      (shadowMethods.whnfCore expression.getAppFn cheapRec cheapProj) actualContext shadowContext state
  beta : ∀ name domain body binder finalState,
    NativeCoreHeadReceipt actualMethods actualContext state expression cheapRec cheapProj (.lam name domain body binder) finalState →
    TypeChecker.M.SuccessTransport
      (actualMethods.whnfCore (TypeChecker.Inner.whnfCoreBetaInput expression.getAppRevArgs 1 body) cheapRec cheapProj)
      (shadowMethods.whnfCore (TypeChecker.Inner.whnfCoreBetaInput expression.getAppRevArgs 1 body) cheapRec cheapProj)
      actualContext shadowContext finalState
  rebuilt : ∀ normalized finalState,
    NativeCoreHeadReceipt actualMethods actualContext state expression cheapRec cheapProj normalized finalState →
    normalized.isLambda = false → (normalized == expression.getAppFn) = false → TypeChecker.M.SuccessTransport
      (actualMethods.whnfCore (normalized.mkAppRevRange 0 expression.getAppRevArgs.size expression.getAppRevArgs) cheapRec cheapProj)
      (shadowMethods.whnfCore (normalized.mkAppRevRange 0 expression.getAppRevArgs.size expression.getAppRevArgs) cheapRec cheapProj)
      actualContext shadowContext finalState
  recursors : ∀ normalized finalState,
    NativeCoreHeadReceipt actualMethods actualContext state expression cheapRec cheapProj normalized finalState →
    normalized.isLambda = false → (normalized == expression.getAppFn) = true → TypeChecker.M.SuccessTransport
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj shadowMethods) actualContext shadowContext finalState
  recursorResults : ∀ normalized finalState reduced reducedState,
    NativeCoreHeadReceipt actualMethods actualContext state expression cheapRec cheapProj normalized finalState →
    normalized.isLambda = false → (normalized == expression.getAppFn) = true →
    TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj actualMethods actualContext finalState = .ok (some reduced, reducedState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore reduced cheapRec cheapProj)
      (shadowMethods.whnfCore reduced cheapRec cheapProj) actualContext shadowContext reducedState
  projections : ∀ parent index source, expression = .proj parent index source → state.whnfCoreCache[expression]? = none →
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceProj index source cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceProj index source cheapRec cheapProj shadowMethods) actualContext shadowContext state
  projectionResults : ∀ parent index source reduced reducedState, expression = .proj parent index source →
    state.whnfCoreCache[expression]? = none →
    TypeChecker.Inner.reduceProj index source cheapRec cheapProj actualMethods actualContext state = .ok (some reduced, reducedState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore reduced cheapRec cheapProj)
      (shadowMethods.whnfCore reduced cheapRec cheapProj) actualContext shadowContext reducedState

theorem TypeChecker.Inner.whnfFVar.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool)
    (locals : actualContext.lctx = shadowContext.lctx)
    (values : ∀ declaration value, actualContext.lctx.find? expression.fvarId! = some declaration →
      declaration.value? true = some value → TypeChecker.M.SuccessTransport
        (actualMethods.whnfCore value cheapRec cheapProj) (shadowMethods.whnfCore value cheapRec cheapProj)
        actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (whnfFVar expression cheapRec cheapProj actualMethods)
      (whnfFVar expression cheapRec cheapProj shadowMethods) actualContext shadowContext state := by
  intro result accepted
  dsimp only [whnfFVar, getLCtx, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
    ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind, whnfCore] at accepted ⊢
  rw [← locals]
  cases selected : actualContext.lctx.find? expression.fvarId! with
  | none =>
    rw [selected] at accepted
    exact accepted
  | some declaration =>
    rw [selected] at accepted
    cases declaration with
    | cdecl index fvar name type binder kind => exact accepted
    | ldecl index fvar name type value nondependent kind =>
      dsimp only [ReaderT.bind, ReaderT.pure, whnfCore] at accepted ⊢
      simp only [bind_pure] at accepted ⊢
      cases nondependent <;> exact values _ value selected rfl result accepted

theorem TypeChecker.Inner.whnfCore'.app_eq (expression : Expr) (cheapRec cheapProj : Bool)
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (application : expression.isApp = true) :
    whnfCore' expression cheapRec cheapProj methods context state =
      ((match state.whnfCoreCache[expression]? with
        | some cached => pure cached
        | none => do
          let normalized ← whnfCore expression.getAppFn cheapRec cheapProj
          match normalized with
          | .lam _ _ body _ => whnfCore'.loop expression cheapRec cheapProj expression.getAppRevArgs 1 body
          | _ =>
            if normalized == expression.getAppFn then
              if let some reduced ← reduceRecursor expression cheapRec cheapProj then
                whnfCore reduced cheapRec cheapProj
              else pure expression
            else do
              let result ← whnfCore (normalized.mkAppRevRange 0 expression.getAppRevArgs.size expression.getAppRevArgs) cheapRec cheapProj
              whnfCore'.save expression cheapRec cheapProj result) methods context state) := by
  cases expression <;> simp only [Expr.isApp, Bool.false_eq_true] at application
  rename_i function argument
  simp only [whnfCore', pure_bind, Expr.withRevApp_eq]
  dsimp only [MonadState.get, getThe, MonadStateOf.get, StateT.get, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  cases cached : state.whnfCoreCache[function.app argument]? <;> rfl

theorem TypeChecker.Inner.whnfCore'.input_not_isMData (expression : Expr) : expression.consumeMData.isMData = false := by
  induction expression with
  | mdata data expression inductionHypothesis => exact inductionHypothesis
  | _ => rfl

theorem TypeChecker.Inner.whnfCore'.fvar_eq (name : FVarId) (cheapRec cheapProj : Bool)
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State) :
    whnfCore' (.fvar name) cheapRec cheapProj methods context state =
      ((if !isLetFVar context.lctx name then pure (Expr.fvar name)
        else match state.whnfCoreCache[Expr.fvar name]? with
          | some cached => pure cached
          | none => do pure (← whnfFVar (.fvar name) cheapRec cheapProj)) methods context state) := by
  simp only [whnfCore', pure_bind]
  dsimp only [getLCtx, MonadState.get, getThe, MonadStateOf.get, StateT.get, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  cases localLet : isLetFVar context.lctx name with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    dsimp only [Bind.bind, ReaderT.bind, StateT.bind, StateT.get, Pure.pure,
      ReaderT.pure, StateT.pure, Except.pure, Except.bind]
    cases cached : state.whnfCoreCache[Expr.fvar name]? <;> rfl

theorem TypeChecker.Inner.whnfCore'.let_eq (name : Name) (domain value body : Expr) (nondependent : Bool)
    (cheapRec cheapProj : Bool) (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State) :
    whnfCore' (.letE name domain value body nondependent) cheapRec cheapProj methods context state =
      ((match state.whnfCoreCache[Expr.letE name domain value body nondependent]? with
        | some cached => pure cached
        | none => do
          let normalized ← whnfCore (body.instantiate1 value) cheapRec cheapProj
          whnfCore'.save (.letE name domain value body nondependent) cheapRec cheapProj normalized) methods context state) := by
  simp only [whnfCore', pure_bind]
  dsimp only [MonadState.get, getThe, MonadStateOf.get, StateT.get, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  cases cached : state.whnfCoreCache[Expr.letE name domain value body nondependent]? <;> rfl

theorem TypeChecker.Inner.whnfCore'.proj_eq (parent : Name) (index : Nat) (source : Expr)
    (cheapRec cheapProj : Bool) (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State) :
    whnfCore' (.proj parent index source) cheapRec cheapProj methods context state =
      ((match state.whnfCoreCache[Expr.proj parent index source]? with
        | some cached => pure cached
        | none => do
          if let some reduced ← reduceProj index source cheapRec cheapProj then
            let normalized ← whnfCore reduced cheapRec cheapProj
            whnfCore'.save (.proj parent index source) cheapRec cheapProj normalized
          else whnfCore'.save (.proj parent index source) cheapRec cheapProj (.proj parent index source)) methods context state) := by
  simp only [whnfCore', pure_bind]
  dsimp only [MonadState.get, getThe, MonadStateOf.get, StateT.get, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  cases cached : state.whnfCoreCache[Expr.proj parent index source]? <;> rfl

theorem TypeChecker.Inner.whnfCore'.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool)
    (locals : actualContext.lctx = shadowContext.lctx)
    (callbacks : NativeCoreCallbacks actualMethods shadowMethods actualContext shadowContext state
      expression.consumeMData cheapRec cheapProj) :
    TypeChecker.M.SuccessTransport (whnfCore' expression cheapRec cheapProj actualMethods)
      (whnfCore' expression cheapRec cheapProj shadowMethods) actualContext shadowContext state := by
  have noMetadata := whnfCore'.input_not_isMData expression
  rw [whnfCore'.consumeMData expression]
  generalize inputEq : expression.consumeMData = input at callbacks noMetadata ⊢
  cases input <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  case mdata data inner => cases noMetadata
  case fvar name =>
    unfold TypeChecker.M.SuccessTransport
    rw [whnfCore'.fvar_eq, whnfCore'.fvar_eq]
    rw [← locals]
    cases isLet : isLetFVar actualContext.lctx name with
    | false => exact TypeChecker.M.SuccessTransport.pure (Expr.fvar name) actualContext shadowContext state
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases cached : state.whnfCoreCache[Expr.fvar name]? with
      | some value => exact TypeChecker.M.SuccessTransport.pure value actualContext shadowContext state
      | none =>
        change TypeChecker.M.SuccessTransport _ _ actualContext shadowContext state
        dsimp only [Bind.bind, ReaderT.bind]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (whnfFVar.transport actualMethods shadowMethods actualContext shadowContext state
            (.fvar name) cheapRec cheapProj locals (callbacks.fvars rfl cached))
        intro result finalState _
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  case letE name domain value body nondependent =>
    unfold TypeChecker.M.SuccessTransport
    rw [whnfCore'.let_eq, whnfCore'.let_eq]
    cases cached : state.whnfCoreCache[Expr.letE name domain value body nondependent]? with
    | some result => exact TypeChecker.M.SuccessTransport.pure result actualContext shadowContext state
    | none =>
      change TypeChecker.M.SuccessTransport _ _ actualContext shadowContext state
      dsimp only [Bind.bind, ReaderT.bind, whnfCore]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.lets name domain value body nondependent rfl cached)
      intro normalized finalState _
      exact whnfCore'.save_transport actualMethods shadowMethods actualContext shadowContext finalState _ _ cheapRec cheapProj
  case proj parent index source =>
    unfold TypeChecker.M.SuccessTransport
    rw [whnfCore'.proj_eq, whnfCore'.proj_eq]
    cases cached : state.whnfCoreCache[Expr.proj parent index source]? with
    | some result => exact TypeChecker.M.SuccessTransport.pure result actualContext shadowContext state
    | none =>
      change TypeChecker.M.SuccessTransport _ _ actualContext shadowContext state
      dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.projections parent index source rfl cached)
      intro reduced finalState accepted
      cases reduced with
      | none => exact whnfCore'.save_transport actualMethods shadowMethods actualContext shadowContext finalState _ _ cheapRec cheapProj
      | some result =>
        dsimp only [Bind.bind, ReaderT.bind, whnfCore]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (callbacks.projectionResults parent index source result finalState rfl cached accepted)
        intro normalized normalizedState _
        exact whnfCore'.save_transport actualMethods shadowMethods actualContext shadowContext normalizedState _ _ cheapRec cheapProj
  case app function argument =>
    unfold TypeChecker.M.SuccessTransport
    rw [whnfCore'.app_eq _ _ _ _ _ _ rfl, whnfCore'.app_eq _ _ _ _ _ _ rfl]
    cases cached : state.whnfCoreCache[function.app argument]? with
    | some result => exact TypeChecker.M.SuccessTransport.pure result actualContext shadowContext state
    | none =>
      change TypeChecker.M.SuccessTransport _ _ actualContext shadowContext state
      dsimp only [Bind.bind, ReaderT.bind, whnfCore]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.heads rfl cached)
      intro normalized finalState accepted
      have receipt : NativeCoreHeadReceipt actualMethods actualContext state (function.app argument)
          cheapRec cheapProj normalized finalState := ⟨rfl, cached, accepted⟩
      cases normalized with
      | lam name domain body binder =>
        dsimp only
        rw [whnfCore'.loop_eq]
        dsimp only [Bind.bind, ReaderT.bind, whnfCore]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.beta name domain body binder finalState receipt)
        intro result resultState _
        exact whnfCore'.save_transport actualMethods shadowMethods actualContext shadowContext resultState _ _ cheapRec cheapProj
      | _ =>
        dsimp only
        split
        · rename_i unchanged
          dsimp only [Bind.bind, ReaderT.bind]
          apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.recursors _ finalState receipt rfl unchanged)
          intro reduced reducedState reducedAccepted
          cases reduced with
          | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
          | some result => exact callbacks.recursorResults _ finalState result reducedState receipt rfl unchanged reducedAccepted
        · rename_i changed
          dsimp only [Bind.bind, ReaderT.bind, whnfCore]
          apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
            (callbacks.rebuilt _ finalState receipt rfl (Bool.eq_false_iff.mpr changed))
          intro result resultState _
          exact whnfCore'.save_transport actualMethods shadowMethods actualContext shadowContext resultState _ _ cheapRec cheapProj

end Lean4Lean
