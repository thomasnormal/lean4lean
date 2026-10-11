import Lean4Lean.Verify.InductiveHeaderInferenceTransport

namespace Lean4Lean
open Lean hiding Environment Exception

def TypeChecker.State.allocateLocal (state : TypeChecker.State) : TypeChecker.State :=
  { state with ngen := state.ngen.next }

def TypeChecker.Context.openLocal (context : TypeChecker.Context) (state : TypeChecker.State)
    (name : Name) (binder : BinderInfo) (type : Expr) : TypeChecker.Context :=
  { context with lctx := context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name type binder }

def TypeChecker.Context.openLet (context : TypeChecker.Context) (state : TypeChecker.State)
    (name : Name) (type value : Expr) : TypeChecker.Context :=
  { context with lctx := context.lctx.mkLetDecl ⟨state.ngen.curr⟩ name type value }

theorem TypeChecker.withLocalDecl_apply (name : Name) (binder : BinderInfo) (type : Expr)
    (continuation : Expr → RecM resultType) (methods : Methods) (context : Context) (state : State) :
    withLocalDecl name binder type continuation methods context state =
      continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLocal state name binder type) state.allocateLocal := by
  rfl

theorem TypeChecker.withLetDecl_apply (name : Name) (type value : Expr)
    (continuation : Expr → RecM resultType) (methods : Methods) (context : Context) (state : State) :
    withLetDecl name type value continuation methods context state =
      continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLet state name type value) state.allocateLocal := by
  rfl

theorem TypeChecker.withLocalDecl_restore (name : Name) (binder : BinderInfo) (type : Expr)
    (continuation : Expr → RecM resultType) (methods : Methods) (context : Context) (state : State) :
    ((do
      let result ← withLocalDecl name binder type continuation
      return (result, ← readThe Context)) : RecM (resultType × Context)) methods context state =
      (continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLocal state name binder type) state.allocateLocal).map
        (fun (result, finalState) => ((result, context), finalState)) := by
  change (continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLocal state name binder type) state.allocateLocal >>=
    fun (result, finalState) => .ok ((result, context), finalState)) = _
  cases continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLocal state name binder type) state.allocateLocal <;> rfl

theorem TypeChecker.withLetDecl_restore (name : Name) (type value : Expr)
    (continuation : Expr → RecM resultType) (methods : Methods) (context : Context) (state : State) :
    ((do
      let result ← withLetDecl name type value continuation
      return (result, ← readThe Context)) : RecM (resultType × Context)) methods context state =
      (continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLet state name type value) state.allocateLocal).map
        (fun (result, finalState) => ((result, context), finalState)) := by
  change (continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLet state name type value) state.allocateLocal >>=
    fun (result, finalState) => .ok ((result, context), finalState)) = _
  cases continuation (.fvar ⟨state.ngen.curr⟩) methods (context.openLet state name type value) state.allocateLocal <;> rfl

theorem TypeChecker.withLocalDecl_transport (actualMethods shadowMethods : Methods)
    (actualContext shadowContext : Context) (state : State) (name : Name) (binder : BinderInfo) (type : Expr)
    (actualNext shadowNext : Expr → RecM resultType)
    (continuation : M.SuccessTransport (actualNext (.fvar ⟨state.ngen.curr⟩) actualMethods)
      (shadowNext (.fvar ⟨state.ngen.curr⟩) shadowMethods)
      (actualContext.openLocal state name binder type) (shadowContext.openLocal state name binder type) state.allocateLocal) :
    M.SuccessTransport (withLocalDecl name binder type actualNext actualMethods)
      (withLocalDecl name binder type shadowNext shadowMethods) actualContext shadowContext state := by
  exact continuation

theorem TypeChecker.withLetDecl_transport (actualMethods shadowMethods : Methods)
    (actualContext shadowContext : Context) (state : State) (name : Name) (type value : Expr)
    (actualNext shadowNext : Expr → RecM resultType)
    (continuation : M.SuccessTransport (actualNext (.fvar ⟨state.ngen.curr⟩) actualMethods)
      (shadowNext (.fvar ⟨state.ngen.curr⟩) shadowMethods)
      (actualContext.openLet state name type value) (shadowContext.openLet state name type value) state.allocateLocal) :
    M.SuccessTransport (withLetDecl name type value actualNext actualMethods)
      (withLetDecl name type value shadowNext shadowMethods) actualContext shadowContext state := by
  exact continuation

def TypeChecker.Inner.inferSort (expression source : Expr) (inferOnly : Bool) : TypeChecker.RecM Expr := do
  ensureSortCore (← inferType expression inferOnly) source

structure NativeSortCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (inferOnly : Bool) : Prop where
  inference : TypeChecker.M.SuccessTransport (actualMethods.inferType expression inferOnly)
    (shadowMethods.inferType expression inferOnly) actualContext shadowContext state
  normalization : ∀ inferred inferredState,
    actualMethods.inferType expression inferOnly actualContext state = .ok (inferred, inferredState) →
    ¬inferred.isSort = true →
    TypeChecker.M.SuccessTransport (actualMethods.whnf inferred) (shadowMethods.whnf inferred)
      actualContext shadowContext inferredState

theorem TypeChecker.Inner.inferSort.transport (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (expression source : Expr) (inferOnly : Bool)
    (callbacks : NativeSortCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferSort expression source inferOnly actualMethods)
      (inferSort expression source inferOnly shadowMethods) actualContext shadowContext state := by
  dsimp only [inferSort, inferType, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.inference
  intro inferred inferredState accepted
  exact ensureSortCore.transport _ _ _ _ _ _ _ (callbacks.normalization inferred inferredState accepted)

def TypeChecker.Inner.lambdaDomain (domain : Expr) (inferOnly : Bool) : TypeChecker.RecM Unit := do
  if !inferOnly then
    let _ ← inferSort domain domain inferOnly
    pure ()

theorem TypeChecker.Inner.lambdaDomain.transport (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (domain : Expr) (inferOnly : Bool)
    (callbacks : inferOnly = false →
      NativeSortCallbacks actualMethods shadowMethods actualContext shadowContext state domain inferOnly) :
    TypeChecker.M.SuccessTransport (lambdaDomain domain inferOnly actualMethods)
      (lambdaDomain domain inferOnly shadowMethods) actualContext shadowContext state := by
  cases inferOnly with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false =>
    dsimp only [lambdaDomain]
    simp only [Bool.not_false, if_true]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (inferSort.transport _ _ _ _ _ _ _ _ (callbacks rfl))
    intro inferred inferredState accepted
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

inductive NativeLambdaReachable (methods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) :
    TypeChecker.Context → TypeChecker.Context → Array Expr → Expr → TypeChecker.State → Prop
  | initial : NativeLambdaReachable methods actualContext shadowContext state root inferOnly
      actualContext shadowContext #[] root state
  | opened {actual shadow fvars name domain body binder currentState checkedState} :
      NativeLambdaReachable methods actualContext shadowContext state root inferOnly
        actual shadow fvars (.lam name domain body binder) currentState →
      TypeChecker.Inner.lambdaDomain (domain.instantiateRev fvars) inferOnly methods actual currentState =
        .ok ((), checkedState) →
      NativeLambdaReachable methods actualContext shadowContext state root inferOnly
        (actual.openLocal checkedState name binder (domain.instantiateRev fvars))
        (shadow.openLocal checkedState name binder (domain.instantiateRev fvars))
        (fvars.push (.fvar ⟨checkedState.ngen.curr⟩)) body checkedState.allocateLocal

theorem NativeLambdaReachable.locals
    (locals : actualContext.lctx = shadowContext.lctx)
    (reached : NativeLambdaReachable methods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) : actual.lctx = shadow.lctx := by
  induction reached with
  | initial => exact locals
  | opened reached accepted inductionHypothesis =>
    simp only [TypeChecker.Context.openLocal, inductionHypothesis]

structure NativeLambdaCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) : Prop where
  domains : ∀ actual shadow fvars name domain body binder currentState,
    NativeLambdaReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars (.lam name domain body binder) currentState → inferOnly = false →
    NativeSortCallbacks actualMethods shadowMethods actual shadow currentState (domain.instantiateRev fvars) inferOnly
  terminals : ∀ actual shadow fvars current currentState,
    NativeLambdaReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState → current.isLambda = false →
    TypeChecker.M.SuccessTransport (actualMethods.inferType (current.instantiateRev fvars) inferOnly)
      (shadowMethods.inferType (current.instantiateRev fvars) inferOnly) actual shadow currentState

theorem TypeChecker.Inner.inferLambda.loop_lam (name : Name) (domain body : Expr)
    (binder : BinderInfo) (fvars : Array Expr) (inferOnly : Bool) :
    inferLambda.loop inferOnly fvars (.lam name domain body binder) = (do
      lambdaDomain (domain.instantiateRev fvars) inferOnly
      withLocalDecl name binder (domain.instantiateRev fvars) fun fresh =>
        inferLambda.loop inferOnly (fvars.push fresh) body) := by
  rw [inferLambda.loop.eq_def]
  cases inferOnly <;>
    simp only [lambdaDomain, inferSort, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_true, if_false, bind_assoc, pure_bind]

theorem TypeChecker.Inner.inferLambda.loop_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (root : Expr) (inferOnly : Bool)
    (callbacks : NativeLambdaCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly)
    (actual shadow : TypeChecker.Context) (fvars : Array Expr) (current : Expr) (currentState : TypeChecker.State)
    (reached : NativeLambdaReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) :
    TypeChecker.M.SuccessTransport (inferLambda.loop inferOnly fvars current actualMethods)
      (inferLambda.loop inferOnly fvars current shadowMethods) actual shadow currentState := by
  induction current generalizing actual shadow fvars currentState with
  | lam name domain body binder domainIH bodyIH =>
    rw [loop_lam]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (lambdaDomain.transport _ _ _ _ _ _ _ (callbacks.domains _ _ _ _ _ _ _ _ reached))
    intro checked checkedState accepted
    cases checked
    apply TypeChecker.withLocalDecl_transport
    exact bodyIH _ _ _ _ (.opened reached accepted)
  | _ =>
    rw [inferLambda.loop.eq_def]
    dsimp only [inferType, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (callbacks.terminals _ _ _ _ _ reached rfl)
    intro inferred inferredState accepted
    have same := reached.locals locals
    intro result success
    change Except.ok (actual.lctx.mkForall fvars inferred.cheapBetaReduce, inferredState) = .ok result at success
    change Except.ok (shadow.lctx.mkForall fvars inferred.cheapBetaReduce, inferredState) = .ok result
    simpa only [same] using success

theorem TypeChecker.Inner.inferLambda.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeLambdaCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferLambda expression inferOnly actualMethods)
      (inferLambda expression inferOnly shadowMethods) actualContext shadowContext state :=
  inferLambda.loop_transport _ _ _ _ locals _ _ _ callbacks _ _ _ _ _ .initial

inductive NativeForallReachable (methods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) :
    TypeChecker.Context → TypeChecker.Context → Array Expr → Array Level → Expr → TypeChecker.State → Prop
  | initial : NativeForallReachable methods actualContext shadowContext state root inferOnly
      actualContext shadowContext #[] #[] root state
  | opened {actual shadow fvars levels name domain body binder currentState inferred checkedState} :
      NativeForallReachable methods actualContext shadowContext state root inferOnly
        actual shadow fvars levels (.forallE name domain body binder) currentState →
      TypeChecker.Inner.inferSort (domain.instantiateRev fvars) (domain.instantiateRev fvars) inferOnly methods actual currentState =
        .ok (inferred, checkedState) →
      NativeForallReachable methods actualContext shadowContext state root inferOnly
        (actual.openLocal checkedState name binder (domain.instantiateRev fvars))
        (shadow.openLocal checkedState name binder (domain.instantiateRev fvars))
        (fvars.push (.fvar ⟨checkedState.ngen.curr⟩)) (levels.push inferred.sortLevel!) body checkedState.allocateLocal

structure NativeForallCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) : Prop where
  domains : ∀ actual shadow fvars levels name domain body binder currentState,
    NativeForallReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars levels (.forallE name domain body binder) currentState →
    NativeSortCallbacks actualMethods shadowMethods actual shadow currentState (domain.instantiateRev fvars) inferOnly
  terminals : ∀ actual shadow fvars levels current currentState,
    NativeForallReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars levels current currentState → current.isForall = false →
    NativeSortCallbacks actualMethods shadowMethods actual shadow currentState (current.instantiateRev fvars) inferOnly

theorem TypeChecker.Inner.inferForall.loop_forall (name : Name) (domain body : Expr)
    (binder : BinderInfo) (fvars : Array Expr) (levels : Array Level) (inferOnly : Bool) :
    inferForall.loop inferOnly fvars levels (.forallE name domain body binder) = (do
      let inferred ← inferSort (domain.instantiateRev fvars) (domain.instantiateRev fvars) inferOnly
      withLocalDecl name binder (domain.instantiateRev fvars) fun fresh =>
        inferForall.loop inferOnly (fvars.push fresh) (levels.push inferred.sortLevel!) body) := by
  rw [inferForall.loop.eq_def]
  simp only [inferSort, bind_assoc]

theorem TypeChecker.Inner.inferForall.loop_terminal (current : Expr) (fvars : Array Expr)
    (levels : Array Level) (inferOnly : Bool) (terminal : current.isForall = false) :
    inferForall.loop inferOnly fvars levels current = (do
      let inferred ← inferSort (current.instantiateRev fvars) current inferOnly
      pure (Expr.sort (levels.foldr mkLevelIMax' inferred.sortLevel!))) := by
  cases current <;> simp only [Expr.isForall] at terminal <;> try contradiction
  all_goals
    rw [inferForall.loop.eq_def]
    simp only [inferSort, bind_assoc]

theorem TypeChecker.Inner.inferForall.loop_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (root : Expr) (inferOnly : Bool)
    (callbacks : NativeForallCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly)
    (actual shadow : TypeChecker.Context) (fvars : Array Expr) (levels : Array Level)
    (current : Expr) (currentState : TypeChecker.State)
    (reached : NativeForallReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars levels current currentState) :
    TypeChecker.M.SuccessTransport (inferForall.loop inferOnly fvars levels current actualMethods)
      (inferForall.loop inferOnly fvars levels current shadowMethods) actual shadow currentState := by
  induction current generalizing actual shadow fvars levels currentState with
  | forallE name domain body binder domainIH bodyIH =>
    rw [loop_forall]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (inferSort.transport _ _ _ _ _ _ _ _ (callbacks.domains _ _ _ _ _ _ _ _ _ reached))
    intro inferred checkedState accepted
    apply TypeChecker.withLocalDecl_transport
    exact bodyIH _ _ _ _ _ (.opened reached accepted)
  | _ =>
    rw [loop_terminal _ _ _ _ rfl]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (inferSort.transport _ _ _ _ _ _ _ _ (callbacks.terminals _ _ _ _ _ _ reached rfl))
    intro inferred inferredState accepted
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.inferForall.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeForallCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferForall expression inferOnly actualMethods)
      (inferForall expression inferOnly shadowMethods) actualContext shadowContext state :=
  inferForall.loop_transport _ _ _ _ _ _ _ callbacks _ _ _ _ _ _ .initial

def TypeChecker.Inner.letDomain (name : Name) (domain value : Expr) (inferOnly : Bool) : TypeChecker.RecM Unit := do
  if !inferOnly then
    let _ ← inferSort domain domain inferOnly
    let valueType ← inferType value inferOnly
    if !(← isDefEq valueType domain) then
      throw <| .letTypeMismatch (← TypeChecker.getEnv) (← getLCtx) name valueType domain

structure NativeLetDomainCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (domain value : Expr) (inferOnly : Bool) : Prop where
  domainSort : NativeSortCallbacks actualMethods shadowMethods actualContext shadowContext state domain inferOnly
  values : ∀ inferred checkedState,
    TypeChecker.Inner.inferSort domain domain inferOnly actualMethods actualContext state = .ok (inferred, checkedState) →
    TypeChecker.M.SuccessTransport (actualMethods.inferType value inferOnly)
      (shadowMethods.inferType value inferOnly) actualContext shadowContext checkedState
  comparisons : ∀ inferred checkedState valueType valueState,
    TypeChecker.Inner.inferSort domain domain inferOnly actualMethods actualContext state = .ok (inferred, checkedState) →
    actualMethods.inferType value inferOnly actualContext checkedState = .ok (valueType, valueState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore valueType domain)
      (shadowMethods.isDefEqCore valueType domain) actualContext shadowContext valueState

theorem TypeChecker.Inner.letDomain.transport (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (name : Name) (domain value : Expr) (inferOnly : Bool)
    (callbacks : inferOnly = false →
      NativeLetDomainCallbacks actualMethods shadowMethods actualContext shadowContext state domain value inferOnly) :
    TypeChecker.M.SuccessTransport (letDomain name domain value inferOnly actualMethods)
      (letDomain name domain value inferOnly shadowMethods) actualContext shadowContext state := by
  cases inferOnly with
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false =>
    dsimp only [letDomain]
    simp only [Bool.not_false, if_true]
    dsimp only [inferType, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (inferSort.transport _ _ _ _ _ _ _ _ (callbacks rfl).domainSort)
    intro inferred checkedState sorted
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      ((callbacks rfl).values inferred checkedState sorted)
    intro valueType valueState accepted
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (isDefEq.transport _ _ _ _ _ _ _ ((callbacks rfl).comparisons _ _ _ _ sorted accepted))
    intro equal comparedState compared
    cases equal with
    | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | false =>
      intro result success
      change (Except.error _ : Except Kernel.Exception (Unit × TypeChecker.State)) = .ok result at success
      contradiction

inductive NativeLetReachable (methods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) :
    TypeChecker.Context → TypeChecker.Context → Array Expr → Expr → TypeChecker.State → Prop
  | initial : NativeLetReachable methods actualContext shadowContext state root inferOnly
      actualContext shadowContext #[] root state
  | opened {actual shadow fvars name domain value body nondependent currentState checkedState} :
      NativeLetReachable methods actualContext shadowContext state root inferOnly
        actual shadow fvars (.letE name domain value body nondependent) currentState →
      TypeChecker.Inner.letDomain name (domain.instantiateRev fvars) (value.instantiateRev fvars) inferOnly methods actual currentState =
        .ok ((), checkedState) →
      NativeLetReachable methods actualContext shadowContext state root inferOnly
        (actual.openLet checkedState name (domain.instantiateRev fvars) (value.instantiateRev fvars))
        (shadow.openLet checkedState name (domain.instantiateRev fvars) (value.instantiateRev fvars))
        (fvars.push (.fvar ⟨checkedState.ngen.curr⟩)) body checkedState.allocateLocal

theorem NativeLetReachable.locals
    (locals : actualContext.lctx = shadowContext.lctx)
    (reached : NativeLetReachable methods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) : actual.lctx = shadow.lctx := by
  induction reached with
  | initial => exact locals
  | opened reached accepted inductionHypothesis =>
    simp only [TypeChecker.Context.openLet, inductionHypothesis]

structure NativeLetCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (root : Expr) (inferOnly : Bool) : Prop where
  domains : ∀ actual shadow fvars name domain value body nondependent currentState,
    NativeLetReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars (.letE name domain value body nondependent) currentState → inferOnly = false →
    NativeLetDomainCallbacks actualMethods shadowMethods actual shadow currentState
      (domain.instantiateRev fvars) (value.instantiateRev fvars) inferOnly
  terminals : ∀ actual shadow fvars current currentState,
    NativeLetReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState → current.isLet = false →
    TypeChecker.M.SuccessTransport (actualMethods.inferType (current.instantiateRev fvars) inferOnly)
      (shadowMethods.inferType (current.instantiateRev fvars) inferOnly) actual shadow currentState

theorem TypeChecker.Inner.inferLet.loop_let (name : Name) (domain value body : Expr)
    (nondependent : Bool) (fvars : Array Expr) (inferOnly : Bool) :
    inferLet.loop inferOnly fvars (.letE name domain value body nondependent) = (do
      letDomain name (domain.instantiateRev fvars) (value.instantiateRev fvars) inferOnly
      withLetDecl name (domain.instantiateRev fvars) (value.instantiateRev fvars) fun fresh =>
        inferLet.loop inferOnly (fvars.push fresh) body) := by
  rw [inferLet.loop.eq_def]
  cases inferOnly <;>
    simp only [letDomain, inferSort, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_true, if_false, bind_assoc, pure_bind, bindIte]

theorem TypeChecker.Inner.inferLet.loop_transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (root : Expr) (inferOnly : Bool)
    (callbacks : NativeLetCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly)
    (actual shadow : TypeChecker.Context) (fvars : Array Expr) (current : Expr) (currentState : TypeChecker.State)
    (reached : NativeLetReachable actualMethods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) :
    TypeChecker.M.SuccessTransport (inferLet.loop inferOnly fvars current actualMethods)
      (inferLet.loop inferOnly fvars current shadowMethods) actual shadow currentState := by
  induction current generalizing actual shadow fvars currentState with
  | letE name domain value body nondependent domainIH valueIH bodyIH =>
    rw [loop_let]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (letDomain.transport _ _ _ _ _ _ _ _ _ (callbacks.domains _ _ _ _ _ _ _ _ _ reached))
    intro checked checkedState accepted
    cases checked
    apply TypeChecker.withLetDecl_transport
    exact bodyIH _ _ _ _ (.opened reached accepted)
  | _ =>
    rw [inferLet.loop.eq_def]
    dsimp only [inferType, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (callbacks.terminals _ _ _ _ _ reached rfl)
    intro inferred inferredState accepted
    have same := reached.locals locals
    intro result success
    change Except.ok (actual.lctx.mkForall fvars inferred.cheapBetaReduce, inferredState) = .ok result at success
    change Except.ok (shadow.lctx.mkForall fvars inferred.cheapBetaReduce, inferredState) = .ok result
    simpa only [same] using success

theorem TypeChecker.Inner.inferLet.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (locals : actualContext.lctx = shadowContext.lctx) (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeLetCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferLet expression inferOnly actualMethods)
      (inferLet expression inferOnly shadowMethods) actualContext shadowContext state :=
  inferLet.loop_transport _ _ _ _ locals _ _ _ callbacks _ _ _ _ _ .initial

structure NativeInferMethodCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (root : Expr) (inferOnly : Bool) : Prop where
  applications : ∀ function argument currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.app function argument) currentState → inferOnly = true →
    NativeInferAppCallbacks actualMethods shadowMethods actualContext shadowContext currentState (.app function argument)
  lambdas : ∀ name domain body binder currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.lam name domain body binder) currentState →
    NativeLambdaCallbacks actualMethods shadowMethods actualContext shadowContext currentState (.lam name domain body binder) inferOnly
  foralls : ∀ name domain body binder currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.forallE name domain body binder) currentState →
    NativeForallCallbacks actualMethods shadowMethods actualContext shadowContext currentState (.forallE name domain body binder) inferOnly
  lets : ∀ name domain value body nondependent currentState,
    NativeInferReachable actualMethods actualContext state root inferOnly (.letE name domain value body nondependent) currentState →
    NativeLetCallbacks actualMethods shadowMethods actualContext shadowContext currentState (.letE name domain value body nondependent) inferOnly
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

theorem NativeInferMethodCallbacks.toCallbacks
    (locals : actualContext.lctx = shadowContext.lctx)
    (callbacks : NativeInferMethodCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly) :
    NativeInferCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly where
  applications := callbacks.applications
  lambdas := fun _ _ _ _ _ reached =>
    TypeChecker.Inner.inferLambda.transport _ _ _ _ locals _ _ _ (callbacks.lambdas _ _ _ _ _ reached)
  foralls := fun _ _ _ _ _ reached =>
    TypeChecker.Inner.inferForall.transport _ _ _ _ _ _ _ (callbacks.foralls _ _ _ _ _ reached)
  lets := fun _ _ _ _ _ _ reached =>
    TypeChecker.Inner.inferLet.transport _ _ _ _ locals _ _ _ (callbacks.lets _ _ _ _ _ _ reached)
  projections := callbacks.projections
  casts := callbacks.casts
  equalities := callbacks.equalities

theorem TypeChecker.Inner.inferType'.headerAxiomMethodTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams) (state : TypeChecker.State)
    (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeInferMethodCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferType' expression inferOnly actualMethods)
      (inferType' expression inferOnly shadowMethods) actualContext shadowContext state :=
  inferType'.headerAxiomTransport _ _ _ _ agreement locals safety parameters _ _ _ (callbacks.toCallbacks locals)

end Lean4Lean
