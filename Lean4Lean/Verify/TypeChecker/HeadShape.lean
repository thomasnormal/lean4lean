import Lean4Lean.Verify.InductiveHeaderWHNFTransport

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

def NativeHeadClean (expression : Expr) : Prop :=
  expression.isMData = false ∧ expression.isLet = false

def TypeChecker.HeadCacheWF (state : TypeChecker.State) : Prop :=
  (∀ key value : Expr, state.whnfCoreCache[key]? = some value → NativeHeadClean value) ∧
  (∀ key value : Expr, state.whnfCache[key]? = some value → NativeHeadClean value)

theorem TypeChecker.HeadCacheWF.empty : HeadCacheWF {} := by
  constructor <;> intro key value found <;> simp at found

theorem TypeChecker.HeadCacheWF.insertCore {state : TypeChecker.State}
    (valid : HeadCacheWF state) (key value : Expr) (clean : NativeHeadClean value) :
    HeadCacheWF { state with whnfCoreCache := state.whnfCoreCache.insert key value } := by
  refine ⟨?_, valid.2⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact clean
  · exact valid.1 query result found

theorem TypeChecker.HeadCacheWF.insertFull {state : TypeChecker.State}
    (valid : HeadCacheWF state) (key value : Expr) (clean : NativeHeadClean value) :
    HeadCacheWF { state with whnfCache := state.whnfCache.insert key value } := by
  refine ⟨valid.1, ?_⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact clean
  · exact valid.2 query result found

def TypeChecker.M.HeadWF (action : TypeChecker.M Result) (post : Result → Prop) : Prop :=
  ∀ context state, TypeChecker.HeadCacheWF state →
    ∀ result finalState, action context state = .ok (result, finalState) →
      TypeChecker.HeadCacheWF finalState ∧ post result

namespace TypeChecker.M.HeadWF

theorem pure {value : Result} {post : Result → Prop} (valid : post value) :
    M.HeadWF (pure value) post := by
  rintro context state caches result finalState accepted
  cases accepted
  exact ⟨caches, valid⟩

theorem bind {action : M Result} {next : Result → M Output}
    {post : Result → Prop} {finalPost : Output → Prop}
    (initial : action.HeadWF post) (continuation : ∀ result, post result → (next result).HeadWF finalPost) :
    (action >>= next).HeadWF finalPost := by
  intro context state caches result finalState accepted
  change (action context state >>= fun intermediate => next intermediate.1 context intermediate.2) =
    .ok (result, finalState) at accepted
  cases evaluated : action context state with
  | error exception => simp [evaluated, Bind.bind, Except.bind] at accepted
  | ok intermediate =>
    have valid := initial context state caches intermediate.1 intermediate.2 evaluated
    exact continuation intermediate.1 valid.2 context intermediate.2 valid.1 result finalState
      (by simpa [evaluated, Bind.bind, Except.bind] using accepted)

theorem mono {action : M Result} {post finalPost : Result → Prop}
    (valid : action.HeadWF post) (implication : ∀ result, post result → finalPost result) :
    action.HeadWF finalPost := by
  intro context state caches result finalState accepted
  have conclusion := valid context state caches result finalState accepted
  exact ⟨conclusion.1, implication result conclusion.2⟩

theorem get {next : State → M Result} {post : Result → Prop}
    (continuation : ∀ state, HeadCacheWF state → (next state).HeadWF post) :
    (do let state ← get; next state : M Result).HeadWF post := by
  intro context state caches result finalState accepted
  exact continuation state caches context state caches result finalState accepted

theorem read {next : Context → M Result} {post : Result → Prop}
    (continuation : ∀ context, (next context).HeadWF post) :
    (do let context ← readThe Context; next context : M Result).HeadWF post := by
  intro context state caches result finalState accepted
  exact continuation context context state caches result finalState accepted

theorem getLCtx {next : LocalContext → M Result} {post : Result → Prop}
    (continuation : ∀ context, (next context).HeadWF post) :
    (do let context ← getLCtx; next context : M Result).HeadWF post := by
  intro context state caches result finalState accepted
  exact continuation context.lctx context state caches result finalState accepted

theorem getEnv {next : Environment → M Result} {post : Result → Prop}
    (continuation : ∀ environment, (next environment).HeadWF post) :
    (do let environment ← getEnv; next environment : M Result).HeadWF post := by
  intro context state caches result finalState accepted
  exact continuation context.env context state caches result finalState accepted

theorem modify (update : State → State) (preserves : ∀ state, HeadCacheWF state → HeadCacheWF (update state)) :
    M.HeadWF (modify update) (fun _ => True) := by
  rintro context state caches result finalState accepted
  cases accepted
  exact ⟨preserves state caches, trivial⟩

theorem throw (exception : Exception) (post : Result → Prop) :
    M.HeadWF (throw exception) post := by
  intro context state caches result finalState accepted
  cases accepted

theorem liftExcept (action : Except Exception Result) :
    M.HeadWF (liftM action) (fun _ => True) := by
  intro context state caches result finalState accepted
  cases action <;> cases accepted
  exact ⟨caches, trivial⟩

end TypeChecker.M.HeadWF

structure TypeChecker.Methods.HeadWF (methods : TypeChecker.Methods) : Prop where
  whnfCore : ∀ expression cheapProj,
    (methods.whnfCore expression cheapProj).HeadWF NativeHeadClean
  whnf : ∀ expression, (methods.whnf expression).HeadWF NativeHeadClean
  inferType : ∀ expression inferOnly, (methods.inferType expression inferOnly).HeadWF (fun _ => True)
  isDefEqCore : ∀ first second, (methods.isDefEqCore first second).HeadWF (fun _ => True)

theorem TypeChecker.Inner.whnfCore'.save_headWF (expression normalized : Expr)
    (cheapProj : Bool) (methods : TypeChecker.Methods) (clean : NativeHeadClean normalized) :
    (whnfCore'.save expression cheapProj normalized methods).HeadWF NativeHeadClean := by
  cases cheapProj
  · exact (TypeChecker.M.HeadWF.modify _ fun state valid => valid.insertCore expression normalized clean).bind
      fun _ _ => .pure clean
  all_goals exact TypeChecker.M.HeadWF.pure clean

theorem TypeChecker.Inner.whnfFVar.headWF (name : FVarId) (cheapProj : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (whnfFVar (.fvar name) cheapProj methods).HeadWF NativeHeadClean := by
  unfold whnfFVar
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getLCtx
  intro localContext
  cases localContext.find? (Expr.fvar name).fvarId! with
  | none => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | some declaration =>
    cases declaration
    · exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
    · dsimp only [ReaderT.bind, whnfCore]
      exact valid.whnfCore _ cheapProj

theorem TypeChecker.Inner.reduceProj.headWF (index : Nat) (source : Expr) (cheapProj : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reduceProj index source cheapProj methods).HeadWF (fun _ => True) := by
  unfold reduceProj reduceProjCore
  dsimp only [Bind.bind, ReaderT.bind]
  have initial : (if cheapProj then whnfCore source cheapProj else whnf source) methods
      |>.HeadWF NativeHeadClean := by
    cases cheapProj
    · exact valid.whnf _
    · exact valid.whnfCore _ _
  refine initial.bind fun normalized _ => ?_
  have finish : ∀ expression : Expr,
      (expression.withApp fun head arguments => do
        let .const name _ := head | return none
        let environment ← getEnv
        let .ctorInfo info ← environment.get name | return none
        return arguments[info.numParams + index]? : RecM (Option Expr)) methods
        |>.HeadWF (fun _ => True) := by
    intro expression
    rw [Expr.withApp_eq]
    cases expression.getAppFn <;> dsimp only [Bind.bind, ReaderT.bind]
    any_goals exact TypeChecker.M.HeadWF.pure trivial
    apply TypeChecker.M.HeadWF.getEnv
    intro environment
    refine (TypeChecker.M.HeadWF.liftExcept _).bind fun info _ => ?_
    cases info <;> exact TypeChecker.M.HeadWF.pure trivial
  cases h : normalized <;> try exact finish _
  case lit literal =>
    cases literal with
    | natVal value => exact TypeChecker.M.HeadWF.pure trivial
    | strVal text =>
      dsimp only [reduceProjCore, Bind.bind, ReaderT.bind, whnf]
      apply TypeChecker.M.HeadWF.bind (valid.whnf (.strLitToConstructor text))
      intro expanded _
      exact finish expanded

theorem TypeChecker.Inner.whnfCore'.headWF (expression : Expr) (cheapProj : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (recursorFrame : ∀ expression,
      (reduceRecursor expression methods).HeadWF (fun _ => True)) :
    (whnfCore' expression cheapProj methods).HeadWF NativeHeadClean := by
  induction expression with
  | mdata data expression inductionHypothesis =>
    simpa only [whnfCore', bind_pure] using inductionHypothesis
  | fvar name =>
    intro context state caches result finalState accepted
    rw [whnfCore'.fvar_eq] at accepted
    split at accepted
    · cases accepted
      exact ⟨caches, rfl, rfl⟩
    · cases cached : state.whnfCoreCache[Expr.fvar name]? with
      | some value =>
        simp only [cached] at accepted
        cases accepted
        exact ⟨caches, caches.1 _ _ cached⟩
      | none =>
        simp only [cached, bind_pure] at accepted
        exact whnfFVar.headWF name cheapProj methods valid context state caches result finalState accepted
  | letE name domain value body nondependent =>
    intro context state caches result finalState accepted
    rw [whnfCore'.let_eq] at accepted
    cases cached : state.whnfCoreCache[Expr.letE name domain value body nondependent]? with
    | some normalized =>
      simp only [cached] at accepted
      cases accepted
      exact ⟨caches, caches.1 _ _ cached⟩
    | none =>
      simp only [cached] at accepted
      have worker : ((do
          let normalized ← whnfCore (body.instantiate1 value) cheapProj
          whnfCore'.save (.letE name domain value body nondependent) cheapProj normalized)
          methods).HeadWF NativeHeadClean := by
        dsimp only [Bind.bind, ReaderT.bind, whnfCore]
        exact (valid.whnfCore _ _).bind
          fun normalized clean => whnfCore'.save_headWF _ normalized cheapProj methods clean
      exact worker context state caches result finalState accepted
  | proj parent index source =>
    intro context state caches result finalState accepted
    rw [whnfCore'.proj_eq] at accepted
    cases cached : state.whnfCoreCache[Expr.proj parent index source]? with
    | some normalized =>
      simp only [cached] at accepted
      cases accepted
      exact ⟨caches, caches.1 _ _ cached⟩
    | none =>
      simp only [cached] at accepted
      have worker : ((do
          if let some reduced ← reduceProj index source cheapProj then
            let normalized ← whnfCore reduced cheapProj
            whnfCore'.save (.proj parent index source) cheapProj normalized
          else whnfCore'.save (.proj parent index source) cheapProj (.proj parent index source))
          methods).HeadWF NativeHeadClean := by
        dsimp only [Bind.bind, ReaderT.bind]
        refine (reduceProj.headWF index source cheapProj methods valid).bind fun reduced _ => ?_
        cases reduced with
        | none => exact whnfCore'.save_headWF _ _ cheapProj methods ⟨rfl, rfl⟩
        | some expression =>
          dsimp only [Bind.bind, ReaderT.bind, whnfCore]
          exact (valid.whnfCore expression cheapProj).bind
            fun normalized clean => whnfCore'.save_headWF _ normalized cheapProj methods clean
      exact worker context state caches result finalState accepted
  | app function argument =>
    let expression := Expr.app function argument
    intro context state caches result finalState accepted
    rw [whnfCore'.app_eq _ _ _ _ _ rfl] at accepted
    cases cached : state.whnfCoreCache[expression]? with
    | some normalized =>
      simp only [expression, cached] at accepted
      cases accepted
      exact ⟨caches, caches.1 _ _ cached⟩
    | none =>
      change state.whnfCoreCache[Expr.app function argument]? = none at cached
      rw [cached] at accepted
      have worker : ((do
          let normalized ← whnfCore expression.getAppFn cheapProj
          match normalized with
          | .lam _ _ body _ => whnfCore'.loop expression cheapProj expression.getAppRevArgs 1 body
          | _ =>
            if normalized == expression.getAppFn then
              if let some reduced ← reduceRecursor expression then
                whnfCore reduced cheapProj
              else pure expression
            else do
              let result ← whnfCore (normalized.mkAppRevRange 0 expression.getAppRevArgs.size
                expression.getAppRevArgs) cheapProj
              whnfCore'.save expression cheapProj result) methods).HeadWF NativeHeadClean := by
        dsimp only [Bind.bind, ReaderT.bind, whnfCore]
        refine (valid.whnfCore expression.getAppFn cheapProj).bind fun normalized _ => ?_
        cases normalized <;> dsimp only [Bind.bind, ReaderT.bind]
        any_goals (
          split
          · dsimp only [Bind.bind, ReaderT.bind]
            refine (recursorFrame expression).bind fun reduced _ => ?_
            cases reduced
            · exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
            · exact valid.whnfCore _ _
          · dsimp only [Bind.bind, ReaderT.bind, whnfCore]
            exact (valid.whnfCore _ _).bind
              fun result clean => whnfCore'.save_headWF expression result cheapProj methods clean)
        rw [whnfCore'.loop_eq]
        dsimp only [Bind.bind, ReaderT.bind, whnfCore]
        exact (valid.whnfCore _ _).bind
          fun result clean => whnfCore'.save_headWF expression result cheapProj methods clean
      exact worker context state caches result finalState accepted
  | _ => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩

def NativeOptionalHeadClean : Option Expr → Prop
  | none => True
  | some expression => NativeHeadClean expression

theorem TypeChecker.Inner.reduceBinNatOp.headWF (operation : Nat → Nat → Nat) (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reduceBinNatOp operation first second methods).HeadWF NativeOptionalHeadClean := by
  unfold reduceBinNatOp
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf first).bind fun normalized _ => ?_
  cases rawNatLitExt? normalized
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, whnf]
    refine (valid.whnf second).bind fun normalized _ => ?_
    cases rawNatLitExt? normalized
    · exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩

theorem TypeChecker.Inner.reducePow.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reducePow first second methods).HeadWF NativeOptionalHeadClean := by
  unfold reducePow
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf first).bind fun normalized _ => ?_
  cases rawNatLitExt? normalized
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, whnf]
    refine (valid.whnf second).bind fun normalized _ => ?_
    cases rawNatLitExt? normalized
    · exact TypeChecker.M.HeadWF.pure trivial
    · dsimp only
      split
      · exact TypeChecker.M.HeadWF.pure trivial
      · exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩

theorem TypeChecker.Inner.reduceBinNatPred.headWF (operation : Nat → Nat → Bool) (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reduceBinNatPred operation first second methods).HeadWF NativeOptionalHeadClean := by
  unfold reduceBinNatPred
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf first).bind fun normalized _ => ?_
  cases rawNatLitExt? normalized
  · exact TypeChecker.M.HeadWF.pure trivial
  · rename_i firstValue
    dsimp only [Bind.bind, ReaderT.bind, whnf]
    refine (valid.whnf second).bind fun normalized _ => ?_
    cases rawNatLitExt? normalized
    · exact TypeChecker.M.HeadWF.pure trivial
    · rename_i secondValue
      cases outcome : operation firstValue secondValue <;> simp only [outcome]
      all_goals exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩

theorem TypeChecker.Inner.reduceNat.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reduceNat expression methods).HeadWF NativeOptionalHeadClean := by
  unfold reduceNat
  simp only [pure_bind, bind_pure]
  by_cases unary : (expression.getAppNumArgs == 1) = true
  · rw [if_pos unary]
    split
    · dsimp only [Bind.bind, ReaderT.bind, whnf]
      refine (valid.whnf expression.appArg!).bind fun normalized _ => ?_
      cases rawNatLitExt? normalized
      · exact TypeChecker.M.HeadWF.pure trivial
      · exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
    · exact TypeChecker.M.HeadWF.pure trivial
  · rw [if_neg unary]
    by_cases binary : (expression.getAppNumArgs == 2) = true
    · rw [if_pos binary]
      cases expression <;> try exact TypeChecker.M.HeadWF.pure trivial
      rename_i function argument
      cases function <;> try exact TypeChecker.M.HeadWF.pure trivial
      rename_i head first
      cases head <;> try exact TypeChecker.M.HeadWF.pure trivial
      dsimp only [ReaderT.bind, ReaderT.pure]
      rename_i name levels
      by_cases selected : (name == ``Nat.add) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.add first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.sub) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.sub first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.mul) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.mul first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.pow) = true
      · rw [if_pos selected]
        exact reducePow.headWF first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.gcd) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.gcd first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.mod) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.mod first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.div) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.div first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.beq) = true
      · rw [if_pos selected]
        exact reduceBinNatPred.headWF Nat.beq first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.ble) = true
      · rw [if_pos selected]
        exact reduceBinNatPred.headWF Nat.ble first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.land) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.land first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.lor) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.lor first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.xor) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.xor first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.shiftLeft) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.shiftLeft first argument methods valid
      rw [if_neg selected]
      by_cases selected : (name == ``Nat.shiftRight) = true
      · rw [if_pos selected]
        exact reduceBinNatOp.headWF Nat.shiftRight first argument methods valid
      rw [if_neg selected]
      exact TypeChecker.M.HeadWF.pure trivial
    · rw [if_neg binary]
      exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.reduceNative.noReduction (environment : Environment) (expression : Expr)
    (result : Option Expr) (accepted : reduceNative environment expression = .ok result) : result = none := by
  unfold reduceNative at accepted
  simp only [pure_bind] at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · cases accepted
        rfl
  · cases accepted
    rfl

theorem TypeChecker.Inner.unfoldDefinitionCore.headWF (expression : Expr) (methods : TypeChecker.Methods) :
    (unfoldDefinitionCore expression methods).HeadWF (fun _ => True) := by
  unfold unfoldDefinitionCore
  simp only [pure_bind]
  cases expression <;> try exact TypeChecker.M.HeadWF.pure trivial
  rename_i name levels
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  cases isDelta environment (Expr.const name levels) with
  | none => exact TypeChecker.M.HeadWF.pure trivial
  | some definition =>
    dsimp only
    split
    · dsimp only [Bind.bind, ReaderT.bind, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        liftM, MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.bind]
      apply TypeChecker.M.HeadWF.get
      intro state caches
      cases state.unfold[Expr.const name levels]? with
      | some value => exact TypeChecker.M.HeadWF.pure trivial
      | none =>
        dsimp only [Bind.bind, ReaderT.bind]
        exact (TypeChecker.M.HeadWF.modify (fun state : State =>
          { state with unfold := state.unfold.insert (.const name levels) (instantiateDeltaValue definition levels) })
            fun _ valid => valid).bind
              (finalPost := fun _ => True) fun _ _ => .pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.unfoldDefinition.headWF (expression : Expr) (methods : TypeChecker.Methods) :
    (unfoldDefinition expression methods).HeadWF (fun _ => True) := by
  unfold unfoldDefinition
  split
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (unfoldDefinitionCore.headWF _ methods).bind fun unfolded _ => ?_
    cases unfolded <;> exact TypeChecker.M.HeadWF.pure trivial
  · exact unfoldDefinitionCore.headWF _ methods

theorem TypeChecker.Inner.whnf'.loop_headWF (expression : Expr) (fuel : Nat)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (recursorFrame : ∀ expression,
      (reduceRecursor expression methods).HeadWF (fun _ => True)) :
    (whnf'.loop expression fuel methods).HeadWF NativeHeadClean := by
  induction fuel generalizing expression with
  | zero => exact TypeChecker.M.HeadWF.throw .deterministicTimeout _
  | succ fuel inductionHypothesis =>
    unfold whnf'.loop
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.HeadWF.getEnv
    intro environment
    refine (whnfCore'.headWF expression false methods valid recursorFrame).bind fun normalized clean => ?_
    intro context state caches result finalState accepted
    cases native : reduceNative environment normalized with
    | error exception =>
      simp only [native, Bind.bind, ReaderT.bind, StateT.bind, Except.bind, liftM,
        MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift] at accepted
      cases accepted
    | ok reduced =>
      have noReduction := reduceNative.noReduction environment normalized reduced native
      subst reduced
      simp only [native] at accepted
      have worker : ((do
          if let some reduced ← reduceNat normalized then return reduced
          let some unfolded ← unfoldDefinition normalized | return normalized
          whnf'.loop unfolded fuel) methods).HeadWF NativeHeadClean := by
        dsimp only [Bind.bind, ReaderT.bind]
        refine (reduceNat.headWF normalized methods valid).bind fun reduced cleanReduction => ?_
        cases reduced with
        | some expression => exact TypeChecker.M.HeadWF.pure cleanReduction
        | none =>
          dsimp only [Bind.bind, ReaderT.bind]
          refine (unfoldDefinition.headWF normalized methods).bind fun unfolded _ => ?_
          cases unfolded
          · exact TypeChecker.M.HeadWF.pure clean
          · exact inductionHypothesis _
      exact worker context state caches result finalState accepted

theorem TypeChecker.Inner.whnfCacheProgram.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (recursorFrame : ∀ expression,
      (reduceRecursor expression methods).HeadWF (fun _ => True)) :
    (whnfCacheProgram expression methods).HeadWF NativeHeadClean := by
  unfold whnfCacheProgram
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.get
  intro state caches
  cases found : state.whnfCache[expression]? with
  | some cached => exact TypeChecker.M.HeadWF.pure (caches.2 _ _ found)
  | none =>
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.HeadWF.read
    intro context
    refine (whnf'.loop_headWF expression context.whnfBudget methods valid recursorFrame).bind
      fun normalized clean => ?_
    exact (TypeChecker.M.HeadWF.modify _ fun state valid => valid.insertFull expression normalized clean).bind
      fun _ _ => .pure clean

theorem TypeChecker.Inner.whnf'.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (recursorFrame : ∀ expression,
      (reduceRecursor expression methods).HeadWF (fun _ => True)) :
    (whnf' expression methods).HeadWF NativeHeadClean := by
  induction expression with
  | mdata data expression inductionHypothesis =>
    simpa only [whnf', bind_pure] using inductionHypothesis
  | fvar name =>
    intro context state caches result finalState accepted
    cases localLet : isLetFVar context.lctx name with
    | false =>
      have easy : whnf' (.fvar name) methods context state = .ok (.fvar name, state) := by
        simp only [whnf']
        dsimp only [getLCtx, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
          MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
          ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, Except.pure, Except.bind]
        simp only [localLet, Bool.not_false, if_true]
        rfl
      rw [easy] at accepted
      cases accepted
      exact ⟨caches, rfl, rfl⟩
    | true =>
      rw [whnf'.cache_eq methods context state (.fvar name) rfl localLet] at accepted
      exact whnfCacheProgram.headWF _ methods valid recursorFrame context state caches result finalState accepted
  | bvar index => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | mvar name => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | sort level => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | forallE name domain body binder => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | lit literal => exact TypeChecker.M.HeadWF.pure ⟨rfl, rfl⟩
  | _ =>
    intro context state caches result finalState accepted
    rw [whnf'.cache_eq methods context state _ rfl rfl] at accepted
    exact whnfCacheProgram.headWF _ methods valid recursorFrame context state caches result finalState accepted

end Lean4Lean
