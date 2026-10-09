import Lean4Lean.Verify.InductiveNormalizedWrappers

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private singletonRange emptyRevRange telescopeCore telescopeNative telescopeNat telescopeDelta
  from Lean4Lean.Verify.InductiveNormalizedWrappers

inductive WrappedSortTelescope : Expr → Expr → Prop where
  | telescope {type : Expr} (htype : SortTelescope type) : WrappedSortTelescope type type
  | mdata (data : MData) {source normalized : Expr}
      (tail : WrappedSortTelescope source normalized) :
      WrappedSortTelescope (.mdata data source) normalized
  | letE (name : Name) (domain value body : Expr) (nondep : Bool) {normalized : Expr}
      (tail : WrappedSortTelescope (body.instantiate1 value) normalized) :
      WrappedSortTelescope (.letE name domain value body nondep) normalized
  | beta (name : Name) (domain value body : Expr) (bi : BinderInfo) {normalized : Expr}
      (tail : WrappedSortTelescope (body.instantiate1 value) normalized) :
      WrappedSortTelescope (.app (.lam name domain body bi) value) normalized

theorem WrappedSortTelescope.shape {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) : SortTelescope normalized := by
  induction trace with
  | telescope htype => exact htype
  | mdata _ _ ih | letE _ _ _ _ _ _ ih | beta _ _ _ _ _ _ ih => exact ih

private theorem savedCoreWF {source normalized : Expr}
    {action : Except Kernel.Exception (Expr × TypeChecker.State)}
    (haction : action.WF fun output => output.1 = normalized) :
    Except.WF (action >>= fun returned => Except.ok (returned.1,
      { returned.2 with whnfCoreCache := returned.2.whnfCoreCache.insert source returned.1 }))
      (fun returned => returned.1 = normalized) := by
  exact Except.WF.bind haction fun returned hreturned => Except.WF.pure hreturned

private theorem singletonBetaLoop (name : Name) (domain body value : Expr) (bi : BinderInfo) :
    TypeChecker.Inner.whnfCore'.loop (.app (.lam name domain body bi) value) false false
      #[value] 1 body =
    TypeChecker.Inner.whnfCore'.loop.cont (.app (.lam name domain body bi) value) false false
      #[value] 1 body := by
  cases body <;> rw [TypeChecker.Inner.whnfCore'.loop.eq_def]
  all_goals rfl

private theorem lambdaCoreStep (name : Name) (domain body : Expr) (bi : BinderInfo)
    (depth : Nat) (ctx : TypeChecker.Context) (state : TypeChecker.State) :
    (TypeChecker.Methods.withFuel (depth + 1)).whnfCore (.lam name domain body bi)
      false false ctx state = .ok (.lam name domain body bi, state) := rfl

private theorem betaCoreStep (name : Name) (domain body value : Expr) (bi : BinderInfo)
    (depth : Nat) (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (hcache : state.whnfCoreCache = ∅) :
    TypeChecker.Inner.whnfCore' (.app (.lam name domain body bi) value) false false
      (TypeChecker.Methods.withFuel (depth + 1)) ctx state =
      ((TypeChecker.Methods.withFuel (depth + 1)).whnfCore
        (body.instantiate1 value) false false ctx state).bind fun result =>
          .ok (result.1, { result.2 with
            whnfCoreCache := result.2.whnfCoreCache.insert
              (.app (.lam name domain body bi) value) result.1 }) := by
  rw [TypeChecker.Inner.whnfCore'.eq_def]
  simp only [get, getThe, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, Except.pure, Except.bind,
    hcache, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [Expr.getAppFn, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList, List.toArray]
  simp only [TypeChecker.Inner.whnfCore, bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [lambdaCoreStep]
  change TypeChecker.Inner.whnfCore'.loop (.app (.lam name domain body bi) value)
    false false #[value] 1 body (TypeChecker.Methods.withFuel (depth + 1)) ctx state = _
  rw [singletonBetaLoop, TypeChecker.Inner.whnfCore'.loop.cont]
  simp only [List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.sub_self, emptyRevRange, singletonRange]
  simp only [TypeChecker.Inner.whnfCore, TypeChecker.Inner.whnfCore'.save,
    bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure,
    monadLift, MonadLift.monadLift, Except.pure, Except.bind,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Bool.not_false, Bool.true_and, ite_true]

private theorem betaCoreZero (name : Name) (domain body value : Expr) (bi : BinderInfo)
    (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (hcache : state.whnfCoreCache = ∅) :
    TypeChecker.Inner.whnfCore' (.app (.lam name domain body bi) value) false false
      (TypeChecker.Methods.withFuel 0) ctx state = .error .deepRecursion := by
  rw [TypeChecker.Inner.whnfCore'.eq_def]
  simp only [get, getThe, bind, ReaderT.bind, StateT.bind, pure,
    ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, Except.pure, Except.bind,
    hcache, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  rfl

theorem WrappedSortTelescope.core {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (depth : Nat)
    (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (hempty : state.whnfCoreCache = ∅) :
    ((TypeChecker.Methods.withFuel depth).whnfCore source false false ctx state).WF
      fun returned => returned.1 = normalized := by
  induction trace generalizing depth ctx state with
  | telescope htype =>
    cases depth with
    | zero => exact Except.WF.throw
    | succ depth =>
      rw [telescopeCore _ htype depth ctx state false false]
      exact Except.WF.pure rfl
  | mdata data tail ih =>
    cases depth with
    | zero => exact Except.WF.throw
    | succ depth =>
      change (TypeChecker.Inner.whnfCore' (.mdata data _) false false
        (TypeChecker.Methods.withFuel depth) ctx state).WF _
      rw [TypeChecker.Inner.whnfCore'.eq_def]
      simp only [bind_pure]
      exact ih (depth + 1) ctx state hempty
  | letE name domain value body nondep tail ih =>
    cases depth with
    | zero => exact Except.WF.throw
    | succ depth =>
      change (TypeChecker.Inner.whnfCore' (.letE name domain value body nondep) false false
        (TypeChecker.Methods.withFuel depth) ctx state).WF _
      rw [TypeChecker.Inner.whnfCore'.eq_def]
      simp only [pure_bind]
      simp only [TypeChecker.Inner.whnfCore, TypeChecker.Inner.whnfCore'.save,
        get, getThe, bind, ReaderT.bind, StateT.bind, pure,
        ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
        liftM, monadLift, MonadLift.monadLift,
        Except.pure, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, hempty, Std.HashMap.getElem?_empty,
        Bool.not_false, Bool.true_and, ite_true]
      exact savedCoreWF (source := .letE name domain value body nondep) (ih depth ctx state hempty)
  | beta name domain value body bi tail ih =>
    cases depth with
    | zero => exact Except.WF.throw
    | succ depth =>
      change (TypeChecker.Inner.whnfCore' (.app (.lam name domain body bi) value) false false
        (TypeChecker.Methods.withFuel depth) ctx state).WF _
      cases depth with
      | zero =>
        rw [betaCoreZero name domain body value bi ctx state hempty]
        exact Except.WF.throw
      | succ depth =>
        rw [betaCoreStep name domain body value bi depth ctx state hempty]
        exact savedCoreWF (source := .app (.lam name domain body bi) value)
          (ih (depth + 1) ctx state hempty)

private inductive CoreWrapper : Expr → Prop where
  | app (function argument : Expr) : CoreWrapper (.app function argument)
  | letE (name : Name) (domain value body : Expr) (nondep : Bool) :
      CoreWrapper (.letE name domain value body nondep)

private theorem coreWrapperNormalized {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) (hsource : CoreWrapper source) :
    NormalizedSortTelescope source normalized := by
  cases hsource
  all_goals
    refine ⟨trace.shape, ?_⟩
    intro ctx result hresult
    let tc : TypeChecker.Context :=
      { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
        lparams := ctx.lparams, fuel := ctx.fuel }
    change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf _ tc {}) =
      .ok result at hresult
    cases hdepth : ctx.fuel.recDepth with
    | zero =>
      rw [hdepth] at hresult
      change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
      cases hresult
    | succ depth =>
      rw [hdepth] at hresult
      change (Prod.fst <$> TypeChecker.Inner.whnf' _ (TypeChecker.Methods.withFuel depth) tc {}) =
        .ok result at hresult
      rw [TypeChecker.Inner.whnf'.eq_def] at hresult
      simp only [pure_bind] at hresult
      simp only [get, getThe, readThe, bind, ReaderT.bind, StateT.bind, pure,
        ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
        MonadReaderOf.read, read, liftM, monadLift, MonadLift.monadLift,
        Except.pure, Except.bind, ReaderT.read, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, Std.HashMap.getElem?_empty,
        tc, Bool.false_eq_true, ite_false] at hresult
      cases hfuel : ctx.fuel.whnf with
      | zero =>
        rw [hfuel, TypeChecker.Inner.whnf'.loop] at hresult
        cases hresult
      | succ fuel =>
        rw [hfuel, TypeChecker.Inner.whnf'.loop] at hresult
        simp only [TypeChecker.getEnv, readThe, bind, ReaderT.bind, StateT.bind, pure,
          ReaderT.pure, StateT.pure,
          MonadReaderOf.read, read, liftM, monadLift, MonadLift.monadLift,
          Except.pure, Except.bind, ReaderT.read] at hresult
        have hcore := trace.core (depth + 1) tc {} rfl
        change (TypeChecker.Inner.whnfCore' _ false false (TypeChecker.Methods.withFuel depth) tc {}).WF _ at hcore
        generalize haction :
          TypeChecker.Inner.whnfCore' _ false false (TypeChecker.Methods.withFuel depth) tc {} = action
          at hcore hresult
        cases action with
        | error error =>
          change Except.error error = .ok result at hresult
          cases hresult
        | ok output =>
          have heq := hcore output rfl
          obtain ⟨output, state⟩ := output
          dsimp only [] at heq
          subst output
          simp only [telescopeNative trace.shape] at hresult
          simp only [StateT.lift, bind, ReaderT.bind, StateT.bind, pure,
            ReaderT.pure, StateT.pure, Except.pure, Except.bind,
            telescopeNat trace.shape, telescopeDelta trace.shape] at hresult
          change Except.ok normalized = .ok result at hresult
          exact (Except.ok.inj hresult).symm

theorem WrappedSortTelescope.normalized {source normalized : Expr}
    (trace : WrappedSortTelescope source normalized) : NormalizedSortTelescope source normalized := by
  induction trace with
  | telescope htype => exact htype.normalized
  | mdata data tail ih => exact ih.mdata data
  | letE name domain value body nondep tail ih =>
    exact coreWrapperNormalized (.letE name domain value body nondep tail)
      (.letE name domain value body nondep)
  | beta name domain value body bi tail ih =>
    exact coreWrapperNormalized (.beta name domain value body bi tail)
      (.app (.lam name domain body bi) value)

end Lean4Lean.AddInductive
