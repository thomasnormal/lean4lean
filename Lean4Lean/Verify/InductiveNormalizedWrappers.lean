import Lean4Lean.Verify.InductiveNormalizedHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem SortTelescope.normalized {type : Expr} (htype : SortTelescope type) :
    NormalizedSortTelescope type type := ⟨htype, htype.whnf⟩

theorem NormalizedSortTelescope.mdata {source normalized : Expr}
    (hsource : NormalizedSortTelescope source normalized) (data : MData) :
    NormalizedSortTelescope (.mdata data source) normalized := by
  refine ⟨hsource.1, ?_⟩
  intro ctx result hresult
  apply hsource.2 ctx result
  change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf
    (.mdata data source)
    { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
      lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
  change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf
    source
    { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
      lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result
  cases hdepth : ctx.fuel.recDepth with
  | zero => simpa [TypeChecker.Methods.withFuel, hdepth] using hresult
  | succ depth =>
    rw [hdepth] at hresult
    change (Prod.fst <$> TypeChecker.Inner.whnf' (.mdata data source)
      (TypeChecker.Methods.withFuel depth)
      { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
        lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
    rw [TypeChecker.Inner.whnf'.eq_def] at hresult
    simpa only [bind_pure] using hresult

private theorem singletonRange (body value : Expr) :
    body.instantiateRange 0 1 #[value] = body.instantiate1 value := by
  simp only [Expr.instantiateRange_eq, Expr.instantiate_eq, Expr.instantiate1_eq]
  rfl

open private mkAppRevRangeAux from Lean.Expr in
private theorem emptyRevRange (source : Expr) (args : Array Expr) :
    source.mkAppRevRange 0 0 args = source := by
  rw [Expr.mkAppRevRange, mkAppRevRangeAux.eq_def]
  simp only [Nat.le_refl, ↓reduceIte]

private theorem telescopeCore (normalized : Expr) (hshape : SortTelescope normalized)
    (depth : Nat) (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (cheapRec cheapProj : Bool) :
    (TypeChecker.Methods.withFuel (depth + 1)).whnfCore normalized cheapRec cheapProj ctx state =
      .ok (normalized, state) := by
  cases hshape <;> rfl

private theorem lambdaCore (name : Name) (domain body : Expr) (bi : BinderInfo)
    (depth : Nat) (ctx : TypeChecker.Context) (state : TypeChecker.State)
    (cheapRec cheapProj : Bool) :
    (TypeChecker.Methods.withFuel (depth + 1)).whnfCore (.lam name domain body bi)
      cheapRec cheapProj ctx state = .ok (.lam name domain body bi, state) := rfl

private theorem telescopeNative {normalized : Expr} (hshape : SortTelescope normalized)
    (env : Kernel.Environment) :
    TypeChecker.Inner.reduceNative env normalized = .ok none := by
  cases hshape <;> rfl

private theorem telescopeNat {normalized : Expr} (hshape : SortTelescope normalized)
    (methods : TypeChecker.Methods) (ctx : TypeChecker.Context) (state : TypeChecker.State) :
    TypeChecker.Inner.reduceNat normalized methods ctx state = .ok (none, state) := by
  cases hshape <;> rfl

private theorem telescopeDelta {normalized : Expr} (hshape : SortTelescope normalized)
    (methods : TypeChecker.Methods) (ctx : TypeChecker.Context) (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinition normalized methods ctx state = .ok (none, state) := by
  cases hshape <;> rfl

theorem SortTelescope.normalizedLet (name : Name) (domain value body : Expr) (nondep : Bool)
    (hnormalized : SortTelescope (body.instantiate1 value)) :
    NormalizedSortTelescope (.letE name domain value body nondep) (body.instantiate1 value) := by
  have hshape : SortTelescope (body.instantiate1' value) := by
    simpa only [Expr.instantiate1_eq] using hnormalized
  refine ⟨hnormalized, ?_⟩
  intro ctx result hresult
  change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf
    (.letE name domain value body nondep)
    { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
      lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
  cases hdepth : ctx.fuel.recDepth with
  | zero =>
    rw [hdepth] at hresult
    change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
    cases hresult
  | succ depth =>
    rw [hdepth] at hresult
    change (Prod.fst <$> TypeChecker.Inner.whnf' (.letE name domain value body nondep)
      (TypeChecker.Methods.withFuel depth) _ {}) = .ok result at hresult
    rw [TypeChecker.Inner.whnf'.eq_def] at hresult
    simp only [pure_bind] at hresult
    simp only [get, getThe, readThe, bind, ReaderT.bind, StateT.bind, pure,
      ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
      MonadReaderOf.read, read, liftM, monadLift, MonadLift.monadLift,
      Except.pure, Except.bind, ReaderT.read, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, Std.HashMap.getElem?_empty,
      Bool.false_eq_true, ite_false] at hresult
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
      rw [TypeChecker.Inner.whnfCore'.eq_def] at hresult
      simp only [TypeChecker.Inner.whnfCore, TypeChecker.Inner.whnfCore'.save,
        get, getThe, bind, ReaderT.bind, StateT.bind, pure,
        ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
        liftM, monadLift, MonadLift.monadLift,
        Except.pure, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, Std.HashMap.getElem?_empty,
        Expr.instantiate1_eq, Bool.not_false, Bool.true_and, ite_true] at hresult
      cases depth with
      | zero =>
        simp only [TypeChecker.Methods.withFuel] at hresult
        change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
        cases hresult
      | succ depth =>
        rw [telescopeCore _ hshape depth _ _ false false] at hresult
        simp only [telescopeNative hshape] at hresult
        simp only [StateT.lift, bind, ReaderT.bind, StateT.bind, pure,
          ReaderT.pure, StateT.pure, Except.pure, Except.bind,
          telescopeNat hshape, telescopeDelta hshape] at hresult
        change Except.ok (body.instantiate1' value) = .ok result at hresult
        simpa only [Expr.instantiate1_eq] using (Except.ok.inj hresult).symm

theorem SortTelescope.normalizedBeta {body : Expr} (htype : SortTelescope body)
    (name : Name) (domain value : Expr) (bi : BinderInfo) :
    NormalizedSortTelescope (.app (.lam name domain body bi) value) (body.instantiate1 value) := by
  have hshape : SortTelescope (body.instantiate1' value) := by
    simpa only [Expr.instantiate1_eq] using htype.instantiate1 value
  refine ⟨htype.instantiate1 value, ?_⟩
  intro ctx result hresult
  change (Prod.fst <$> (TypeChecker.Methods.withFuel ctx.fuel.recDepth).whnf
    (.app (.lam name domain body bi) value)
    { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
      lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
  cases hdepth : ctx.fuel.recDepth with
  | zero =>
    rw [hdepth] at hresult
    change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
    cases hresult
  | succ depth =>
    rw [hdepth] at hresult
    change (Prod.fst <$> TypeChecker.Inner.whnf' (.app (.lam name domain body bi) value)
      (TypeChecker.Methods.withFuel depth)
      { env := ctx.env, safety := ctx.safety, lctx := ctx.lctx,
        lparams := ctx.lparams, fuel := ctx.fuel } {}) = .ok result at hresult
    rw [TypeChecker.Inner.whnf'.eq_def] at hresult
    simp only [pure_bind] at hresult
    simp only [get, getThe, readThe, bind, ReaderT.bind, StateT.bind, pure,
      ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
      MonadReaderOf.read, read, liftM, monadLift, MonadLift.monadLift,
      Except.pure, Except.bind, ReaderT.read, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, Std.HashMap.getElem?_empty,
      Bool.false_eq_true, ite_false] at hresult
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
      rw [TypeChecker.Inner.whnfCore'.eq_def] at hresult
      simp only [TypeChecker.Inner.whnfCore, TypeChecker.Inner.whnfCore'.save,
        get, getThe, bind, ReaderT.bind, StateT.bind, pure,
        ReaderT.pure, StateT.pure, StateT.get, MonadStateOf.get,
        liftM, monadLift, MonadLift.monadLift,
        Except.pure, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, Std.HashMap.getElem?_empty,
        Expr.withRevApp_eq] at hresult
      simp only [Expr.getAppFn] at hresult
      cases depth with
      | zero =>
        simp only [TypeChecker.Methods.withFuel] at hresult
        change Except.error Kernel.Exception.deepRecursion = .ok result at hresult
        cases hresult
      | succ depth =>
        rw [lambdaCore name domain body bi depth _ _ false false] at hresult
        simp only [Expr.getAppRevArgs_eq, Expr.getAppArgsRevList] at hresult
        have hnotlambda : ∀ lamName lamDomain lamBody lamBi,
            body = Expr.lam lamName lamDomain lamBody lamBi → False := by
          intro lamName lamDomain lamBody lamBi heq
          cases htype <;> cases heq
        rw [TypeChecker.Inner.whnfCore'.loop] at hresult
        all_goals try exact hnotlambda
        cases htype
        all_goals
          rw [TypeChecker.Inner.whnfCore'.loop.cont] at hresult
          simp only [List.size_toArray, List.length_cons, List.length_nil,
            Nat.zero_add, Nat.sub_self, emptyRevRange, singletonRange] at hresult
          simp only [TypeChecker.Inner.whnfCore, TypeChecker.Inner.whnfCore'.save,
            bind, ReaderT.bind, StateT.bind, pure,
            ReaderT.pure, StateT.pure,
            monadLift, MonadLift.monadLift,
            Except.pure, Except.bind, modify, modifyGet,
            MonadStateOf.modifyGet, StateT.modifyGet, Expr.instantiate1_eq,
            Bool.not_false, Bool.true_and, ite_true] at hresult
          rw [telescopeCore _ hshape depth _ _ false false] at hresult
          simp only [telescopeNative hshape] at hresult
          simp only [StateT.lift, bind, ReaderT.bind, StateT.bind, pure,
            ReaderT.pure, StateT.pure, Except.pure, Except.bind,
            telescopeNat hshape, telescopeDelta hshape] at hresult
          change Except.ok _ = .ok result at hresult
          simpa only [Expr.instantiate1_eq] using (Except.ok.inj hresult).symm

end Lean4Lean.AddInductive
