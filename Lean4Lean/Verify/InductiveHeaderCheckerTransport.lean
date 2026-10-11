import Lean4Lean.Verify.InductiveConstructorFreshness

namespace Lean4Lean
open Lean hiding Environment Exception

theorem HeaderAxiomLookupAgreement.unchanged
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name)
    (untouched : ¬changed name) : actual.find? name = shadow.find? name := by
  rcases agreement name with same | ⟨member, _⟩
  · exact same
  · exact False.elim (untouched member)

theorem HeaderAxiomLookupAgreement.constructors
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) :
    (actual.find? name).bind (fun info => match info with | .ctorInfo info => some info | _ => none) =
      (shadow.find? name).bind (fun info => match info with | .ctorInfo info => some info | _ => none) := by
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [same]
  · rw [actualLookup, shadowLookup]
    rfl

theorem HeaderAxiomLookupAgreement.recursors
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) :
    (actual.find? name).bind (fun info => match info with | .recInfo info => some info | _ => none) =
      (shadow.find? name).bind (fun info => match info with | .recInfo info => some info | _ => none) := by
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [same]
  · rw [actualLookup, shadowLookup]
    rfl

theorem HeaderAxiomLookupAgreement.constructorApp
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (expression : Expr) :
    expression.isConstructorApp?' actual = expression.isConstructorApp?' shadow := by
  cases head : expression.getAppFn <;> (simp only [Expr.isConstructorApp?', head]; try rfl)
  rename_i name levels
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [same]
  · rw [actualLookup, shadowLookup]
    rfl

theorem HeaderAxiomLookupAgreement.delta
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (expression : Expr) :
    TypeChecker.Inner.isDelta actual expression = TypeChecker.Inner.isDelta shadow expression := by
  cases head : expression.getAppFn <;> (simp only [TypeChecker.Inner.isDelta, head]; try rfl)
  rename_i name levels
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [same]
  · rw [actualLookup, shadowLookup]
    simp [headerAxiomInfo, ConstantInfo.hasValue]

theorem TypeChecker.Inner.inferConstant.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (name : Name) (levels : List Level) (inferOnly : Bool) :
    (TypeChecker.Inner.inferConstant context name levels inferOnly).WF fun result =>
      TypeChecker.Inner.inferConstant { context with env := shadow } name levels inferOnly = .ok result := by
  intro result accepted
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · cases found : context.env.find? name with
    | none =>
      simp [TypeChecker.Inner.inferConstant, Kernel.Environment.get, found] at accepted
      change (Except.error _ : Except Kernel.Exception Expr) = .ok result at accepted
      contradiction
    | some info =>
      have shadowFound : shadow.find? name = some info := same.symm.trans found
      simpa [TypeChecker.Inner.inferConstant, Kernel.Environment.get, found, shadowFound,
        TypeChecker.Inner.checkLevel] using accepted
  · simpa [TypeChecker.Inner.inferConstant, Kernel.Environment.get, actualLookup, shadowLookup,
      TypeChecker.Inner.checkLevel, headerAxiomInfo, ConstantInfo.instantiateTypeLevelParams,
      ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.toConstantVal, ConstantInfo.isUnsafe] using accepted

theorem TypeChecker.Inner.unfoldDefinitionCore.headerAxiomTransport
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.Inner.unfoldDefinitionCore expression methods context state =
      TypeChecker.Inner.unfoldDefinitionCore expression methods { context with env := shadow } state := by
  cases expression <;> try rfl
  rename_i name levels
  dsimp only [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.getEnv, liftM,
    MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind]
  rw [agreement.delta]
  cases selected : TypeChecker.Inner.isDelta shadow (.const name levels) <;> dsimp only
  · rfl
  · split <;> try rfl
    split <;> try rfl
    dsimp only [Bind.bind, Pure.pure, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
      Except.pure, Except.bind, MonadState.get, getThe, MonadStateOf.get, StateT.get,
      liftM, MonadLift.monadLift, MonadLiftT.monadLift]
    cases cached : state.unfold[Expr.const name levels]? <;> rfl

theorem TypeChecker.Inner.inferType'.headerConstantTransport
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) (inferOnly : Bool) :
    (TypeChecker.Inner.inferType' (.const name levels) inferOnly methods context state).WF fun result =>
      TypeChecker.Inner.inferType' (.const name levels) inferOnly methods { context with env := shadow } state =
        .ok result := by
  intro result accepted
  simp only [TypeChecker.Inner.inferType', Expr.hasLooseBVars, Expr.looseBVarRange_eq,
    Expr.looseBVarRange', Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false] at accepted ⊢
  dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, MonadReader.read, readThe,
    MonadReaderOf.read, ReaderT.read, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
    Except.pure, Except.bind, StateT.lift] at accepted ⊢
  cases cached : (cond inferOnly state.inferTypeI state.inferTypeC)[Expr.const name levels]? with
  | some value => simpa only [cached] using accepted
  | none =>
    simp only [cached] at accepted ⊢
    dsimp only [Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
      Except.pure, Except.bind, StateT.lift] at accepted ⊢
    cases inferred : TypeChecker.Inner.inferConstant context name levels inferOnly with
    | error error =>
      rw [inferred] at accepted
      contradiction
    | ok value =>
      have transported := TypeChecker.Inner.inferConstant.headerAxiomTransport context shadow agreement
        name levels inferOnly value inferred
      rw [inferred] at accepted
      rw [transported]
      simpa only [Except.bind] using accepted

theorem TypeChecker.Inner.unfoldDefinition.headerAxiomTransport
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.Inner.unfoldDefinition expression methods context state =
      TypeChecker.Inner.unfoldDefinition expression methods { context with env := shadow } state := by
  simp only [TypeChecker.Inner.unfoldDefinition]
  split
  · dsimp only [Bind.bind, ReaderT.bind, StateT.bind]
    rw [TypeChecker.Inner.unfoldDefinitionCore.headerAxiomTransport methods context shadow agreement]
    cases selected : TypeChecker.Inner.unfoldDefinitionCore expression.getAppFn methods
        { context with env := shadow } state with
    | error error => rfl
    | ok returned =>
      rcases returned with ⟨value, finalState⟩
      cases value <;> rfl
  · exact TypeChecker.Inner.unfoldDefinitionCore.headerAxiomTransport methods context shadow agreement state expression

theorem TypeChecker.Inner.inferType.headerConstantTransport
    (fuel : Nat) (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) (inferOnly : Bool) :
    (TypeChecker.Inner.inferType (.const name levels) inferOnly (TypeChecker.Methods.withFuel fuel)
      context state).WF fun result =>
      TypeChecker.Inner.inferType (.const name levels) inferOnly (TypeChecker.Methods.withFuel fuel)
        { context with env := shadow } state = .ok result := by
  cases fuel with
  | zero => exact .throw
  | succ fuel =>
    exact TypeChecker.Inner.inferType'.headerConstantTransport (TypeChecker.Methods.withFuel fuel)
      context shadow agreement state name levels inferOnly

theorem TypeChecker.checkType.headerConstantTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) :
    (TypeChecker.checkType (.const name levels) context state).WF fun result =>
      TypeChecker.checkType (.const name levels) { context with env := shadow } state = .ok result := by
  exact TypeChecker.Inner.inferType.headerConstantTransport context.fuel.recDepth context shadow agreement
    state name levels false

theorem TypeChecker.inferType.headerConstantTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) :
    (TypeChecker.inferType (.const name levels) context state).WF fun result =>
      TypeChecker.inferType (.const name levels) { context with env := shadow } state = .ok result := by
  exact TypeChecker.Inner.inferType.headerConstantTransport context.fuel.recDepth context shadow agreement
    state name levels true

end Lean4Lean
