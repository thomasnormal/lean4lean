import Lean4Lean.Verify.InductiveHeaderTelescopeTransport

namespace Lean4Lean
open Lean hiding Environment Exception

def nativeProjectionView (expression : Expr) : Expr × Array Expr :=
  expression.withApp fun head arguments => (head, arguments)

theorem _root_.Lean.Expr.withApp_projectionView (expression : Expr) (callback : Expr → Array Expr → resultType) :
    expression.withApp callback = callback (nativeProjectionView expression).1 (nativeProjectionView expression).2 := by
  exact (Expr.withApp_rel expression (fun head arguments => (head, arguments)) callback
    (fun view result => callback view.1 view.2 = result) (fun _ _ => rfl)).symm

inductive NativeForInReachable (step : itemType → valueType → TypeChecker.M (ForInStep valueType))
    (context : TypeChecker.Context) (state : TypeChecker.State) (items : List itemType) (initial : valueType) :
    List itemType → valueType → TypeChecker.State → Prop
  | initial : NativeForInReachable step context state items initial items initial state
  | yielded {item remaining current currentState next nextState} :
      NativeForInReachable step context state items initial (item :: remaining) current currentState →
      step item current context currentState = .ok (.yield next, nextState) →
      NativeForInReachable step context state items initial remaining next nextState

theorem TypeChecker.RecM.forIn_transport
    (actualMethods shadowMethods : Methods) (actualContext shadowContext : Context) (state : State)
    (items : List itemType) (initial : valueType) (actualStep shadowStep : itemType → valueType → RecM (ForInStep valueType))
    (callbacks : ∀ item remaining current currentState,
      NativeForInReachable (fun item current => actualStep item current actualMethods)
        actualContext state items initial (item :: remaining) current currentState →
      M.SuccessTransport (actualStep item current actualMethods) (shadowStep item current shadowMethods)
        actualContext shadowContext currentState) :
    M.SuccessTransport ((forIn items initial actualStep) actualMethods) ((forIn items initial shadowStep) shadowMethods)
      actualContext shadowContext state := by
  have auxiliary : ∀ remaining current currentState,
      NativeForInReachable (fun item current => actualStep item current actualMethods)
        actualContext state items initial remaining current currentState →
      M.SuccessTransport ((forIn remaining current actualStep) actualMethods)
        ((forIn remaining current shadowStep) shadowMethods) actualContext shadowContext currentState := by
    intro remaining
    induction remaining with
    | nil => intro current currentState reached; exact M.SuccessTransport.pure _ _ _ _
    | cons item remaining inductionHypothesis =>
      intro current currentState reached
      rw [List.forIn_cons, List.forIn_cons]
      dsimp only [Bind.bind, ReaderT.bind]
      apply M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks item remaining current currentState reached)
      intro next nextState accepted
      cases next with
      | done value => exact M.SuccessTransport.pure _ _ _ _
      | yield value => exact inductionHypothesis value nextState (.yielded reached accepted)
  exact auxiliary items initial state .initial

def TypeChecker.Inner.nativeProjectionFailure (environment : Kernel.Environment) (source : Expr) : TypeChecker.RecM resultType := do
  throw <| .invalidProj environment (← getLCtx) source

def TypeChecker.Inner.nativeProjectionParameter (environment : Kernel.Environment) (source : Expr)
    (arguments : Array Expr) (index : Nat) (current : Expr) : TypeChecker.RecM (ForInStep Expr) := do
  let .forallE _ _ body _ ← whnf current | nativeProjectionFailure environment source
  return .yield (body.instantiate1 arguments[index]!)

def TypeChecker.Inner.nativeProjectionParameters (environment : Kernel.Environment) (source : Expr)
    (arguments : Array Expr) (parameters : Nat) (initial : Expr) : TypeChecker.RecM Expr :=
  forIn [:parameters] initial (nativeProjectionParameter environment source arguments)

def TypeChecker.Inner.nativeProjectionField (environment : Kernel.Environment) (source : Expr)
    (parent : Name) (structureExpr : Expr) (propositional : Bool) (index : Nat) (current : Expr) :
    TypeChecker.RecM (ForInStep Expr) := do
  let .forallE _ domain body _ ← whnf current | nativeProjectionFailure environment source
  if body.hasLooseBVars then
    if propositional then
      if !(← isProp domain) then nativeProjectionFailure environment source
    return .yield (body.instantiate1 (.proj parent index structureExpr))
  else
    return .yield body

def TypeChecker.Inner.nativeProjectionFields (environment : Kernel.Environment) (source : Expr)
    (parent : Name) (structureExpr : Expr) (propositional : Bool) (fields : Nat) (initial : Expr) : TypeChecker.RecM Expr :=
  forIn [:fields] initial (nativeProjectionField environment source parent structureExpr propositional)

def TypeChecker.Inner.nativeProjectionFinal (environment : Kernel.Environment) (source : Expr)
    (propositional : Bool) (current : Expr) : TypeChecker.RecM Expr := do
  let .forallE _ domain _ _ ← whnf current | nativeProjectionFailure environment source
  if propositional then
    if !(← isProp domain) then nativeProjectionFailure environment source
  return domain

def TypeChecker.Inner.nativeProjectionMaybeProp (expression : Expr) : TypeChecker.RecM Bool := do
  return !(← getSortLevel expression).isNeverZero

def TypeChecker.Inner.nativeProjectionBody (parent : Name) (index : Nat) (structureExpr normalized : Expr) : TypeChecker.RecM Expr :=
  normalized.withApp fun head arguments => do
    let environment ← TypeChecker.getEnv
    let source := .proj parent index structureExpr
    let .const name levels := head | nativeProjectionFailure environment source
    if parent != name then nativeProjectionFailure environment source
    let .inductInfo header ← environment.get name | nativeProjectionFailure environment source
    let [constructor] := header.ctors | nativeProjectionFailure environment source
    if arguments.size != header.numParams + header.numIndices then nativeProjectionFailure environment source
    let information ← environment.get constructor
    let current ← nativeProjectionParameters environment source arguments header.numParams (information.instantiateTypeLevelParams levels)
    let propositional ← nativeProjectionMaybeProp normalized
    let current ← nativeProjectionFields environment source name structureExpr propositional index current
    nativeProjectionFinal environment source propositional current

set_option maxHeartbeats 800000 in
theorem TypeChecker.Inner.inferProj.body_eq (parent : Name) (index : Nat) (structureExpr structureType : Expr) :
    inferProj parent index structureExpr structureType = (do
      let normalized ← whnf structureType
      nativeProjectionBody parent index structureExpr normalized) := by
  simp only [inferProj, nativeProjectionBody, nativeProjectionParameters, nativeProjectionFields,
    nativeProjectionFinal, nativeProjectionMaybeProp, pure_bind]
  simp only [nativeProjectionFailure, bind_assoc]
  rfl

theorem TypeChecker.Inner.nativeProjectionFailure.transport {resultType : Type}
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) :
    TypeChecker.M.SuccessTransport (nativeProjectionFailure (resultType := resultType) actualContext.env source actualMethods)
      (nativeProjectionFailure shadowContext.env source shadowMethods) actualContext shadowContext state := by
  intro result accepted
  change (Except.error _ : Except Kernel.Exception (resultType × TypeChecker.State)) = .ok result at accepted
  contradiction

structure NativeProjectionPropCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) : Prop where
  inference : TypeChecker.M.SuccessTransport (actualMethods.inferType expression true)
    (shadowMethods.inferType expression true) actualContext shadowContext state
  normalization : ∀ inferred inferredState,
    actualMethods.inferType expression true actualContext state = .ok (inferred, inferredState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnf inferred) (shadowMethods.whnf inferred)
      actualContext shadowContext inferredState

theorem NativeProjectionPropCallbacks.transport
    (callbacks : NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext state expression) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isProp expression actualMethods)
      (TypeChecker.Inner.isProp expression shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.isProp.transport _ _ _ _ _ _ callbacks.inference callbacks.normalization

theorem NativeProjectionPropCallbacks.maybeTransport
    (callbacks : NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext state expression) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.nativeProjectionMaybeProp expression actualMethods)
      (TypeChecker.Inner.nativeProjectionMaybeProp expression shadowMethods) actualContext shadowContext state := by
  dsimp only [TypeChecker.Inner.nativeProjectionMaybeProp, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (TypeChecker.Inner.getSortLevel.transport _ _ _ _ _ _ callbacks.inference callbacks.normalization)
  intro level finalState _
  exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.nativeProjectionParameter.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (arguments : Array Expr) (index : Nat) (current : Expr)
    (normalization : TypeChecker.M.SuccessTransport (actualMethods.whnf current) (shadowMethods.whnf current)
      actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (nativeProjectionParameter actualContext.env source arguments index current actualMethods)
      (nativeProjectionParameter shadowContext.env source arguments index current shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeProjectionParameter, whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ normalization
  intro normalized normalizedState accepted
  cases normalized <;> try exact nativeProjectionFailure.transport _ _ _ _ _ _
  exact TypeChecker.M.SuccessTransport.pure _ _ _ _

structure NativeProjectionParameterCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (source : Expr) (arguments : Array Expr) (parameters : Nat) (initial : Expr) : Prop where
  normalizations : ∀ index remaining current currentState,
    NativeForInReachable (fun index current =>
      TypeChecker.Inner.nativeProjectionParameter actualContext.env source arguments index current actualMethods)
      actualContext state (List.range' 0 parameters) initial (index :: remaining) current currentState →
    TypeChecker.M.SuccessTransport (actualMethods.whnf current) (shadowMethods.whnf current)
      actualContext shadowContext currentState

theorem TypeChecker.Inner.nativeProjectionParameters.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (arguments : Array Expr) (parameters : Nat) (initial : Expr)
    (callbacks : NativeProjectionParameterCallbacks actualMethods shadowMethods actualContext shadowContext state
      source arguments parameters initial) :
    TypeChecker.M.SuccessTransport (nativeProjectionParameters actualContext.env source arguments parameters initial actualMethods)
      (nativeProjectionParameters shadowContext.env source arguments parameters initial shadowMethods)
      actualContext shadowContext state := by
  unfold nativeProjectionParameters
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply TypeChecker.RecM.forIn_transport
  intro index remaining current currentState reached
  exact nativeProjectionParameter.transport _ _ _ _ _ _ _ _ _
    (callbacks.normalizations index remaining current currentState reached)

theorem TypeChecker.Inner.nativeProjectionField.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (parent : Name) (structureExpr : Expr)
    (propositional : Bool) (index : Nat) (current : Expr)
    (normalization : TypeChecker.M.SuccessTransport (actualMethods.whnf current) (shadowMethods.whnf current)
      actualContext shadowContext state)
    (domains : ∀ name domain body binder normalizedState,
      actualMethods.whnf current actualContext state = .ok (.forallE name domain body binder, normalizedState) →
      body.hasLooseBVars = true → propositional = true →
      NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState domain) :
    TypeChecker.M.SuccessTransport (nativeProjectionField actualContext.env source parent structureExpr propositional index current actualMethods)
      (nativeProjectionField shadowContext.env source parent structureExpr propositional index current shadowMethods)
      actualContext shadowContext state := by
  dsimp only [nativeProjectionField, whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ normalization
  intro normalized normalizedState accepted
  cases normalized <;> try exact nativeProjectionFailure.transport _ _ _ _ _ _
  rename_i name domain body binder
  by_cases dependent : body.hasLooseBVars = true
  · simp only [dependent, if_true]
    cases propositional with
    | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | true =>
      simp only [if_true]
      dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (domains name domain body binder normalizedState accepted dependent rfl).transport
      intro prop propState checked
      cases prop with
      | false => exact nativeProjectionFailure.transport actualMethods shadowMethods _ _ _ _
      | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  · simp only [dependent, Bool.false_eq_true, if_false]
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

structure NativeProjectionFieldCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (source : Expr) (parent : Name) (structureExpr : Expr) (propositional : Bool) (fields : Nat) (initial : Expr) : Prop where
  normalizations : ∀ index remaining current currentState,
    NativeForInReachable (fun index current =>
      TypeChecker.Inner.nativeProjectionField actualContext.env source parent structureExpr propositional index current actualMethods)
      actualContext state (List.range' 0 fields) initial (index :: remaining) current currentState →
    TypeChecker.M.SuccessTransport (actualMethods.whnf current) (shadowMethods.whnf current)
      actualContext shadowContext currentState
  domains : ∀ index remaining current currentState name domain body binder normalizedState,
    NativeForInReachable (fun index current =>
      TypeChecker.Inner.nativeProjectionField actualContext.env source parent structureExpr propositional index current actualMethods)
      actualContext state (List.range' 0 fields) initial (index :: remaining) current currentState →
    actualMethods.whnf current actualContext currentState = .ok (.forallE name domain body binder, normalizedState) →
    body.hasLooseBVars = true → propositional = true →
    NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState domain

theorem TypeChecker.Inner.nativeProjectionFields.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (parent : Name) (structureExpr : Expr)
    (propositional : Bool) (fields : Nat) (initial : Expr)
    (callbacks : NativeProjectionFieldCallbacks actualMethods shadowMethods actualContext shadowContext state
      source parent structureExpr propositional fields initial) :
    TypeChecker.M.SuccessTransport (nativeProjectionFields actualContext.env source parent structureExpr propositional fields initial actualMethods)
      (nativeProjectionFields shadowContext.env source parent structureExpr propositional fields initial shadowMethods)
      actualContext shadowContext state := by
  unfold nativeProjectionFields
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply TypeChecker.RecM.forIn_transport
  intro index remaining current currentState reached
  exact nativeProjectionField.transport _ _ _ _ _ _ _ _ _ _ _
    (callbacks.normalizations index remaining current currentState reached)
    (fun name domain body binder normalizedState accepted dependent prop =>
      callbacks.domains index remaining current currentState name domain body binder normalizedState reached accepted dependent prop)

structure NativeProjectionFinalCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (propositional : Bool) (current : Expr) : Prop where
  normalization : TypeChecker.M.SuccessTransport (actualMethods.whnf current) (shadowMethods.whnf current)
    actualContext shadowContext state
  domains : ∀ name domain body binder normalizedState,
    actualMethods.whnf current actualContext state = .ok (.forallE name domain body binder, normalizedState) →
    propositional = true → NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState domain

theorem TypeChecker.Inner.nativeProjectionFinal.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (source : Expr) (propositional : Bool) (current : Expr)
    (callbacks : NativeProjectionFinalCallbacks actualMethods shadowMethods actualContext shadowContext state propositional current) :
    TypeChecker.M.SuccessTransport (nativeProjectionFinal actualContext.env source propositional current actualMethods)
      (nativeProjectionFinal shadowContext.env source propositional current shadowMethods) actualContext shadowContext state := by
  dsimp only [nativeProjectionFinal, whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.normalization
  intro normalized normalizedState accepted
  cases normalized <;> try exact nativeProjectionFailure.transport _ _ _ _ _ _
  rename_i name domain body binder
  cases propositional with
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    simp only [if_true]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (callbacks.domains name domain body binder normalizedState accepted rfl).transport
    intro prop propState checked
    cases prop with
    | false => exact nativeProjectionFailure.transport actualMethods shadowMethods _ _ _ _
    | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem HeaderAxiomLookupAgreement.instantiatedType
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) (levels : List Level)
    (information : ConstantInfo) (found : actual.find? name = some information) :
    ∃ shadowInformation, shadow.find? name = some shadowInformation ∧
      shadowInformation.instantiateTypeLevelParams levels = information.instantiateTypeLevelParams levels := by
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · exact ⟨information, same.symm.trans found, rfl⟩
  · cases Option.some.inj (actualLookup.symm.trans found)
    exact ⟨headerAxiomInfo header, shadowLookup, rfl⟩

structure NativeProjectionEntryReceipt (context : TypeChecker.Context) (parent : Name) (normalized : Expr)
    (header : InductiveVal) (levels : List Level) (arguments : Array Expr) (information : ConstantInfo) : Prop where
  view : nativeProjectionView normalized = (.const parent levels, arguments)
  parentLookup : context.env.find? parent = some (.inductInfo header)
  arity : arguments.size = header.numParams + header.numIndices
  constructorLookup : ∃ constructor, header.ctors = [constructor] ∧ context.env.find? constructor = some information

structure NativeProjectionBodyCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr normalized : Expr) : Prop where
  parameters : ∀ header levels arguments information,
    NativeProjectionEntryReceipt actualContext parent normalized header levels arguments information →
    NativeProjectionParameterCallbacks actualMethods shadowMethods actualContext shadowContext state
      (.proj parent index structureExpr) arguments header.numParams (information.instantiateTypeLevelParams levels)
  propositions : ∀ header levels arguments information,
    NativeProjectionEntryReceipt actualContext parent normalized header levels arguments information →
    ∀ parameterType parameterState,
    TypeChecker.Inner.nativeProjectionParameters actualContext.env (.proj parent index structureExpr) arguments
      header.numParams (information.instantiateTypeLevelParams levels) actualMethods actualContext state = .ok (parameterType, parameterState) →
    NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext parameterState normalized
  fields : ∀ header levels arguments information,
    NativeProjectionEntryReceipt actualContext parent normalized header levels arguments information →
    ∀ parameterType parameterState propositional propState,
    TypeChecker.Inner.nativeProjectionParameters actualContext.env (.proj parent index structureExpr) arguments
      header.numParams (information.instantiateTypeLevelParams levels) actualMethods actualContext state = .ok (parameterType, parameterState) →
    TypeChecker.Inner.nativeProjectionMaybeProp normalized actualMethods actualContext parameterState = .ok (propositional, propState) →
    NativeProjectionFieldCallbacks actualMethods shadowMethods actualContext shadowContext propState
      (.proj parent index structureExpr) parent structureExpr propositional index parameterType
  finalization : ∀ header levels arguments information,
    NativeProjectionEntryReceipt actualContext parent normalized header levels arguments information →
    ∀ parameterType parameterState propositional propState current currentState,
    TypeChecker.Inner.nativeProjectionParameters actualContext.env (.proj parent index structureExpr) arguments
      header.numParams (information.instantiateTypeLevelParams levels) actualMethods actualContext state = .ok (parameterType, parameterState) →
    TypeChecker.Inner.nativeProjectionMaybeProp normalized actualMethods actualContext parameterState = .ok (propositional, propState) →
    TypeChecker.Inner.nativeProjectionFields actualContext.env (.proj parent index structureExpr) parent structureExpr propositional
      index parameterType actualMethods actualContext propState = .ok (current, currentState) →
    NativeProjectionFinalCallbacks actualMethods shadowMethods actualContext shadowContext currentState propositional current

structure NativeProjectionCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr structureType : Expr) : Prop where
  normalization : TypeChecker.M.SuccessTransport (actualMethods.whnf structureType) (shadowMethods.whnf structureType)
    actualContext shadowContext state
  bodies : ∀ normalized normalizedState,
    actualMethods.whnf structureType actualContext state = .ok (normalized, normalizedState) →
    NativeProjectionBodyCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState parent index structureExpr normalized

theorem TypeChecker.Inner.nativeProjectionBody.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (index : Nat) (structureExpr normalized : Expr)
    (stable : actualContext.env.find? parent = shadowContext.env.find? parent)
    (callbacks : NativeProjectionBodyCallbacks actualMethods shadowMethods actualContext shadowContext state parent index structureExpr normalized) :
    TypeChecker.M.SuccessTransport (nativeProjectionBody parent index structureExpr normalized actualMethods)
      (nativeProjectionBody parent index structureExpr normalized shadowMethods) actualContext shadowContext state := by
  intro result accepted
  simp only [nativeProjectionBody, Expr.withApp_projectionView] at accepted ⊢
  rcases view : nativeProjectionView normalized with ⟨head, arguments⟩
  simp only [view] at accepted ⊢
  dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
    ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted ⊢
  cases head <;> try (change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted; contradiction)
  rename_i name levels
  by_cases matching : parent = name
  · subst name
    simp only [bne_iff_ne, ne_self_iff_false, if_false] at accepted ⊢
    cases parentLookup : actualContext.env.find? parent with
    | none =>
      simp only [Kernel.Environment.get, parentLookup] at accepted
      change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
      contradiction
    | some parentInformation =>
      have shadowParent := stable.symm.trans parentLookup
      simp only [Kernel.Environment.get, parentLookup, shadowParent] at accepted ⊢
      dsimp only [StateT.lift, Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted ⊢
      cases parentInformation <;> try (change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted; contradiction)
      rename_i header
      dsimp only [] at accepted ⊢
      cases constructors : header.ctors with
      | nil =>
        simp only [constructors] at accepted
        change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
        contradiction
      | cons constructor remaining =>
        cases remaining with
        | cons another remaining =>
          simp only [constructors] at accepted
          change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
          contradiction
        | nil =>
          simp only [constructors] at accepted ⊢
          by_cases arity : arguments.size = header.numParams + header.numIndices
          · simp only [arity, ne_self_iff_false, if_false] at accepted ⊢
            cases constructorLookup : actualContext.env.find? constructor with
            | none =>
              simp only [constructorLookup] at accepted
              change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
              contradiction
            | some information =>
              obtain ⟨shadowInformation, shadowLookup, sameType⟩ :=
                agreement.instantiatedType constructor levels information constructorLookup
              simp only [constructorLookup, shadowLookup] at accepted ⊢
              dsimp only [StateT.lift, Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted ⊢
              rw [sameType]
              have entry : NativeProjectionEntryReceipt actualContext parent normalized header levels arguments information :=
                { view, parentLookup, arity, constructorLookup := ⟨constructor, constructors, constructorLookup⟩ }
              have continuation : TypeChecker.M.SuccessTransport
                  ((do
                    let parameterType ← nativeProjectionParameters actualContext.env (.proj parent index structureExpr) arguments
                      header.numParams (information.instantiateTypeLevelParams levels)
                    let propositional ← nativeProjectionMaybeProp normalized
                    let current ← nativeProjectionFields actualContext.env (.proj parent index structureExpr) parent structureExpr
                      propositional index parameterType
                    nativeProjectionFinal actualContext.env (.proj parent index structureExpr) propositional current) actualMethods)
                  ((do
                    let parameterType ← nativeProjectionParameters shadowContext.env (.proj parent index structureExpr) arguments
                      header.numParams (information.instantiateTypeLevelParams levels)
                    let propositional ← nativeProjectionMaybeProp normalized
                    let current ← nativeProjectionFields shadowContext.env (.proj parent index structureExpr) parent structureExpr
                      propositional index parameterType
                    nativeProjectionFinal shadowContext.env (.proj parent index structureExpr) propositional current) shadowMethods)
                  actualContext shadowContext state := by
                dsimp only [Bind.bind, ReaderT.bind]
                apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
                  (nativeProjectionParameters.transport _ _ _ _ _ _ _ _ _ (callbacks.parameters _ _ _ _ entry))
                intro parameterType parameterState parametersAccepted
                apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
                  (callbacks.propositions _ _ _ _ entry _ _ parametersAccepted).maybeTransport
                intro propositional propState propositionAccepted
                apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
                  (nativeProjectionFields.transport _ _ _ _ _ _ _ _ _ _ _
                    (callbacks.fields _ _ _ _ entry _ _ _ _ parametersAccepted propositionAccepted))
                intro current currentState fieldsAccepted
                exact nativeProjectionFinal.transport _ _ _ _ _ _ _ _
                  (callbacks.finalization _ _ _ _ entry _ _ _ _ _ _ parametersAccepted propositionAccepted fieldsAccepted)
              exact continuation result accepted
          · rw [if_pos arity] at accepted
            change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
            contradiction
  · have different : (parent != name) = true := by simpa only [bne_iff_ne] using matching
    simp only [different, if_true] at accepted
    change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
    contradiction

theorem TypeChecker.Inner.inferProj.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (index : Nat) (structureExpr structureType : Expr)
    (untouched : ¬changed parent)
    (callbacks : NativeProjectionCallbacks actualMethods shadowMethods actualContext shadowContext state parent index structureExpr structureType) :
    TypeChecker.M.SuccessTransport (inferProj parent index structureExpr structureType actualMethods)
      (inferProj parent index structureExpr structureType shadowMethods) actualContext shadowContext state := by
  rw [inferProj.body_eq]
  dsimp only [whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.normalization
  intro normalized normalizedState accepted
  exact nativeProjectionBody.transport _ _ _ _ agreement _ _ _ _ _ (agreement.unchanged parent untouched)
    (callbacks.bodies normalized normalizedState accepted)

theorem TypeChecker.Inner.nativeProjectionBody.entryOfSuccess
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr normalized : Expr) (result : Expr × TypeChecker.State)
    (accepted : nativeProjectionBody parent index structureExpr normalized methods context state = .ok result) :
    ∃ header levels arguments information, NativeProjectionEntryReceipt context parent normalized header levels arguments information := by
  simp only [nativeProjectionBody, Expr.withApp_projectionView] at accepted
  rcases view : nativeProjectionView normalized with ⟨head, arguments⟩
  simp only [view] at accepted
  dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, Pure.pure, Bind.bind,
    ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted
  cases head <;> try (change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted; contradiction)
  rename_i name levels
  by_cases matching : parent = name
  · subst name
    simp only [bne_iff_ne, ne_self_iff_false, if_false] at accepted
    cases parentLookup : context.env.find? parent with
    | none =>
      simp only [Kernel.Environment.get, parentLookup] at accepted
      change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
      contradiction
    | some parentInformation =>
      simp only [Kernel.Environment.get, parentLookup] at accepted
      dsimp only [StateT.lift, Bind.bind, ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind] at accepted
      cases parentInformation <;> try (change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted; contradiction)
      rename_i header
      dsimp only [] at accepted
      cases constructors : header.ctors with
      | nil =>
        simp only [constructors] at accepted
        change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
        contradiction
      | cons constructor remaining =>
        cases remaining with
        | cons another remaining =>
          simp only [constructors] at accepted
          change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
          contradiction
        | nil =>
          simp only [constructors] at accepted
          by_cases arity : arguments.size = header.numParams + header.numIndices
          · simp only [arity, ne_self_iff_false, if_false] at accepted
            cases constructorLookup : context.env.find? constructor with
            | none =>
              simp only [constructorLookup] at accepted
              change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
              contradiction
            | some information =>
              exact ⟨header, levels, arguments, information,
                { view := view, parentLookup := parentLookup, arity := arity,
                  constructorLookup := ⟨constructor, constructors, constructorLookup⟩ }⟩
          · rw [if_pos arity] at accepted
            change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
            contradiction
  · have different : (parent != name) = true := by simpa only [bne_iff_ne] using matching
    simp only [different, if_true] at accepted
    change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
    contradiction

def NativeProjectionMetadataFrame (actual shadow : Kernel.Environment) (parent : Name) : Prop :=
  ∀ header, actual.find? parent = some (.inductInfo header) →
    actual.find? parent = shadow.find? parent ∨ ∀ constructor ∈ header.ctors, actual.find? constructor = none

theorem NativeProjectionMetadataFrame.ofConstructorFreshness
    (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (constructorHeaders : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : AddInductive.ConstructorsFresh actual types) (parent : Name) :
    NativeProjectionMetadataFrame actual shadow parent := by
  intro header lookup
  by_cases stable : actual.find? parent = shadow.find? parent
  · exact .inl stable
  · exact .inr (agreement.missingChangedHeader constructorHeaders fresh parent header lookup stable)

theorem TypeChecker.Inner.nativeProjectionBody.stagedTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (index : Nat) (structureExpr normalized : Expr)
    (metadata : NativeProjectionMetadataFrame actualContext.env shadowContext.env parent)
    (callbacks : NativeProjectionBodyCallbacks actualMethods shadowMethods actualContext shadowContext state parent index structureExpr normalized) :
    TypeChecker.M.SuccessTransport (nativeProjectionBody parent index structureExpr normalized actualMethods)
      (nativeProjectionBody parent index structureExpr normalized shadowMethods) actualContext shadowContext state := by
  intro result accepted
  obtain ⟨header, levels, arguments, information, entry⟩ := nativeProjectionBody.entryOfSuccess _ _ _ _ _ _ _ _ accepted
  rcases metadata header entry.parentLookup with stable | missing
  · exact nativeProjectionBody.transport _ _ _ _ agreement _ _ _ _ _ stable callbacks result accepted
  · obtain ⟨constructor, constructors, found⟩ := entry.constructorLookup
    have absent := missing constructor (by simp only [constructors, List.mem_cons, List.not_mem_nil, or_false])
    rw [absent] at found
    contradiction

theorem TypeChecker.Inner.inferProj.headerAxiomStagedTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (index : Nat) (structureExpr structureType : Expr)
    (metadata : NativeProjectionMetadataFrame actualContext.env shadowContext.env parent)
    (callbacks : NativeProjectionCallbacks actualMethods shadowMethods actualContext shadowContext state parent index structureExpr structureType) :
    TypeChecker.M.SuccessTransport (inferProj parent index structureExpr structureType actualMethods)
      (inferProj parent index structureExpr structureType shadowMethods) actualContext shadowContext state := by
  rw [inferProj.body_eq]
  dsimp only [whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.normalization
  intro normalized normalizedState accepted
  exact nativeProjectionBody.stagedTransport _ _ _ _ agreement _ _ _ _ _ metadata (callbacks.bodies _ _ accepted)

theorem TypeChecker.Inner.nativeProjectionBody.axiomParentRejects
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr normalized : Expr) (information : AxiomVal)
    (lookup : context.env.find? parent = some (.axiomInfo information)) :
    (nativeProjectionBody parent index structureExpr normalized methods context state).WF fun _ => False := by
  intro result accepted
  obtain ⟨header, levels, arguments, constructorInformation, entry⟩ := nativeProjectionBody.entryOfSuccess _ _ _ _ _ _ _ _ accepted
  have found := entry.parentLookup
  rw [lookup] at found
  cases Option.some.inj found

theorem TypeChecker.Inner.inferProj.entryOfSuccess
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr structureType : Expr) (result : Expr × TypeChecker.State)
    (accepted : inferProj parent index structureExpr structureType methods context state = .ok result) :
    ∃ normalized normalizedState header levels arguments information,
      methods.whnf structureType context state = .ok (normalized, normalizedState) ∧
      NativeProjectionEntryReceipt context parent normalized header levels arguments information := by
  rw [inferProj.body_eq] at accepted
  dsimp only [whnf, Bind.bind, ReaderT.bind, StateT.bind] at accepted
  cases normalization : methods.whnf structureType context state with
  | error error => simp only [normalization, Except.bind] at accepted; contradiction
  | ok returned =>
    rcases returned with ⟨normalized, normalizedState⟩
    simp only [normalization, Except.bind] at accepted
    obtain ⟨header, levels, arguments, information, entry⟩ := nativeProjectionBody.entryOfSuccess _ _ _ _ _ _ _ _ accepted
    exact ⟨normalized, normalizedState, header, levels, arguments, information, rfl, entry⟩

theorem TypeChecker.Inner.inferProj.axiomParentRejects
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr structureType : Expr) (information : AxiomVal)
    (lookup : context.env.find? parent = some (.axiomInfo information)) :
    (inferProj parent index structureExpr structureType methods context state).WF fun _ => False := by
  intro result accepted
  obtain ⟨normalized, normalizedState, header, levels, arguments, constructorInformation, normalization, entry⟩ :=
    inferProj.entryOfSuccess _ _ _ _ _ _ _ _ accepted
  have found := entry.parentLookup
  rw [lookup] at found
  cases Option.some.inj found

theorem TypeChecker.Inner.inferProj.absentParentConstructors
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (parent : Name) (index : Nat) (structureExpr structureType : Expr) (header : InductiveVal)
    (lookup : context.env.find? parent = some (.inductInfo header))
    (missing : ∀ constructor ∈ header.ctors, context.env.find? constructor = none) :
    (inferProj parent index structureExpr structureType methods context state).WF fun _ => False := by
  intro result accepted
  obtain ⟨normalized, normalizedState, reachedHeader, levels, arguments, information, normalization, entry⟩ :=
    inferProj.entryOfSuccess _ _ _ _ _ _ _ _ accepted
  have same := ConstantInfo.inductInfo.inj (Option.some.inj (lookup.symm.trans entry.parentLookup))
  subst reachedHeader
  obtain ⟨constructor, constructors, found⟩ := entry.constructorLookup
  have absent := missing constructor (by simp only [constructors, List.mem_cons, List.not_mem_nil, or_false])
  rw [absent] at found
  contradiction

structure NativeHeaderInferCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
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
    NativeProjectionMetadataFrame actualContext.env shadowContext.env parent ∧
      NativeProjectionCallbacks actualMethods shadowMethods actualContext shadowContext sourceState parent index source sourceType
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

theorem NativeHeaderInferCallbacks.toMethodCallbacks
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (callbacks : NativeHeaderInferCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly) :
    NativeInferMethodCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly where
  applications := callbacks.applications
  lambdas := callbacks.lambdas
  foralls := callbacks.foralls
  lets := callbacks.lets
  projections := fun parent index source currentState sourceType sourceState reached accepted =>
    let receipt := callbacks.projections parent index source currentState sourceType sourceState reached accepted
    TypeChecker.Inner.inferProj.headerAxiomStagedTransport _ _ _ _ agreement _ _ _ _ _ receipt.1 receipt.2
  casts := callbacks.casts
  equalities := callbacks.equalities

theorem TypeChecker.Inner.inferType'.headerAxiomCallbackTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (locals : actualContext.lctx = shadowContext.lctx) (safety : actualContext.safety = shadowContext.safety)
    (parameters : actualContext.lparams = shadowContext.lparams) (state : TypeChecker.State)
    (expression : Expr) (inferOnly : Bool)
    (callbacks : NativeHeaderInferCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly) :
    TypeChecker.M.SuccessTransport (inferType' expression inferOnly actualMethods)
      (inferType' expression inferOnly shadowMethods) actualContext shadowContext state :=
  inferType'.headerAxiomMethodTransport _ _ _ _ agreement locals safety parameters _ _ _ (callbacks.toMethodCallbacks agreement)

end Lean4Lean
