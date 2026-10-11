import Lean4Lean.Verify.InductiveHeaderComparisonTransport

namespace Lean4Lean
open Lean hiding Environment Exception

theorem TypeChecker.RecM.or_transport (actualMethods shadowMethods : Methods)
    (actualContext shadowContext : Context) (state : State) (actualFirst shadowFirst actualSecond shadowSecond : RecM Bool)
    (first : M.SuccessTransport (actualFirst actualMethods) (shadowFirst shadowMethods) actualContext shadowContext state)
    (second : ∀ nextState, actualFirst actualMethods actualContext state = .ok (false, nextState) →
      M.SuccessTransport (actualSecond actualMethods) (shadowSecond shadowMethods) actualContext shadowContext nextState) :
    M.SuccessTransport ((actualFirst <||> actualSecond) actualMethods) ((shadowFirst <||> shadowSecond) shadowMethods)
      actualContext shadowContext state := by
  dsimp only [orM, Bind.bind, ReaderT.bind]
  apply M.SuccessTransport.bind _ _ _ _ _ _ _ first
  intro equal nextState accepted
  cases equal with
  | true => exact M.SuccessTransport.pure _ _ _ _
  | false => exact second _ accepted

structure NativeEtaExpansionCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  inference : (first.isLambda && !second.isLambda) = true →
    TypeChecker.M.SuccessTransport (actualMethods.inferType second true) (shadowMethods.inferType second true)
      actualContext shadowContext state
  normalization : ∀ inferred inferredState, (first.isLambda && !second.isLambda) = true →
    actualMethods.inferType second true actualContext state = .ok (inferred, inferredState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnf inferred) (shadowMethods.whnf inferred)
      actualContext shadowContext inferredState
  comparison : ∀ inferred inferredState name domain body binder normalizedState,
    (first.isLambda && !second.isLambda) = true →
    actualMethods.inferType second true actualContext state = .ok (inferred, inferredState) →
    actualMethods.whnf inferred actualContext inferredState = .ok (.forallE name domain body binder, normalizedState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore first (.lam name domain (.app second (.bvar 0)) binder))
      (shadowMethods.isDefEqCore first (.lam name domain (.app second (.bvar 0)) binder)) actualContext shadowContext normalizedState

theorem TypeChecker.Inner.tryEtaExpansionCore.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (tryEtaExpansionCore first second actualMethods)
      (tryEtaExpansionCore first second shadowMethods) actualContext shadowContext state := by
  unfold tryEtaExpansionCore
  cases eligible : first.isLambda && !second.isLambda with
  | false => simp only [Bool.false_eq_true, if_false]; exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    simp only [if_true]
    dsimp only [inferType, whnf, Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.inference eligible)
    intro inferred inferredState inferredAccepted
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.normalization _ _ eligible inferredAccepted)
    intro normalized normalizedState normalizedAccepted
    cases normalized with
    | forallE name domain body binder =>
      exact isDefEq.transport _ _ _ _ _ _ _
        (callbacks.comparison _ _ _ _ _ _ _ eligible inferredAccepted normalizedAccepted)
    | _ => exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.tryEtaExpansion.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (forward : NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second)
    (backward : ∀ nextState, tryEtaExpansionCore first second actualMethods actualContext state = .ok (false, nextState) →
      NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first) :
    TypeChecker.M.SuccessTransport (tryEtaExpansion first second actualMethods)
      (tryEtaExpansion first second shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.RecM.or_transport
  · exact tryEtaExpansionCore.transport _ _ _ _ _ _ _ forward
  · intro nextState accepted
    exact tryEtaExpansionCore.transport _ _ _ _ _ _ _ (backward _ accepted)

structure NativeProofIrrelCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  firstInference : TypeChecker.M.SuccessTransport (actualMethods.inferType first true) (shadowMethods.inferType first true)
    actualContext shadowContext state
  proposition : ∀ firstType firstState,
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext firstState firstType
  secondInference : ∀ firstType firstState propositionState,
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    TypeChecker.Inner.isProp firstType actualMethods actualContext firstState = .ok (true, propositionState) →
    TypeChecker.M.SuccessTransport (actualMethods.inferType second true) (shadowMethods.inferType second true)
      actualContext shadowContext propositionState
  comparison : ∀ firstType firstState propositionState secondType secondState,
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    TypeChecker.Inner.isProp firstType actualMethods actualContext firstState = .ok (true, propositionState) →
    actualMethods.inferType second true actualContext propositionState = .ok (secondType, secondState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstType secondType)
      (shadowMethods.isDefEqCore firstType secondType) actualContext shadowContext secondState

theorem TypeChecker.Inner.isDefEqProofIrrel.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeProofIrrelCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (isDefEqProofIrrel first second actualMethods)
      (isDefEqProofIrrel first second shadowMethods) actualContext shadowContext state := by
  dsimp only [isDefEqProofIrrel, inferType, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.firstInference
  intro firstType firstState firstAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.proposition _ _ firstAccepted).transport
  intro propositional propositionState propositionAccepted
  cases propositional with
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    dsimp only [inferType, toLBoolM, Bind.bind, ReaderT.bind]
    change TypeChecker.M.SuccessTransport
      ((pure PUnit.unit : TypeChecker.M PUnit) >>= fun _ => do
        let secondType ← actualMethods.inferType second true
        return (← isDefEq firstType secondType actualMethods).toLBool)
      ((pure PUnit.unit : TypeChecker.M PUnit) >>= fun _ => do
        let secondType ← shadowMethods.inferType second true
        return (← isDefEq firstType secondType shadowMethods).toLBool) actualContext shadowContext propositionState
    simp only [pure_bind]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (callbacks.secondInference _ _ _ firstAccepted propositionAccepted)
    intro secondType secondState secondAccepted
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
      (isDefEq.transport _ _ _ _ _ _ _ (callbacks.comparison _ _ _ _ _ firstAccepted propositionAccepted secondAccepted))
    intro equal finalState accepted
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

structure NativeOffsetCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  comparison : ∀ firstPredecessor secondPredecessor,
    (TypeChecker.Inner.isNatZero first && TypeChecker.Inner.isNatZero second) = false →
    TypeChecker.Inner.isNatSuccOf? first = some firstPredecessor →
    TypeChecker.Inner.isNatSuccOf? second = some secondPredecessor →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstPredecessor secondPredecessor)
      (shadowMethods.isDefEqCore firstPredecessor secondPredecessor) actualContext shadowContext state

theorem TypeChecker.Inner.isDefEqOffset.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeOffsetCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (isDefEqOffset first second actualMethods)
      (isDefEqOffset first second shadowMethods) actualContext shadowContext state := by
  unfold isDefEqOffset
  cases zeros : isNatZero first && isNatZero second with
  | true => simp only [if_true]; exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false =>
    simp only [Bool.false_eq_true, if_false, pure_bind]
    cases firstFound : isNatSuccOf? first with
    | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | some firstPredecessor =>
      cases secondFound : isNatSuccOf? second with
      | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | some secondPredecessor =>
        exact TypeChecker.RecM.toLBoolM_transport _ _ _ _ _ _ _ (callbacks.comparison _ _ zeros firstFound secondFound)

structure NativeStringExpansionCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  comparison : ∀ text function argument, first = .lit (.strVal text) → second = .app function argument →
    (function == .const ``String.ofList []) = true →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore (.strLitToConstructor text) second)
      (shadowMethods.isDefEqCore (.strLitToConstructor text) second) actualContext shadowContext state

theorem TypeChecker.Inner.tryStringLitExpansionCore.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (tryStringLitExpansionCore first second actualMethods)
      (tryStringLitExpansionCore first second shadowMethods) actualContext shadowContext state := by
  cases first with
  | lit literal =>
    cases literal with
    | strVal text =>
      cases second with
      | app function argument =>
        unfold tryStringLitExpansionCore
        by_cases constructor : (function == .const ``String.ofList []) = true
        · simp only [constructor, if_true, pure_bind]
          exact TypeChecker.RecM.toLBoolM_transport actualMethods shadowMethods actualContext shadowContext state
            (isDefEqCore (.strLitToConstructor text) (.app function argument))
            (isDefEqCore (.strLitToConstructor text) (.app function argument)) (callbacks.comparison _ _ _ rfl rfl constructor)
        · simp only [constructor]
          exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | _ => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | natVal _ => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | _ => exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.tryStringLitExpansion.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr)
    (forward : NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second)
    (backward : ∀ nextState, tryStringLitExpansionCore first second actualMethods actualContext state = .ok (.undef, nextState) →
      NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first) :
    TypeChecker.M.SuccessTransport (tryStringLitExpansion first second actualMethods)
      (tryStringLitExpansion first second shadowMethods) actualContext shadowContext state := by
  dsimp only [tryStringLitExpansion, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (tryStringLitExpansionCore.transport _ _ _ _ _ _ _ forward)
  intro result nextState accepted
  cases result with
  | undef => exact tryStringLitExpansionCore.transport _ _ _ _ _ _ _ (backward _ accepted)
  | true => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _

inductive NativeForInPrimeReachable (items : List itemType)
    (step : (item : itemType) → item ∈ items → valueType → TypeChecker.M (ForInStep valueType))
    (context : TypeChecker.Context) (state : TypeChecker.State) (initial : valueType) :
    List itemType → valueType → TypeChecker.State → Prop
  | initial : NativeForInPrimeReachable items step context state initial items initial state
  | yielded {item remaining current currentState next nextState} (member : item ∈ items) :
      NativeForInPrimeReachable items step context state initial (item :: remaining) current currentState →
      step item member current context currentState = .ok (.yield next, nextState) →
      NativeForInPrimeReachable items step context state initial remaining next nextState

theorem TypeChecker.RecM.forIn'_transport (actualMethods shadowMethods : Methods)
    (actualContext shadowContext : Context) (state : State) (items : List itemType) (initial : valueType)
    (actualStep shadowStep : (item : itemType) → item ∈ items → valueType → RecM (ForInStep valueType))
    (callbacks : ∀ item remaining current currentState (member : item ∈ items),
      NativeForInPrimeReachable items (fun item member current => actualStep item member current actualMethods)
        actualContext state initial (item :: remaining) current currentState →
      M.SuccessTransport (actualStep item member current actualMethods) (shadowStep item member current shadowMethods)
        actualContext shadowContext currentState) :
    M.SuccessTransport ((forIn' items initial actualStep) actualMethods) ((forIn' items initial shadowStep) shadowMethods)
      actualContext shadowContext state := by
  have auxiliary : ∀ remaining (subset : ∀ item, item ∈ remaining → item ∈ items) current currentState,
      NativeForInPrimeReachable items (fun item member current => actualStep item member current actualMethods)
        actualContext state initial remaining current currentState →
      M.SuccessTransport
        ((forIn' remaining current (fun item member value => actualStep item (subset item member) value)) actualMethods)
        ((forIn' remaining current (fun item member value => shadowStep item (subset item member) value)) shadowMethods)
        actualContext shadowContext currentState := by
    intro remaining
    induction remaining with
    | nil => intro subset current currentState reached; exact M.SuccessTransport.pure _ _ _ _
    | cons item remaining inductionHypothesis =>
      intro subset current currentState reached
      rw [List.forIn'_cons, List.forIn'_cons]
      dsimp only [Bind.bind, ReaderT.bind]
      apply M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks _ _ _ _ _ reached)
      intro selected nextState accepted
      cases selected with
      | done value => exact M.SuccessTransport.pure _ _ _ _
      | yield value => exact inductionHypothesis _ _ _ (.yielded _ reached accepted)
  exact auxiliary items (fun _ member => member) initial state .initial

def TypeChecker.Inner.nativeEtaStructFields (information : ConstructorVal) (first : Expr) (arguments : Array Expr) : TypeChecker.RecM Bool := do
  for member : index in [information.numParams:arguments.size] do
    unless ← isDefEq (.proj information.induct (index - information.numParams) first) (arguments[index]'member.upper) do return false
  return true

def TypeChecker.Inner.nativeEtaStructField (information : ConstructorVal) (first : Expr) (arguments : Array Expr)
    (index : Nat) (inBounds : index < arguments.size) (_ : MProd (Option Bool) PUnit) : TypeChecker.RecM (ForInStep (MProd (Option Bool) PUnit)) := do
  if ← isDefEq (.proj information.induct (index - information.numParams) first) arguments[index] then
    return .yield ⟨none, ⟨⟩⟩
  else return .done ⟨some false, ⟨⟩⟩

def TypeChecker.Inner.nativeEtaStructFieldListStep (information : ConstructorVal) (first : Expr) (arguments : Array Expr)
    (index : Nat) (member : index ∈ List.range' information.numParams (arguments.size - information.numParams))
    (current : MProd (Option Bool) PUnit) : TypeChecker.RecM (ForInStep (MProd (Option Bool) PUnit)) :=
  nativeEtaStructField information first arguments index (by
    rcases List.mem_range'.mp member with ⟨offset, bound, indexing⟩
    omega) current

theorem TypeChecker.Inner.nativeEtaStructFields.list_eq (information : ConstructorVal) (first : Expr) (arguments : Array Expr) :
    nativeEtaStructFields information first arguments = (do
      let returned ← forIn' (List.range' information.numParams (arguments.size - information.numParams))
        ⟨none, ⟨⟩⟩ (nativeEtaStructFieldListStep information first arguments)
      return returned.fst.getD true) := by
  unfold nativeEtaStructFields
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  unfold nativeEtaStructFieldListStep nativeEtaStructField
  simp only [pure_bind]
  congr 1
  funext returned
  cases returned with
  | mk result ignored => cases result <;> rfl

structure NativeEtaStructFieldCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State)
    (information : ConstructorVal) (first : Expr) (arguments : Array Expr) : Prop where
  comparisons : ∀ index remaining current currentState (member : index ∈ List.range' information.numParams (arguments.size - information.numParams)),
    NativeForInPrimeReachable (List.range' information.numParams (arguments.size - information.numParams))
      (fun index member current => TypeChecker.Inner.nativeEtaStructFieldListStep information first arguments index member current actualMethods)
      actualContext state ⟨none, ⟨⟩⟩ (index :: remaining) current currentState →
    TypeChecker.M.SuccessTransport
      (actualMethods.isDefEqCore (.proj information.induct (index - information.numParams) first) (arguments[index]'(by
        rcases List.mem_range'.mp member with ⟨offset, bound, indexing⟩
        omega)))
      (shadowMethods.isDefEqCore (.proj information.induct (index - information.numParams) first) (arguments[index]'(by
        rcases List.mem_range'.mp member with ⟨offset, bound, indexing⟩
        omega))) actualContext shadowContext currentState

theorem TypeChecker.Inner.nativeEtaStructFields.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (information : ConstructorVal) (first : Expr) (arguments : Array Expr)
    (callbacks : NativeEtaStructFieldCallbacks actualMethods shadowMethods actualContext shadowContext state information first arguments) :
    TypeChecker.M.SuccessTransport (nativeEtaStructFields information first arguments actualMethods)
      (nativeEtaStructFields information first arguments shadowMethods) actualContext shadowContext state := by
  rw [list_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (TypeChecker.RecM.forIn'_transport _ _ _ _ _ _ _ _ _ (by
      intro index remaining current currentState member reached
      dsimp only [nativeEtaStructFieldListStep, nativeEtaStructField, Bind.bind, ReaderT.bind]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (isDefEq.transport _ _ _ _ _ _ _ (callbacks.comparisons _ _ _ _ member reached))
      intro equal nextState accepted
      cases equal <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _))
  intro returned returnedState accepted
  exact TypeChecker.M.SuccessTransport.pure _ _ _ _

def nativeConstructorLookup (environment : Kernel.Environment) (name : Name) : Except Kernel.Exception (Option ConstructorVal) := do
  let .ctorInfo information ← environment.get name | return none
  return some information

theorem HeaderAxiomLookupAgreement.nativeConstructorLookup
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) :
    Except.SuccessTransport (Lean4Lean.nativeConstructorLookup actual name) (Lean4Lean.nativeConstructorLookup shadow name) := by
  intro result accepted
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · unfold Lean4Lean.nativeConstructorLookup Kernel.Environment.get at accepted ⊢
    rw [← same]
    cases found : actual.find? name with
    | none => simp only [found, Bind.bind, Except.bind] at accepted; contradiction
    | some information => simpa only [found] using accepted
  · simp only [Lean4Lean.nativeConstructorLookup, Kernel.Environment.get, actualLookup, shadowLookup, headerAxiomInfo,
      Pure.pure, Except.pure, Bind.bind, Except.bind] at accepted ⊢
    exact accepted

theorem HeaderAxiomLookupAgreement.structureLikeOfFalse
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (parent : Name)
    (notStructure : actual.isStructureLike parent = false) : shadow.isStructureLike parent = false := by
  rcases agreement parent with same | ⟨_, header, actualLookup, shadowLookup⟩
  · simpa only [Kernel.Environment.isStructureLike, ← same] using notStructure
  · simp only [Kernel.Environment.isStructureLike, shadowLookup, headerAxiomInfo]

def NativeEtaStructMetadataFrame (actual shadow : Kernel.Environment) (second : Expr) : Prop :=
  ∀ name levels information, second.getAppFn = .const name levels →
    actual.find? name = some (.ctorInfo information) →
    (second.getAppNumArgs == information.numParams + information.numFields) = true →
    actual.isStructureLike information.induct = true → actual.find? information.induct = shadow.find? information.induct

theorem NativeEtaStructMetadataFrame.ofShadowParents
    (agreement : HeaderAxiomLookupAgreement changed actual shadow)
    (parents : ∀ name levels information, second.getAppFn = .const name levels →
      actual.find? name = some (.ctorInfo information) →
      (second.getAppNumArgs == information.numParams + information.numFields) = true →
      actual.isStructureLike information.induct = true →
      ∃ header, shadow.find? information.induct = some (.inductInfo header)) :
    NativeEtaStructMetadataFrame actual shadow second := by
  intro name levels information head lookup arity structureLike
  obtain ⟨header, shadowLookup⟩ := parents name levels information head lookup arity structureLike
  exact agreement.stableInductiveParent information.induct header shadowLookup

structure NativeEtaStructEntryReceipt (context : TypeChecker.Context) (second : Expr) (information : ConstructorVal) : Prop where
  lookup : ∃ name levels, second.getAppFn = .const name levels ∧ context.env.find? name = some (.ctorInfo information)
  arity : (second.getAppNumArgs == information.numParams + information.numFields) = true
  structureLike : context.env.isStructureLike information.induct = true

def TypeChecker.Inner.nativeEtaStructBody (information : ConstructorVal) (first second : Expr) : TypeChecker.RecM Bool := do
  let firstType ← inferType first
  let secondType ← inferType second
  if ← isDefEq firstType secondType then
    nativeEtaStructFields information first second.getAppArgs
  else return false

theorem TypeChecker.Inner.tryEtaStructCore.body_eq (first second : Expr) :
    tryEtaStructCore first second = (do
      let .const name _ := second.getAppFn | return false
      let environment ← TypeChecker.getEnv
      let some information ← nativeConstructorLookup environment name | return false
      unless second.getAppNumArgs == information.numParams + information.numFields do return false
      unless environment.isStructureLike information.induct do return false
      nativeEtaStructBody information first second) := by
  unfold tryEtaStructCore nativeConstructorLookup nativeEtaStructBody nativeEtaStructFields
  simp only [liftM_bind, bind_assoc, pure_bind]
  cases head : second.getAppFn <;> (simp only []; try rfl)
  congr 1
  funext environment
  congr 1
  funext information
  cases information <;> simp only [liftM_pure, pure_bind]
  all_goals rfl

structure NativeEtaStructCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  metadata : NativeEtaStructMetadataFrame actualContext.env shadowContext.env second
  firstInference : ∀ information, NativeEtaStructEntryReceipt actualContext second information →
    TypeChecker.M.SuccessTransport (actualMethods.inferType first true) (shadowMethods.inferType first true)
      actualContext shadowContext state
  secondInference : ∀ information firstType firstState,
    NativeEtaStructEntryReceipt actualContext second information →
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    TypeChecker.M.SuccessTransport (actualMethods.inferType second true) (shadowMethods.inferType second true)
      actualContext shadowContext firstState
  typeComparison : ∀ information firstType firstState secondType secondState,
    NativeEtaStructEntryReceipt actualContext second information →
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    actualMethods.inferType second true actualContext firstState = .ok (secondType, secondState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore firstType secondType)
      (shadowMethods.isDefEqCore firstType secondType) actualContext shadowContext secondState
  fields : ∀ information firstType firstState secondType secondState comparedState,
    NativeEtaStructEntryReceipt actualContext second information →
    actualMethods.inferType first true actualContext state = .ok (firstType, firstState) →
    actualMethods.inferType second true actualContext firstState = .ok (secondType, secondState) →
    TypeChecker.Inner.isDefEq firstType secondType actualMethods actualContext secondState = .ok (true, comparedState) →
    NativeEtaStructFieldCallbacks actualMethods shadowMethods actualContext shadowContext comparedState information first second.getAppArgs

theorem TypeChecker.Inner.nativeEtaStructBody.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (first second : Expr) (information : ConstructorVal)
    (entry : NativeEtaStructEntryReceipt actualContext second information)
    (callbacks : NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (nativeEtaStructBody information first second actualMethods)
      (nativeEtaStructBody information first second shadowMethods) actualContext shadowContext state := by
  dsimp only [nativeEtaStructBody, inferType, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.firstInference _ entry)
  intro firstType firstState firstAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.secondInference _ _ _ entry firstAccepted)
  intro secondType secondState secondAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
    (isDefEq.transport _ _ _ _ _ _ _ (callbacks.typeComparison _ _ _ _ _ entry firstAccepted secondAccepted))
  intro equal comparedState comparisonAccepted
  cases equal with
  | false => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  | true =>
    exact nativeEtaStructFields.transport _ _ _ _ _ _ _ _
      (callbacks.fields _ _ _ _ _ _ entry firstAccepted secondAccepted comparisonAccepted)

theorem TypeChecker.Inner.tryEtaStructCore.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (tryEtaStructCore first second actualMethods)
      (tryEtaStructCore first second shadowMethods) actualContext shadowContext state := by
  intro result accepted
  rw [body_eq] at accepted ⊢
  cases head : second.getAppFn <;> simp only [head] at accepted <;> dsimp only [] at accepted ⊢ <;> try exact accepted
  rename_i name levels
  dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, TypeChecker.getEnv, MonadReader.read, readThe, MonadReaderOf.read,
    ReaderT.read, Bind.bind, ReaderT.bind, StateT.bind, StateT.lift, Pure.pure, ReaderT.pure, StateT.pure,
    Except.pure, Except.bind] at accepted ⊢
  cases lookup : nativeConstructorLookup actualContext.env name with
  | error error => rw [lookup] at accepted; contradiction
  | ok found =>
    have shadowLookup := agreement.nativeConstructorLookup name found lookup
    rw [lookup] at accepted
    rw [shadowLookup]
    dsimp only [Except.bind] at accepted ⊢
    cases found with
    | none => exact accepted
    | some information =>
      have present : actualContext.env.find? name = some (.ctorInfo information) := by
        unfold nativeConstructorLookup Kernel.Environment.get at lookup
        cases constant : actualContext.env.find? name with
        | none => simp only [constant, Bind.bind, Except.bind] at lookup; contradiction
        | some constantInfo =>
          cases constantInfo <;> simp only [constant, Bind.bind, Except.bind, Pure.pure, Except.pure] at lookup
          all_goals cases Except.ok.inj lookup
          all_goals rfl
      cases arity : second.getAppNumArgs == information.numParams + information.numFields with
      | false => simp only [arity, Bool.false_eq_true, if_false] at accepted ⊢; exact accepted
      | true =>
        simp only [arity, if_true] at accepted ⊢
        cases structureLike : actualContext.env.isStructureLike information.induct with
        | false =>
          have shadowFalse := agreement.structureLikeOfFalse information.induct structureLike
          simpa only [structureLike, shadowFalse, Bool.false_eq_true, if_false] using accepted
        | true =>
          have stable := callbacks.metadata name levels information head present arity structureLike
          have shadowTrue := (agreement.structureLike information.induct stable).symm.trans structureLike
          simp only [structureLike, shadowTrue, if_true] at accepted ⊢
          have entry : NativeEtaStructEntryReceipt actualContext second information :=
            { lookup := ⟨name, levels, head, present⟩, arity, structureLike }
          exact nativeEtaStructBody.transport _ _ _ _ _ _ _ _ entry callbacks result accepted

theorem TypeChecker.Inner.tryEtaStruct.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (forward : NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second)
    (backward : ∀ nextState, tryEtaStructCore first second actualMethods actualContext state = .ok (false, nextState) →
      NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext nextState second first) :
    TypeChecker.M.SuccessTransport (tryEtaStruct first second actualMethods)
      (tryEtaStruct first second shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.RecM.or_transport
  · exact tryEtaStructCore.transport _ _ _ _ agreement _ _ _ forward
  · intro nextState accepted
    exact tryEtaStructCore.transport _ _ _ _ agreement _ _ _ (backward _ accepted)

def nativeUnitLikeMetadata (environment : Kernel.Environment) (parent : Name) : Except Kernel.Exception Bool := do
  let .inductInfo { isRec := false, ctors := [constructor], numIndices := 0, .. } ← environment.get parent | return false
  let some information ← nativeConstructorLookup environment constructor | return false
  return information.numFields == 0

theorem nativeUnitLikeMetadata.transport
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (parent : Name)
    (metadata : NativeProjectionMetadataFrame actual shadow parent) :
    Except.SuccessTransport (nativeUnitLikeMetadata actual parent) (nativeUnitLikeMetadata shadow parent) := by
  intro result accepted
  rcases agreement parent with same | ⟨_, header, actualLookup, shadowLookup⟩
  · unfold nativeUnitLikeMetadata Kernel.Environment.get at accepted ⊢
    rw [← same]
    cases found : actual.find? parent with
    | none => simp only [found, Bind.bind, Except.bind] at accepted; contradiction
    | some information =>
      simp only [found, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted ⊢
      cases information <;> try exact accepted
      rename_i header
      cases header with
      | mk base parameters indices families constructors nested recursive safety reflexive =>
        cases base
        cases indices <;> cases recursive <;> cases constructors <;> try exact accepted
        all_goals
          rename_i constructor remaining
          cases remaining with
          | cons another remaining => exact accepted
          | nil =>
            first
            | exact accepted
            | exact Except.SuccessTransport.bind _ _ _ _ (agreement.nativeConstructorLookup constructor)
                (fun selected _ => by cases selected <;> exact Except.SuccessTransport.refl _) result accepted
  · rcases metadata header actualLookup with stable | missing
    · rw [actualLookup, shadowLookup] at stable
      dsimp only [headerAxiomInfo] at stable
      cases Option.some.inj stable
    · unfold nativeUnitLikeMetadata Kernel.Environment.get at accepted ⊢
      simp only [actualLookup, shadowLookup, headerAxiomInfo, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted ⊢
      cases header with
      | mk base parameters indices families constructors nested recursive safety reflexive =>
        cases base
        cases indices <;> cases recursive <;> cases constructors <;> try exact accepted
        all_goals
          rename_i constructor remaining
          cases remaining with
          | cons another remaining => exact accepted
          | nil =>
            first
            | exact accepted
            | have absent := missing constructor (by simp)
              simp only [nativeConstructorLookup, Kernel.Environment.get, absent, Bind.bind, Except.bind] at accepted
              contradiction

def TypeChecker.Inner.nativeUnitLikeBody (normalized second : Expr) : TypeChecker.RecM Bool := do
  let .const parent _ := normalized.getAppFn | return false
  let environment ← TypeChecker.getEnv
  if ← nativeUnitLikeMetadata environment parent then
    isDefEqCore normalized (← inferType second)
  else return false

theorem TypeChecker.Inner.isDefEqUnitLike.body_eq (first second : Expr) :
    isDefEqUnitLike first second = (do
      let normalized ← whnf (← inferType first)
      nativeUnitLikeBody normalized second) := by
  unfold isDefEqUnitLike nativeUnitLikeBody nativeUnitLikeMetadata nativeConstructorLookup
  simp only [liftM_bind, bind_assoc]
  congr 1
  funext inferred
  congr 1
  funext normalized
  cases head : normalized.getAppFn <;> (simp only []; try rfl)
  congr 1
  funext environment
  congr 1
  funext information
  cases information <;> (try simp only [liftM_pure, pure_bind]; try rfl)
  rename_i header
  cases header with
  | mk base parameters indices families constructors nested recursive safety reflexive =>
    cases base
    cases indices <;> cases recursive <;> cases constructors <;> (try simp only []; try rfl)
    rename_i constructor remaining
    cases remaining with
    | cons another remaining => rfl
    | nil =>
      simp only [liftM_bind, bind_assoc]
      congr 1
      funext constructorInfo
      cases constructorInfo <;> (simp only [liftM_pure, pure_bind]; try rfl)
      rename_i constructorValue
      cases constructorValue with
      | mk base induct index parameters fields safety =>
        cases base
        cases fields <;> rfl

structure NativeUnitLikeBodyCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (normalized second : Expr) : Prop where
  metadata : ∀ parent levels, normalized.getAppFn = .const parent levels →
    NativeProjectionMetadataFrame actualContext.env shadowContext.env parent
  inference : ∀ parent levels metadataState, normalized.getAppFn = .const parent levels →
    (liftM (nativeUnitLikeMetadata actualContext.env parent) : TypeChecker.M Bool) actualContext state = .ok (true, metadataState) →
    TypeChecker.M.SuccessTransport (actualMethods.inferType second true) (shadowMethods.inferType second true)
      actualContext shadowContext metadataState
  comparison : ∀ parent levels metadataState secondType secondState,
    normalized.getAppFn = .const parent levels →
    (liftM (nativeUnitLikeMetadata actualContext.env parent) : TypeChecker.M Bool) actualContext state = .ok (true, metadataState) →
    actualMethods.inferType second true actualContext metadataState = .ok (secondType, secondState) →
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore normalized secondType)
      (shadowMethods.isDefEqCore normalized secondType) actualContext shadowContext secondState

theorem TypeChecker.Inner.nativeUnitLikeBody.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (normalized second : Expr)
    (callbacks : NativeUnitLikeBodyCallbacks actualMethods shadowMethods actualContext shadowContext state normalized second) :
    TypeChecker.M.SuccessTransport (nativeUnitLikeBody normalized second actualMethods)
      (nativeUnitLikeBody normalized second shadowMethods) actualContext shadowContext state := by
  unfold nativeUnitLikeBody
  cases head : normalized.getAppFn <;> (simp only []; try exact TypeChecker.M.SuccessTransport.pure _ _ _ _)
  rename_i parent levels
  intro result accepted
  dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, TypeChecker.getEnv, MonadReader.read, readThe, MonadReaderOf.read,
    ReaderT.read, Bind.bind, ReaderT.bind, StateT.bind, StateT.lift, Pure.pure, ReaderT.pure, StateT.pure,
    Except.pure, Except.bind] at accepted ⊢
  cases metadataFound : nativeUnitLikeMetadata actualContext.env parent with
  | error error => rw [metadataFound] at accepted; contradiction
  | ok eligible =>
    have shadowFound := nativeUnitLikeMetadata.transport agreement parent (callbacks.metadata _ _ head) eligible metadataFound
    rw [metadataFound] at accepted
    rw [shadowFound]
    dsimp only [Except.bind] at accepted ⊢
    cases eligible with
    | false => exact accepted
    | true =>
      have metadataAccepted : (liftM (nativeUnitLikeMetadata actualContext.env parent) : TypeChecker.M Bool)
          actualContext state = .ok (true, state) := by
        dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rw [metadataFound]
      have continuation : TypeChecker.M.SuccessTransport
          (do let secondType ← actualMethods.inferType second true; actualMethods.isDefEqCore normalized secondType)
          (do let secondType ← shadowMethods.inferType second true; shadowMethods.isDefEqCore normalized secondType)
          actualContext shadowContext state := by
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.inference _ _ _ head metadataAccepted)
        intro secondType secondState secondAccepted
        exact callbacks.comparison _ _ _ _ _ head metadataAccepted secondAccepted
      exact continuation result accepted

structure NativeUnitLikeCallbacks (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) (state : TypeChecker.State) (first second : Expr) : Prop where
  inference : TypeChecker.M.SuccessTransport (actualMethods.inferType first true) (shadowMethods.inferType first true)
    actualContext shadowContext state
  normalization : ∀ inferred inferredState, actualMethods.inferType first true actualContext state = .ok (inferred, inferredState) →
    TypeChecker.M.SuccessTransport (actualMethods.whnf inferred) (shadowMethods.whnf inferred) actualContext shadowContext inferredState
  bodies : ∀ inferred inferredState normalized normalizedState,
    actualMethods.inferType first true actualContext state = .ok (inferred, inferredState) →
    actualMethods.whnf inferred actualContext inferredState = .ok (normalized, normalizedState) →
    NativeUnitLikeBodyCallbacks actualMethods shadowMethods actualContext shadowContext normalizedState normalized second

theorem TypeChecker.Inner.isDefEqUnitLike.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (first second : Expr)
    (callbacks : NativeUnitLikeCallbacks actualMethods shadowMethods actualContext shadowContext state first second) :
    TypeChecker.M.SuccessTransport (isDefEqUnitLike first second actualMethods)
      (isDefEqUnitLike first second shadowMethods) actualContext shadowContext state := by
  rw [body_eq]
  dsimp only [inferType, whnf, Bind.bind, ReaderT.bind]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ callbacks.inference
  intro inferred inferredState inferredAccepted
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (callbacks.normalization _ _ inferredAccepted)
  intro normalized normalizedState normalizedAccepted
  exact nativeUnitLikeBody.transport _ _ _ _ agreement _ _ _ (callbacks.bodies _ _ _ _ inferredAccepted normalizedAccepted)

end Lean4Lean
