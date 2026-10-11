import Lean4Lean.Verify.InductiveHeaderRecursorTransport

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment

theorem headerAxiomView.quotInit (env : Kernel.Environment) (infos : List InductiveVal) :
    (headerAxiomView env infos).quotInit = env.quotInit := by
  induction infos generalizing env with
  | nil => rfl
  | cons info infos inductionHypothesis =>
    change (headerAxiomView (env.add (headerAxiomInfo info)) infos).quotInit = env.quotInit
    exact inductionHypothesis _

private theorem registerHeadersQuotInit (infos : List InductiveVal) (env : Kernel.Environment) (allowPrimitive : Bool) :
    (infos.foldlM (fun (current : Kernel.Environment) (info : InductiveVal) => do
      current.checkName info.name allowPrimitive
      pure (current.add (.inductInfo info))) env).WF (fun result => result.quotInit = env.quotInit) := by
  induction infos generalizing env with
  | nil =>
    intro result accepted
    cases Except.ok.inj accepted
    rfl
  | cons info infos inductionHypothesis =>
    intro result accepted
    simp only [List.foldlM_cons, bind_assoc, pure_bind] at accepted
    cases checked : env.checkName info.name allowPrimitive with
    | error error =>
      simp only [checked, Bind.bind, Except.bind] at accepted
      cases accepted
    | ok value =>
      simp only [checked, Bind.bind, Except.bind] at accepted
      exact inductionHypothesis (env.add (.inductInfo info)) result accepted

theorem AddInductive.declareInductiveTypes.quotInit (stats : InductiveStats) (parameters : Nat)
    (types : Array InductiveType) (nested : Nat) (isUnsafe : Bool) (context : Context) :
    (declareInductiveTypes stats parameters types nested isUnsafe context).WF
      (fun result => result.quotInit = context.env.quotInit) := by
  unfold declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  exact registerHeadersQuotInit _ _ _

structure NativeRecursorEntryReceipt (context : TypeChecker.Context) (expression : Expr)
    (info : RecursorVal) (major : Expr) : Prop where
  constant : expression.getAppFn.isConst = true
  recursor : context.env.find? expression.getAppFn.constName! = some (.recInfo info)
  selected : expression.getAppArgs[info.getMajorIdx]? = some major

structure NativeRecursorMajorReceipt (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (info : RecursorVal) (major adapted : Expr)
    (adaptedState : TypeChecker.State) : Prop extends NativeRecursorEntryReceipt context expression info major where
  adaptation : ((if info.k then
      toCtorWhenK context.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq info major
    else pure major) methods) context state = .ok (adapted, adaptedState)

theorem inductiveReduceRec.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (expression : Expr)
    (parents : ∀ info major, NativeRecursorEntryReceipt actualContext expression info major →
      actualContext.env.find? info.getMajorInduct = shadowContext.env.find? info.getMajorInduct)
    (kTypes : ∀ info major, NativeRecursorEntryReceipt actualContext expression info major →
      info.k = true → TypeChecker.M.SuccessTransport
        (do actualMethods.whnf (← actualMethods.inferType major true))
        (do shadowMethods.whnf (← shadowMethods.inferType major true)) actualContext shadowContext state)
    (kComparisons : ∀ info major, NativeRecursorEntryReceipt actualContext expression info major →
      info.k = true → ∀ type finalState constructor,
      (do actualMethods.whnf (← actualMethods.inferType major true)) actualContext state = .ok (type, finalState) →
      type.getAppFn.constName! = info.getMajorInduct → mkNullaryCtor actualContext.env type info.numParams = some constructor →
      TypeChecker.M.SuccessTransport
        (do TypeChecker.Inner.isDefEq type (← actualMethods.inferType constructor true) actualMethods)
        (do TypeChecker.Inner.isDefEq type (← shadowMethods.inferType constructor true) shadowMethods)
        actualContext shadowContext finalState)
    (normalization : ∀ info major adapted adaptedState,
      NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState →
      TypeChecker.M.SuccessTransport (actualMethods.whnf adapted) (shadowMethods.whnf adapted)
        actualContext shadowContext adaptedState)
    (strings : ∀ info major adapted adaptedState text normalizedState,
      NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState →
      actualMethods.whnf adapted actualContext adaptedState = .ok (.lit (.strVal text), normalizedState) →
      TypeChecker.M.SuccessTransport (actualMethods.whnf (.strLitToConstructor text))
        (shadowMethods.whnf (.strLitToConstructor text)) actualContext shadowContext normalizedState)
    (structureTypes : ∀ info major adapted adaptedState normalized normalizedState,
      NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState →
      actualMethods.whnf adapted actualContext adaptedState = .ok (normalized, normalizedState) →
      normalized.isLit = false → actualContext.env.isStructureLike info.getMajorInduct = true →
      (normalized.isConstructorApp?' actualContext.env).isSome = false → TypeChecker.M.SuccessTransport
        (do actualMethods.whnf (← actualMethods.inferType normalized true))
        (do shadowMethods.whnf (← shadowMethods.inferType normalized true)) actualContext shadowContext normalizedState)
    (structureSorts : ∀ info major adapted adaptedState normalized normalizedState,
      NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState →
      actualMethods.whnf adapted actualContext adaptedState = .ok (normalized, normalizedState) →
      normalized.isLit = false → actualContext.env.isStructureLike info.getMajorInduct = true →
      (normalized.isConstructorApp?' actualContext.env).isSome = false → ∀ type finalState,
      (do actualMethods.whnf (← actualMethods.inferType normalized true)) actualContext normalizedState = .ok (type, finalState) →
      type.getAppFn.isConstOf info.getMajorInduct = true → TypeChecker.M.SuccessTransport
        (do actualMethods.whnf (← actualMethods.inferType type true))
        (do shadowMethods.whnf (← shadowMethods.inferType type true)) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport
      (inductiveReduceRec actualContext.env expression TypeChecker.Inner.whnf TypeChecker.Inner.inferType
        TypeChecker.Inner.isDefEq actualMethods)
      (inductiveReduceRec shadowContext.env expression TypeChecker.Inner.whnf TypeChecker.Inner.inferType
        TypeChecker.Inner.isDefEq shadowMethods) actualContext shadowContext state := by
  unfold inductiveReduceRec
  cases head : expression.getAppFn <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  rename_i recursorName levels
  dsimp only
  rcases agreement recursorName with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [← same]
    cases found : actualContext.env.find? recursorName with
    | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    | some information =>
      cases information <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      rename_i info
      have recursor : actualContext.env.find? expression.getAppFn.constName! = some (.recInfo info) := by
        simpa only [head, Expr.constName!] using found
      dsimp only
      cases selected : expression.getAppArgs[info.getMajorIdx]? with
      | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | some major =>
        have entry : NativeRecursorEntryReceipt actualContext expression info major :=
          ⟨by simp only [head, Expr.isConst], recursor, selected⟩
        simp only [pure_bind]
        dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
        by_cases isK : info.k = true
        case' pos =>
          simp only [isK, if_true]
          dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
          apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
            (toCtorWhenK.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext agreement
              state info major isK (parents info major entry) (kTypes info major entry isK)
              (kComparisons info major entry isK))
          intro adapted adaptedState accepted
          have receipt : NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState :=
            ⟨entry, by simpa only [isK, if_true] using accepted⟩
        case' neg =>
          have noK := Bool.eq_false_iff.mpr isK
          simp only [noK, Bool.false_eq_true, if_false]
          let adapted := major
          let adaptedState := state
          have receipt : NativeRecursorMajorReceipt actualMethods actualContext state expression info major adapted adaptedState :=
            ⟨entry, by simp only [noK, Bool.false_eq_true, if_false]; rfl⟩
        all_goals
          try dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
          apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (normalization info major adapted adaptedState receipt)
          intro normalized normalizedState normalizedAccepted
          cases normalized with
          | lit literal =>
            cases literal with
            | natVal value =>
              dsimp only
              cases rule : getRecRuleFor info (.natLitToConstructor value) <;>
                repeat' first | exact TypeChecker.M.SuccessTransport.pure _ _ _ _ | dsimp only | split
            | strVal text =>
              dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
              apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
                (strings info major adapted adaptedState text normalizedState receipt normalizedAccepted)
              intro expanded expandedState _
              cases rule : getRecRuleFor info expanded <;>
                repeat' first | exact TypeChecker.M.SuccessTransport.pure _ _ _ _ | dsimp only | split
          | _ =>
            dsimp only [Bind.bind, ReaderT.bind]
            apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
              (toCtorWhenStruct.headerAxiomTransport actualMethods shadowMethods actualContext shadowContext agreement
                normalizedState info.getMajorInduct _ (parents info major entry)
                (structureTypes info major adapted adaptedState _ normalizedState receipt normalizedAccepted rfl)
                (structureSorts info major adapted adaptedState _ normalizedState receipt normalizedAccepted rfl))
            intro expanded expandedState _
            cases rule : getRecRuleFor info expanded <;>
              repeat' first | exact TypeChecker.M.SuccessTransport.pure _ _ _ _ | dsimp only | split
  · rw [actualLookup, shadowLookup]
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem quotReduceRec.transport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr)
    (liftNormalization : expression.getAppFn.isConstOf ``Quot.lift = true → ∀ inBounds : 5 < expression.getAppArgs.size,
      TypeChecker.M.SuccessTransport (actualMethods.whnf expression.getAppArgs[5])
        (shadowMethods.whnf expression.getAppArgs[5]) actualContext shadowContext state)
    (indNormalization : expression.getAppFn.isConstOf ``Quot.ind = true → ∀ inBounds : 4 < expression.getAppArgs.size,
      TypeChecker.M.SuccessTransport (actualMethods.whnf expression.getAppArgs[4])
        (shadowMethods.whnf expression.getAppArgs[4]) actualContext shadowContext state) :
    TypeChecker.M.SuccessTransport (quotReduceRec expression TypeChecker.Inner.whnf actualMethods)
      (quotReduceRec expression TypeChecker.Inner.whnf shadowMethods) actualContext shadowContext state := by
  unfold quotReduceRec
  cases head : expression.getAppFn <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  rename_i name levels
  dsimp only
  by_cases lift : name == ``Quot.lift
  · simp only [lift, if_true]
    by_cases inBounds : 5 < expression.getAppArgs.size
    · simp only [inBounds, dite_true]
      dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
        (liftNormalization (by simpa only [head, Expr.isConstOf] using lift) inBounds)
      intro normalized finalState _
      repeat' first | exact TypeChecker.M.SuccessTransport.pure _ _ _ _ | dsimp only | split
    · simp only [inBounds, dite_false]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  · simp only [Bool.eq_false_iff.mpr lift, Bool.false_eq_true, if_false]
    by_cases ind : name == ``Quot.ind
    · simp only [ind, if_true]
      by_cases inBounds : 4 < expression.getAppArgs.size
      · simp only [inBounds, dite_true]
        dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (indNormalization (by simpa only [head, Expr.isConstOf] using ind) inBounds)
        intro normalized finalState _
        repeat' first | exact TypeChecker.M.SuccessTransport.pure _ _ _ _ | dsimp only | split
      · simp only [inBounds, dite_false]
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    · simp only [Bool.eq_false_iff.mpr ind, Bool.false_eq_true, if_false]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem TypeChecker.Inner.reduceRecursor.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (quotients : actualContext.env.quotInit = true → TypeChecker.M.SuccessTransport
      (quotReduceRec expression TypeChecker.Inner.whnf actualMethods)
      (quotReduceRec expression TypeChecker.Inner.whnf shadowMethods) actualContext shadowContext state)
    (inductives : ∀ finalState,
      ((if actualContext.env.quotInit then quotReduceRec expression TypeChecker.Inner.whnf else pure none) actualMethods)
        actualContext state = .ok (none, finalState) → TypeChecker.M.SuccessTransport
      (inductiveReduceRec actualContext.env expression
        (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
        TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq actualMethods)
      (inductiveReduceRec shadowContext.env expression
        (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
        TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq shadowMethods) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj shadowMethods)
      actualContext shadowContext state := by
  change TypeChecker.M.SuccessTransport
    ((do
      if actualContext.env.quotInit then
        if let some reduced ← quotReduceRec expression TypeChecker.Inner.whnf then return some reduced
      if let some reduced ← inductiveReduceRec actualContext.env expression
          (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
          TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq then return some reduced
      return none) actualMethods)
    ((do
      if shadowContext.env.quotInit then
        if let some reduced ← quotReduceRec expression TypeChecker.Inner.whnf then return some reduced
      if let some reduced ← inductiveReduceRec shadowContext.env expression
          (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
          TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq then return some reduced
      return none) shadowMethods) actualContext shadowContext state
  rw [← quotInit]
  by_cases initialized : actualContext.env.quotInit = true
  case' pos =>
    simp only [initialized, if_true, pure_bind]
    dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (quotients initialized)
    intro quotientResult quotientState accepted
    cases quotientResult <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    have continuation := inductives quotientState (by simpa only [initialized, if_true] using accepted)
  case' neg =>
    have uninitialized := Bool.eq_false_iff.mpr initialized
    simp only [uninitialized, Bool.false_eq_true, if_false, pure_bind]
    let quotientState := state
    have continuation := inductives quotientState (by simp only [uninitialized, Bool.false_eq_true, if_false]; rfl)
  all_goals
    try dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ continuation
    intro reduced finalState _
    cases reduced <;> exact TypeChecker.M.SuccessTransport.pure _ _ _ _

end Lean4Lean
