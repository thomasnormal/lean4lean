import Lean4Lean.Verify.TypeChecker.InferenceHeadFrame
import Lean4Lean.Verify.InductiveHeaderDefEqCoreTransport

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TypeChecker.RecM.toLBoolM_headWF (action : TypeChecker.RecM Bool) (methods : TypeChecker.Methods)
    (valid : (action methods).HeadWF (fun _ => True)) :
    (toLBoolM action methods).HeadWF (fun _ => True) := by
  dsimp only [toLBoolM, Bind.bind, ReaderT.bind]
  exact valid.bind fun _ _ => .pure trivial

theorem TypeChecker.RecM.or_headWF (first second : TypeChecker.RecM Bool) (methods : TypeChecker.Methods)
    (firstFrame : (first methods).HeadWF (fun _ => True))
    (secondFrame : (second methods).HeadWF (fun _ => True)) :
    ((first <||> second) methods).HeadWF (fun _ => True) := by
  dsimp only [orM, Bind.bind, ReaderT.bind]
  refine firstFrame.bind fun equal _ => ?_
  cases equal
  · exact secondFrame
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.RecM.forInListPrime_headWF (elements : List Element) (initial : Value)
    (body : (element : Element) → element ∈ elements → Value → TypeChecker.RecM (ForInStep Value))
    (methods : TypeChecker.Methods)
    (framed : ∀ element member value, (body element member value methods).HeadWF (fun _ => True)) :
    (forIn' elements initial body methods).HeadWF (fun _ => True) := by
  have auxiliary : ∀ (remaining : List Element) (subset : ∀ element, element ∈ remaining → element ∈ elements) value,
      (forIn' remaining value (fun element member current => body element (subset element member) current)
        methods).HeadWF (fun _ => True) := by
    intro remaining
    induction remaining with
    | nil => intro subset value; exact TypeChecker.M.HeadWF.pure trivial
    | cons element remaining inductionHypothesis =>
      intro subset value
      rw [List.forIn'_cons]
      dsimp only [Bind.bind, ReaderT.bind]
      refine (framed _ _ value).bind fun step _ => ?_
      cases step
      · exact TypeChecker.M.HeadWF.pure trivial
      · exact inductionHypothesis _ _
  exact auxiliary elements (fun _ member => member) initial

theorem TypeChecker.Inner.nativeBinderContinuation.headWF (name : Name) (binder : BinderInfo)
    (domain firstBody secondBody : Expr) (substitution : Array Expr)
    (next : Array Expr → TypeChecker.RecM Bool) (methods : TypeChecker.Methods)
    (framed : ∀ substitution, (next substitution methods).HeadWF (fun _ => True)) :
    (nativeBinderContinuation name binder domain firstBody secondBody substitution next methods).HeadWF
      (fun _ => True) := by
  unfold nativeBinderContinuation
  split
  · exact withLocalDecl.headWF _ _ _ _ methods _ fun _ => framed _
  · exact framed _

theorem TypeChecker.Inner.nativeBinderComparisonStep.headWF (name : Name) (binder : BinderInfo)
    (firstDomain secondDomain firstBody secondBody : Expr) (substitution : Array Expr)
    (next : Array Expr → TypeChecker.RecM Bool) (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (framed : ∀ substitution, (next substitution methods).HeadWF (fun _ => True)) :
    (nativeBinderComparisonStep name binder firstDomain secondDomain firstBody secondBody substitution next
      methods).HeadWF (fun _ => True) := by
  unfold nativeBinderComparisonStep
  split
  · exact nativeBinderContinuation.headWF _ _ _ _ _ _ _ methods framed
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
    cases equal <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    · exact TypeChecker.M.HeadWF.pure trivial
    · exact nativeBinderContinuation.headWF _ _ _ _ _ _ _ methods framed

theorem TypeChecker.Inner.isDefEqLambda.headWF (first second : Expr) (substitution : Array Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqLambda first second substitution methods).HeadWF (fun _ => True) := by
  induction first generalizing second substitution with
  | lam name domain body binder domainIH bodyIH =>
    cases second <;> try exact isDefEq.headWF _ _ methods valid
    rw [isDefEqLambda.lam_eq]
    exact nativeBinderComparisonStep.headWF _ _ _ _ _ _ _ _ methods valid fun _ => bodyIH _ _
  | _ => cases second <;> exact isDefEq.headWF _ _ methods valid

theorem TypeChecker.Inner.isDefEqForall.headWF (first second : Expr) (substitution : Array Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqForall first second substitution methods).HeadWF (fun _ => True) := by
  induction first generalizing second substitution with
  | forallE name domain body binder domainIH bodyIH =>
    cases second <;> try exact isDefEq.headWF _ _ methods valid
    rw [isDefEqForall.forall_eq]
    exact nativeBinderComparisonStep.headWF _ _ _ _ _ _ _ _ methods valid fun _ => bodyIH _ _
  | _ => cases second <;> exact isDefEq.headWF _ _ methods valid

theorem TypeChecker.Inner.nativeQuickProbe.headWF (first second : Expr) (useHash : Bool) :
    (nativeQuickProbe first second useHash).HeadWF (fun _ => True) := by
  intro context state caches result finalState accepted
  unfold nativeQuickProbe at accepted
  generalize probeEq : state.eqvManager.isEquiv useHash first second = probe at accepted
  rcases probe with ⟨equal, manager⟩
  cases accepted
  exact ⟨caches, trivial⟩

theorem TypeChecker.Inner.nativeQuickBody.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeQuickBody first second methods).HeadWF (fun _ => True) := by
  unfold nativeQuickBody
  cases first <;> cases second <;> first
    | exact TypeChecker.RecM.toLBoolM_headWF _ methods (isDefEqLambda.headWF _ _ _ methods valid)
    | exact TypeChecker.RecM.toLBoolM_headWF _ methods (isDefEqForall.headWF _ _ _ methods valid)
    | exact TypeChecker.RecM.toLBoolM_headWF _ methods (isDefEq.headWF _ _ methods valid)
    | exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.quickIsDefEq.headWF (first second : Expr) (useHash : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (quickIsDefEq first second useHash methods).HeadWF (fun _ => True) := by
  rw [quickIsDefEq.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  refine (nativeQuickProbe.headWF first second useHash).bind fun equal _ => ?_
  cases equal
  · exact nativeQuickBody.headWF first second methods valid
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.isDefEqArgs.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqArgs first second methods).HeadWF (fun _ => True) := by
  induction first generalizing second with
  | app function argument functionIH argumentIH =>
    cases second <;> try exact TypeChecker.M.HeadWF.pure trivial
    unfold isDefEqArgs
    dsimp only [Bind.bind, ReaderT.bind]
    refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
    cases equal
    · exact TypeChecker.M.HeadWF.pure trivial
    · exact functionIH _
  | _ => cases second <;> exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.isDefEqApp.loop_headWF (firstArguments secondArguments : Array Expr)
    (sameSize : firstArguments.size = secondArguments.size) (index : Nat)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqApp.loop firstArguments secondArguments sameSize index methods).HeadWF (fun _ => True) := by
  generalize distanceEq : firstArguments.size - index = distance
  induction distance using Nat.strongRecOn generalizing index with
  | ind distance inductionHypothesis =>
    rw [isDefEqApp.loop.eq_def]
    split
    · rename_i inRange
      dsimp only [Bind.bind, ReaderT.bind]
      refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
      cases equal
      · exact TypeChecker.M.HeadWF.pure trivial
      · exact inductionHypothesis _ (by omega) (index + 1) rfl
    · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.isDefEqApp.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqApp first second methods).HeadWF (fun _ => True) := by
  unfold isDefEqApp
  simp only [pure_bind]
  split
  · rw [Expr.withApp_eq, Expr.withApp_eq]
    split
    · dsimp only [Bind.bind, ReaderT.bind]
      refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
      cases equal
      · exact TypeChecker.M.HeadWF.pure trivial
      · exact isDefEqApp.loop_headWF _ _ _ 0 methods valid
    · exact TypeChecker.M.HeadWF.pure trivial
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.tryEtaExpansionCore.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryEtaExpansionCore first second methods).HeadWF (fun _ => True) := by
  unfold tryEtaExpansionCore
  split
  · dsimp only [Bind.bind, ReaderT.bind, inferType, whnf]
    refine (valid.inferType second true).bind fun inferred _ => ?_
    refine (valid.whnf inferred).bind fun normalized _ => ?_
    cases normalized <;> first | exact isDefEq.headWF _ _ methods valid | exact TypeChecker.M.HeadWF.pure trivial
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.tryEtaExpansion.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryEtaExpansion first second methods).HeadWF (fun _ => True) :=
  TypeChecker.RecM.or_headWF _ _ methods
    (tryEtaExpansionCore.headWF first second methods valid) (tryEtaExpansionCore.headWF second first methods valid)

theorem TypeChecker.Inner.isDefEqProofIrrel.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqProofIrrel first second methods).HeadWF (fun _ => True) := by
  unfold isDefEqProofIrrel
  dsimp only [Bind.bind, ReaderT.bind, inferType]
  refine (valid.inferType first true).bind fun inferred _ => ?_
  refine (isProp.headWF inferred methods valid).bind fun proposition _ => ?_
  cases proposition <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, inferType]
    refine (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind fun _ _ => ?_
    refine (valid.inferType second true).bind fun secondType _ => ?_
    exact TypeChecker.RecM.toLBoolM_headWF _ methods (isDefEq.headWF _ _ methods valid)

theorem TypeChecker.Inner.isDefEqOffset.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqOffset first second methods).HeadWF (fun _ => True) := by
  unfold isDefEqOffset
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · cases isNatSuccOf? first <;> cases isNatSuccOf? second <;> first
      | exact TypeChecker.RecM.toLBoolM_headWF _ methods (valid.isDefEqCore _ _)
      | exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.tryStringLitExpansionCore.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryStringLitExpansionCore first second methods).HeadWF (fun _ => True) := by
  unfold tryStringLitExpansionCore
  cases first <;> try exact TypeChecker.M.HeadWF.pure trivial
  rename_i literal
  cases literal <;> try exact TypeChecker.M.HeadWF.pure trivial
  cases second <;> try exact TypeChecker.M.HeadWF.pure trivial
  simp only [pure_bind]
  split
  · exact TypeChecker.RecM.toLBoolM_headWF (isDefEqCore _ _) methods (valid.isDefEqCore _ _)
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.tryStringLitExpansion.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryStringLitExpansion first second methods).HeadWF (fun _ => True) := by
  unfold tryStringLitExpansion
  dsimp only [Bind.bind, ReaderT.bind]
  refine (tryStringLitExpansionCore.headWF _ _ methods valid).bind fun equal _ => ?_
  cases equal <;> first | exact tryStringLitExpansionCore.headWF _ _ methods valid | exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeEtaStructField.headWF (information : ConstructorVal) (first : Expr)
    (arguments : Array Expr) (index : Nat) (inBounds : index < arguments.size)
    (current : MProd (Option Bool) PUnit) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeEtaStructField information first arguments index inBounds current methods).HeadWF (fun _ => True) := by
  unfold nativeEtaStructField
  dsimp only [Bind.bind, ReaderT.bind]
  refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
  cases equal <;> exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeEtaStructFields.headWF (information : ConstructorVal) (first : Expr)
    (arguments : Array Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeEtaStructFields information first arguments methods).HeadWF (fun _ => True) := by
  rw [nativeEtaStructFields.list_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  refine (TypeChecker.RecM.forInListPrime_headWF _ _ _ methods ?_).bind fun _ _ => .pure trivial
  intro index member current
  exact nativeEtaStructField.headWF _ _ _ _ _ current methods valid

theorem TypeChecker.Inner.nativeEtaStructBody.headWF (information : ConstructorVal) (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeEtaStructBody information first second methods).HeadWF (fun _ => True) := by
  unfold nativeEtaStructBody
  dsimp only [Bind.bind, ReaderT.bind, inferType]
  refine (valid.inferType first true).bind fun firstType _ => ?_
  refine (valid.inferType second true).bind fun secondType _ => ?_
  refine (isDefEq.headWF firstType secondType methods valid).bind fun equal _ => ?_
  cases equal
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact nativeEtaStructFields.headWF _ _ _ methods valid

theorem TypeChecker.Inner.tryEtaStructCore.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryEtaStructCore first second methods).HeadWF (fun _ => True) := by
  rw [tryEtaStructCore.body_eq]
  cases second.getAppFn <;> try exact TypeChecker.M.HeadWF.pure trivial
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  refine (TypeChecker.M.HeadWF.liftExcept _).bind fun information _ => ?_
  cases information
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only
    split
    · split
      · exact nativeEtaStructBody.headWF _ _ _ methods valid
      · exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.tryEtaStruct.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryEtaStruct first second methods).HeadWF (fun _ => True) :=
  TypeChecker.RecM.or_headWF _ _ methods
    (tryEtaStructCore.headWF first second methods valid) (tryEtaStructCore.headWF second first methods valid)

theorem TypeChecker.Inner.nativeUnitLikeBody.headWF (normalized second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeUnitLikeBody normalized second methods).HeadWF (fun _ => True) := by
  unfold nativeUnitLikeBody
  cases normalized.getAppFn <;> try exact TypeChecker.M.HeadWF.pure trivial
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  refine (TypeChecker.M.HeadWF.liftExcept _).bind fun unitLike _ => ?_
  cases unitLike
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact (valid.inferType second true).bind fun inferred _ => valid.isDefEqCore normalized inferred

theorem TypeChecker.Inner.isDefEqUnitLike.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqUnitLike first second methods).HeadWF (fun _ => True) := by
  rw [isDefEqUnitLike.body_eq]
  dsimp only [Bind.bind, ReaderT.bind, inferType, whnf]
  refine (valid.inferType first true).bind fun inferred _ => ?_
  refine (valid.whnf inferred).bind fun normalized _ => ?_
  exact nativeUnitLikeBody.headWF normalized second methods valid

theorem TypeChecker.Inner.cacheFailure.headWF (first second : Expr) :
    (cacheFailure first second).HeadWF (fun _ => True) :=
  TypeChecker.M.HeadWF.modify _ fun _ caches => caches

theorem TypeChecker.Inner.tryUnfoldProjApp.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (tryUnfoldProjApp expression methods).HeadWF (fun _ => True) := by
  unfold tryUnfoldProjApp
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, whnfCore]
    refine (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind fun _ _ => ?_
    exact (valid.whnfCore expression false false).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.nativeDeltaUnfold.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDeltaUnfold expression methods).HeadWF (fun _ => True) := by
  unfold nativeDeltaUnfold
  dsimp only [Bind.bind, ReaderT.bind, whnfCore]
  exact (unfoldDefinition.headWF expression methods).bind fun unfolded _ =>
    (valid.whnfCore unfolded.get! false true).mono fun _ _ => trivial

theorem TypeChecker.Inner.nativeDeltaContinue.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDeltaContinue first second methods).HeadWF (fun _ => True) := by
  unfold nativeDeltaContinue
  dsimp only [Bind.bind, ReaderT.bind]
  exact (quickIsDefEq.headWF first second false methods valid).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.nativeDeltaSingle.headWF (side : NativeDeltaSide) (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDeltaSingle side first second methods).HeadWF (fun _ => True) := by
  unfold nativeDeltaSingle
  dsimp only [Bind.bind, ReaderT.bind]
  exact (nativeDeltaUnfold.headWF _ methods valid).bind fun _ _ => nativeDeltaContinue.headWF _ _ methods valid

theorem TypeChecker.Inner.nativeDeltaPair.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDeltaPair first second methods).HeadWF (fun _ => True) := by
  unfold nativeDeltaPair
  dsimp only [Bind.bind, ReaderT.bind]
  refine (nativeDeltaUnfold.headWF _ methods valid).bind fun normalizedFirst _ => ?_
  exact (nativeDeltaUnfold.headWF _ methods valid).bind fun normalizedSecond _ =>
    nativeDeltaContinue.headWF normalizedFirst normalizedSecond methods valid

theorem TypeChecker.Inner.nativeDeltaArguments.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDeltaArguments first second methods).HeadWF (fun _ => True) := by
  unfold nativeDeltaArguments
  simp only [pure_bind]
  have fallback : ((do cacheFailure first second; nativeDeltaPair first second : RecM ReductionStatus)
      methods).HeadWF (fun _ => True) := by
    dsimp only [Bind.bind, ReaderT.bind]
    exact (cacheFailure.headWF first second).bind fun _ _ => nativeDeltaPair.headWF first second methods valid
  split
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (isDefEqArgs.headWF first second methods valid).bind fun equal _ => ?_
    cases equal
    · exact fallback
    · exact TypeChecker.M.HeadWF.pure trivial
  · exact fallback

theorem TypeChecker.Inner.nativeLazyDeltaRun.headWF (plan : NativeLazyDeltaPlan) (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeLazyDeltaRun plan first second methods).HeadWF (fun _ => True) := by
  cases plan with
  | unknown => exact TypeChecker.M.HeadWF.pure trivial
  | projection side =>
    unfold nativeLazyDeltaRun
    dsimp only [Bind.bind, ReaderT.bind]
    refine (tryUnfoldProjApp.headWF _ methods valid).bind fun normalized _ => ?_
    cases normalized
    · exact nativeDeltaSingle.headWF _ _ _ methods valid
    · exact nativeDeltaContinue.headWF _ _ methods valid
  | unfold side => exact nativeDeltaSingle.headWF _ _ _ methods valid
  | both arguments =>
    cases arguments
    · exact nativeDeltaPair.headWF _ _ methods valid
    · exact nativeDeltaArguments.headWF _ _ methods valid

theorem TypeChecker.Inner.lazyDeltaReductionStep.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (lazyDeltaReductionStep first second methods).HeadWF (fun _ => True) := by
  rw [lazyDeltaReductionStep.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  apply TypeChecker.M.HeadWF.get
  intro state caches
  exact nativeLazyDeltaRun.headWF _ first second methods valid

theorem TypeChecker.Inner.nativeLazyDeltaTail.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeLazyDeltaTail first second methods).HeadWF (fun _ => True) := by
  unfold nativeLazyDeltaTail
  dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  refine (TypeChecker.M.HeadWF.liftExcept _).bind fun reducedFirst _ => ?_
  cases reducedFirst <;> dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
  · refine (TypeChecker.M.HeadWF.liftExcept _).bind fun reducedSecond _ => ?_
    cases reducedSecond <;> dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
    · exact (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind
        fun _ _ => lazyDeltaReductionStep.headWF first second methods valid
    · exact (valid.isDefEqCore _ _).bind fun _ _ => .pure trivial
  · exact (valid.isDefEqCore _ _).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.nativeLazyDeltaNaturalTail.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeLazyDeltaNaturalTail first second methods).HeadWF (fun _ => True) := by
  unfold nativeLazyDeltaNaturalTail
  dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
  refine (reduceNat.headWF first methods valid).bind fun reducedFirst _ => ?_
  cases reducedFirst <;> dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
  · refine (reduceNat.headWF second methods valid).bind fun reducedSecond _ => ?_
    cases reducedSecond <;> dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
    · exact (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind
        fun _ _ => nativeLazyDeltaTail.headWF first second methods valid
    · exact (valid.isDefEqCore _ _).bind fun _ _ => .pure trivial
  · exact (valid.isDefEqCore _ _).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.nativeLazyDeltaRound.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeLazyDeltaRound first second methods).HeadWF (fun _ => True) := by
  unfold nativeLazyDeltaRound
  dsimp only [Bind.bind, ReaderT.bind]
  refine (isDefEqOffset.headWF first second methods valid).bind fun offset _ => ?_
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind fun _ _ => ?_
    apply TypeChecker.M.HeadWF.read
    intro context
    dsimp only
    split
    · exact nativeLazyDeltaNaturalTail.headWF first second methods valid
    · exact nativeLazyDeltaTail.headWF first second methods valid

theorem TypeChecker.Inner.lazyDeltaReduction.loop_headWF (first second : Expr) (fuel : Nat)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (lazyDeltaReduction.loop first second fuel methods).HeadWF (fun _ => True) := by
  induction fuel generalizing first second with
  | zero => exact TypeChecker.M.HeadWF.throw _ _
  | succ fuel inductionHypothesis =>
    rw [lazyDeltaReduction.loop_round_eq]
    dsimp only [Bind.bind, ReaderT.bind]
    refine (nativeLazyDeltaRound.headWF first second methods valid).bind fun status _ => ?_
    cases status
    · exact inductionHypothesis _ _
    · exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.lazyDeltaReduction.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (lazyDeltaReduction first second methods).HeadWF (fun _ => True) := by
  unfold lazyDeltaReduction
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.read
  intro context
  exact lazyDeltaReduction.loop_headWF first second context.fuel.lazyDelta methods valid

theorem TypeChecker.Inner.nativeDefEqFallback.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqFallback first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqFallback
  dsimp only [Bind.bind, ReaderT.bind]
  refine (isDefEqApp.headWF first second methods valid).bind fun equal _ => ?_
  cases equal <;> simp only [Bool.false_eq_true, if_true, if_false]
  all_goals try dsimp only [Bind.bind, ReaderT.bind]
  · refine (tryEtaExpansion.headWF first second methods valid).bind fun expanded _ => ?_
    cases expanded <;> simp only [Bool.false_eq_true, if_true, if_false]
    all_goals try dsimp only [Bind.bind, ReaderT.bind]
    · refine (tryEtaStruct.headWF first second methods valid).bind fun structureEqual _ => ?_
      cases structureEqual <;> simp only [Bool.false_eq_true, if_true, if_false]
      all_goals try dsimp only [Bind.bind, ReaderT.bind]
      · refine (tryStringLitExpansion.headWF first second methods valid).bind fun stringEqual _ => ?_
        split
        · exact TypeChecker.M.HeadWF.pure trivial
        · dsimp only [Bind.bind, ReaderT.bind]
          refine (isDefEqUnitLike.headWF first second methods valid).bind fun unitEqual _ => ?_
          cases unitEqual <;> exact TypeChecker.M.HeadWF.pure trivial
      · exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqRenormalize.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqRenormalize first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqRenormalize
  dsimp only [Bind.bind, ReaderT.bind, whnfCore, isDefEqCore]
  refine (valid.whnfCore first false false).bind fun normalizedFirst _ => ?_
  refine (valid.whnfCore second false false).bind fun normalizedSecond _ => ?_
  split
  · exact valid.isDefEqCore normalizedFirst normalizedSecond
  · exact nativeDefEqFallback.headWF first second methods valid

theorem TypeChecker.Inner.nativeDefEqSimple.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqSimple first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqSimple
  cases first <;> cases second <;> try exact TypeChecker.M.HeadWF.pure trivial
  dsimp only
  split
  · exact isDefEq.headWF _ _ methods valid
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqUnknown.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqUnknown first second methods).HeadWF (fun _ => True) := by
  rw [nativeDefEqUnknown.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  refine (nativeDefEqSimple.headWF first second methods valid).bind fun equal _ => ?_
  cases equal
  · exact nativeDefEqRenormalize.headWF first second methods valid
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqDelta.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqDelta first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqDelta
  dsimp only [Bind.bind, ReaderT.bind]
  refine (lazyDeltaReduction.headWF first second methods valid).bind fun status _ => ?_
  cases status <;> first | exact nativeDefEqUnknown.headWF _ _ methods valid | exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqProof.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqProof first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqProof
  dsimp only [Bind.bind, ReaderT.bind]
  refine (isDefEqProofIrrel.headWF first second methods valid).bind fun proof _ => ?_
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact nativeDefEqDelta.headWF first second methods valid

theorem TypeChecker.Inner.nativeDefEqRecheck.headWF (first second normalizedFirst normalizedSecond : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqRecheck first second normalizedFirst normalizedSecond methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqRecheck
  split
  · exact quickIsDefEq.headWF normalizedFirst normalizedSecond false methods valid
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqNormalized.headWF (first second normalizedFirst normalizedSecond : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqNormalized first second normalizedFirst normalizedSecond methods).HeadWF (fun _ => True) := by
  rw [nativeDefEqNormalized.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  refine (nativeDefEqRecheck.headWF _ _ _ _ methods valid).bind fun rechecked _ => ?_
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact nativeDefEqProof.headWF normalizedFirst normalizedSecond methods valid

theorem TypeChecker.Inner.nativeDefEqCheap.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqCheap first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqCheap
  dsimp only [Bind.bind, ReaderT.bind, whnfCore]
  refine (valid.whnfCore first false true).bind fun normalizedFirst _ => ?_
  refine (valid.whnfCore second false true).bind fun normalizedSecond _ => ?_
  exact nativeDefEqNormalized.headWF first second normalizedFirst normalizedSecond methods valid

theorem TypeChecker.Inner.nativeDefEqBoolShortcut.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqBoolShortcut first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqBoolShortcut
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.read
  intro context
  split
  · dsimp only [Bind.bind, ReaderT.bind, whnf]
    exact (valid.whnf first).bind fun _ _ => .pure trivial
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqShort.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqShort first second methods).HeadWF (fun _ => True) := by
  rw [nativeDefEqShort.entry_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  refine (nativeDefEqBoolShortcut.headWF first second methods valid).bind fun equal _ => ?_
  cases equal
  · exact nativeDefEqCheap.headWF first second methods valid
  · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeDefEqEntry.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeDefEqEntry first second methods).HeadWF (fun _ => True) := by
  unfold nativeDefEqEntry
  dsimp only [Bind.bind, ReaderT.bind]
  refine (quickIsDefEq.headWF first second true methods valid).bind fun quick _ => ?_
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact nativeDefEqShort.headWF first second methods valid

theorem TypeChecker.Inner.isDefEqCore'.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEqCore' first second methods).HeadWF (fun _ => True) := by
  rw [isDefEqCore'.entry_eq]
  exact nativeDefEqEntry.headWF first second methods valid

theorem TypeChecker.Methods.withFuel.isDefEqCore_succ_headWF (fuel : Nat) (valid : (withFuel fuel).HeadWF)
    (first second : Expr) : ((withFuel (fuel + 1)).isDefEqCore first second).HeadWF (fun _ => True) :=
  TypeChecker.Inner.isDefEqCore'.headWF first second (withFuel fuel) valid

theorem TypeChecker.Methods.withFuel.headWF (fuel : Nat) : (withFuel fuel).HeadWF := by
  induction fuel with
  | zero => exact zero_headWF
  | succ fuel inductionHypothesis =>
    constructor
    · exact whnfCore_succ_headWF fuel inductionHypothesis
    · exact whnf_succ_headWF fuel inductionHypothesis
    · exact inferType_succ_headWF fuel inductionHypothesis
    · exact isDefEqCore_succ_headWF fuel inductionHypothesis

theorem TypeChecker.RecM.run_headWF (action : TypeChecker.RecM Result) (post : Result → Prop)
    (framed : ∀ methods, methods.HeadWF → (action methods).HeadWF post) : action.run.HeadWF post := by
  unfold run
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.read
  intro context
  exact framed (Methods.withFuel context.fuel.recDepth) (Methods.withFuel.headWF _)

theorem TypeChecker.whnf.headWF (expression : Expr) : (whnf expression).HeadWF NativeHeadClean :=
  RecM.run_headWF _ _ fun _ valid => valid.whnf expression

theorem TypeChecker.whnfCore.headWF (expression : Expr) : (whnfCore expression).HeadWF NativeHeadClean :=
  RecM.run_headWF _ _ fun _ valid => valid.whnfCore expression false false

theorem TypeChecker.inferType.headWF (expression : Expr) : (inferType expression).HeadWF (fun _ => True) :=
  RecM.run_headWF _ _ fun _ valid => valid.inferType expression true

theorem TypeChecker.checkType.headWF (expression : Expr) : (checkType expression).HeadWF (fun _ => True) :=
  RecM.run_headWF _ _ fun _ valid => valid.inferType expression false

theorem TypeChecker.isDefEq.headWF (first second : Expr) : (isDefEq first second).HeadWF (fun _ => True) :=
  RecM.run_headWF _ _ fun methods valid => Inner.isDefEq.headWF first second methods valid

theorem TypeChecker.M.HeadWF.fromEmpty {action : TypeChecker.M Result} {post : Result → Prop}
    (framed : action.HeadWF post) (context : TypeChecker.Context) {result : Result}
    {finalState : TypeChecker.State} (accepted : action context {} = .ok (result, finalState)) :
    TypeChecker.HeadCacheWF finalState ∧ post result :=
  framed context {} TypeChecker.HeadCacheWF.empty result finalState accepted

theorem TypeChecker.M.HeadWF.run {action : TypeChecker.M Result} {post : Result → Prop}
    (framed : action.HeadWF post) (environment : Kernel.Environment) (safety : DefinitionSafety)
    (locals : LocalContext) (parameters : List Name) (fuel : FuelConfig) {result : Result}
    (accepted : action.run environment safety locals parameters fuel = .ok result) : post result := by
  let context : TypeChecker.Context := { env := environment, safety, lctx := locals, lparams := parameters, fuel }
  change Except.map Prod.fst (action context {}) = .ok result at accepted
  cases evaluated : action context {} with
  | error exception =>
    simp only [evaluated, Except.map] at accepted
    cases accepted
  | ok returned =>
    rcases returned with ⟨value, finalState⟩
    simp only [evaluated, Except.map] at accepted
    cases accepted
    exact (framed.fromEmpty context evaluated).2

end Lean4Lean
