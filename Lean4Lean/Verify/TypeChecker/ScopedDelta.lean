import Lean4Lean.Verify.TypeChecker.ScopedComparison

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem _root_.Lean4Lean.TypeChecker.M.ScopeWF.lift {context : VContext} {state : VState}
    {action : M Result} {post} (valid : action.ScopeWF context state post) :
    (liftM action : RecM Result).ScopeWF context state post := fun _ _ => valid

theorem cacheFailure.scopeWF {context : VContext} {state : VState} :
    (cacheFailure first second).ScopeWF context state (fun _ _ => True) := by
  rintro caches wellFormed _ _ ⟨⟩
  exact ⟨{ state with toState := _ }, rfl, .rfl, { wellFormed with }, caches, trivial⟩

theorem tryUnfoldProjApp.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (tryUnfoldProjApp expression).ScopeWF context state fun result _ =>
      ∀ normalized, result = some normalized →
        context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic := by
  simp only [tryUnfoldProjApp]
  split <;> [exact RecM.ScopeWF.pure nofun; skip]
  refine (whnfCore.scopeWF translated).bind fun _ _ _ normalized => ?_
  refine RecM.ScopeWF.pure ?_
  split <;> rintro _ ⟨⟩
  exact ⟨normalized.1, normalized.2.1⟩

theorem lazyDeltaReductionStep.scopeWFOf {context : VContext} {state : VState}
    (lookup : ∀ {name ci ci'}, context.env.find? name = some ci →
      context.venv.constants name = some ci' → ci.name = name ∧
        TrConstant context.safety context.venv ci ci')
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (lazyDeltaReductionStep first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) := by
  unfold lazyDeltaReductionStep
  refine RecM.ScopeWF.getEnv ?_
  extract_lets delta continueComparison unfoldBoth afterArguments
  have unfoldOne {state expression semantic information}
      (translated : context.TrExprS expression semantic)
      (definition : isDelta context.env expression = some information) :
      (delta expression).ScopeWF context state (fun result _ => context.TrExpr result semantic) := by
    obtain ⟨name, found, ⟨_, instantiated⟩, levels, headEq, levelCount⟩ :=
      isDelta_is_some.1 definition
    obtain ⟨_, stack⟩ := AppStack.build (expression.mkAppList_getAppArgsList ▸ translated)
    have .const semanticLookup _ translatedLevels := headEq ▸ stack.tr
    obtain ⟨_, _, registeredLevels, _⟩ := lookup found semanticLookup
    refine (unfoldDefinition.scopeWF translated).bind fun unfolded _ _ unfolding => ?_
    obtain _ | normalized := unfolded
    · cases unfolding found instantiated headEq levelCount
    obtain ⟨_, _, structural, equality⟩ := unfolding
    exact (whnfCore.scopeWF structural).mono fun _ _ _ normalized =>
      normalized.2.1.defeq context.Ewf context.Δwf equality
  have continueWith {state first second}
      (firstTranslation : context.TrExpr first firstSemantic)
      (secondTranslation : context.TrExpr second secondSemantic) :
      (continueComparison first second).ScopeWF context state
        (fun result _ => result.WF context firstSemantic secondSemantic true) := by
    let ⟨_, firstStructural, firstEquality⟩ := firstTranslation
    let ⟨_, secondStructural, secondEquality⟩ := secondTranslation
    refine (quickIsDefEq.scopeWF firstStructural secondStructural).bind
      fun _ _ _ compared => RecM.ScopeWF.pure ?_
    split
    · exact ⟨rfl, firstTranslation, secondTranslation⟩
    · exact firstEquality.symm.trans context.Ewf context.Δwf (compared rfl)
        |>.trans context.Ewf context.Δwf secondEquality
    · exact ⟨firstTranslation, secondTranslation⟩
  split
  · exact RecM.ScopeWF.pure
      ⟨firstTranslation.trExpr context.Ewf context.Δwf, secondTranslation.trExpr context.Ewf context.Δwf⟩
  · refine (tryUnfoldProjApp.scopeWF secondTranslation).bind fun _ _ _ normalized => ?_
    split
    · exact continueWith (firstTranslation.trExpr context.Ewf context.Δwf) (normalized _ rfl).2
    · exact (unfoldOne firstTranslation ‹_›).bind fun _ _ _ normalized =>
        continueWith normalized (secondTranslation.trExpr context.Ewf context.Δwf)
  · refine (tryUnfoldProjApp.scopeWF firstTranslation).bind fun _ _ _ normalized => ?_
    split
    · exact continueWith (normalized _ rfl).2 (secondTranslation.trExpr context.Ewf context.Δwf)
    · exact (unfoldOne secondTranslation ‹_›).bind fun _ _ _ normalized =>
        continueWith (firstTranslation.trExpr context.Ewf context.Δwf) normalized
  rename_i firstDefinition secondDefinition firstDelta secondDelta
  extract_lets firstHints secondHints
  split <;> [skip; split]
  · exact (unfoldOne secondTranslation ‹_›).bind fun _ _ _ normalized =>
      continueWith (firstTranslation.trExpr context.Ewf context.Δwf) normalized
  · exact (unfoldOne firstTranslation ‹_›).bind fun _ _ _ normalized =>
      continueWith normalized (secondTranslation.trExpr context.Ewf context.Δwf)
  have unfoldBothWF {state} : (unfoldBoth ⟨⟩).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) :=
    (unfoldOne firstTranslation ‹_›).bind fun _ _ _ firstNormalized =>
      (unfoldOne secondTranslation ‹_›).bind fun _ _ _ secondNormalized =>
        continueWith firstNormalized secondNormalized
  refine RecM.ScopeWF.get ?_
  split <;> [skip; exact unfoldBothWF]
  split <;> [skip; exact cacheFailure.scopeWF.lift.bind fun _ _ _ _ => unfoldBothWF]
  rename_i eligible equivalentLevels
  simp at eligible
  cases ptrEqConstantInfo_eq eligible.1.1.2
  obtain ⟨_, firstFound, ⟨_, _⟩, firstLevels, firstHead, firstLevelCount⟩ :=
    isDelta_is_some.1 firstDelta
  obtain ⟨_, secondFound, ⟨_, _⟩, secondLevels, secondHead, secondLevelCount⟩ :=
    isDelta_is_some.1 secondDelta
  simp [firstHead, secondHead, Expr.constLevels!] at equivalentLevels
  obtain ⟨_, firstStack⟩ := AppStack.build (first.mkAppList_getAppArgsList ▸ firstTranslation)
  obtain ⟨_, secondStack⟩ := AppStack.build (second.mkAppList_getAppArgsList ▸ secondTranslation)
  have .const (us' := firstLevels) firstLookup firstLevelTranslation firstLevelCount := firstHead ▸ firstStack.tr
  have .const (us' := secondLevels) secondLookup secondLevelTranslation _ := secondHead ▸ secondStack.tr
  cases (context.trenv.find?_uniq firstFound firstLookup).1
  cases (context.trenv.find?_uniq secondFound secondLookup).1
  cases firstLookup.symm.trans secondLookup
  have headEquality := VEnv.IsDefEq.constDF firstLookup
    (Γ := context.vlctx.toCtx) (.of_mapM_ofLevel firstLevelTranslation) (.of_mapM_ofLevel secondLevelTranslation)
    ((Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 firstLevelTranslation)).symm.trans
      firstLevelCount)
    (Level.isEquivList_wf equivalentLevels firstLevelTranslation secondLevelTranslation)
  refine (isDefEqArgs.scopeWF ⟨_, firstStack.tr, _, secondStack.tr, _, headEquality⟩
    firstTranslation secondTranslation).bind fun _ _ _ compared => ?_
  split <;> [skip; exact cacheFailure.scopeWF.lift.bind fun _ _ _ _ => unfoldBothWF]
  trace_state
  exact RecM.ScopeWF.pure (compared (by assumption))

theorem lazyDeltaReductionStep.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (lazyDeltaReductionStep first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) :=
  lazyDeltaReductionStep.scopeWFOf context.trenv.find?_uniq firstTranslation secondTranslation

theorem isDefEqOffset.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqOffset first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) := by
  unfold isDefEqOffset
  split
  · rename_i bothZero
    simp at bothZero
    cases isNatZero_wf bothZero.1 firstTranslation
    cases isNatZero_wf bothZero.2 secondTranslation
    exact RecM.ScopeWF.pure fun _ => .refl (firstTranslation.wf context.Ewf context.Δwf)
  · refine RecM.ScopeWF.pureBind ?_
    split <;> [skip; exact RecM.ScopeWF.pure nofun]
    obtain ⟨_, firstPredecessor, rfl⟩ := isNatSuccOf?_wf ‹_› firstTranslation
    obtain ⟨_, secondPredecessor, rfl⟩ := isNatSuccOf?_wf ‹_› secondTranslation
    refine RecM.ScopeWF.toLBoolM <| (isDefEqCore.scopeWF firstPredecessor secondPredecessor).mono
      fun _ _ _ compared accepted => ?_
    obtain ⟨_, firstTyping⟩ := firstTranslation.wf context.Ewf context.Δwf
    obtain ⟨_, _, functionType, argumentType⟩ := firstTyping.hasType.1.app_inv context.Ewf context.Δwf
    exact ⟨_, functionType.appDF ((compared accepted).of_l context.Ewf context.Δwf argumentType)⟩

theorem reduceNat.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (reduceNat expression).ScopeWF context state fun result _ =>
      ∀ normalized, result = some normalized →
        context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic := by
  exact ((reduceNat.scopeHeadWF translated).andWF (reduceNat.WF translated)).mono
    fun _ _ _ result => result.2

theorem lazyDeltaReduction.loop.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (lazyDeltaReduction.loop first second budget).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic) := by
  induction budget generalizing state first second firstSemantic secondSemantic with
  | zero => exact RecM.ScopeWF.throw
  | succ budget inductionHypothesis =>
    unfold loop
    extract_lets afterNative
    refine (isDefEqOffset.scopeWF firstTranslation secondTranslation).bind
      fun offset _ _ compared => ?_
    have afterNativeWF : ∀ {state}, (afterNative ⟨⟩).ScopeWF context state
        (fun result _ => result.WF context firstSemantic secondSemantic) := by
      intro state
      refine RecM.ScopeWF.getEnv ?_
      refine (RecM.ScopeWF.liftExcept reduceNative.WF).bind fun _ _ _ nativeRejected => ?_
      split <;> [cases nativeRejected _ rfl; skip]
      refine (RecM.ScopeWF.liftExcept reduceNative.WF).bind fun _ _ _ nativeRejected => ?_
      split <;> [cases nativeRejected _ rfl; skip]
      refine (lazyDeltaReductionStep.scopeWF firstTranslation secondTranslation).bind
        fun result _ _ reduction => ?_
      cases result with
      | «continue» tn sn =>
        obtain ⟨_, ⟨_, firstStructural, firstEquality⟩,
          ⟨_, secondStructural, secondEquality⟩⟩ := reduction
        exact (inductionHypothesis firstStructural secondStructural).mono
          fun _ _ _ reduced => reduced.defeq firstEquality secondEquality
      | unknown tn sn =>
        simpa [ReductionStatus.WF] using (RecM.ScopeWF.pure reduction)
      | true =>
        simpa [ReductionStatus.WF] using (RecM.ScopeWF.pure reduction)
      | false tn sn =>
        simpa [ReductionStatus.WF] using (RecM.ScopeWF.pure reduction)
    by_cases offsetNotUndef : offset != .undef
    · by_cases offsetIsTrue : offset == .true
      · have offsetEq : offset = .true := by
          cases offset <;> simp_all
        simp [offsetNotUndef, offsetIsTrue, ReductionStatus.bool]
        exact RecM.ScopeWF.pure (compared offsetEq)
      · simp [offsetNotUndef, offsetIsTrue, ReductionStatus.bool]
        exact RecM.ScopeWF.pure ⟨
          firstTranslation.trExpr context.Ewf context.Δwf,
          secondTranslation.trExpr context.Ewf context.Δwf⟩
    simp [offsetNotUndef]
    refine RecM.ScopeWF.readThe ?_
    split
    · refine (reduceNat.scopeWF firstTranslation).bind fun _ _ _ normalized => ?_
      split
      · obtain ⟨_, structural, equality⟩ := (normalized _ rfl).2
        rw [map_eq_pure_bind]
        refine (isDefEqCore.scopeWF structural secondTranslation).bind fun _ _ _ compared => ?_
        exact RecM.ScopeWF.pure <| ReductionStatus.WF.bool
          ((structural.trExpr context.Ewf context.Δwf).defeq
            context.Ewf context.Δwf equality)
          (secondTranslation.trExpr context.Ewf context.Δwf)
          (fun accepted => equality.symm.trans context.Ewf context.Δwf (compared accepted))
      refine (reduceNat.scopeWF secondTranslation).bind fun _ _ _ normalized => ?_
      split
      · obtain ⟨_, structural, equality⟩ := (normalized _ rfl).2
        rw [map_eq_pure_bind]
        refine (isDefEqCore.scopeWF firstTranslation structural).bind fun _ _ _ compared => ?_
        exact RecM.ScopeWF.pure <| ReductionStatus.WF.bool
          (firstTranslation.trExpr context.Ewf context.Δwf)
          ((structural.trExpr context.Ewf context.Δwf).defeq
            context.Ewf context.Δwf equality)
          (fun accepted => (compared accepted).trans context.Ewf context.Δwf equality)
      exact afterNativeWF (state := _)
    · exact afterNativeWF (state := _)


theorem lazyDeltaReduction.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (lazyDeltaReduction first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic) := by
  unfold lazyDeltaReduction
  exact RecM.ScopeWF.readThe (lazyDeltaReduction.loop.scopeWF firstTranslation secondTranslation)

theorem tryStringLitExpansionCore.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (tryStringLitExpansionCore first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) := by
  unfold tryStringLitExpansionCore
  iterate 3 split <;> [skip; exact RecM.ScopeWF.pure nofun]
  let .lit _ constructorTranslation := firstTranslation
  exact RecM.ScopeWF.toLBoolM (isDefEqCore.scopeWF constructorTranslation secondTranslation)

theorem tryStringLitExpansion.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (tryStringLitExpansion first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) := by
  refine (tryStringLitExpansionCore.scopeWF firstTranslation secondTranslation).bind fun _ _ _ compared => ?_
  split <;> [skip; exact RecM.ScopeWF.pure compared]
  exact (tryStringLitExpansionCore.scopeWF secondTranslation firstTranslation).mono
    fun _ _ _ compared accepted => (compared accepted).symm

end Lean4Lean.TypeChecker.Inner
