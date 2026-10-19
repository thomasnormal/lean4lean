import Lean4Lean.Theory.Typing.QuotSpineExposure

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private proofApplicationType from Lean4Lean.Theory.Typing.QuotSpineExposure

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

/-- Actual Prop-source firing after normally related component reductions have
finished. The left major is arbitrary; no simulation certificate is required. -/
theorem normal_quot_prop_root
    {sourceUniverse targetUniverse : VLevel}
    {domain relation target function respect major right resultType : VExpr}
    {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) resultType)
    (rightTyped : environment.HasType universes locals right resultType)
    (zeroChecked : zeroLike sourceUniverse = true)
    (domainNormal : @NormalEq (environmentWF.reductionParams universes) locals
      domain (values (.inl (some (some (some (some none)))))))
    (functionNormal : @NormalEq (environmentWF.reductionParams universes) locals
      function (values (.inl (some none))))
    (matched : quotLiftPattern.Matches right levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals right
        (quotLiftPatternResult.apply levels values) ∧
      Steps environmentWF universes locals
        (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
          domain) relation) target) function) respect) major) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels values) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels values) resultType := by
  letI := environmentWF.reductionParams universes
  have rewriteStep : ParRed locals right (quotLiftPatternResult.apply levels values) :=
    .extra (.quot registered) matched checked (fun _ => .rfl)
  have computed : unfold
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) =
      some (.app function (selector domain relation major)) := by
    simp only [unfold, zeroChecked, ite_true]
  obtain ⟨_, inductionRegistered, liftRegistered, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  obtain ⟨_, _, levelsEqual, sourceWF, _, domainTyped, relationTyped,
    _, functionTyped, _, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered typed
  cases levelsEqual
  have zeroEqual := (zeroLike_iff sourceUniverse).mp zeroChecked
  have domainProp := IsDefEq.defeqDF
    (IsDefEq.sortDF sourceWF (by trivial) zeroEqual) domainTyped
  have quotientEqual := IsDefEq.constDF quotientRegistered
    (ls := [sourceUniverse]) (ls' := [.zero]) (by simpa using sourceWF)
    (by simp [VLevel.WF]) (by rfl) (.cons zeroEqual .nil) (Γ := locals)
  have first := quotientEqual.appDF domainTyped
  simp [VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar] at first
  have second := first.appDF relationTyped
  simp [VExpr.inst] at second
  have majorProp := second.defeq majorTyped
  have selectedTyped := selector_hasType environmentWF.ordered quotientRegistered
    constructorRegistered inductionRegistered domainProp relationTyped majorProp
  have joinedFunctionTyped := functionTyped
  have path : Steps environmentWF universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major)
      (.app function (selector domain relation major)) :=
    ReflTransGen.tail .rfl (.unfold computed)
  let .app functionMatched constructorMatched := matched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .const := functionMatched
  let .var constructorMatched := constructorMatched
  let .var constructorMatched := constructorMatched
  let .var constructorMatched := constructorMatched
  let .const := constructorMatched
  obtain ⟨_, _, rfl, _, _, rightDomainTyped, _, _, _, _, rightMajorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered rightTyped
  obtain ⟨_, _, _, constructorDomainTyped, _, valueTyped, _⟩ :=
    quotMk_inv environmentWF localsWF constructorRegistered rightMajorTyped
  simp only [quotLiftPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at checked
  have alignedValue :=
    (checked.1.symm.of_l environmentWF localsWF constructorDomainTyped).defeq valueTyped
  have reducedValue := alignedValue
  have leftValue := ((domainNormal.defeq localsWF).symm.of_l environmentWF localsWF
    rightDomainTyped).defeq reducedValue
  have reducedFunction := ((functionNormal.defeq localsWF).of_l environmentWF localsWF
    joinedFunctionTyped).hasType.2
  exact ⟨_, rewriteStep, path,
    .appDF joinedFunctionTyped reducedFunction selectedTyped leftValue functionNormal
      (.proofIrrel domainProp selectedTyped leftValue),
    path.hasType registered localsWF typed, rewriteStep.hasType localsWF rightTyped⟩


include environmentWF in
private theorem proofSpineType
    (localsWF : OnCtx locals (environment.IsType universes))
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (proofTyped : environment.HasType universes locals function proposition)
    (typed : environment.HasType universes locals (applyArguments function arguments) type) :
    environment.HasType universes locals type (.sort .zero) := by
  induction arguments generalizing function proposition with
  | nil =>
    exact propositionTyped.defeqU_l environmentWF localsWF
      (proofTyped.uniqU environmentWF localsWF typed)
  | cons argument arguments induction =>
    obtain ⟨_, applicationTyped⟩ := HasType.spine_head (environmentWF := environmentWF)
      (function := .app function argument) (arguments := arguments) localsWF typed
    exact induction (proofApplicationType (environmentWF := environmentWF) localsWF
      propositionTyped proofTyped applicationTyped) applicationTyped typed

theorem Steps.applyArguments
    (path : Steps environmentWF universes locals function result) (arguments : List VExpr) :
    Steps environmentWF universes locals (applyArguments function arguments)
      (applyArguments result arguments) := by
  induction arguments generalizing function result with
  | nil => exact path
  | cons argument arguments induction => exact induction (path.app .rfl)

theorem _root_.Lean4Lean.VEnv.ParRed.applyArguments
    (step : @ParRed (environmentWF.reductionParams universes) locals function result)
    (arguments : List VExpr) :
    @ParRed (environmentWF.reductionParams universes) locals
      (applyArguments function arguments) (applyArguments result arguments) := by
  letI := environmentWF.reductionParams universes
  induction arguments generalizing function result with
  | nil => exact step
  | cons argument arguments induction => exact induction (step.app .rfl)

private theorem constantNormalCases
    (normal : @NormalEq (environmentWF.reductionParams universes) locals
      (.const name leftLevels) (.const name rightLevels)) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∨
      ∃ proposition, environment.HasType universes locals proposition (.sort .zero) ∧
        environment.HasType universes locals (.const name leftLevels) proposition ∧
        environment.HasType universes locals (.const name rightLevels) proposition := by
  cases normal with
  | refl typed =>
    clear typed
    apply Or.inl
    induction leftLevels with
    | nil => exact .nil
    | cons level levels induction => exact .cons rfl induction
  | constDF _ _ _ _ equal => exact .inl equal
  | proofIrrel propositionTyped leftTyped rightTyped =>
    exact .inr ⟨_, propositionTyped, leftTyped, rightTyped⟩

private theorem rigidPropJoin
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (zeroChecked : zeroLike sourceUniverse = true)
    (exposed : RigidSpine environmentWF universes ``Quot.lift
      [sourceUniverse, targetUniverse] locals left arguments) :
    OnCtx locals (environment.IsType universes) →
    ∀ {domain relation target function respect major : VExpr} {pending : List VExpr}
      {values : quotLiftPattern.Path → VExpr},
      arguments = [domain, relation, target, function, respect, major] ++ pending →
      quotLiftPattern.Matches
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
          [domain, relation, target, function, respect, major])
        [sourceUniverse, targetUniverse] values →
      quotLiftPatternCheck.OK (environment.IsDefEqU universes locals)
        [sourceUniverse, targetUniverse] values →
      ∃ joined, Steps environmentWF universes locals left joined ∧
        @NormalEq (environmentWF.reductionParams universes) locals joined
          (applyArguments (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) pending) := by
  letI := environmentWF.reductionParams universes
  induction exposed with
  | proof propositionTyped leftTyped rightTyped =>
    intro localsWF domain relation target function respect major pending values equation matched checked
    have step : ParRed _ _ (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) :=
      .extra (.quot registered) matched checked (fun _ => .rfl)
    have finalTyped := (step.applyArguments (environmentWF := environmentWF)
      (universes := universes) pending).hasType localsWF
      (show environment.HasType universes _ _ _ from by
        simpa only [equation, applyArguments_append, Params.env, Params.univs,
        WF.reductionParams] using rightTyped)
    exact ⟨_, .rfl, .proofIrrel propositionTyped leftTyped finalTyped⟩
  | @spine leftLevels leftArguments type arguments locals typed heads normals =>
    intro localsWF domain relation target function respect major pending values equation matched checked
    have step : ParRed _ _ (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) :=
      .extra (.quot registered) matched checked (fun _ => .rfl)
    rcases constantNormalCases heads with levelsEqual | ⟨proposition, propositionTyped, headProof, _⟩
    · cases levelsEqual with
      | cons sourceEqual levelsEqual =>
        cases levelsEqual with
        | cons targetEqual levelsEqual =>
          cases levelsEqual
          rw [equation] at normals
          cases normals with
          | @cons leftDomain _ _ _ domainNormal normals =>
            cases normals with
            | @cons leftRelation _ _ _ relationNormal normals =>
              cases normals with
              | @cons leftTarget _ _ _ targetNormal normals =>
                cases normals with
                | @cons leftFunction _ _ _ functionNormal normals =>
                  cases normals with
                  | @cons leftRespect _ _ _ respectNormal normals =>
                    cases normals with
                    | @cons leftMajor _ leftPending _ majorNormal pendingNormal =>
                      obtain ⟨_, rootTyped⟩ := HasType.spine_head (environmentWF := environmentWF)
                        (arguments := leftPending) localsWF typed
                      have rootNormal := normal_spine_congr
                        (arguments := [leftDomain, leftRelation, leftTarget, leftFunction, leftRespect, leftMajor])
                        localsWF rootTyped heads
                        (.cons domainNormal (.cons relationNormal (.cons targetNormal
                          (.cons functionNormal (.cons respectNormal (.cons majorNormal .nil))))))
                      have rightRootTyped := ((rootNormal.defeq localsWF).of_l
                        environmentWF localsWF rootTyped).hasType.2
                      have leftZero := (zeroLike_iff _).mpr
                        (sourceEqual.trans ((zeroLike_iff _).mp zeroChecked))
                      have captures : values (.inl (some (some (some (some none))))) = domain ∧
                          values (.inl (some none)) = function := by
                        let .app functionMatched _ := matched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .const := functionMatched
                        exact ⟨rfl, rfl⟩
                      obtain ⟨rootResult, _, rootSteps, joinedNormal, _, _⟩ :=
                        normal_quot_prop_root registered localsWF rootTyped rightRootTyped
                          leftZero
                          (by simpa only [captures.1] using domainNormal)
                          (by simpa only [captures.2] using functionNormal) matched checked
                      have path := rootSteps.applyArguments leftPending
                      exact ⟨_, path, normal_spine_congr localsWF
                        (path.hasType registered localsWF typed) joinedNormal pendingNormal⟩
    · have typeProp := proofSpineType (environmentWF := environmentWF)
        localsWF propositionTyped headProof typed
      have sourceNormal := normal_spine_congr localsWF typed heads normals
      have rightTyped := ((sourceNormal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2
      have finalTyped := (step.applyArguments (environmentWF := environmentWF)
        (universes := universes) pending).hasType localsWF
        (show environment.HasType universes _ _ _ from by
        simpa only [equation, applyArguments_append, Params.env, Params.univs,
          WF.reductionParams] using rightTyped)
      exact ⟨_, .rfl, .proofIrrel typeProp typed finalTyped⟩
  | @lam arguments binder bodyType leftBody locals functionTyped body induction =>
    intro localsWF domain relation target function respect major pending values equation matched checked
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, binderTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    have extendedWF : OnCtx (binder :: locals) (environment.IsType universes) :=
      ⟨localsWF, _, binderTyped⟩
    have liftedMatched : quotLiftPattern.Matches
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
          [domain.lift, relation.lift, target.lift, function.lift, respect.lift, major.lift])
        [sourceUniverse, targetUniverse] (fun path => (values path).lift) := by
      simpa only [applyArguments_liftN, List.map_cons, List.map_nil, VExpr.lift,
        VExpr.liftN] using
        (Pattern.matches_liftN.mpr ⟨values, matched, fun _ => rfl⟩ :
          quotLiftPattern.Matches
            (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
              [domain, relation, target, function, respect, major]).lift
            [sourceUniverse, targetUniverse] (fun path => (values path).lift))
    have liftedChecked := Pattern.Check.OK.weakN (W := Ctx.LiftN.one (A := binder))
      quotLiftPatternCheck checked
    obtain ⟨bodyResult, bodySteps, bodyNormal⟩ := induction extendedWF
      (pending := pending.map VExpr.lift ++ [.bvar 0])
      (by simp only [equation, List.map_append, List.map_cons, List.map_nil, List.append_assoc])
      liftedMatched liftedChecked
    have step : ParRed _ _ (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) :=
      .extra (.quot registered) matched checked (fun _ => .rfl)
    have finalFunctionTyped := (step.applyArguments (environmentWF := environmentWF)
      (universes := universes) pending).hasType localsWF
      (show environment.HasType universes _ _ _ from by
        simpa only [equation, applyArguments_append, Params.env, Params.univs,
        WF.reductionParams] using functionTyped)
    refine ⟨_, bodySteps.lam, .etaL finalFunctionTyped ?_⟩
    simpa only [applyArguments_append, applyArguments, VExpr.lift,
      applyArguments_liftN, Pattern.RHS.apply_liftN] using bodyNormal

private theorem matchedLiftSpine
    (matched : quotLiftPattern.Matches right levels values) :
    ∃ major, right = applyArguments (.const ``Quot.lift levels)
      [values (.inl (some (some (some (some none))))),
        values (.inl (some (some (some none)))), values (.inl (some (some none))),
        values (.inl (some none)), values (.inl none), major] := by
  let .app functionMatched _ := matched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .var functionMatched := functionMatched
  let .const := functionMatched
  exact ⟨_, rfl⟩

/-- Any normally related left source follows a checked Prop-source quotient
firing, beneath any finite related argument list. The actual left path is
constructed from hereditary exposure; no matching or simulation premise is
required of the left source. Both endpoints retain the original result type. -/
theorem normal_quot_prop_join
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (zeroChecked : zeroLike sourceUniverse = true)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (argumentsNormal : List.Forall₂
      (@NormalEq (environmentWF.reductionParams universes) locals) pending pending')
    (typed : environment.HasType universes locals (applyArguments left pending) type)
    (matched : quotLiftPattern.Matches right [sourceUniverse, targetUniverse] values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals)
      [sourceUniverse, targetUniverse] values) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals (applyArguments right pending')
        (applyArguments (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) pending') ∧
      Steps environmentWF universes locals (applyArguments left pending) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (applyArguments (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) pending') ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals
        (applyArguments (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) pending') type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨major, equation⟩ := matchedLiftSpine matched
  obtain ⟨initial, corePath, exposed, _, _, _⟩ := normal_spine_expose_applications localsWF
    (by simpa only [equation] using normal) argumentsNormal typed
  obtain ⟨joined, finalPath, finalNormal⟩ := rigidPropJoin registered zeroChecked exposed
    localsWF rfl (by simpa only [← equation] using matched) checked
  have path : Steps environmentWF universes locals (applyArguments left pending) joined :=
    (Steps.core corePath).trans finalPath
  have joinedTyped := path.hasType registered localsWF typed
  have rightStep : ParRed locals right (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) :=
    .extra (.quot registered) matched checked (fun _ => .rfl)
  exact ⟨joined, rightStep.applyArguments pending',
    path, finalNormal, joinedTyped,
    ((finalNormal.defeq localsWF).of_l environmentWF localsWF joinedTyped).hasType.2⟩

private theorem reduceMatchedCaptures
    {pattern : Pattern} {values reducedValues : pattern.Path → VExpr}
    (matched : pattern.Matches source levels values)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (values path) (reducedValues path)) :
    ∃ reduced, @ParRed (environmentWF.reductionParams universes) locals source reduced ∧
      pattern.Matches reduced levels reducedValues := by
  letI := environmentWF.reductionParams universes
  induction matched with
  | const =>
    refine ⟨_, .const, ?_⟩
    rw [show reducedValues = nofun from by funext path; cases path]
    exact .const
  | var matched induction =>
    obtain ⟨reduced, step, matched⟩ := induction (reducedValues := fun path => reducedValues (some path))
      (fun path => reductions (some path))
    refine ⟨_, .app step (reductions none), ?_⟩
    rw [show reducedValues = fun path => path.elim (reducedValues none)
      (fun path => reducedValues (some path)) from by funext path; cases path <;> rfl]
    exact matched.var
  | app _ _ functionIH argumentIH =>
    obtain ⟨reducedFunction, functionStep, functionMatched⟩ :=
      functionIH (reducedValues := fun path => reducedValues (.inl path)) (fun path => reductions (.inl path))
    obtain ⟨reducedArgument, argumentStep, argumentMatched⟩ :=
      argumentIH (reducedValues := fun path => reducedValues (.inr path)) (fun path => reductions (.inr path))
    refine ⟨_, .app functionStep argumentStep, ?_⟩
    rw [show reducedValues = Sum.elim (fun path => reducedValues (.inl path))
      (fun path => reducedValues (.inr path)) from by funext path; cases path <;> rfl]
    exact functionMatched.app argumentMatched

/-- The complete Prop-source application EXTRA induction clause. Only the
original function and argument simulations are required. All right captures
may reduce, and the actual equality checks are transported to those reductions
before hereditary joining handles arbitrary left witness shapes. -/
theorem CoreSimulates.app_quot_prop_extra
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (sourceTyped : environment.HasType universes locals (.app function argument) type)
    (rightTyped : environment.HasType universes locals (.app rightFunction rightArgument) type)
    (functionSimulation : CoreSimulates environmentWF universes locals function rightFunction)
    (argumentSimulation : CoreSimulates environmentWF universes locals argument rightArgument)
    (zeroChecked : zeroLike sourceUniverse = true)
    (matched : quotLiftPattern.Matches (.app rightFunction rightArgument)
      [sourceUniverse, targetUniverse] values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals)
      [sourceUniverse, targetUniverse] values)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (values path) (reducedValues path)) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals (.app rightFunction rightArgument)
        (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] reducedValues) ∧
      Steps environmentWF universes locals (.app function argument) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] reducedValues) ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals
        (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] reducedValues) type := by
  letI := environmentWF.reductionParams universes
  have captureEqual (path) : environment.IsDefEqU universes locals (values path) (reducedValues path) := by
    obtain ⟨_, typed⟩ := rightTyped.matches_inv localsWF matched path
    exact ((reductions path).defeq localsWF typed).toU
  have reducedChecked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals)
      [sourceUniverse, targetUniverse] reducedValues := by
    simp only [quotLiftPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at checked ⊢
    exact ⟨(captureEqual _).symm.trans environmentWF localsWF
        (checked.1.trans environmentWF localsWF (captureEqual _)),
      (captureEqual _).symm.trans environmentWF localsWF
        (checked.2.1.trans environmentWF localsWF (captureEqual _)), trivial⟩
  obtain ⟨reducedFunction, reducedArgument, functionStep, argumentStep, reducedMatched⟩ :
      ∃ reducedFunction reducedArgument,
        ParRed locals rightFunction reducedFunction ∧ ParRed locals rightArgument reducedArgument ∧
        quotLiftPattern.Matches (.app reducedFunction reducedArgument)
          [sourceUniverse, targetUniverse] reducedValues := by
    cases matched with
    | app functionMatched argumentMatched =>
      obtain ⟨reducedFunction, functionStep, functionMatched⟩ :=
        reduceMatchedCaptures functionMatched (fun path => reductions (.inl path))
      obtain ⟨reducedArgument, argumentStep, argumentMatched⟩ :=
        reduceMatchedCaptures argumentMatched (fun path => reductions (.inr path))
      refine ⟨reducedFunction, reducedArgument, functionStep, argumentStep, ?_⟩
      rw [show reducedValues = Sum.elim (fun path => reducedValues (.inl path))
        (fun path => reducedValues (.inr path)) from by funext path; cases path <;> rfl]
      exact functionMatched.app argumentMatched
  obtain ⟨leftFunction, functionSteps, functionNormal⟩ := functionSimulation functionStep
  obtain ⟨leftArgument, argumentSteps, argumentNormal⟩ := argumentSimulation argumentStep
  obtain ⟨_, _, functionTyped, argumentTyped⟩ := sourceTyped.app_inv environmentWF.ordered localsWF
  have leftFunctionTyped := functionSteps.hasType registered localsWF functionTyped
  have leftArgumentTyped := argumentSteps.hasType registered localsWF argumentTyped
  have normal := NormalEq.appDF leftFunctionTyped
    ((functionNormal.defeq localsWF).of_l environmentWF localsWF leftFunctionTyped).hasType.2
    leftArgumentTyped ((argumentNormal.defeq localsWF).of_l environmentWF localsWF leftArgumentTyped).hasType.2
    functionNormal argumentNormal
  have initial := functionSteps.app argumentSteps
  obtain ⟨joined, _, finalPath, finalNormal, joinedTyped, finalTyped⟩ := normal_quot_prop_join
    registered localsWF zeroChecked normal (List.Forall₂.nil : List.Forall₂ (NormalEq locals) [] [])
    (initial.hasType registered localsWF sourceTyped) reducedMatched reducedChecked
  exact ⟨joined, .extra (.quot registered) matched checked reductions,
    initial.trans finalPath, finalNormal, joinedTyped, finalTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
