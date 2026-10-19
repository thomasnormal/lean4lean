import Lean4Lean.Theory.Typing.QuotNormalBeta

namespace Lean4Lean.VEnv.QuotPropReduction

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

/-- When both sources really match, normal equality of the captures transports
the two actual equality checks. This works at every source universe. Only the
function and payload occur in the rule's result and need recursive simulation.
No general preservation of matching by normal equality is assumed. -/
theorem CoreSimulates.quot_constructor_extra
    {left right resultType : VExpr} {leftLevels rightLevels : List VLevel}
    {leftValues rightValues reducedValues : quotLiftPattern.Path → VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftTyped : environment.HasType universes locals left resultType)
    (rightTyped : environment.HasType universes locals right resultType)
    (leftMatched : quotLiftPattern.Matches left leftLevels leftValues)
    (rightMatched : quotLiftPattern.Matches right rightLevels rightValues)
    (capturesNormal : ∀ path, @NormalEq (environmentWF.reductionParams universes) locals
      (leftValues path) (rightValues path))
    (functionSimulation : CoreSimulates environmentWF universes locals
      (leftValues (.inl (some none))) (rightValues (.inl (some none))))
    (valueSimulation : CoreSimulates environmentWF universes locals
      (leftValues (.inr none)) (rightValues (.inr none)))
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) rightLevels rightValues)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (rightValues path) (reducedValues path)) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals right
        (quotLiftPatternResult.apply rightLevels reducedValues) ∧
      @ParRed (environmentWF.reductionParams universes) locals left
        (quotLiftPatternResult.apply leftLevels leftValues) ∧
      Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply rightLevels reducedValues) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply rightLevels reducedValues) resultType := by
  letI := environmentWF.reductionParams universes
  have leftChecked : quotLiftPatternCheck.OK
      (environment.IsDefEqU universes locals) leftLevels leftValues := by
    simp only [quotLiftPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at checked ⊢
    exact ⟨((capturesNormal (.inl (some (some (some (some none)))))).defeq localsWF).trans
        environmentWF localsWF (checked.1.trans environmentWF localsWF
          ((capturesNormal (.inr (some (some none)))).defeq localsWF).symm),
      ((capturesNormal (.inl (some (some (some none))))).defeq localsWF).trans
        environmentWF localsWF (checked.2.1.trans environmentWF localsWF
          ((capturesNormal (.inr (some none))).defeq localsWF).symm), trivial⟩
  have rightStep : ParRed locals right (quotLiftPatternResult.apply rightLevels reducedValues) :=
    .extra (.quot registered) rightMatched checked reductions
  have leftStep : ParRed locals left (quotLiftPatternResult.apply leftLevels leftValues) :=
    .extra (.quot registered) leftMatched leftChecked (fun _ => .rfl)
  have resultTyped := leftStep.hasType localsWF leftTyped
  obtain ⟨_, _, functionTyped, valueTyped⟩ := resultTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨joinedFunction, functionSteps, functionNormal⟩ :=
    functionSimulation (reductions (.inl (some none)))
  obtain ⟨joinedValue, valueSteps, valueNormal⟩ := valueSimulation (reductions (.inr none))
  have joinedFunctionTyped := functionSteps.hasType registered localsWF functionTyped
  have joinedValueTyped := valueSteps.hasType registered localsWF valueTyped
  have reducedFunctionTyped := ((functionNormal.defeq localsWF).of_l environmentWF localsWF
    joinedFunctionTyped).hasType.2
  have reducedValueTyped := ((valueNormal.defeq localsWF).of_l environmentWF localsWF
    joinedValueTyped).hasType.2
  have path : Steps environmentWF universes locals left (.app joinedFunction joinedValue) :=
    (ReflTransGen.tail .rfl (.core leftStep)).trans (functionSteps.app valueSteps)
  exact ⟨_, rightStep, leftStep, path,
    .appDF joinedFunctionTyped reducedFunctionTyped joinedValueTyped reducedValueTyped
      functionNormal valueNormal,
    path.hasType registered localsWF leftTyped, rightStep.hasType localsWF rightTyped⟩

/-- Prop-source firing does not require the left major to match a constructor.
The right side uses the actual quotient pattern, equality checks, and parallel
reductions. Only the function capture needs a recursive simulation hypothesis;
proof irrelevance joins the selected left proof to the reduced right payload. -/
theorem CoreSimulates.quot_prop_extra
    {sourceUniverse targetUniverse : VLevel}
    {domain relation target function respect major right resultType : VExpr}
    {levels : List VLevel} {values reducedValues : quotLiftPattern.Path → VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) resultType)
    (rightTyped : environment.HasType universes locals right resultType)
    (zeroChecked : zeroLike sourceUniverse = true)
    (domainNormal : @NormalEq (environmentWF.reductionParams universes) locals
      domain (values (.inl (some (some (some (some none)))))))
    (functionSimulation : CoreSimulates environmentWF universes locals
      function (values (.inl (some none))))
    (matched : quotLiftPattern.Matches right levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (values path) (reducedValues path)) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals right
        (quotLiftPatternResult.apply levels reducedValues) ∧
      Steps environmentWF universes locals
        (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
          domain) relation) target) function) respect) major) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels reducedValues) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels reducedValues) resultType := by
  letI := environmentWF.reductionParams universes
  have rewriteStep : ParRed locals right (quotLiftPatternResult.apply levels reducedValues) :=
    .extra (.quot registered) matched checked reductions
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
  obtain ⟨joinedFunction, functionSteps, functionNormal⟩ :=
    functionSimulation (reductions (.inl (some none)))
  have joinedFunctionTyped := functionSteps.hasType registered localsWF functionTyped
  have path : Steps environmentWF universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major)
      (.app joinedFunction (selector domain relation major)) :=
    (ReflTransGen.tail .rfl (.unfold computed)).trans (functionSteps.app .rfl)
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
  have reducedValue := (reductions (.inr none)).hasType localsWF alignedValue
  have leftValue := ((domainNormal.defeq localsWF).symm.of_l environmentWF localsWF
    rightDomainTyped).defeq reducedValue
  have reducedFunction := ((functionNormal.defeq localsWF).of_l environmentWF localsWF
    joinedFunctionTyped).hasType.2
  exact ⟨_, rewriteStep, path,
    .appDF joinedFunctionTyped reducedFunction selectedTyped leftValue functionNormal
      (.proofIrrel domainProp selectedTyped leftValue),
    path.hasType registered localsWF typed, rewriteStep.hasType localsWF rightTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
