import Lean4Lean.Theory.Typing.QuotMajorExposure

/-! # Nonzero-source quotient EXTRA replay

The original major simulation supplies a normal constructor comparison after
all actual right captures reduce. Actual head separation exposes a constructor
on the left; its dependent parameter equalities reconstruct the real pattern
checks. The function and major simulations are exactly recursive premises.
-/

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private reduceMatchedCaptures from Lean4Lean.Theory.Typing.QuotHereditaryExtra

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

private theorem matchedConstructorShape
    (matched : (Pattern.varN (.const ``Quot.mk) 3).Matches source levels captures) :
    source = .app (.app (.app (.const ``Quot.mk levels) (captures (some (some none))))
      (captures (some none))) (captures none) := by
  cases matched with
  | var h => cases h with
    | var h => cases h with
      | var h => cases h with
        | const => rfl

/-- Nonzero-source root EXTRA, with an arbitrary left major. Both original
recursive simulations suffice, and every right capture may reduce. -/
theorem CoreSimulates.quot_nonzero_extra
    {sourceUniverse targetUniverse : VLevel}
    {domain relation target function respect major rightPrefix rightMajor resultType : VExpr}
    {levels : List VLevel} {values reducedValues : quotLiftPattern.Path → VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) resultType)
    (rightTyped : environment.HasType universes locals (.app rightPrefix rightMajor) resultType)
    (nonzero : zeroLike sourceUniverse = false)
    (domainNormal : @NormalEq (environmentWF.reductionParams universes) locals
      domain (values (.inl (some (some (some (some none)))))))
    (relationNormal : @NormalEq (environmentWF.reductionParams universes) locals
      relation (values (.inl (some (some (some none))))))
    (functionSimulation : CoreSimulates environmentWF universes locals
      function (values (.inl (some none))))
    (majorSimulation : CoreSimulates environmentWF universes locals major rightMajor)
    (matched : quotLiftPattern.Matches (.app rightPrefix rightMajor) levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (values path) (reducedValues path)) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals (.app rightPrefix rightMajor)
        (quotLiftPatternResult.apply levels reducedValues) ∧
      Steps environmentWF universes locals
        (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
          domain) relation) target) function) respect) major) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels reducedValues) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels reducedValues) resultType := by
  letI := environmentWF.reductionParams universes
  have rightStep : ParRed locals (.app rightPrefix rightMajor)
      (quotLiftPatternResult.apply levels reducedValues) :=
    .extra (.quot registered) matched checked reductions
  have captureEqual (path) : environment.IsDefEqU universes locals
      (values path) (reducedValues path) := by
    obtain ⟨_, captureTyped⟩ := rightTyped.matches_inv localsWF matched path
    exact ((reductions path).defeq localsWF captureTyped).toU
  obtain ⟨_, _, _, constructorRegistered, _, _⟩ := environmentWF.quotientObjects registered
  obtain ⟨_, _, levelShape, _, _, _, _, _, _, _, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF (environmentWF.quotientObjects registered).2.2.1 typed
  have ⟨rfl, rest⟩ := List.cons.inj levelShape
  have ⟨rfl, _⟩ := List.cons.inj rest
  obtain ⟨_, _, _, rightMajorTyped⟩ := rightTyped.app_inv environmentWF.ordered localsWF
  obtain ⟨reducedMajor, majorStep, majorMatched⟩ :
      ∃ reducedMajor, ParRed locals rightMajor reducedMajor ∧
        ∃ constructorLevels, (Pattern.varN (.const ``Quot.mk) 3).Matches
          reducedMajor constructorLevels (fun path => reducedValues (.inr path)) := by
    cases matched with
    | app _ majorMatched =>
      obtain ⟨reducedMajor, step, hm⟩ := reduceMatchedCaptures majorMatched
        (fun path => reductions (.inr path))
      exact ⟨reducedMajor, step, _, hm⟩
  obtain ⟨joinedMajor, majorSteps, majorNormal⟩ := majorSimulation majorStep
  obtain ⟨constructorLevels, majorMatched⟩ := majorMatched
  have reducedMajorTyped := majorStep.hasType localsWF rightMajorTyped
  have majorShape : ∃ constructorUniverse,
      reducedMajor = .app (.app (.app (.const ``Quot.mk [constructorUniverse])
        (reducedValues (.inr (some (some none)))))
        (reducedValues (.inr (some none)))) (reducedValues (.inr none)) := by
    have shape := matchedConstructorShape majorMatched
    rw [shape] at reducedMajorTyped
    obtain ⟨u, rfl, _⟩ := quotMk_inv environmentWF localsWF constructorRegistered reducedMajorTyped
    exact ⟨u, shape⟩
  obtain ⟨constructorUniverse, majorShape⟩ := majorShape
  rw [majorShape] at majorNormal
  have joinedMajorTyped := majorSteps.hasType registered localsWF majorTyped
  obtain ⟨leftUniverse, leftDomain, leftRelation, leftValue, exposed, _, domains, relations,
      payloads, exposedTyped⟩ := normal_quot_major_constructor registered localsWF nonzero
        joinedMajorTyped majorNormal
  have domainEqual : environment.IsDefEqU universes locals domain leftDomain :=
    (domainNormal.defeq localsWF).trans environmentWF localsWF
      (checked.1.trans environmentWF localsWF
        ((captureEqual (.inr (some (some none)))).trans environmentWF localsWF
          (domains.defeq localsWF).symm))
  have relationEqual : environment.IsDefEqU universes locals relation leftRelation :=
    (relationNormal.defeq localsWF).trans environmentWF localsWF
      (checked.2.1.trans environmentWF localsWF
        ((captureEqual (.inr (some none))).trans environmentWF localsWF
          (relations.defeq localsWF).symm))
  obtain ⟨joinedFunction, functionSteps, functionNormal⟩ :=
    functionSimulation (reductions (.inl (some none)))
  have prefixBase : Steps environmentWF universes locals
      (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse]) domain) relation) target)
      (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse]) domain) relation) target) := .rfl
  have prefixSteps := (prefixBase.app functionSteps).app (argument := respect) .rfl
  have initial := prefixSteps.app (majorSteps.trans (Steps.core exposed))
  have initialTyped := initial.hasType registered localsWF typed
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift)
    (ls := [sourceUniverse, targetUniverse]) |>.var (a' := domain) |>.var (a' := relation)
    |>.var (a' := target) |>.var (a' := joinedFunction) |>.var (a' := respect)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [leftUniverse])
    |>.var (a' := leftDomain) |>.var (a' := leftRelation) |>.var (a' := leftValue)
  have leftMatched := functionMatched.app constructorMatched
  have leftStep : ParRed locals _ (.app joinedFunction leftValue) :=
    .extra (.quot registered) leftMatched ⟨domainEqual, relationEqual, trivial⟩ (fun _ => .rfl)
  have resultTyped := leftStep.hasType localsWF initialTyped
  obtain ⟨_, _, joinedFunctionTyped, leftValueTyped⟩ :=
    resultTyped.app_inv environmentWF.ordered localsWF
  have reducedFunctionTyped := ((functionNormal.defeq localsWF).of_l environmentWF localsWF
    joinedFunctionTyped).hasType.2
  have reducedValueTyped := ((payloads.defeq localsWF).of_l environmentWF localsWF
    leftValueTyped).hasType.2
  have path := initial.trans (Steps.core (.tail .rfl leftStep))
  exact ⟨_, rightStep, path,
    .appDF joinedFunctionTyped reducedFunctionTyped leftValueTyped reducedValueTyped
      functionNormal payloads,
    Steps.hasType registered localsWF path typed, rightStep.hasType localsWF rightTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
