import Lean4Lean.Theory.Typing.QuotNonzeroExtra

/-! # Application simulation for actual checked quotient reduction

Hereditary exposure joins an actual checked root firing at every source universe.
This closes the application clause using only its original recursive simulations.
-/

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private matchedConstructorShape from Lean4Lean.Theory.Typing.QuotNonzeroExtra
open private proofSpineType constantNormalCases matchedLiftSpine reduceMatchedCaptures
  from Lean4Lean.Theory.Typing.QuotHereditaryExtra

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

/-- Join an already normally related root at a nonzero source. Neither a
matching certificate nor a recursive simulation is required of the left major. -/
theorem normal_quot_nonzero_root
    {sourceUniverse targetUniverse : VLevel}
    {domain relation target function respect major rightPrefix rightMajor resultType : VExpr}
    {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
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
    (functionNormal : @NormalEq (environmentWF.reductionParams universes) locals
      function (values (.inl (some none))))
    (majorNormal : @NormalEq (environmentWF.reductionParams universes) locals major rightMajor)
    (matched : quotLiftPattern.Matches (.app rightPrefix rightMajor) levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals (.app rightPrefix rightMajor)
        (quotLiftPatternResult.apply levels values) ∧
      Steps environmentWF universes locals
        (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
          domain) relation) target) function) respect) major) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels values) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels values) resultType := by
  letI := environmentWF.reductionParams universes
  have rightStep : ParRed locals (.app rightPrefix rightMajor)
      (quotLiftPatternResult.apply levels values) :=
    .extra (.quot registered) matched checked (fun _ => .rfl)
  obtain ⟨_, _, liftRegistered, constructorRegistered, _, _⟩ := environmentWF.quotientObjects registered
  obtain ⟨_, _, levelShape, _, _, _, _, _, _, _, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered typed
  have ⟨rfl, rest⟩ := List.cons.inj levelShape
  have ⟨rfl, _⟩ := List.cons.inj rest
  obtain ⟨_, _, _, rightMajorTyped⟩ := rightTyped.app_inv environmentWF.ordered localsWF
  have majorShape : ∃ constructorUniverse,
      rightMajor = .app (.app (.app (.const ``Quot.mk [constructorUniverse])
        (values (.inr (some (some none))))) (values (.inr (some none)))) (values (.inr none)) := by
    cases matched with
    | app _ majorMatched =>
      have shape := matchedConstructorShape majorMatched
      rw [shape] at rightMajorTyped
      obtain ⟨u, rfl, _⟩ := quotMk_inv environmentWF localsWF constructorRegistered rightMajorTyped
      exact ⟨u, shape⟩
  obtain ⟨constructorUniverse, majorShape⟩ := majorShape
  rw [majorShape] at majorNormal
  obtain ⟨leftUniverse, leftDomain, leftRelation, leftValue, exposed, _, domains, relations,
      payloads, _⟩ := normal_quot_major_constructor registered localsWF nonzero majorTyped majorNormal
  have domainEqual := (domainNormal.defeq localsWF).trans environmentWF localsWF
    (checked.1.trans environmentWF localsWF (domains.defeq localsWF).symm)
  have relationEqual := (relationNormal.defeq localsWF).trans environmentWF localsWF
    (checked.2.1.trans environmentWF localsWF (relations.defeq localsWF).symm)
  have initial : Steps environmentWF universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) _ :=
    Steps.app .rfl (Steps.core exposed)
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift)
    (ls := [sourceUniverse, targetUniverse]) |>.var (a' := domain) |>.var (a' := relation)
    |>.var (a' := target) |>.var (a' := function) |>.var (a' := respect)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [leftUniverse])
    |>.var (a' := leftDomain) |>.var (a' := leftRelation) |>.var (a' := leftValue)
  have leftStep : ParRed locals _ (.app function leftValue) :=
    .extra (.quot registered) (functionMatched.app constructorMatched)
      ⟨domainEqual, relationEqual, trivial⟩ (fun _ => .rfl)
  have resultTyped := leftStep.hasType localsWF (initial.hasType registered localsWF typed)
  obtain ⟨_, _, functionTyped, valueTyped⟩ := resultTyped.app_inv environmentWF.ordered localsWF
  have path := initial.trans (Steps.core (.tail .rfl leftStep))
  exact ⟨_, rightStep, path,
    .appDF functionTyped ((functionNormal.defeq localsWF).of_l environmentWF localsWF functionTyped).hasType.2
      valueTyped ((payloads.defeq localsWF).of_l environmentWF localsWF valueTyped).hasType.2
      functionNormal payloads, resultTyped, rightStep.hasType localsWF rightTyped⟩

/-- The actual root join dispatches on the source universe without imposing
constructor matching on a Prop major or losing actual nonzero parameter checks. -/
theorem normal_quot_root
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect) major) resultType)
    (rightTyped : environment.HasType universes locals (.app rightPrefix rightMajor) resultType)
    (domainNormal : @NormalEq (environmentWF.reductionParams universes) locals
      domain (values (.inl (some (some (some (some none)))))))
    (relationNormal : @NormalEq (environmentWF.reductionParams universes) locals
      relation (values (.inl (some (some (some none))))))
    (functionNormal : @NormalEq (environmentWF.reductionParams universes) locals
      function (values (.inl (some none))))
    (majorNormal : @NormalEq (environmentWF.reductionParams universes) locals major rightMajor)
    (matched : quotLiftPattern.Matches (.app rightPrefix rightMajor) levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals (.app rightPrefix rightMajor)
        (quotLiftPatternResult.apply levels values) ∧
      Steps environmentWF universes locals
        (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
          domain) relation) target) function) respect) major) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels values) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels values) resultType := by
  cases zero : zeroLike sourceUniverse with
  | true => exact normal_quot_prop_root registered localsWF typed rightTyped zero domainNormal functionNormal matched checked
  | false =>
    exact normal_quot_nonzero_root registered localsWF typed rightTyped zero
      domainNormal relationNormal functionNormal majorNormal matched checked

private theorem rigidQuotJoin
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
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
                      have captures : values (.inl (some (some (some (some none))))) = domain ∧
                          values (.inl (some (some (some none)))) = relation ∧
                          values (.inl (some none)) = function := by
                        let .app functionMatched _ := matched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .var functionMatched := functionMatched
                        let .const := functionMatched
                        exact ⟨rfl, rfl, rfl⟩
                      obtain ⟨rootResult, _, rootSteps, joinedNormal, _, _⟩ :=
                        normal_quot_root registered localsWF rootTyped rightRootTyped
                          (by simpa only [captures.1] using domainNormal)
                          (by simpa only [captures.2.1] using relationNormal)
                          (by simpa only [captures.2.2] using functionNormal) majorNormal matched checked
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

/-- Any normally related left source follows a checked quotient quotient
firing, beneath any finite related argument list. The actual left path is
constructed from hereditary exposure; no matching or simulation premise is
required of the left source. Both endpoints retain the original result type. -/
theorem normal_quot_join
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
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
  obtain ⟨joined, finalPath, finalNormal⟩ := rigidQuotJoin registered exposed
    localsWF rfl (by simpa only [← equation] using matched) checked
  have path : Steps environmentWF universes locals (applyArguments left pending) joined :=
    (Steps.core corePath).trans finalPath
  have joinedTyped := path.hasType registered localsWF typed
  have rightStep : ParRed locals right (quotLiftPatternResult.apply [sourceUniverse, targetUniverse] values) :=
    .extra (.quot registered) matched checked (fun _ => .rfl)
  exact ⟨joined, rightStep.applyArguments pending',
    path, finalNormal, joinedTyped,
    ((finalNormal.defeq localsWF).of_l environmentWF localsWF joinedTyped).hasType.2⟩

/-- The complete all-universe application EXTRA induction clause. Only the
original function and argument simulations are required. All right captures
may reduce, and the actual equality checks are transported to those reductions
before hereditary joining handles arbitrary left witness shapes. -/
theorem CoreSimulates.app_quot_extra
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (sourceTyped : environment.HasType universes locals (.app function argument) type)
    (rightTyped : environment.HasType universes locals (.app rightFunction rightArgument) type)
    (functionSimulation : CoreSimulates environmentWF universes locals function rightFunction)
    (argumentSimulation : CoreSimulates environmentWF universes locals argument rightArgument)
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
  obtain ⟨joined, _, finalPath, finalNormal, joinedTyped, finalTyped⟩ := normal_quot_join
    registered localsWF normal (List.Forall₂.nil : List.Forall₂ (NormalEq locals) [] [])
    (initial.hasType registered localsWF sourceTyped) reducedMatched reducedChecked
  exact ⟨joined, .extra (.quot registered) matched checked reductions,
    initial.trans finalPath, finalNormal, joinedTyped, finalTyped⟩

include environmentWF in
/-- Actual matched quotient applications have exactly the two stored universes. -/
private theorem matchedLiftLevels
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals right type)
    (matched : quotLiftPattern.Matches right levels values) :
    ∃ sourceUniverse targetUniverse, levels = [sourceUniverse, targetUniverse] := by
  obtain ⟨major, shape⟩ := matchedLiftSpine matched
  rw [shape] at typed
  obtain ⟨u, v, levels, _⟩ := quotLift_inv environmentWF localsWF
    (environmentWF.quotientObjects registered).2.2.1 typed
  exact ⟨u, v, levels⟩

/-- The complete application induction clause: congruence, root beta and every
actual stored EXTRA. The left function and argument are arbitrary. -/
theorem CoreSimulates.app
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftFunctionTyped : environment.HasType universes locals function (.forallE domain body))
    (rightFunctionTyped : environment.HasType universes locals rightFunction (.forallE domain body))
    (leftArgumentTyped : environment.HasType universes locals argument domain)
    (rightArgumentTyped : environment.HasType universes locals rightArgument domain)
    (functionsNormal : @NormalEq (environmentWF.reductionParams universes) locals function rightFunction)
    (argumentsNormal : @NormalEq (environmentWF.reductionParams universes) locals argument rightArgument)
    (functionSimulation : CoreSimulates environmentWF universes locals function rightFunction)
    (argumentSimulation : CoreSimulates environmentWF universes locals argument rightArgument) :
    CoreSimulates environmentWF universes locals (.app function argument) (.app rightFunction rightArgument) := by
  letI := environmentWF.reductionParams universes
  have applicationNormal := NormalEq.appDF leftFunctionTyped rightFunctionTyped
    leftArgumentTyped rightArgumentTyped functionsNormal argumentsNormal
  have sourceTyped := leftFunctionTyped.app leftArgumentTyped
  have rightTyped := ((applicationNormal.defeq localsWF).of_l environmentWF localsWF sourceTyped).hasType.2
  intro result reduction
  cases reduction with
  | app functions arguments =>
    exact CoreSimulates.app_congr registered localsWF leftFunctionTyped rightFunctionTyped
      leftArgumentTyped rightArgumentTyped functionSimulation argumentSimulation functions arguments
  | beta bodies arguments =>
    obtain ⟨joined, _, steps, normal, _⟩ := CoreSimulates.app_beta registered localsWF
      (leftFunctionTyped.app leftArgumentTyped) functionSimulation argumentSimulation bodies arguments
    exact ⟨joined, steps, normal⟩
  | extra rule matched checked reductions =>
    cases rule with
    | delta => cases matched
    | quot actualRegistered =>
      obtain ⟨u, v, rfl⟩ := matchedLiftLevels (environmentWF := environmentWF) actualRegistered localsWF
        (rightFunctionTyped.app rightArgumentTyped) matched
      obtain ⟨joined, _, steps, normal, _⟩ := CoreSimulates.app_quot_extra actualRegistered localsWF
        sourceTyped rightTyped
        functionSimulation argumentSimulation matched checked reductions
      exact ⟨joined, steps, normal⟩

/-- Every actual normal equality simulates the original core reduction by the
repaired candidate paths. This replaces the false core-only simulation target;
it does not assert confluence of either reduction relation. -/
theorem normal_core_simulates
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right) :
    CoreSimulates environmentWF universes locals left right := by
  letI := environmentWF.reductionParams universes
  induction normal with
  | refl typed => exact fun {_} => CoreSimulates.refl localsWF typed
  | sortDF leftWF rightWF equal => exact fun {_} => CoreSimulates.sortDF leftWF rightWF equal
  | constDF found leftWF rightWF arity levels => exact fun {_} => CoreSimulates.constDF localsWF found leftWF rightWF arity levels
  | appDF leftFunction rightFunction leftArgument rightArgument functions arguments functionIH argumentIH =>
    exact fun {_} => CoreSimulates.app registered localsWF leftFunction rightFunction leftArgument rightArgument functions arguments
      (functionIH localsWF) (argumentIH localsWF)
  | lamDF leftDomain rightDomain bodies bodyIH =>
    exact fun {_} => CoreSimulates.lamDF registered localsWF leftDomain rightDomain bodies
      (bodyIH ⟨localsWF, _, leftDomain.hasType.1⟩)
  | forallEDF domainEqual domains bodyTyped bodies domainIH bodyIH =>
    exact fun {_} => CoreSimulates.forallEDF registered localsWF domainEqual domains bodyTyped bodies (domainIH localsWF)
      (bodyIH ⟨localsWF, _, domainEqual.hasType.1⟩)
  | etaL functionTyped bodies bodyIH =>
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    exact fun {_} => CoreSimulates.etaL localsWF functionTyped (bodyIH ⟨localsWF, _, domainTyped⟩)
  | etaR functionTyped bodies bodyIH =>
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    exact fun {_} => CoreSimulates.etaR localsWF functionTyped (bodyIH ⟨localsWF, _, domainTyped⟩)
  | proofIrrel propositionTyped leftTyped rightTyped =>
    exact fun {_} => CoreSimulates.proofIrrel localsWF propositionTyped leftTyped rightTyped

/-- The repaired one-step simulation retains any supplied original type on
both outputs, including a converted dependent result type. -/
theorem normal_parRed_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals left type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (reduction : @ParRed (environmentWF.reductionParams universes) locals right result) :
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined result ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals result type :=
  CoreSimulates.typed registered localsWF typed
    (normal_core_simulates registered localsWF normal) reduction

/-- Every finite original-core path is simulated by repaired candidate paths.
Intermediate normal comparisons are consumed directly, without transitivity
of NormalEq or any confluence theorem. -/
theorem normal_parRedS_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals left type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (reduction : @ParRedS (environmentWF.reductionParams universes) locals right result) :
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined result ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals result type := by
  letI := environmentWF.reductionParams universes
  induction reduction with
  | rfl =>
    exact ⟨_, .rfl, normal, typed,
      ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2⟩
  | tail previous step induction =>
    obtain ⟨middle, path, compared, middleTyped, _⟩ := induction
    obtain ⟨joined, rest, finalNormal, joinedTyped, resultTyped⟩ :=
      normal_parRed_join registered localsWF middleTyped compared step
    exact ⟨joined, path.trans rest, finalNormal, joinedTyped, resultTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
