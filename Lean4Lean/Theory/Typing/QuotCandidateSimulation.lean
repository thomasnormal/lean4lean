import Lean4Lean.Theory.Typing.QuotApplicationSimulation

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private proofSpineType constantNormalCases
  from Lean4Lean.Theory.Typing.QuotHereditaryExtra

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

private theorem liftSelectorTyped
    (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
        [domain, relation, target, function, respect, major]) type)
    (zeroChecked : zeroLike sourceUniverse = true) :
    environment.HasType universes locals domain (.sort .zero) ∧
      environment.HasType universes locals (selector domain relation major) domain := by
  obtain ⟨_, inductionRegistered, liftRegistered, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  obtain ⟨_, _, levelsEqual, sourceWF, _, domainTyped, relationTyped,
    _, _, _, majorTyped, _⟩ :=
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
  exact ⟨domainProp, selector_hasType environmentWF.ordered quotientRegistered
    constructorRegistered inductionRegistered domainProp relationTyped (second.defeq majorTyped)⟩

/-- Normally related Prop-source lift roots unfold to normally related results,
including neutral majors and unrelated proof witnesses. -/
theorem normal_unfold_root
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftTyped : environment.HasType universes locals
      (applyArguments (.const ``Quot.lift [leftSource, leftTarget])
        [domain, relation, target, function, respect, major]) type)
    (rightTyped : environment.HasType universes locals
      (applyArguments (.const ``Quot.lift [rightSource, rightTarget])
        [domain', relation', target', function', respect', major']) type)
    (leftZero : zeroLike leftSource = true)
    (rightZero : zeroLike rightSource = true)
    (domains : @NormalEq (environmentWF.reductionParams universes) locals domain domain')
    (functions : @NormalEq (environmentWF.reductionParams universes) locals function function') :
    @NormalEq (environmentWF.reductionParams universes) locals
      (.app function (selector domain relation major))
      (.app function' (selector domain' relation' major')) := by
  letI := environmentWF.reductionParams universes
  obtain ⟨domainProp, leftSelector⟩ := liftSelectorTyped environmentWF registered localsWF leftTyped leftZero
  obtain ⟨_, rightSelector⟩ := liftSelectorTyped environmentWF registered localsWF rightTyped rightZero
  have alignedSelector := ((domains.defeq localsWF).symm.of_l environmentWF localsWF
    ((domains.defeq localsWF).of_l environmentWF localsWF domainProp).hasType.2 ).defeq rightSelector
  obtain ⟨_, _, liftRegistered, _⟩ := environmentWF.quotientObjects registered
  obtain ⟨_, _, levelsEqual, _, _, _, _, _, functionTyped, _, _, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered leftTyped
  cases levelsEqual
  exact .appDF functionTyped
    ((functions.defeq localsWF).of_l environmentWF localsWF functionTyped).hasType.2
    leftSelector alignedSelector functions (.proofIrrel domainProp leftSelector alignedSelector)

private theorem rigidUnfoldJoin
    {sourceUniverse targetUniverse : VLevel}
    (registered : environment.defeqs quotDefEq)
    (zeroChecked : zeroLike sourceUniverse = true)
    (exposed : RigidSpine environmentWF universes ``Quot.lift
      [sourceUniverse, targetUniverse] locals left arguments) :
    OnCtx locals (environment.IsType universes) →
    ∀ {domain relation target function respect major : VExpr} {pending : List VExpr},
      arguments = [domain, relation, target, function, respect, major] ++ pending →
      ∃ joined, Steps environmentWF universes locals left joined ∧
        @NormalEq (environmentWF.reductionParams universes) locals joined
          (applyArguments (.app function (selector domain relation major)) pending) := by
  letI := environmentWF.reductionParams universes
  induction exposed with
  | @proof proposition left arguments locals propositionTyped leftTyped rightTyped =>
    intro localsWF domain relation target function respect major pending equation
    have step : Steps environmentWF universes locals
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
          [domain, relation, target, function, respect, major])
        (.app function (selector domain relation major)) :=
      .tail .rfl (.unfold (by simp only [applyArguments, unfold, zeroChecked, ite_true]))
    have finalTyped := (step.applyArguments pending).hasType registered localsWF
      (show environment.HasType universes _ _ _ from by
        simpa only [equation, applyArguments_append] using rightTyped)
    exact ⟨_, .rfl, .proofIrrel propositionTyped leftTyped finalTyped⟩
  | @spine leftLevels leftArguments type arguments locals typed heads normals =>
    intro localsWF domain relation target function respect major pending equation
    have step : Steps environmentWF universes locals
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
          [domain, relation, target, function, respect, major])
        (.app function (selector domain relation major)) :=
      .tail .rfl (.unfold (by simp only [applyArguments, unfold, zeroChecked, ite_true]))
    rcases constantNormalCases heads with levelsEqual | ⟨proposition, propositionTyped, headProof, _⟩
    · cases levelsEqual with
      | @cons leftSource _ _ _ sourceEqual levelsEqual =>
        cases levelsEqual with
        | @cons leftTargetUniverse _ _ _ targetEqual levelsEqual =>
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
                      have joinedNormal := normal_unfold_root registered localsWF rootTyped rightRootTyped
                        leftZero zeroChecked domainNormal functionNormal
                      have rootSteps : Steps environmentWF universes locals
                          (applyArguments (.const ``Quot.lift [leftSource, leftTargetUniverse]) [leftDomain, leftRelation, leftTarget, leftFunction, leftRespect, leftMajor])
                          (.app leftFunction (selector leftDomain leftRelation leftMajor)) :=
                        .tail .rfl (.unfold (by simp only [applyArguments, unfold, leftZero, ite_true]))
                      have path := rootSteps.applyArguments leftPending
                      exact ⟨_, path, normal_spine_congr localsWF
                        (path.hasType registered localsWF typed) joinedNormal pendingNormal⟩
    · have typeProp := proofSpineType (environmentWF := environmentWF)
        localsWF propositionTyped headProof typed
      have sourceNormal := normal_spine_congr localsWF typed heads normals
      have rightTyped := ((sourceNormal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2
      have finalTyped := (step.applyArguments pending).hasType registered localsWF
        (show environment.HasType universes _ _ _ from by
          simpa only [equation, applyArguments_append] using rightTyped)
      exact ⟨_, .rfl, .proofIrrel typeProp typed finalTyped⟩
  | @lam arguments binder bodyType leftBody locals functionTyped body induction =>
    intro localsWF domain relation target function respect major pending equation
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, binderTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    have extendedWF : OnCtx (binder :: locals) (environment.IsType universes) :=
      ⟨localsWF, _, binderTyped⟩
    obtain ⟨bodyResult, bodySteps, bodyNormal⟩ := induction extendedWF
      (domain := domain.lift) (relation := relation.lift) (target := target.lift)
      (function := function.lift) (respect := respect.lift) (major := major.lift)
      (pending := pending.map VExpr.lift ++ [.bvar 0])
      (by simp only [equation, List.map_append, List.map_cons, List.map_nil, List.append_assoc])
    have step : Steps environmentWF universes locals
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
          [domain, relation, target, function, respect, major])
        (.app function (selector domain relation major)) :=
      .tail .rfl (.unfold (by simp only [applyArguments, unfold, zeroChecked, ite_true]))
    have finalFunctionTyped := (step.applyArguments pending).hasType registered localsWF
      (show environment.HasType universes _ _ _ from by
        simpa only [equation, applyArguments_append] using functionTyped)
    refine ⟨_, bodySteps.lam, .etaL finalFunctionTyped ?_⟩
    simpa only [applyArguments_append, applyArguments, VExpr.lift,
      applyArguments_liftN, VExpr.liftN, selector_liftN] using bodyNormal

/-- Every actual normal comparison simulates a Prop-source unfolding, beneath
any finite related argument list. Hereditary exposure handles arbitrary left
shapes; neutral majors need no constructor-matching premise. -/
theorem normal_unfold_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments left pending) type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (argumentsNormal : List.Forall₂
      (@NormalEq (environmentWF.reductionParams universes) locals) pending pending')
    (unfolded : unfold right = some result) :
    ∃ joined, Steps environmentWF universes locals (applyArguments left pending) joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined (applyArguments result pending') ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals (applyArguments result pending') type := by
  letI := environmentWF.reductionParams universes
  unfold unfold at unfolded
  split at unfolded <;> try contradiction
  rename_i sourceUniverse targetUniverse domain relation target function respect major
  split at unfolded <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj unfolded
  obtain ⟨initial, corePath, exposed, _, _, _⟩ := normal_spine_expose_applications localsWF
    (show NormalEq locals left
      (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse])
        [domain, relation, target, function, respect, major]) from normal) argumentsNormal typed
  obtain ⟨joined, finalPath, finalNormal⟩ := rigidUnfoldJoin registered zeroChecked exposed localsWF rfl
  have path : Steps environmentWF universes locals (applyArguments left pending) joined :=
    (Steps.core corePath).trans finalPath
  have joinedTyped := path.hasType registered localsWF typed
  exact ⟨joined, path, finalNormal, joinedTyped,
    ((finalNormal.defeq localsWF).of_l environmentWF localsWF joinedTyped).hasType.2⟩

/-- Root eta expansion is simulated from any actual normal comparison. -/
theorem normal_funEta_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals left type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (functionTyped : environment.HasType universes locals right (.forallE domain body)) :
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (.lam domain (.app right.lift (.bvar 0))) ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals (.lam domain (.app right.lift (.bvar 0))) type := by
  letI := environmentWF.reductionParams universes
  have leftFunctionTyped := ((normal.defeq localsWF).of_r environmentWF localsWF functionTyped).hasType.1
  obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
  obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
  have bodyNormal := NormalEq.appDF
    (leftFunctionTyped.weak environmentWF.ordered) (functionTyped.weak environmentWF.ordered)
    (HasType.bvar .zero) (HasType.bvar .zero)
    (normal.weakN (Ctx.LiftN.one (A := domain))) (.refl (HasType.bvar .zero))
  have compared := NormalEq.lamDF domainTyped domainTyped bodyNormal
  have path : Steps environmentWF universes locals left (.lam domain (.app left.lift (.bvar 0))) :=
    .tail .rfl (.funEta leftFunctionTyped)
  have joinedTyped := path.hasType registered localsWF typed
  exact ⟨_, path, compared, joinedTyped,
    ((compared.defeq localsWF).of_l environmentWF localsWF joinedTyped).hasType.2⟩


/-- Simulation of the entire candidate relation, using finite candidate paths
on the left and a direct normal comparison at the endpoint. -/
def CandidateSimulates (environmentWF : environment.WF) (universes : Nat)
    (locals : List VExpr) (left right : VExpr) : Prop :=
  ∀ {result}, Step environmentWF universes locals right result →
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined result

/-- Actual normal equality simulates every candidate step: original checked
core reduction, Prop-source unfolding, eta expansion, and congruence. -/
theorem normal_candidate_simulates
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right) :
    CandidateSimulates environmentWF universes locals left right := by
  letI := environmentWF.reductionParams universes
  revert localsWF
  induction normal with
  | refl typed =>
    intro localsWF result step
    exact ⟨_, .tail .rfl step, .refl (step.hasType registered localsWF typed)⟩
  | proofIrrel propositionTyped leftTyped rightTyped =>
    intro localsWF result step
    exact ⟨_, .rfl, .proofIrrel propositionTyped leftTyped
      (step.hasType registered localsWF rightTyped)⟩
  | etaL functionTyped bodies bodyIH =>
    intro localsWF result step
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    obtain ⟨bodyResult, bodySteps, compared⟩ := bodyIH ⟨localsWF, _, domainTyped⟩
      (.app (step.weakN Ctx.LiftN.one) (.core .bvar))
    exact ⟨_, bodySteps.lam, .etaL (step.hasType registered localsWF functionTyped) compared⟩
  | @sortDF leftLevel rightLevel context leftWF rightWF equal =>
    intro localsWF result step
    have normal := NormalEq.sortDF (Γ := context) leftWF rightWF equal
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
  | @constDF name constant leftLevels rightLevels context found leftWF rightWF arity levels =>
    intro localsWF result step
    have normal := NormalEq.constDF (Γ := context) found leftWF rightWF arity levels
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
  | appDF leftFunction rightFunction leftArgument rightArgument functions arguments functionIH argumentIH =>
    intro localsWF result step
    have normal := NormalEq.appDF leftFunction rightFunction leftArgument rightArgument functions arguments
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
    | app functionStep argumentStep =>
      obtain ⟨functionResult, functionPath, functionNormal⟩ := functionIH localsWF functionStep
      obtain ⟨argumentResult, argumentPath, argumentNormal⟩ := argumentIH localsWF argumentStep
      have functionTyped := functionPath.hasType registered localsWF leftFunction
      have argumentTyped := argumentPath.hasType registered localsWF leftArgument
      exact ⟨_, functionPath.app argumentPath,
        .appDF functionTyped
          ((functionNormal.defeq localsWF).of_l environmentWF localsWF functionTyped).hasType.2
          argumentTyped ((argumentNormal.defeq localsWF).of_l environmentWF localsWF argumentTyped).hasType.2
          functionNormal argumentNormal⟩
  | lamDF leftDomainEqual rightDomainEqual bodies bodyIH =>
    intro localsWF result step
    have normal := NormalEq.lamDF leftDomainEqual rightDomainEqual bodies
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
    | lam domainStep bodyStep =>
      have extendedWF := show OnCtx (_ :: _) (environment.IsType universes) from
        ⟨localsWF, _, leftDomainEqual.hasType.1⟩
      obtain ⟨_, bodyEqual⟩ := bodies.defeq extendedWF
      have targetBodyTyped := bodyEqual.hasType.2.defeqDFC environmentWF.ordered
        (.succ .zero rightDomainEqual)
      have convertedStep := bodyStep.defeqDFC localsWF
        (.succ .zero rightDomainEqual.symm) targetBodyTyped
      obtain ⟨bodyResult, bodySteps, compared⟩ := bodyIH extendedWF convertedStep
      have convertedSteps := bodySteps.defeqDFC registered localsWF
        (.succ .zero leftDomainEqual) bodyEqual.hasType.1
      exact ⟨_, convertedSteps.lam,
        .lamDF leftDomainEqual (rightDomainEqual.trans
          (domainStep.defeq registered localsWF rightDomainEqual.hasType.2)) compared⟩
  | forallEDF domainEqual domains bodyTyped bodies domainIH bodyIH =>
    intro localsWF result step
    have normal := NormalEq.forallEDF domainEqual domains bodyTyped bodies
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
    | forallE domainStep bodyStep =>
      obtain ⟨domainResult, domainSteps, joinedDomain⟩ := domainIH localsWF domainStep
      have extendedWF := show OnCtx (_ :: _) (environment.IsType universes) from
        ⟨localsWF, _, domainEqual.hasType.1⟩
      have targetBodyTyped := bodyTyped.defeqU_l environmentWF extendedWF (bodies.defeq extendedWF)
      have rightDomainEqual := domainEqual.transU_l environmentWF localsWF (domains.defeq localsWF)
      have convertedStep := bodyStep.defeqDFC localsWF
        (.succ .zero rightDomainEqual.symm)
        (targetBodyTyped.defeqDFC environmentWF.ordered (.succ .zero rightDomainEqual))
      obtain ⟨bodyResult, bodySteps, joinedBody⟩ := bodyIH extendedWF convertedStep
      have convertedSteps := bodySteps.defeqDFC registered localsWF
        (.succ .zero domainEqual) bodyTyped
      have reducedRightDomainEqual := rightDomainEqual.trans
        (domainStep.defeq registered localsWF rightDomainEqual.hasType.2)
      exact ⟨_, domainSteps.forallE convertedSteps,
        .forallEDF (reducedRightDomainEqual.transU_l environmentWF localsWF
          (joinedDomain.defeq localsWF).symm) joinedDomain
          (bodySteps.hasType registered extendedWF bodyTyped) joinedBody⟩
  | etaR functionTyped bodies bodyIH =>
    intro localsWF result step
    have normal := NormalEq.etaR functionTyped bodies
    obtain ⟨_, equal⟩ := normal.defeq localsWF
    have typed := equal.hasType.1
    cases step with
    | core reduced =>
      obtain ⟨joined, path, compared, _⟩ := normal_parRed_join registered localsWF
        typed normal reduced
      exact ⟨joined, path, compared⟩
    | unfold unfolded =>
      obtain ⟨joined, path, compared, _⟩ := normal_unfold_join registered localsWF
        (pending := []) (pending' := []) typed normal .nil unfolded
      exact ⟨joined, path, compared⟩
    | funEta functionTyped =>
      obtain ⟨joined, path, compared, _⟩ := normal_funEta_join registered localsWF
        typed normal functionTyped
      exact ⟨joined, path, compared⟩
    | lam domainStep bodyStep =>
      obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
      obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
      obtain ⟨bodyResult, bodySteps, compared⟩ := bodyIH ⟨localsWF, _, domainTyped⟩ bodyStep
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta functionTyped)).trans bodySteps.lam,
        .lamDF domainTyped (domainStep.defeq registered localsWF domainTyped) compared⟩

/-- Candidate-step simulation preserves any supplied original result type on
both endpoints, including converted dependent types. -/
theorem normal_step_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals left type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (step : Step environmentWF universes locals right result) :
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined result ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals result type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨joined, path, compared⟩ := normal_candidate_simulates registered localsWF normal step
  have joinedTyped := path.hasType registered localsWF typed
  exact ⟨joined, path, compared, joinedTyped,
    ((compared.defeq localsWF).of_l environmentWF localsWF joinedTyped).hasType.2⟩

/-- Every finite candidate path is simulated without transitivity of normal
equality or any confluence or inverse-weakening theorem. -/
theorem normal_steps_join
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals left type)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left right)
    (path : Steps environmentWF universes locals right result) :
    ∃ joined, Steps environmentWF universes locals left joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined result ∧
      environment.HasType universes locals joined type ∧
      environment.HasType universes locals result type := by
  letI := environmentWF.reductionParams universes
  induction path with
  | rfl =>
    exact ⟨_, .rfl, normal, typed,
      ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2⟩
  | tail previous step induction =>
    obtain ⟨middle, initial, compared, middleTyped, _⟩ := induction
    obtain ⟨joined, rest, finalNormal, joinedTyped, resultTyped⟩ :=
      normal_step_join registered localsWF middleTyped compared step
    exact ⟨joined, initial.trans rest, finalNormal, joinedTyped, resultTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
