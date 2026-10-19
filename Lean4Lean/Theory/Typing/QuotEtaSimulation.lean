import Lean4Lean.Theory.Typing.QuotPrefixReduction

namespace Lean4Lean.VEnv.QuotPropReduction

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

/-- Forward transport beneath eta's retained binder needs no inverse weakening. -/
theorem Step.etaCongr {source result domain : VExpr}
    (step : Step environmentWF universes locals source result) :
    Step environmentWF universes locals
      (.lam domain (.app source.lift (.bvar 0)))
      (.lam domain (.app result.lift (.bvar 0))) := by
  letI := environmentWF.reductionParams universes
  exact .lam (.core .rfl) (.app (step.weakN Ctx.LiftN.one) (.core .rfl))

theorem Steps.etaCongr {source result domain : VExpr}
    (steps : Steps environmentWF universes locals source result) :
    Steps environmentWF universes locals
      (.lam domain (.app source.lift (.bvar 0)))
      (.lam domain (.app result.lift (.bvar 0))) := by
  induction steps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction step.etaCongr

theorem Steps.forallE {domain domain' body body' : VExpr}
    (domainSteps : Steps environmentWF universes locals domain domain')
    (bodySteps : Steps environmentWF universes (domain :: locals) body body') :
    Steps environmentWF universes locals (.forallE domain body) (.forallE domain' body') := by
  letI := environmentWF.reductionParams universes
  have bodies : Steps environmentWF universes locals
      (.forallE domain body) (.forallE domain body') := by
    induction bodySteps with
    | rfl => exact .rfl
    | tail _ step induction => exact .tail induction (.forallE (.core .rfl) step)
  refine bodies.trans ?_
  induction domainSteps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (.forallE step (.core .rfl))

/-- Root eta expansion commutes with every finite candidate path, including
unfolding and further eta expansions. Both paths have the same typed endpoint. -/
theorem eta_steps_join {source result domain body resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (functionTyped : environment.HasType universes locals source (.forallE domain body))
    (typed : environment.HasType universes locals source resultType)
    (steps : Steps environmentWF universes locals source result) :
    Steps environmentWF universes locals
      (.lam domain (.app source.lift (.bvar 0)))
      (.lam domain (.app result.lift (.bvar 0))) ∧
    Step environmentWF universes locals result (.lam domain (.app result.lift (.bvar 0))) ∧
    environment.HasType universes locals
      (.lam domain (.app result.lift (.bvar 0))) resultType := by
  have resultFunctionTyped := steps.hasType registered localsWF functionTyped
  have resultTyped := steps.hasType registered localsWF typed
  have finalStep := Step.funEta (environmentWF := environmentWF) resultFunctionTyped
  exact ⟨steps.etaCongr, finalStep, finalStep.hasType registered localsWF resultTyped⟩

/-- Eta followed by beta joins simultaneous candidate paths in the function and
argument. The result keeps the original application type, even when dependent. -/
theorem eta_apply_join {source result argument argument' domain body resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (functionTyped : environment.HasType universes locals source (.forallE domain body))
    (typed : environment.HasType universes locals (.app source argument) resultType)
    (functionSteps : Steps environmentWF universes locals source result)
    (argumentSteps : Steps environmentWF universes locals argument argument') :
    Step environmentWF universes locals (.app source argument)
      (.app (.lam domain (.app source.lift (.bvar 0))) argument) ∧
    Steps environmentWF universes locals
      (.app (.lam domain (.app source.lift (.bvar 0))) argument)
      (.app result argument') ∧
    Steps environmentWF universes locals (.app source argument) (.app result argument') ∧
    environment.HasType universes locals (.app result argument') resultType := by
  letI := environmentWF.reductionParams universes
  have expanded := (functionSteps.etaCongr (domain := domain)).app argumentSteps
  have beta : ParRed locals
      (.app (.lam domain (.app result.lift (.bvar 0))) argument') (.app result argument') := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar, Nat.lt_irrefl,
      if_false, if_true, VExpr.liftN_zero] using
      (ParRed.beta (A := domain) (Γ := locals)
        (ParRed.rfl (e := .app result.lift (.bvar 0))) (ParRed.rfl (e := argument')))
  have direct := functionSteps.app argumentSteps
  exact ⟨.app (.funEta functionTyped) (.core .rfl),
    .tail expanded (.core beta), direct, direct.hasType registered localsWF typed⟩

/-- The replacement simulation obligation uses candidate paths on the left and
the actual original parallel reduction on the right. This definition does not
assert that every normal equality satisfies it. -/
def CoreSimulates (environmentWF : environment.WF) (universes : Nat)
    (locals : List VExpr) (left right : VExpr) : Prop :=
  ∀ {result}, @ParRed (environmentWF.reductionParams universes) locals right result →
    ∃ leftResult, Steps environmentWF universes locals left leftResult ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftResult result

theorem CoreSimulates.refl {source type : VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source type) :
    CoreSimulates environmentWF universes locals source source := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  exact ⟨result, .tail .rfl (.core reduction), .refl (reduction.hasType localsWF typed)⟩

theorem CoreSimulates.sortDF {left right : VLevel}
    (leftWF : left.WF universes) (rightWF : right.WF universes) (equal : left ≈ right) :
    CoreSimulates environmentWF universes locals (.sort left) (.sort right) := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  cases reduction with
  | sort => exact ⟨_, .rfl, .sortDF leftWF rightWF equal⟩
  | extra _ matched => cases matched

theorem CoreSimulates.constDF {name : Lean.Name} {constant : VConstant}
    {left right : List VLevel}
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants name = some constant)
    (leftWF : ∀ level ∈ left, level.WF universes)
    (rightWF : ∀ level ∈ right, level.WF universes)
    (arity : left.length = constant.uvars) (equal : List.Forall₂ (· ≈ ·) left right) :
    CoreSimulates environmentWF universes locals (.const name left) (.const name right) := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  obtain ⟨leftResult, steps, normal⟩ := NormalEq.parRed_constDF
    localsWF registered leftWF rightWF arity equal reduction
  exact ⟨leftResult, Steps.core steps, normal⟩

theorem CoreSimulates.proofIrrel {proposition left right : VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (leftTyped : environment.HasType universes locals left proposition)
    (rightTyped : environment.HasType universes locals right proposition) :
    CoreSimulates environmentWF universes locals left right := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  exact ⟨left, .rfl, .proofIrrel propositionTyped leftTyped (reduction.hasType localsWF rightTyped)⟩

/-- The eta-left induction clause only needs the recursive body simulation. -/
theorem CoreSimulates.etaL {source domain body otherBody : VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (functionTyped : environment.HasType universes locals source (.forallE domain body))
    (bodySimulation : CoreSimulates environmentWF universes (domain :: locals)
      otherBody (.app source.lift (.bvar 0))) :
    CoreSimulates environmentWF universes locals (.lam domain otherBody) source := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  obtain ⟨bodyResult, bodySteps, normal⟩ :=
    bodySimulation (.app (reduction.weakN Ctx.LiftN.one) .bvar)
  exact ⟨_, bodySteps.lam, .etaL (reduction.hasType localsWF functionTyped) normal⟩

/-- The eta-right induction clause expands the source and keeps its binder.
Unlike inverse reduction transport, this remains valid for checked rewriting. -/
theorem CoreSimulates.etaR {source domain body otherBody : VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (functionTyped : environment.HasType universes locals source (.forallE domain body))
    (bodySimulation : CoreSimulates environmentWF universes (domain :: locals)
      (.app source.lift (.bvar 0)) otherBody) :
    CoreSimulates environmentWF universes locals source (.lam domain otherBody) := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  cases reduction with
  | lam domainReduction bodyReduction =>
    obtain ⟨bodyResult, bodySteps, normal⟩ := bodySimulation bodyReduction
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    exact ⟨_, (ReflTransGen.tail .rfl (.funEta functionTyped)).trans bodySteps.lam,
      .lamDF domainTyped (domainReduction.defeq localsWF domainTyped) normal⟩
  | extra _ matched => cases matched

/-- Lambda simulation transports the recursive body path through the actual
domain conversions, including reduction of the target domain. -/
theorem CoreSimulates.lamDF {domain leftDomain rightDomain leftBody rightBody : VExpr}
    {level : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftDomainEqual : environment.IsDefEq universes locals domain leftDomain (.sort level))
    (rightDomainEqual : environment.IsDefEq universes locals domain rightDomain (.sort level))
    (bodyNormal : @NormalEq (environmentWF.reductionParams universes)
      (domain :: locals) leftBody rightBody)
    (bodySimulation : CoreSimulates environmentWF universes (domain :: locals) leftBody rightBody) :
    CoreSimulates environmentWF universes locals (.lam leftDomain leftBody) (.lam rightDomain rightBody) := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  cases reduction with
  | lam domainReduction bodyReduction =>
    have extendedWF : OnCtx (domain :: locals) (environment.IsType universes) :=
      ⟨localsWF, _, leftDomainEqual.hasType.1⟩
    obtain ⟨_, bodyEqual⟩ := bodyNormal.defeq extendedWF
    have targetBodyTyped := bodyEqual.hasType.2.defeqDFC environmentWF.ordered
      (.succ .zero rightDomainEqual)
    have convertedReduction := bodyReduction.defeqDFC localsWF
      (.succ .zero rightDomainEqual.symm) targetBodyTyped
    obtain ⟨bodyResult, bodySteps, normal⟩ := bodySimulation convertedReduction
    have convertedSteps := bodySteps.defeqDFC registered localsWF
      (.succ .zero leftDomainEqual) bodyEqual.hasType.1
    exact ⟨_, convertedSteps.lam,
      .lamDF leftDomainEqual (rightDomainEqual.trans
        (domainReduction.defeq localsWF rightDomainEqual.hasType.2)) normal⟩
  | extra _ matched => cases matched

/-- The forall induction clause combines domain and body simulations without
dropping any dependent binder. -/
theorem CoreSimulates.forallEDF {domain leftDomain rightDomain leftBody rightBody : VExpr}
    {domainLevel bodyLevel : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (domainEqual : environment.IsDefEq universes locals domain leftDomain (.sort domainLevel))
    (domainNormal : @NormalEq (environmentWF.reductionParams universes) locals leftDomain rightDomain)
    (bodyTyped : environment.HasType universes (domain :: locals) leftBody (.sort bodyLevel))
    (bodyNormal : @NormalEq (environmentWF.reductionParams universes)
      (domain :: locals) leftBody rightBody)
    (domainSimulation : CoreSimulates environmentWF universes locals leftDomain rightDomain)
    (bodySimulation : CoreSimulates environmentWF universes (domain :: locals) leftBody rightBody) :
    CoreSimulates environmentWF universes locals
      (.forallE leftDomain leftBody) (.forallE rightDomain rightBody) := by
  letI := environmentWF.reductionParams universes
  intro result reduction
  cases reduction with
  | forallE domainReduction bodyReduction =>
    obtain ⟨domainResult, domainSteps, joinedDomain⟩ := domainSimulation domainReduction
    have extendedWF : OnCtx (domain :: locals) (environment.IsType universes) :=
      ⟨localsWF, _, domainEqual.hasType.1⟩
    have targetBodyTyped := bodyTyped.defeqU_l environmentWF extendedWF (bodyNormal.defeq extendedWF)
    have rightDomainEqual := domainEqual.transU_l environmentWF localsWF (domainNormal.defeq localsWF)
    have convertedReduction := bodyReduction.defeqDFC localsWF
      (.succ .zero rightDomainEqual.symm)
      (targetBodyTyped.defeqDFC environmentWF.ordered (.succ .zero rightDomainEqual))
    obtain ⟨bodyResult, bodySteps, joinedBody⟩ := bodySimulation convertedReduction
    have convertedSteps := bodySteps.defeqDFC registered localsWF
      (.succ .zero domainEqual) bodyTyped
    have reducedRightDomainEqual := rightDomainEqual.trans
      (domainReduction.defeq localsWF rightDomainEqual.hasType.2)
    exact ⟨_, domainSteps.forallE convertedSteps,
      .forallEDF (reducedRightDomainEqual.transU_l environmentWF localsWF
        (joinedDomain.defeq localsWF).symm) joinedDomain
        (bodySteps.hasType registered extendedWF bodyTyped) joinedBody⟩
  | extra _ matched => cases matched

/-- The application congruence case of the simulation induction. Root beta and
checked EXTRA still require their own cases before a full application theorem. -/
theorem CoreSimulates.app_congr {leftFunction rightFunction leftArgument rightArgument : VExpr}
    {functionResult argumentResult domain body : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftFunctionTyped : environment.HasType universes locals leftFunction (.forallE domain body))
    (rightFunctionTyped : environment.HasType universes locals rightFunction (.forallE domain body))
    (leftArgumentTyped : environment.HasType universes locals leftArgument domain)
    (rightArgumentTyped : environment.HasType universes locals rightArgument domain)
    (functionSimulation : CoreSimulates environmentWF universes locals leftFunction rightFunction)
    (argumentSimulation : CoreSimulates environmentWF universes locals leftArgument rightArgument)
    (functionReduction : @ParRed (environmentWF.reductionParams universes) locals rightFunction functionResult)
    (argumentReduction : @ParRed (environmentWF.reductionParams universes) locals rightArgument argumentResult) :
    ∃ leftResult, Steps environmentWF universes locals (.app leftFunction leftArgument) leftResult ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftResult (.app functionResult argumentResult) := by
  letI := environmentWF.reductionParams universes
  obtain ⟨_, functionSteps, functionNormal⟩ := functionSimulation functionReduction
  obtain ⟨_, argumentSteps, argumentNormal⟩ := argumentSimulation argumentReduction
  exact ⟨_, functionSteps.app argumentSteps,
    .appDF (functionSteps.hasType registered localsWF leftFunctionTyped)
      (functionReduction.hasType localsWF rightFunctionTyped)
      (argumentSteps.hasType registered localsWF leftArgumentTyped)
      (argumentReduction.hasType localsWF rightArgumentTyped) functionNormal argumentNormal⟩

/-- A proved simulation witness retains the original result type on BOTH
endpoints; no inverse weakening or normal-equality transitivity is required. -/
theorem CoreSimulates.typed {left right result type : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftTyped : environment.HasType universes locals left type)
    (simulation : CoreSimulates environmentWF universes locals left right)
    (reduction : @ParRed (environmentWF.reductionParams universes) locals right result) :
    ∃ leftResult, Steps environmentWF universes locals left leftResult ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftResult result ∧
      environment.HasType universes locals leftResult type ∧
      environment.HasType universes locals result type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨leftResult, steps, normal⟩ := simulation reduction
  have typed := steps.hasType registered localsWF leftTyped
  exact ⟨leftResult, steps, normal, typed,
    ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2⟩

end Lean4Lean.VEnv.QuotPropReduction
