import Lean4Lean.Theory.LevelZero
import Lean4Lean.Theory.Typing.QuotReduction
import Lean4Lean.Theory.Typing.ConcreteReduction

namespace Lean4Lean.VEnv.QuotPropReduction

section

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {domain relation major : VExpr}

def quotient (domain relation : VExpr) : VExpr :=
  .app (.app (.const ``Quot [.zero]) domain) relation

def selector (domain relation major : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.ind [.zero]) domain) relation)
    (.lam (quotient domain relation) domain.lift)) (.lam domain (.bvar 0))) major

def unfold : VExpr → Option VExpr
  | .app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, _])
      domain) relation) _) function) _) major =>
    if zeroLike sourceUniverse then some (.app function (selector domain relation major)) else none
  | _ => none

theorem selector_liftN (domain relation major : VExpr) (count depth : Nat) :
    (selector domain relation major).liftN count depth =
      selector (domain.liftN count depth) (relation.liftN count depth)
        (major.liftN count depth) := by
  simp only [selector, quotient, VExpr.liftN, ← VExpr.lift_liftN']
  simp [liftVar]

theorem selector_inst (domain relation major argument : VExpr) (depth : Nat) :
    (selector domain relation major).inst argument depth =
      selector (domain.inst argument depth) (relation.inst argument depth)
        (major.inst argument depth) := by
  simp only [selector, quotient, VExpr.inst, ← VExpr.lift_instN_lo]
  simp [VExpr.instVar]

theorem unfold_liftN {source result : VExpr} (unfolded : unfold source = some result)
    (count depth : Nat) :
    unfold (source.liftN count depth) = some (result.liftN count depth) := by
  unfold unfold at unfolded
  split at unfolded <;> try contradiction
  split at unfolded <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj unfolded
  simp only [unfold, VExpr.liftN, selector_liftN, zeroChecked, ite_true]

theorem unfold_inst {source result : VExpr} (unfolded : unfold source = some result)
    (argument : VExpr) (depth : Nat) :
    unfold (source.inst argument depth) = some (result.inst argument depth) := by
  unfold unfold at unfolded
  split at unfolded <;> try contradiction
  split at unfolded <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj unfolded
  simp only [unfold, VExpr.inst, selector_inst, zeroChecked, ite_true]

private theorem instantiateLifted (expression argument : VExpr) (depth : Nat) :
    (expression.liftN (depth + 1)).inst argument depth = expression.liftN depth := by
  rw [Nat.add_comm depth 1, ← VExpr.liftN'_liftN_lo expression 1 depth, VExpr.inst_liftN]

theorem quotient_hasType
    (quotientRegistered : environment.constants ``Quot = some quotConst)
    (domainTyped : environment.HasType universes locals domain (.sort .zero))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero)))) :
    environment.HasType universes locals (quotient domain relation) (.sort .zero) := by
  have head := HasType.const quotientRegistered (ls := [.zero]) (by simp [VLevel.WF])
    (by rfl) (Γ := locals) (U := universes)
  simp [quotConst, VExpr.instL, VLevel.inst] at head
  have first := head.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at first
  simpa [instantiateLifted, VExpr.inst, VExpr.instVar, quotient] using first.app relationTyped

theorem selector_hasType
    (environmentOrdered : environment.Ordered)
    (quotientRegistered : environment.constants ``Quot = some quotConst)
    (constructorRegistered : environment.constants ``Quot.mk = some quotMkConst)
    (inductionRegistered : environment.constants ``Quot.ind = some quotIndConst)
    (domainTyped : environment.HasType universes locals domain (.sort .zero))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (majorTyped : environment.HasType universes locals major (quotient domain relation)) :
    environment.HasType universes locals (selector domain relation major) domain := by
  have quotientTyped := quotient_hasType quotientRegistered domainTyped relationTyped
  have motiveTyped := HasType.lam quotientTyped (domainTyped.weak environmentOrdered)
  have relationWeak : environment.HasType universes (domain :: locals) relation.lift
      (.forallE domain.lift (.forallE domain.lift.lift (.sort .zero))) := by
    simpa only [VExpr.lift, VExpr.liftN, ← VExpr.lift_liftN'] using
      relationTyped.weak environmentOrdered
  have constructorTyped := quotMk_hasType constructorRegistered (by trivial)
    (domainTyped.weak environmentOrdered) relationWeak
    (HasType.bvar (Γ := domain :: locals) .zero)
  have motiveBeta := IsDefEq.beta
    ((domainTyped.weak environmentOrdered).weak environmentOrdered) constructorTyped
  simp [instantiateLifted] at motiveBeta
  have minorTyped := HasType.lam domainTyped
    (IsDefEq.defeqDF motiveBeta.symm (HasType.bvar .zero))
  have head := HasType.const inductionRegistered (ls := [.zero]) (by simp [VLevel.WF])
    (by rfl) (Γ := locals) (U := universes)
  simp [quotIndConst, VExpr.instL, VLevel.inst] at head
  have first := head.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.app relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at second
  have third := second.app motiveTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at third
  have minorExpected : environment.HasType universes locals (.lam domain (.bvar 0))
      (.forallE domain (.app (VExpr.lam (quotient domain relation) domain.lift).lift
        (.app (.app (.app (.const ``Quot.mk [.zero]) domain.lift) relation.lift) (.bvar 0)))) := by
    simpa only [quotient, VExpr.lift, VExpr.liftN, VExpr.lift_liftN'] using minorTyped
  have fourth := third.app minorExpected
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at fourth
  have final := fourth.app majorTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at final
  have resultBeta := IsDefEq.beta (domainTyped.weak environmentOrdered) majorTyped
  simpa [selector, quotient, VExpr.inst_lift] using IsDefEq.defeqDF resultBeta final

theorem unfold_lift
    {targetUniverse : VLevel} {target function respect resultType : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (typed : environment.HasType universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [.zero, targetUniverse])
        domain) relation) target) function) respect) major) resultType) :
    environment.IsDefEq universes locals
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [.zero, targetUniverse])
        domain) relation) target) function) respect) major)
      (.app function (selector domain relation major)) resultType := by
  obtain ⟨_, inductionRegistered, liftRegistered, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  obtain ⟨sourceUniverse, actualTargetUniverse, levels, sourceWF, targetWF,
    domainTyped, relationTyped, targetTyped, functionTyped, respectTyped, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered typed
  cases levels
  have selectorTyped := selector_hasType environmentWF.ordered quotientRegistered
    constructorRegistered inductionRegistered domainTyped relationTyped majorTyped
  have constructorTyped := quotMk_hasType constructorRegistered sourceWF
    domainTyped relationTyped selectorTyped
  have quotientTyped := quotient_hasType quotientRegistered domainTyped relationTyped
  have majorEqual := IsDefEq.proofIrrel quotientTyped majorTyped constructorTyped
  obtain ⟨_, _, prefixTyped, actualMajorTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  have first := (prefixTyped.appDF (majorEqual.toU.of_l environmentWF localsWF actualMajorTyped)).toU
    |>.of_l environmentWF localsWF typed
  have second := quotLift_beta environmentWF localsWF registered sourceWF targetWF
    domainTyped relationTyped targetTyped functionTyped respectTyped selectorTyped
  exact first.trans (second.toU.of_l environmentWF localsWF first.hasType.2)

theorem unfold_sound {source result resultType : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (unfolded : unfold source = some result)
    (typed : environment.HasType universes locals source resultType) :
    environment.IsDefEq universes locals source result resultType := by
  unfold unfold at unfolded
  split at unfolded <;> try contradiction
  rename_i sourceUniverse targetUniverse domain relation target function respect major
  split at unfolded <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj unfolded
  obtain ⟨_, _, liftRegistered, _⟩ := environmentWF.quotientObjects registered
  obtain ⟨_, _, levels, sourceWF, targetWF, domainTyped, relationTyped,
    targetTyped, functionTyped, respectTyped, majorTyped, _⟩ :=
    quotLift_inv environmentWF localsWF liftRegistered typed
  cases levels
  have zeroEqual := (zeroLike_iff sourceUniverse).mp zeroChecked
  have headEqual := IsDefEq.constDF liftRegistered
    (ls := [sourceUniverse, targetUniverse]) (ls' := [.zero, targetUniverse])
    (by simpa using And.intro sourceWF targetWF) (by simpa [VLevel.WF] using targetWF)
    (by rfl) (.cons zeroEqual (.cons rfl .nil)) (Γ := locals)
  have first := headEqual.appDF domainTyped
  simp [VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar] at first
  have second := first.appDF relationTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at second
  have third := second.appDF targetTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at third
  have fourth := third.appDF functionTyped
  simp [instantiateLifted, VExpr.inst, VExpr.instVar] at fourth
  have fifth := fourth.appDF respectTyped
  simp [instantiateLifted, VExpr.inst] at fifth
  have normalized := (fifth.appDF majorTyped).toU.of_l environmentWF localsWF typed
  exact normalized.trans (unfold_lift environmentWF localsWF registered normalized.hasType.2)

theorem selector_normalEq {value : VExpr}
    (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (domainTyped : environment.HasType universes locals domain (.sort .zero))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (majorTyped : environment.HasType universes locals major (quotient domain relation))
    (valueTyped : environment.HasType universes locals value domain) :
    @NormalEq (environmentWF.reductionParams universes) locals
      (selector domain relation major) value := by
  letI := environmentWF.reductionParams universes
  obtain ⟨_, inductionRegistered, _, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  exact .proofIrrel domainTyped (selector_hasType environmentWF.ordered quotientRegistered
    constructorRegistered inductionRegistered domainTyped relationTyped majorTyped) valueTyped

theorem unfolding_join {function target value : VExpr}
    (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (domainTyped : environment.HasType universes locals domain (.sort .zero))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (majorTyped : environment.HasType universes locals major (quotient domain relation))
    (functionTyped : environment.HasType universes locals function (.forallE domain target.lift))
    (valueTyped : environment.HasType universes locals value domain) :
    @NormalEq (environmentWF.reductionParams universes) locals
      (.app function (selector domain relation major)) (.app function value) := by
  letI := environmentWF.reductionParams universes
  obtain ⟨_, inductionRegistered, _, constructorRegistered, quotientRegistered, _⟩ :=
    environmentWF.quotientObjects registered
  exact .appDF functionTyped functionTyped
    (selector_hasType environmentWF.ordered quotientRegistered constructorRegistered
      inductionRegistered domainTyped relationTyped majorTyped) valueTyped
    (.refl functionTyped)
    (selector_normalEq environmentWF registered domainTyped relationTyped majorTyped valueTyped)

end

theorem selector_normalEq_of_params [parameters : Params]
    (quotientRegistered : parameters.env.constants ``Quot = some quotConst)
    (constructorRegistered : parameters.env.constants ``Quot.mk = some quotMkConst)
    (inductionRegistered : parameters.env.constants ``Quot.ind = some quotIndConst)
    (domainTyped : parameters.env.HasType parameters.univs locals domain (.sort .zero))
    (relationTyped : parameters.env.HasType parameters.univs locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (majorTyped : parameters.env.HasType parameters.univs locals major (quotient domain relation))
    (valueTyped : parameters.env.HasType parameters.univs locals value domain) :
    NormalEq locals (selector domain relation major) value :=
  .proofIrrel domainTyped (selector_hasType parameters.henv.ordered quotientRegistered
    constructorRegistered inductionRegistered domainTyped relationTyped majorTyped) valueTyped

theorem unfolding_join_of_params [parameters : Params] {target : VExpr}
    (quotientRegistered : parameters.env.constants ``Quot = some quotConst)
    (constructorRegistered : parameters.env.constants ``Quot.mk = some quotMkConst)
    (inductionRegistered : parameters.env.constants ``Quot.ind = some quotIndConst)
    (domainTyped : parameters.env.HasType parameters.univs locals domain (.sort .zero))
    (relationTyped : parameters.env.HasType parameters.univs locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (majorTyped : parameters.env.HasType parameters.univs locals major (quotient domain relation))
    (functionTyped : parameters.env.HasType parameters.univs locals function (.forallE domain target.lift))
    (valueTyped : parameters.env.HasType parameters.univs locals value domain) :
    NormalEq locals (.app function (selector domain relation major)) (.app function value) :=
  .appDF functionTyped functionTyped
    (selector_hasType parameters.henv.ordered quotientRegistered constructorRegistered
      inductionRegistered domainTyped relationTyped majorTyped) valueTyped
    (.refl functionTyped)
    (selector_normalEq_of_params quotientRegistered constructorRegistered inductionRegistered
      domainTyped relationTyped majorTyped valueTyped)

inductive Step {environment : VEnv} (environmentWF : environment.WF) (universes : Nat) :
    List VExpr → VExpr → VExpr → Prop where
  | core : @ParRed (environmentWF.reductionParams universes) locals source result →
      Step environmentWF universes locals source result
  | unfold : unfold source = some result → Step environmentWF universes locals source result
  | funEta : environment.HasType universes locals source (.forallE domain body) →
      Step environmentWF universes locals source (.lam domain (.app source.lift (.bvar 0)))
  | app : Step environmentWF universes locals function function' →
      Step environmentWF universes locals argument argument' →
      Step environmentWF universes locals (.app function argument) (.app function' argument')
  | lam : Step environmentWF universes locals domain domain' →
      Step environmentWF universes (domain :: locals) body body' →
      Step environmentWF universes locals (.lam domain body) (.lam domain' body')
  | forallE : Step environmentWF universes locals domain domain' →
      Step environmentWF universes (domain :: locals) body body' →
      Step environmentWF universes locals (.forallE domain body) (.forallE domain' body')

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}

theorem Step.weakN {environmentWF : environment.WF} {source result : VExpr}
    (insertion : Ctx.LiftN count depth locals extended)
    (step : Step environmentWF universes locals source result) :
    Step environmentWF universes extended (source.liftN count depth) (result.liftN count depth) := by
  letI := environmentWF.reductionParams universes
  induction step generalizing depth extended with
  | core reduction => exact .core (reduction.weakN insertion)
  | unfold unfolded => exact .unfold (unfold_liftN unfolded count depth)
  | funEta typed =>
    simpa [VExpr.liftN, ← VExpr.lift_liftN', liftVar] using
      Step.funEta (typed.weakN environmentWF.ordered insertion)
  | app _ _ functionIH argumentIH => exact .app (functionIH insertion) (argumentIH insertion)
  | lam _ _ domainIH bodyIH => exact .lam (domainIH insertion) (bodyIH insertion.succ)
  | forallE _ _ domainIH bodyIH => exact .forallE (domainIH insertion) (bodyIH insertion.succ)

theorem Step.instN {environmentWF : environment.WF} {source result argument argumentType : VExpr}
    (substitution : Ctx.InstN base argument argumentType depth locals substituted)
    (argumentTyped : environment.HasType universes base argument argumentType)
    (step : Step environmentWF universes locals source result) :
    Step environmentWF universes substituted (source.inst argument depth) (result.inst argument depth) := by
  letI := environmentWF.reductionParams universes
  induction step generalizing depth substituted with
  | core reduction => exact .core (ParRed.instN ParRed.rfl argumentTyped substitution reduction)
  | unfold unfolded => exact .unfold (unfold_inst unfolded argument depth)
  | funEta typed =>
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, VExpr.instVar_lower] using
      Step.funEta (typed.instN environmentWF.ordered substitution argumentTyped)
  | app _ _ functionIH argumentIH => exact .app (functionIH substitution) (argumentIH substitution)
  | lam _ _ domainIH bodyIH => exact .lam (domainIH substitution) (bodyIH substitution.succ)
  | forallE _ _ domainIH bodyIH => exact .forallE (domainIH substitution) (bodyIH substitution.succ)

theorem Step.defeq {environmentWF : environment.WF} {source result resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (step : Step environmentWF universes locals source result)
    (typed : environment.HasType universes locals source resultType) :
    environment.IsDefEq universes locals source result resultType := by
  letI := environmentWF.reductionParams universes
  induction step generalizing resultType with
  | core reduction => exact reduction.defeq localsWF typed
  | unfold unfolded => exact unfold_sound environmentWF localsWF registered unfolded typed
  | funEta functionTyped => exact typed.trans_l environmentWF localsWF (IsDefEq.eta functionTyped).symm
  | app _ _ functionIH argumentIH =>
    obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv environmentWF.ordered localsWF
    exact typed.trans_l environmentWF localsWF
      ((functionIH localsWF functionTyped).appDF (argumentIH localsWF argumentTyped))
  | lam _ _ domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := typed.lam_inv environmentWF.ordered localsWF
    exact typed.trans_l environmentWF localsWF
      (.lamDF (domainIH localsWF domainTyped) (bodyIH ⟨localsWF, _, domainTyped⟩ bodyTyped))
  | forallE _ _ domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := typed.forallE_inv environmentWF.ordered
    exact typed.trans_l environmentWF localsWF
      (.forallEDF (domainIH localsWF domainTyped) (bodyIH ⟨localsWF, _, domainTyped⟩ bodyTyped))

theorem Step.hasType {environmentWF : environment.WF} {source result resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (step : Step environmentWF universes locals source result)
    (typed : environment.HasType universes locals source resultType) :
    environment.HasType universes locals result resultType :=
  (step.defeq registered localsWF typed).hasType.2

def Steps (environmentWF : environment.WF) (universes : Nat) (locals : List VExpr) :
    VExpr → VExpr → Prop := ReflTransGen (Step environmentWF universes locals)

theorem Steps.core {environmentWF : environment.WF} {source result : VExpr}
    (steps : @ParRedS (environmentWF.reductionParams universes) locals source result) :
    Steps environmentWF universes locals source result := by
  induction steps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (.core step)

theorem Steps.defeq {environmentWF : environment.WF} {source result resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (steps : Steps environmentWF universes locals source result)
    (typed : environment.HasType universes locals source resultType) :
    environment.IsDefEq universes locals source result resultType := by
  induction steps with
  | rfl => exact typed
  | tail _ step induction => exact induction.trans (step.defeq registered localsWF induction.hasType.2)

theorem Steps.hasType {environmentWF : environment.WF} {source result resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (steps : Steps environmentWF universes locals source result)
    (typed : environment.HasType universes locals source resultType) :
    environment.HasType universes locals result resultType :=
  (steps.defeq registered localsWF typed).hasType.2

/-- Canonical Prop-source unfolding joins the actual checked quotient EXTRA
rule, including all its parallel argument reductions. Both endpoints retain
the original application type; constructor parameters need only pass the
existing rule's equality checks. -/
theorem unfold_extra_join {environmentWF : environment.WF}
    {source unfolded resultType : VExpr} {levels : List VLevel}
    {values reducedValues : quotLiftPattern.Path → VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source resultType)
    (computed : unfold source = some unfolded)
    (matched : quotLiftPattern.Matches source levels values)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values)
    (reductions : ∀ path, @ParRed (environmentWF.reductionParams universes) locals
      (values path) (reducedValues path)) :
    ∃ joined,
      @ParRed (environmentWF.reductionParams universes) locals source
        (quotLiftPatternResult.apply levels reducedValues) ∧
      Step environmentWF universes locals unfolded joined ∧
      @NormalEq (environmentWF.reductionParams universes) locals joined
        (quotLiftPatternResult.apply levels reducedValues) ∧
      environment.HasType universes locals joined resultType ∧
      environment.HasType universes locals (quotLiftPatternResult.apply levels reducedValues) resultType := by
  letI := environmentWF.reductionParams universes
  have rewriteStep : ParRed locals source (quotLiftPatternResult.apply levels reducedValues) :=
    .extra (.quot registered) matched checked reductions
  have unfoldedTyped := (unfold_sound environmentWF localsWF registered computed typed).hasType.2
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
  obtain ⟨_, _, liftRegistered, constructorRegistered, quotientRegistered, _⟩ := environmentWF.quotientObjects registered
  obtain ⟨sourceUniverse, targetUniverse, rfl, sourceWF, _, domainTyped, relationTyped,
    _, functionTyped, _, majorTyped, _⟩ := quotLift_inv environmentWF localsWF liftRegistered typed
  obtain ⟨_, _, _, constructorDomainTyped, _, valueTyped, _⟩ :=
    quotMk_inv environmentWF localsWF constructorRegistered majorTyped
  simp only [quotLiftPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at checked
  have alignedValue := (checked.1.symm.of_l environmentWF localsWF constructorDomainTyped).defeq valueTyped
  have reducedValue := (reductions (.inr none)).hasType localsWF alignedValue
  have reducedFunction := (reductions (.inl (some none))).hasType localsWF functionTyped
  simp only [unfold] at computed
  split at computed <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj computed
  have zeroEqual := (zeroLike_iff sourceUniverse).mp zeroChecked
  have domainProp := IsDefEq.defeqDF (IsDefEq.sortDF sourceWF (by trivial) zeroEqual) domainTyped
  have quotientEqual := IsDefEq.constDF quotientRegistered
    (ls := [sourceUniverse]) (ls' := [.zero]) (by simpa using sourceWF)
    (by simp [VLevel.WF]) (by rfl) (.cons zeroEqual .nil) (Γ := locals)
  have first := quotientEqual.appDF domainTyped
  simp [VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar] at first
  have second := first.appDF relationTyped
  simp [VExpr.inst] at second
  have majorProp := second.defeq majorTyped
  refine ⟨_, rewriteStep, .core (.app (reductions (.inl (some none))) .rfl),
    ?_, ?_, rewriteStep.hasType localsWF typed⟩
  · exact unfolding_join (target := _) environmentWF registered domainProp relationTyped
      majorProp reducedFunction reducedValue
  · exact (ParRed.app (reductions (.inl (some none))) .rfl).hasType localsWF unfoldedTyped

private theorem constMatches_name {name otherName : Lean.Name} {levels matchedLevels : List VLevel}
    {values : (Pattern.const name).Path → VExpr}
    (matched : (Pattern.const name).Matches (.const otherName levels) matchedLevels values) :
    name = otherName := by
  cases matched
  rfl

private theorem spineMatches_count {firstName secondName : Lean.Name}
    {count secondCount : Nat} {expression : VExpr} {levels otherLevels : List VLevel}
    {values : (Pattern.varN (.const firstName) count).Path → VExpr}
    {otherValues : (Pattern.varN (.const secondName) secondCount).Path → VExpr}
    (first : (Pattern.varN (.const firstName) count).Matches expression levels values)
    (second : (Pattern.varN (.const secondName) secondCount).Matches expression otherLevels otherValues) :
    count = secondCount := by
  induction count generalizing secondCount expression with
  | zero =>
    cases first
    cases secondCount with
    | zero => rfl
    | succ secondCount => cases second
  | succ count induction =>
    cases first with
    | var first =>
      cases secondCount with
      | zero => cases second
      | succ secondCount =>
        cases second with
        | var second => exact congrArg Nat.succ (induction first second)

/-- A proper quotient-lift prefix can only reduce its supplied arguments.
Registered quotient names cannot be definition heads, and the quotient rule
needs all six arguments. -/
theorem liftPrefix_parRed_inv {environmentWF : environment.WF} {count : Nat}
    {source reduced : VExpr} {levels : List VLevel}
    {values : (Pattern.varN (.const ``Quot.lift) count).Path → VExpr}
    (registered : environment.defeqs quotDefEq) (bounded : count ≤ 5)
    (matched : (Pattern.varN (.const ``Quot.lift) count).Matches source levels values)
    (reduction : @ParRed (environmentWF.reductionParams universes) locals source reduced) :
    ∃ reducedValues,
      (Pattern.varN (.const ``Quot.lift) count).Matches reduced levels reducedValues ∧
      ∀ path, @ParRed (environmentWF.reductionParams universes) locals
        (values path) (reducedValues path) := by
  letI := environmentWF.reductionParams universes
  induction count generalizing source reduced with
  | zero =>
    cases matched
    cases reduction with
    | const => exact ⟨_, .const, nofun⟩
    | extra rule matched _ _ =>
      cases rule with
      | delta closed definitionRegistered =>
        exact False.elim (environmentWF.rewriteMetadata.quotientNames definitionRegistered registered
          ``Quot.lift (.tail _ (.tail _ (.head _))) (constMatches_name matched))
      | quot => cases matched
  | succ count induction =>
    cases matched with
    | var matched =>
      cases reduction with
      | app functionReduction argumentReduction =>
        obtain ⟨reducedValues, resultMatched, argumentsReduced⟩ := induction (Nat.le_trans (Nat.le_succ count) bounded) matched functionReduction
        refine ⟨_, .var resultMatched, ?_⟩
        rintro (_ | path)
        · exact argumentReduction
        · exact argumentsReduced path
      | beta => exact False.elim (Pattern.Matches.not_lam matched)
      | extra rule extraMatched _ _ =>
        cases rule with
        | delta => cases extraMatched
        | quot =>
          cases extraMatched with
          | app prefixMatched _ =>
            have equal := spineMatches_count matched prefixMatched
            exact False.elim (Nat.not_succ_le_self 5 (equal ▸ bounded))

/-- The canonical selector preserves simultaneous reductions of its domain,
relation and major, including the lifted domain under its generated motive. -/
theorem selector_parRed [parameters : Params]
    {domain domain' relation relation' major major' : VExpr}
    (domainReduction : ParRed locals domain domain')
    (relationReduction : ParRed locals relation relation')
    (majorReduction : ParRed locals major major') :
    ParRed locals (selector domain relation major) (selector domain' relation' major') := by
  unfold selector quotient
  exact .app (.app (.app (.app (.app .rfl domainReduction) relationReduction)
    (.lam (.app (.app .rfl domainReduction) relationReduction) (domainReduction.weakN .one)))
    (.lam domainReduction .rfl)) majorReduction

/-- Every original parallel reduction from an unfoldable quotient application
joins canonical unfolding modulo normal equality. The congruence case has an
identical endpoint; the checked EXTRA case uses the Prop selector join. -/
theorem unfold_parRed_join {environmentWF : environment.WF} {source unfolded reduced resultType : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source resultType)
    (computed : unfold source = some unfolded)
    (reduction : @ParRed (environmentWF.reductionParams universes) locals source reduced) :
    ∃ left right,
      Step environmentWF universes locals unfolded left ∧
      Steps environmentWF universes locals reduced right ∧
      @NormalEq (environmentWF.reductionParams universes) locals left right ∧
      environment.HasType universes locals left resultType ∧
      environment.HasType universes locals right resultType := by
  letI := environmentWF.reductionParams universes
  have originalComputed := computed
  have unfoldedTyped := (unfold_sound environmentWF localsWF registered computed typed).hasType.2
  unfold unfold at computed
  split at computed <;> try contradiction
  rename_i sourceUniverse targetUniverse domain relation target function respect major
  split at computed <;> try contradiction
  rename_i zeroChecked
  cases Option.some.inj computed
  cases reduction with
  | app prefixReduction majorReduction =>
    have matched := Pattern.Matches.const (c := ``Quot.lift) (ls := [sourceUniverse, targetUniverse])
      |>.var (a' := domain) |>.var (a' := relation) |>.var (a' := target)
      |>.var (a' := function) |>.var (a' := respect)
    obtain ⟨reducedValues, reducedMatched, argumentsReduced⟩ :=
      liftPrefix_parRed_inv registered (by decide : 5 ≤ 5) matched prefixReduction
    let .var reducedMatched := reducedMatched
    let .var reducedMatched := reducedMatched
    let .var reducedMatched := reducedMatched
    let .var reducedMatched := reducedMatched
    let .var reducedMatched := reducedMatched
    let .const := reducedMatched
    have congruence := ParRed.app (argumentsReduced (some none))
      (selector_parRed (argumentsReduced (some (some (some (some none)))))
        (argumentsReduced (some (some (some none)))) majorReduction)
    have joinedTyped := congruence.hasType localsWF unfoldedTyped
    refine ⟨_, _, .core congruence, .tail .rfl (.unfold ?_), .refl joinedTyped, joinedTyped, joinedTyped⟩
    simp only [unfold, zeroChecked, ite_true]
    rfl
  | extra rule matched checked argumentsReduced =>
    cases rule with
    | delta => cases matched
    | quot =>
      obtain ⟨joined, _, step, normal, joinedTyped, resultTyped⟩ :=
        unfold_extra_join registered localsWF typed originalComputed matched checked argumentsReduced
      exact ⟨joined, _, step, .rfl, normal, joinedTyped, resultTyped⟩

end Lean4Lean.VEnv.QuotPropReduction
