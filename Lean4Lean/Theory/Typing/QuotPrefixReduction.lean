import Lean4Lean.Theory.Typing.QuotPropReduction

namespace Lean4Lean.VEnv.QuotPropReduction

open private applicationArgumentTyped from Lean4Lean.Theory.Typing.QuotReduction

def expand : Nat → VExpr → VExpr → Option VExpr
  | 0, source, _ => unfold source
  | remaining + 1, source, .forallE domain body =>
    (expand remaining (.app source.lift (.bvar 0)) body).map (.lam domain)
  | _, _, _ => none

def applyArguments : VExpr → List VExpr → VExpr
  | function, [] => function
  | function, argument :: arguments => applyArguments (.app function argument) arguments

def spine : VExpr → VExpr × List VExpr
  | .app function argument =>
    let (head, arguments) := spine function
    (head, arguments ++ [argument])
  | expression => (expression, [])

def applyType : VExpr → List VExpr → Option VExpr
  | type, [] => some type
  | .forallE _ body, argument :: arguments => applyType (body.inst argument) arguments
  | _, _ => none

def unfoldPrefix (source : VExpr) : Option VExpr := do
  let (.const ``Quot.lift levels, arguments) := spine source | none
  if arguments.length > 6 then none else
  let type ← applyType (quotLiftConst.type.instL levels) arguments
  expand (6 - arguments.length) source type

theorem applyArguments_append (function : VExpr) (first second : List VExpr) :
    applyArguments function (first ++ second) = applyArguments (applyArguments function first) second := by
  induction first generalizing function with
  | nil => rfl
  | cons argument arguments induction => exact induction (.app function argument)

theorem applyArguments_spine (source : VExpr) :
    applyArguments (spine source).1 (spine source).2 = source := by
  induction source with
  | app function argument functionIH _ =>
    simp only [spine, applyArguments_append, applyArguments, functionIH]
  | _ => rfl

theorem spine_applyArguments (source : VExpr) (arguments : List VExpr) :
    spine (applyArguments source arguments) = ((spine source).1, (spine source).2 ++ arguments) := by
  induction arguments generalizing source with
  | nil => simp only [applyArguments, List.append_nil]
  | cons argument arguments induction =>
    simpa only [applyArguments, spine, List.append_assoc, List.singleton_append] using
      induction (.app source argument)

theorem applyType_append (type : VExpr) (first second : List VExpr) :
    applyType type (first ++ second) = (applyType type first >>= fun residual => applyType residual second) := by
  induction first generalizing type with
  | nil => rfl
  | cons argument arguments induction =>
    cases type <;> simp only [List.cons_append, applyType, bind, Option.bind] <;> try rfl
    exact induction _

theorem unfoldPrefix_complete {sourceUniverse targetUniverse : VLevel} {arguments : List VExpr}
    (zeroChecked : zeroLike sourceUniverse = true)
    (bounded : arguments.length ≤ 6) :
    (unfoldPrefix (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) arguments)).isSome = true := by
  match arguments with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] =>
    simp [unfoldPrefix, spine, applyType, quotLiftConst,
      expand, unfold, applyArguments, zeroChecked, VExpr.instL, VLevel.inst,
      VExpr.lift, VExpr.liftN, VExpr.inst, VExpr.instVar, liftVar]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp only [List.length_cons] at bounded
    omega

/-- Prefix expansion commutes with substitution beneath every retained binder. -/
theorem expand_inst {source type result : VExpr}
    (expanded : expand remaining source type = some result) (argument : VExpr) (depth : Nat) :
    expand remaining (source.inst argument depth) (type.inst argument depth) =
      some (result.inst argument depth) := by
  induction remaining generalizing source type result depth with
  | zero => exact unfold_inst expanded argument depth
  | succ remaining induction =>
    cases type <;> try contradiction
    rename_i domain body
    simp only [expand, Option.map_eq_some_iff] at expanded
    obtain ⟨expandedBody, bodyExpanded, rfl⟩ := expanded
    have substituted := induction bodyExpanded (depth + 1)
    simpa only [expand, VExpr.inst, ← VExpr.lift_instN_lo, VExpr.instVar_lower] using
      congrArg (Option.map (VExpr.lam (domain.inst argument depth))) substituted

/-- Applying an expanded prefix exposes exactly the remaining expansion. -/
theorem expand_apply {source domain body result : VExpr}
    (expanded : expand (remaining + 1) source (.forallE domain body) = some result)
    (argument : VExpr) :
    ∃ expandedBody, result = .lam domain expandedBody ∧
      expand remaining (.app source argument) (body.inst argument) =
        some (expandedBody.inst argument) := by
  simp only [expand, Option.map_eq_some_iff] at expanded
  obtain ⟨expandedBody, bodyExpanded, rfl⟩ := expanded
  refine ⟨expandedBody, rfl, ?_⟩
  simpa [VExpr.inst, VExpr.instVar, VExpr.inst_lift] using expand_inst bodyExpanded argument 0

/-- For every partial quotient-lift spine, applying the generated lambda and
expanding the next prefix produce definitionally identical bodies. -/
theorem unfoldPrefix_apply {levels : List VLevel} {arguments : List VExpr} {result : VExpr}
    (bounded : arguments.length < 6)
    (expanded : unfoldPrefix (applyArguments (.const ``Quot.lift levels) arguments) = some result)
    (argument : VExpr) :
    ∃ domain expandedBody, result = .lam domain expandedBody ∧
      unfoldPrefix (applyArguments (.const ``Quot.lift levels) (arguments ++ [argument])) =
        some (expandedBody.inst argument) := by
  have remaining : 6 - arguments.length = (5 - arguments.length) + 1 := by omega
  simp only [unfoldPrefix, spine_applyArguments, spine, List.nil_append] at expanded
  simp only [show ¬arguments.length > 6 by omega, ↓reduceIte, bind, Option.bind_eq_some_iff] at expanded
  obtain ⟨type, computed, expanded⟩ := expanded
  rw [remaining] at expanded
  cases type <;> try contradiction
  rename_i domain body
  obtain ⟨expandedBody, resultShape, appliedExpanded⟩ := expand_apply expanded argument
  refine ⟨domain, expandedBody, resultShape, ?_⟩
  have appliedBound : ¬(arguments ++ [argument]).length > 6 := by simp only [List.length_append, List.length_singleton]; omega
  have appliedRemaining : 6 - (arguments ++ [argument]).length = 5 - arguments.length := by
    simp only [List.length_append, List.length_singleton]; omega
  simpa only [unfoldPrefix, spine_applyArguments, spine, List.nil_append, appliedBound, ↓reduceIte,
    applyType_append, computed, bind, Option.bind, applyType, appliedRemaining,
    applyArguments_append, applyArguments] using appliedExpanded

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}

theorem Steps.weakN {environmentWF : environment.WF}
    (insertion : Ctx.LiftN count depth locals extended)
    (steps : Steps environmentWF universes locals source result) :
    Steps environmentWF universes extended (source.liftN count depth) (result.liftN count depth) := by
  induction steps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (step.weakN insertion)

theorem Steps.instN {environmentWF : environment.WF} {argument argumentType : VExpr}
    (substitution : Ctx.InstN base argument argumentType depth locals substituted)
    (argumentTyped : environment.HasType universes base argument argumentType)
    (steps : Steps environmentWF universes locals source result) :
    Steps environmentWF universes substituted (source.inst argument depth) (result.inst argument depth) := by
  induction steps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (step.instN substitution argumentTyped)

theorem Step.defeqDFC {environmentWF : environment.WF}
    (baseWF : OnCtx base (environment.IsType universes))
    (conversion : IsDefEqCtx environment universes base locals converted)
    (typed : environment.HasType universes locals source type)
    (step : Step environmentWF universes locals source result) :
    Step environmentWF universes converted source result := by
  letI := environmentWF.reductionParams universes
  induction step generalizing converted type with
  | core reduction => exact .core (reduction.defeqDFC baseWF conversion typed)
  | unfold unfolded => exact .unfold unfolded
  | funEta functionTyped => exact .funEta (functionTyped.defeqDFC environmentWF.ordered conversion)
  | app _ _ functionIH argumentIH =>
    obtain ⟨_, _, functionTyped, argumentTyped⟩ :=
      typed.app_inv environmentWF.ordered (conversion.isType' baseWF)
    exact .app (functionIH conversion functionTyped) (argumentIH conversion argumentTyped)
  | lam _ _ domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ :=
      typed.lam_inv environmentWF.ordered (conversion.isType' baseWF)
    exact .lam (domainIH conversion domainTyped) (bodyIH (conversion.succ domainTyped) bodyTyped)
  | forallE _ _ domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := typed.forallE_inv environmentWF.ordered
    exact .forallE (domainIH conversion domainTyped) (bodyIH (conversion.succ domainTyped) bodyTyped)

theorem Steps.defeqDFC {environmentWF : environment.WF}
    (registered : environment.defeqs quotDefEq)
    (baseWF : OnCtx base (environment.IsType universes))
    (conversion : IsDefEqCtx environment universes base locals converted)
    (typed : environment.HasType universes locals source type)
    (steps : Steps environmentWF universes locals source result) :
    Steps environmentWF universes converted source result := by
  induction steps with
  | rfl => exact .rfl
  | tail previous step induction =>
    exact .tail induction (step.defeqDFC baseWF conversion
      (Steps.hasType registered (conversion.isType' baseWF) previous typed))

theorem applyArguments_headTyped
    (environmentOrdered : environment.Ordered)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments function arguments) resultType) :
    ∃ type, environment.HasType universes locals function type := by
  induction arguments generalizing function with
  | nil => exact ⟨_, typed⟩
  | cons argument arguments induction =>
    obtain ⟨_, applicationTyped⟩ := induction typed
    obtain ⟨_, _, functionTyped, _⟩ := applicationTyped.app_inv environmentOrdered localsWF
    exact ⟨_, functionTyped⟩

theorem applyType_hasType
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments function arguments) resultType)
    (functionTyped : environment.HasType universes locals function functionType)
    (computed : applyType functionType arguments = some type) :
    environment.HasType universes locals (applyArguments function arguments) type := by
  induction arguments generalizing function functionType with
  | nil => cases Option.some.inj computed; exact functionTyped
  | cons argument arguments induction =>
    cases functionType <;> try contradiction
    obtain ⟨_, applicationTyped⟩ := applyArguments_headTyped
      (function := .app function argument) (arguments := arguments) environmentWF.ordered localsWF typed
    have argumentTyped := applicationArgumentTyped environmentWF localsWF applicationTyped functionTyped
    exact induction typed (functionTyped.app argumentTyped) computed

theorem Steps.app {environmentWF : environment.WF}
    (functionSteps : Steps environmentWF universes locals function function')
    (argumentSteps : Steps environmentWF universes locals argument argument') :
    Steps environmentWF universes locals (.app function argument) (.app function' argument') := by
  letI := environmentWF.reductionParams universes
  have arguments : Steps environmentWF universes locals (.app function argument) (.app function argument') := by
    induction argumentSteps with
    | rfl => exact .rfl
    | tail _ step induction => exact .tail induction (.app (.core .rfl) step)
  refine arguments.trans ?_
  induction functionSteps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (.app step (.core .rfl))

theorem Steps.lam {environmentWF : environment.WF}
    (bodySteps : Steps environmentWF universes (domain :: locals) body body') :
    Steps environmentWF universes locals (.lam domain body) (.lam domain body') := by
  letI := environmentWF.reductionParams universes
  induction bodySteps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (.lam (.core .rfl) step)

theorem etaBody_hasType
    (environmentOrdered : environment.Ordered)
    (typed : environment.HasType universes locals source (.forallE domain body)) :
    environment.HasType universes (domain :: locals) (.app source.lift (.bvar 0)) body := by
  have lifted := typed.weak environmentOrdered (B := domain)
  change environment.HasType universes (domain :: locals) source.lift
    (.forallE domain.lift (body.liftN 1 1)) at lifted
  simpa only [VExpr.instN_bvar0] using lifted.appDF (HasType.bvar .zero)

theorem expand_steps {environmentWF : environment.WF} {source result type : VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source type)
    (expanded : expand remaining source type = some result) :
    Steps environmentWF universes locals source result := by
  induction remaining generalizing locals source type result with
  | zero => exact .tail .rfl (.unfold expanded)
  | succ remaining induction =>
    cases type <;> try contradiction
    rename_i domain body
    simp only [expand, Option.map_eq_some_iff] at expanded
    obtain ⟨expandedBody, bodyExpanded, rfl⟩ := expanded
    obtain ⟨_, typeTyped⟩ := typed.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    have bodySteps := induction (locals := domain :: locals) ⟨localsWF, _, domainTyped⟩
      (etaBody_hasType environmentWF.ordered typed) bodyExpanded
    exact (ReflTransGen.tail .rfl (.funEta typed)).trans bodySteps.lam

theorem expand_sound {environmentWF : environment.WF} {source result type : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source type)
    (expanded : expand remaining source type = some result) :
    environment.IsDefEq universes locals source result type :=
  (expand_steps (environmentWF := environmentWF) localsWF typed expanded).defeq registered localsWF typed

/-- The eta/application critical pair has an identical endpoint: expanding the
function and beta reducing its application agrees with expanding the applied
function. The endpoint retains the original dependent result type. -/
theorem expand_apply_join {environmentWF : environment.WF}
    {source domain body result argument : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (functionTyped : environment.HasType universes locals source (.forallE domain body))
    (argumentTyped : environment.HasType universes locals argument domain)
    (expanded : expand (remaining + 1) source (.forallE domain body) = some result) :
    ∃ expandedBody, result = .lam domain expandedBody ∧
      expand remaining (.app source argument) (body.inst argument) =
        some (expandedBody.inst argument) ∧
      Steps environmentWF universes locals (.app source argument) (.app result argument) ∧
      @ParRed (environmentWF.reductionParams universes) locals
        (.app result argument) (expandedBody.inst argument) ∧
      Steps environmentWF universes locals (.app source argument) (expandedBody.inst argument) ∧
      environment.HasType universes locals (expandedBody.inst argument) (body.inst argument) := by
  letI := environmentWF.reductionParams universes
  obtain ⟨expandedBody, resultShape, appliedExpanded⟩ := expand_apply expanded argument
  have functionSteps := expand_steps (environmentWF := environmentWF) localsWF functionTyped expanded
  have functionApplication := functionSteps.app (show Steps environmentWF universes locals argument argument from .rfl)
  have beta : ParRed locals (.app result argument) (expandedBody.inst argument) :=
    resultShape ▸ ParRed.beta .rfl .rfl
  have appliedSteps := expand_steps (environmentWF := environmentWF) localsWF
    (functionTyped.app argumentTyped) appliedExpanded
  exact ⟨expandedBody, resultShape, appliedExpanded, functionApplication, beta, appliedSteps,
    appliedSteps.hasType registered localsWF (functionTyped.app argumentTyped)⟩

theorem prefix_steps {environmentWF : environment.WF} {source result type : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source type)
    (expanded : unfoldPrefix source = some result) :
    Steps environmentWF universes locals source result := by
  unfold unfoldPrefix at expanded
  generalize spineEquation : spine source = decomposition at expanded
  obtain ⟨head, arguments⟩ := decomposition
  split at expanded <;> try contradiction
  rename_i levels
  cases levels
  split at expanded <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at expanded
  obtain ⟨computedType, computed, expanded⟩ := expanded
  have reconstructed := applyArguments_spine source
  rw [spineEquation] at reconstructed
  have actualTyped := reconstructed ▸ typed
  obtain ⟨_, headTyped⟩ := applyArguments_headTyped environmentWF.ordered localsWF actualTyped
  obtain ⟨constant, lookup, levelsWF, arity⟩ := headTyped.const_inv environmentWF.ordered localsWF
  obtain ⟨_, _, liftRegistered, _⟩ := environmentWF.quotientObjects registered
  rw [liftRegistered] at lookup
  cases lookup
  have canonicalHead := HasType.const liftRegistered levelsWF arity (Γ := locals)
  have canonicalTyped := applyType_hasType environmentWF localsWF actualTyped canonicalHead computed
  rw [reconstructed] at canonicalTyped
  exact expand_steps (environmentWF := environmentWF) localsWF canonicalTyped expanded

theorem prefix_sound {environmentWF : environment.WF} {source result type : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals source type)
    (expanded : unfoldPrefix source = some result) :
    environment.IsDefEq universes locals source result type :=
  (prefix_steps (environmentWF := environmentWF) registered localsWF typed expanded).defeq
    registered localsWF typed

theorem prefix_reduces {environmentWF : environment.WF}
    {sourceUniverse targetUniverse : VLevel} {type : VExpr} {arguments : List VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (zeroEquivalent : sourceUniverse ≈ .zero)
    (bounded : arguments.length ≤ 6)
    (typed : environment.HasType universes locals
      (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) arguments) type) :
    ∃ result,
      unfoldPrefix (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) arguments) = some result ∧
      Steps environmentWF universes locals
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) arguments) result ∧
      environment.IsDefEq universes locals
        (applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) arguments) result type := by
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp
    (unfoldPrefix_complete ((zeroLike_iff _).mpr zeroEquivalent) bounded (targetUniverse := targetUniverse))
  have steps := prefix_steps (environmentWF := environmentWF) registered localsWF typed computed
  exact ⟨result, computed, steps, steps.defeq registered localsWF typed⟩

/-- The actual prefix algorithm closes its eta/beta application overlap at every
partial spine. Both paths reach exactly the same term at the original application
type; no normal-equality simulation or strengthening principle is used. -/
theorem prefix_apply_join {environmentWF : environment.WF}
    {levels : List VLevel} {arguments : List VExpr} {result argument type : VExpr}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (bounded : arguments.length < 6)
    (typed : environment.HasType universes locals
      (.app (applyArguments (.const ``Quot.lift levels) arguments) argument) type)
    (expanded : unfoldPrefix (applyArguments (.const ``Quot.lift levels) arguments) = some result) :
    ∃ domain expandedBody, result = .lam domain expandedBody ∧
      unfoldPrefix (.app (applyArguments (.const ``Quot.lift levels) arguments) argument) =
        some (expandedBody.inst argument) ∧
      Steps environmentWF universes locals
        (.app (applyArguments (.const ``Quot.lift levels) arguments) argument) (.app result argument) ∧
      @ParRed (environmentWF.reductionParams universes) locals
        (.app result argument) (expandedBody.inst argument) ∧
      Steps environmentWF universes locals
        (.app (applyArguments (.const ``Quot.lift levels) arguments) argument) (expandedBody.inst argument) ∧
      environment.HasType universes locals (expandedBody.inst argument) type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨domain, expandedBody, resultShape, appliedExpanded⟩ := unfoldPrefix_apply bounded expanded argument
  rw [applyArguments_append] at appliedExpanded
  obtain ⟨_, _, functionTyped, _⟩ := typed.app_inv environmentWF.ordered localsWF
  have functionSteps := prefix_steps (environmentWF := environmentWF) registered localsWF functionTyped expanded
  have functionApplication := functionSteps.app (show Steps environmentWF universes locals argument argument from .rfl)
  have beta : ParRed locals (.app result argument) (expandedBody.inst argument) :=
    resultShape ▸ ParRed.beta .rfl .rfl
  have appliedSteps := prefix_steps (environmentWF := environmentWF) registered localsWF typed appliedExpanded
  exact ⟨domain, expandedBody, resultShape, appliedExpanded, functionApplication, beta, appliedSteps,
    appliedSteps.hasType registered localsWF typed⟩

end Lean4Lean.VEnv.QuotPropReduction
