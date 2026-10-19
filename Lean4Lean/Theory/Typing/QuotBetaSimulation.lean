import Lean4Lean.Theory.Typing.SimultaneousNormalSubstitution
import Lean4Lean.Theory.Typing.QuotEtaSimulation

namespace Lean4Lean.VEnv.QuotPropReduction

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

theorem Steps.lam_congr {domain domain' body body' : VExpr}
    (domainSteps : Steps environmentWF universes locals domain domain')
    (bodySteps : Steps environmentWF universes (domain :: locals) body body') :
    Steps environmentWF universes locals (.lam domain body) (.lam domain' body') := by
  letI := environmentWF.reductionParams universes
  have bodies := bodySteps.lam
  refine bodies.trans ?_
  induction domainSteps with
  | rfl => exact .rfl
  | tail _ step induction => exact .tail induction (.lam step (.core .rfl))

/-- Every occurrence of the substituted argument follows its candidate path,
including duplicated occurrences and occurrences beneath retained binders. -/
theorem Steps.instN_argument {argument argument' argumentType expression : VExpr}
    (substitution : Ctx.InstN base argument argumentType depth sourceLocals targetLocals)
    (argumentSteps : Steps environmentWF universes base argument argument') :
    Steps environmentWF universes targetLocals
      (expression.inst argument depth) (expression.inst argument' depth) := by
  induction expression generalizing depth sourceLocals targetLocals with
  | bvar index =>
    induction substitution generalizing index with
    | zero =>
      cases index with
      | zero => simpa only [VExpr.inst, VExpr.instVar_zero] using argumentSteps
      | succ index => exact .rfl
    | succ substitution induction =>
      cases index with
      | zero => exact .rfl
      | succ index =>
        simpa only [VExpr.inst, VExpr.instVar_succ] using
          (induction (index := index)).weakN Ctx.LiftN.one
  | sort | const => exact .rfl
  | app _ _ functionIH argumentIH => exact (functionIH substitution).app (argumentIH substitution)
  | lam _ _ domainIH bodyIH => exact (domainIH substitution).lam_congr (bodyIH substitution.succ)
  | forallE _ _ domainIH bodyIH => exact (domainIH substitution).forallE (bodyIH substitution.succ)

/-- Simultaneous candidate reduction of the body and the substituted argument. -/
theorem Steps.instN_both {argument argument' argumentType source result : VExpr}
    (substitution : Ctx.InstN base argument argumentType depth sourceLocals targetLocals)
    (argumentTyped : environment.HasType universes base argument argumentType)
    (bodySteps : Steps environmentWF universes sourceLocals source result)
    (argumentSteps : Steps environmentWF universes base argument argument') :
    Steps environmentWF universes targetLocals
      (source.inst argument depth) (result.inst argument' depth) :=
  (bodySteps.instN substitution argumentTyped).trans
    (argumentSteps.instN_argument substitution)

/-- The beta branch for normally related lambda bodies, after the recursive
body and argument simulations have produced their actual witnesses. Both
endpoints retain the ORIGINAL application result type. -/
theorem CoreSimulates.lam_beta
    {domain leftDomain rightDomain leftBody rightBody argument rightArgument : VExpr}
    {bodyResult argumentResult resultType : VExpr} {level : VLevel}
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (leftDomainEqual : environment.IsDefEq universes locals domain leftDomain (.sort level))
    (rightDomainEqual : environment.IsDefEq universes locals domain rightDomain (.sort level))
    (argumentTyped : environment.HasType universes locals argument domain)
    (sourceTyped : environment.HasType universes locals (.app (.lam leftDomain leftBody) argument) resultType)
    (bodySimulation : CoreSimulates environmentWF universes (domain :: locals) leftBody rightBody)
    (argumentSimulation : CoreSimulates environmentWF universes locals argument rightArgument)
    (bodyReduction : @ParRed (environmentWF.reductionParams universes)
      (rightDomain :: locals) rightBody bodyResult)
    (rightBodyTyped : environment.HasType universes (rightDomain :: locals) rightBody rightBodyType)
    (argumentReduction : @ParRed (environmentWF.reductionParams universes) locals rightArgument argumentResult) :
    ∃ leftResult,
      @ParRed (environmentWF.reductionParams universes) locals
        (.app (.lam rightDomain rightBody) rightArgument) (bodyResult.inst argumentResult) ∧
      Steps environmentWF universes locals (.app (.lam leftDomain leftBody) argument) leftResult ∧
      @NormalEq (environmentWF.reductionParams universes) locals leftResult (bodyResult.inst argumentResult) ∧
      environment.HasType universes locals leftResult resultType ∧
      environment.HasType universes locals (bodyResult.inst argumentResult) resultType := by
  letI := environmentWF.reductionParams universes
  have convertedReduction := bodyReduction.defeqDFC localsWF
    (.succ .zero rightDomainEqual.symm) rightBodyTyped
  obtain ⟨leftBodyResult, bodySteps, bodyNormal⟩ := bodySimulation convertedReduction
  obtain ⟨leftArgumentResult, argumentSteps, argumentNormal⟩ := argumentSimulation argumentReduction
  have instantiatedSteps := bodySteps.instN_both Ctx.InstN.zero argumentTyped argumentSteps
  have beta : ParRed locals (.app (.lam leftDomain leftBody) argument) (leftBody.inst argument) :=
    .beta .rfl .rfl
  have leftSteps : Steps environmentWF universes locals
      (.app (.lam leftDomain leftBody) argument) (leftBodyResult.inst leftArgumentResult) :=
    (ReflTransGen.tail .rfl (.core beta)).trans instantiatedSteps
  have reducedArgumentTyped := argumentSteps.hasType registered localsWF argumentTyped
  have normal := NormalEq.instDF localsWF leftDomainEqual.hasType.1 reducedArgumentTyped argumentNormal bodyNormal
  have leftTyped := leftSteps.hasType registered localsWF sourceTyped
  exact ⟨_, .beta bodyReduction argumentReduction, leftSteps, normal, leftTyped,
    ((normal.defeq localsWF).of_l environmentWF localsWF leftTyped).hasType.2⟩

end Lean4Lean.VEnv.QuotPropReduction
