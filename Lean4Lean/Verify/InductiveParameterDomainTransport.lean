import Lean4Lean.Verify.InductiveParameterPrefixTyping

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem ParameterPrefix.toCtx_length (parameters : ParameterPrefix base source identifiers) :
    source.vlctx.toCtx.length = identifiers.length + base.vlctx.toCtx.length := by
  induction parameters with
  | nil => simp
  | snoc _ induction =>
    simpa [VLCtx.toCtx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg Nat.succ induction

private theorem parameterDomainContextTail
    {env : VEnv} {universes : Nat} {base source target : List VExpr} {domain targetDomain : VExpr}
    (contexts : env.IsDefEqCtx universes base (domain :: source) (targetDomain :: target))
    (proper : base.length < (domain :: source).length) :
    ∃ level, env.IsDefEqCtx universes base source target ∧
      env.IsDefEq universes source domain targetDomain (.sort level) := by
  cases contexts with
  | zero => omega
  | succ contexts domainEquality => exact ⟨_, contexts, domainEquality⟩

theorem ParameterPrefix.forall_defeq
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId} {body targetBody : VExpr} {level : VLevel}
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (contexts : env.IsDefEqCtx universes.length base.vlctx.toCtx source.vlctx.toCtx target.vlctx.toCtx)
    (bodyEquality : env.IsDefEq universes.length source.vlctx.toCtx body targetBody (.sort level)) :
    ∃ resultLevel, env.IsDefEq universes.length base.vlctx.toCtx
      (source.mkForall' identifiers.length parameters.bound body)
      (target.mkForall' targetIdentifiers.length targetParameters.bound targetBody) (.sort resultLevel) := by
  induction parameters generalizing target targetIdentifiers body targetBody level with
  | nil =>
    cases targetParameters with
    | nil => exact ⟨_, bodyEquality⟩
    | snoc => simp at length
  | @snoc previous identifiers identifier name nativeDomain domain binder parameters induction =>
    cases targetParameters with
    | nil => simp at length
    | @snoc target targetIdentifiers targetIdentifier targetName targetNativeDomain targetDomain targetBinder targetParameters =>
      have proper : base.vlctx.toCtx.length < (domain :: previous.vlctx.toCtx).length := by
        simp only [List.length_cons, parameters.toCtx_length]
        omega
      obtain ⟨_, previousContexts, domainEquality⟩ := parameterDomainContextTail contexts proper
      have previousLength : identifiers.length = targetIdentifiers.length := by simpa using length
      simpa only [List.length_append, List.length_singleton, MLCtx.mkForall'] using
        induction targetParameters previousLength previousContexts (.forallEDF domainEquality bodyEquality)

theorem replaceParams.prefix_typedInto_defeq
    {env : VEnv} {universes : List Name} {base source target : MLCtx} {identifiers : List FVarId}
    {insertionLift : Lift} (envWF : env.WF) (sourceWF : source.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0)
    {functionType resultType : VExpr} {replacements : List Expr} {arguments : List VExpr}
    (functionEquality : env.IsDefEqU universes.length target.vlctx.toCtx
      ((source.mkForall' identifiers.length parameters.bound semanticType).lift' insertionLift) functionType)
    (argumentTyping : TypedParameterArguments env universes target functionType replacements arguments resultType)
    (length : identifiers.length = replacements.length)
    (nativeEnv : Kernel.Environment) (state : State) :
    (replaceParams replacements.toArray body (identifiers.map Expr.fvar).toArray nativeEnv state).WF
      fun returned => returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList replacements ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes target.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length target.vlctx.toCtx resultSemantic resultType ∧
          env.IsDefEq universes.length target.vlctx.toCtx resultSemantic
            (applyParameterArguments
              ((source.mkLambda' identifiers.length parameters.bound semantic).lift' insertionLift) arguments)
            resultType := by
  have closed : Closed body 0 := source.noBV ▸ translated.closed
  rw [replaceParams.prefix_eq identifiers replacements body nativeEnv state
    ⟨closed.looseBVarRange_zero, argumentTyping.closed⟩ (parameters.nodup sourceWF) length]
  have abstraction := sourceWF.mkLambda_trS envWF translated typed identifiers.length parameters.bound
  rw [parameters.drop] at abstraction
  have functionTyped := (abstraction.2.weak' envWF.ordered insertion.toCtx).defeqU_r
    envWF targetWF.tr.wf.toCtx functionEquality
  have applied := argumentTyping.apply
    (abstraction.1.weakFV' envWF.ordered insertion targetWF.tr.wf) functionTyped
  have beta : BetaReduce ((source.mkLambda identifiers.length parameters.bound body).mkAppList replacements)
      ((body.abstractList identifiers).instantiateRevList replacements) := by
    have lambdas : LambdaBodyN replacements.length
        (source.mkLambda identifiers.length parameters.bound body) (body.abstractList identifiers) := by
      simpa only [← length] using parameters.lambdaBody sourceWF body
    apply BetaReduce.inst_reduce (fn := body.abstractList identifiers) argumentTyping.closed [] lambdas
    simp [Expr.instantiateList_reverse]
  have result := (applied.1.trExpr envWF.ordered targetWF.tr.wf).beta envWF targetWF.tr.wf beta
  have resultClosed : Closed ((body.abstractList identifiers).instantiateRevList replacements) 0 :=
    target.noBV ▸ result.closed
  obtain ⟨resultSemantic, resultTranslated, resultEquality⟩ := result
  have equality := resultEquality.of_r envWF targetWF.tr.wf applied.2
  exact Except.WF.pure ⟨rfl, rfl, resultClosed, resultClosed.looseBVarRange_zero,
    resultTranslated.fvarsIn, _, resultTranslated, equality.hasType.1, equality⟩

theorem replaceParams.prefix_rename_defeq_typed
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId}
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (contexts : env.IsDefEqCtx universes.length base.vlctx.toCtx source.vlctx.toCtx target.vlctx.toCtx)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Kernel.Environment) (state : State) :
    (replaceParams (targetIdentifiers.map Expr.fvar).toArray body
      (identifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList (targetIdentifiers.map Expr.fvar) ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes target.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length target.vlctx.toCtx resultSemantic semanticType := by
  obtain ⟨_, typeTyped⟩ := typed.isType envWF.ordered sourceWF.tr.wf.toCtx
  obtain ⟨level, typeEquality⟩ := parameters.forall_defeq targetParameters length contexts typeTyped
  have insertedEquality := typeEquality.weak' envWF.ordered targetParameters.insertion.toCtx
  obtain ⟨arguments, argumentTyping⟩ := targetParameters.arguments envWF targetWF semanticType
  have lifted (expression : VExpr) : expression.lift' (.skipN .refl targetIdentifiers.length) =
      expression.liftN targetIdentifiers.length :=
    VExpr.lift'_consN_skipN (e := expression) (n := targetIdentifiers.length) (k := 0)
  have typedArguments : TypedParameterArguments env universes target
      ((target.mkForall' targetIdentifiers.length targetParameters.bound semanticType).lift'
        (.skipN .refl targetIdentifiers.length)) (targetIdentifiers.map Expr.fvar) arguments semanticType := by
    rw [lifted]
    exact argumentTyping
  exact (replaceParams.prefix_typedInto_defeq envWF sourceWF parameters translated typed targetWF
    targetParameters.insertion ⟨_, insertedEquality⟩ typedArguments (by simpa using length) nativeEnv state).mono
      fun _ ⟨unchanged, equation, closed, scope, support, resultSemantic, translation, typing, _⟩ =>
        ⟨unchanged, equation, closed, scope, support, resultSemantic, translation, typing⟩

theorem isNestedInductiveApp?.defeqTypedRebinding
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId} {expression : Expr} {semantic semanticType : VExpr}
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (contexts : env.IsDefEqCtx universes.length base.vlctx.toCtx source.vlctx.toCtx target.vlctx.toCtx)
    (translated : TrExprS env universes source.vlctx expression semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Kernel.Environment) (state : State) :
    ((do
      let some info ← isNestedInductiveApp? expression | return none
      let rebound ← replaceParams (targetIdentifiers.map Expr.fvar).toArray
        (mkAppRange expression.getAppFn 0 info.numParams expression.getAppArgs)
        (identifiers.map Expr.fvar).toArray
      return some rebound : M (Option Expr)) nativeEnv state).WF fun returned =>
        returned.2 = state ∧ ∀ rebound, returned.1 = some rebound →
          Closed rebound 0 ∧ rebound.looseBVarRange' = 0 ∧
          rebound.FVarsIn (· ∈ target.vlctx.fvars) ∧
          ∃ info prefixSemantic resultSemantic resultType, NestedAppScope expression info ∧
            rebound = ((mkAppRange expression.getAppFn 0 info.numParams expression.getAppArgs).abstractList
              identifiers).instantiateRevList (targetIdentifiers.map Expr.fvar) ∧
            TrExprS env universes source.vlctx
              (mkAppRange expression.getAppFn 0 info.numParams expression.getAppArgs) prefixSemantic ∧
            env.HasType universes.length source.vlctx.toCtx prefixSemantic resultType ∧
            TrExprS env universes target.vlctx rebound resultSemantic ∧
            env.HasType universes.length target.vlctx.toCtx resultSemantic resultType := by
  refine (isNestedInductiveApp?.typedPrefix translated typed nativeEnv state).bind ?_
  rintro ⟨selected, current⟩ ⟨unchanged, receipts⟩
  change current = state at unchanged
  subst current
  cases selected with
  | none => exact Except.WF.pure ⟨rfl, by simp⟩
  | some info =>
    obtain ⟨scopeReceipt, prefixSemantic, prefixType, prefixTranslated, prefixTyped⟩ := receipts info rfl
    refine (replaceParams.prefix_rename_defeq_typed envWF sourceWF targetWF parameters targetParameters
      length contexts prefixTranslated prefixTyped nativeEnv state).bind ?_
    rintro ⟨rebound, current⟩ ⟨unchanged, equation, closed, scope, support, resultSemantic, translated, typed⟩
    change current = state at unchanged
    subst current
    exact Except.WF.pure ⟨rfl, fun result equality => by
      cases equality
      exact ⟨closed, scope, support, info, prefixSemantic, resultSemantic, prefixType,
        scopeReceipt, equation, prefixTranslated, prefixTyped, translated, typed⟩⟩

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

theorem isDefEq.acceptedParameterDomain
    {context : VContext} {initial : VState} {final : State}
    {sourceDomain targetDomain : Expr} {sourceSemantic targetSemantic : VExpr} {level : VLevel}
    (sourceTranslated : context.TrExprS sourceDomain sourceSemantic)
    (targetTranslated : context.TrExprS targetDomain targetSemantic)
    (sourceTyped : context.HasType sourceSemantic (.sort level))
    (initialWF : initial.WF context)
    (accepted : isDefEq sourceDomain targetDomain context.toContext initial.toState = .ok (true, final)) :
    context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
      sourceSemantic targetSemantic (.sort level) := by
  obtain ⟨_, _, _, _, equality⟩ := isDefEq.WF sourceTranslated targetTranslated initialWF true final accepted
  exact (equality rfl).of_l context.Ewf context.Δwf.toCtx sourceTyped

theorem isDefEq.acceptedParameterContextStep
    {context : VContext} {initial : VState} {final : State} {base target : List VExpr}
    {sourceDomain targetDomain : Expr} {sourceSemantic targetSemantic : VExpr} {level : VLevel}
    (contexts : context.venv.IsDefEqCtx context.lparams.length base context.vlctx.toCtx target)
    (sourceTranslated : context.TrExprS sourceDomain sourceSemantic)
    (targetTranslated : context.TrExprS targetDomain targetSemantic)
    (sourceTyped : context.HasType sourceSemantic (.sort level))
    (initialWF : initial.WF context)
    (accepted : isDefEq sourceDomain targetDomain context.toContext initial.toState = .ok (true, final)) :
    context.venv.IsDefEqCtx context.lparams.length base
      (sourceSemantic :: context.vlctx.toCtx) (targetSemantic :: target) :=
  .succ contexts (isDefEq.acceptedParameterDomain sourceTranslated targetTranslated sourceTyped initialWF accepted)

end Lean4Lean.TypeChecker
