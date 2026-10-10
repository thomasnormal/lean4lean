import Lean4Lean.Verify.InductiveSingletonParameterReplacement

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel
open TypeChecker (MLCtx)

inductive ParameterPrefix (base : MLCtx) : MLCtx → List FVarId → Prop where
  | nil : ParameterPrefix base base []
  | snoc (parameters : ParameterPrefix base source identifiers) :
      ParameterPrefix base (.vlam identifier name nativeDomain domain binder source)
        (identifiers ++ [identifier])

theorem ParameterPrefix.bound (parameters : ParameterPrefix base source identifiers) :
    identifiers.length ≤ source.length := by
  induction parameters with
  | nil => simp
  | snoc _ induction => simpa using Nat.succ_le_succ induction

theorem ParameterPrefix.drop (parameters : ParameterPrefix base source identifiers) :
    source.dropN identifiers.length parameters.bound = base := by
  induction parameters with
  | nil => rfl
  | snoc _ induction => simpa using induction

theorem ParameterPrefix.fvars (parameters : ParameterPrefix base source identifiers) :
    source.vlctx.fvars = identifiers.reverse ++ base.vlctx.fvars := by
  induction parameters with
  | nil => rfl
  | snoc _ induction => simp [induction]

theorem ParameterPrefix.fvarRevList (parameters : ParameterPrefix base source identifiers) :
    source.fvarRevList identifiers.length parameters.bound = identifiers.reverse := by
  induction parameters with
  | nil => rfl
  | snoc _ induction => simp [induction]

theorem ParameterPrefix.nodup (parameters : ParameterPrefix base source identifiers)
    (sourceWF : source.WF env universes) : identifiers.Nodup := by
  have distinct := sourceWF.fvars_nodup
  rw [parameters.fvars] at distinct
  exact List.nodup_reverse.mp (List.pairwise_append.mp distinct).1

private theorem abstractList_lam (name : Name) (nativeDomain expression : Expr)
    (binder : BinderInfo) (selected : List FVarId) (depth : Nat) :
    (Expr.lam name nativeDomain expression binder).abstractList selected depth =
      .lam name (nativeDomain.abstractList selected depth)
        (expression.abstractList selected (depth + 1)) binder := by
  induction selected generalizing expression nativeDomain with
  | nil => rfl
  | cons identifier _ induction =>
    simpa only [Expr.abstractList, Expr.abstract1] using
      induction (nativeDomain.abstract1 identifier depth) (expression.abstract1 identifier (depth + 1))

theorem ParameterPrefix.lambdaBody (parameters : ParameterPrefix base source identifiers)
    (sourceWF : source.WF env universes) (body : Expr) :
    LambdaBodyN identifiers.length (source.mkLambda identifiers.length parameters.bound body)
      (body.abstractList identifiers) := by
  induction parameters generalizing body with
  | nil => exact .zero
  | @snoc source identifiers identifier name nativeDomain domain binder parameters induction =>
    have fresh : identifier ∉ identifiers := by
      have absent := sourceWF.1.tr.find?_eq_none.mp sourceWF.2.1
      rw [parameters.fvars] at absent
      simp only [List.mem_append, List.mem_reverse] at absent
      exact fun member => absent (Or.inl member)
    have previous := induction sourceWF.1 (.lam name nativeDomain (body.abstract1 identifier) binder)
    rw [abstractList_lam] at previous
    have next := previous.add (LambdaBodyN.succ LambdaBodyN.zero)
    simpa only [List.length_append, List.length_singleton, MLCtx.mkLambda,
      Expr.abstractList_append, Expr.abstractList, Nat.add_comm 1,
      Expr.abstract1_abstractList fresh] using next

inductive TypedParameterArguments (env : VEnv) (universes : List Name) (base : MLCtx) :
    VExpr → List Expr → List VExpr → VExpr → Prop where
  | nil : TypedParameterArguments env universes base result [] [] result
  | cons (translated : TrExprS env universes base.vlctx replacement argument)
      (typed : env.HasType universes.length base.vlctx.toCtx argument domain)
      (remaining : TypedParameterArguments env universes base (codomain.inst argument)
        replacements arguments result) :
      TypedParameterArguments env universes base (.forallE domain codomain)
        (replacement :: replacements) (argument :: arguments) result

def applyParameterArguments : VExpr → List VExpr → VExpr
  | function, [] => function
  | function, argument :: arguments => applyParameterArguments (.app function argument) arguments

theorem TypedParameterArguments.length (arguments : TypedParameterArguments env universes base
    functionType replacements semantics resultType) : replacements.length = semantics.length := by
  induction arguments with
  | nil => rfl
  | cons _ _ _ induction => exact congrArg Nat.succ induction

theorem TypedParameterArguments.closed (arguments : TypedParameterArguments env universes base
    functionType replacements semantics resultType) : ∀ replacement ∈ replacements, Closed replacement 0 := by
  induction arguments with
  | nil => simp
  | cons translated _ _ induction =>
    simpa only [List.mem_cons, forall_eq_or_imp] using
      And.intro (base.noBV ▸ translated.closed) induction

theorem TypedParameterArguments.apply (arguments : TypedParameterArguments env universes base
    functionType replacements semantics resultType)
    {function : Expr} {semantic : VExpr}
    (translated : TrExprS env universes base.vlctx function semantic)
    (typed : env.HasType universes.length base.vlctx.toCtx semantic functionType) :
    TrExprS env universes base.vlctx (function.mkAppList replacements)
      (applyParameterArguments semantic semantics) ∧
    env.HasType universes.length base.vlctx.toCtx
      (applyParameterArguments semantic semantics) resultType := by
  induction arguments generalizing function semantic with
  | nil => exact ⟨translated, typed⟩
  | cons argumentTranslated argumentTyped _ induction =>
    exact induction (.app typed argumentTyped translated argumentTranslated) (typed.app argumentTyped)

theorem replaceParams.prefix_eq (identifiers : List FVarId) (replacements : List Expr)
    (body : Expr) (nativeEnv : Environment) (state : State)
    (scope : body.looseBVarRange' = 0 ∧ ∀ replacement ∈ replacements, Closed replacement 0)
    (distinct : identifiers.Nodup)
    (length : identifiers.length = replacements.length) :
    replaceParams replacements.toArray body (identifiers.map Expr.fvar).toArray nativeEnv state =
      .ok ((body.abstractList identifiers).instantiateRevList replacements, state) := by
  rw [replaceParams.eq_ok _ _ _ _ _ (by simpa using length)]
  rw [Expr.abstract_eq_of_scope scope.1 distinct, Expr.instantiateRev_eq, Expr.instantiate_eq,
    Array.toList_reverse, List.toList_toArray]
  rw [Expr.instantiateMany_eq_instantiateList _ _ _ ?_, Expr.instantiateList_reverse]
  intro replacement member
  exact (scope.2 replacement (by simpa using member)).looseBVarRange_zero

theorem replaceParams.prefix_typed
    {env : VEnv} {universes : List Name} {base source : MLCtx} {identifiers : List FVarId}
    (envWF : env.WF) (sourceWF : source.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    {body : Expr} {semantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic (.sort level))
    {replacements : List Expr} {arguments : List VExpr}
    (argumentTyping : TypedParameterArguments env universes base
      (source.mkForall' identifiers.length parameters.bound (.sort level)) replacements arguments (.sort level))
    (length : identifiers.length = replacements.length)
    (nativeEnv : Environment) (state : State) :
    (replaceParams replacements.toArray body (identifiers.map Expr.fvar).toArray nativeEnv state).WF
      fun returned => returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList replacements ∧
        TrExpr env universes base.vlctx returned.1
          (applyParameterArguments (source.mkLambda' identifiers.length parameters.bound semantic) arguments) ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes base.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length base.vlctx.toCtx resultSemantic (.sort level) ∧
          env.IsDefEq universes.length base.vlctx.toCtx resultSemantic
            (applyParameterArguments (source.mkLambda' identifiers.length parameters.bound semantic) arguments)
            (.sort level) := by
  have closed : Closed body 0 := source.noBV ▸ translated.closed
  rw [replaceParams.prefix_eq identifiers replacements body nativeEnv state
    ⟨closed.looseBVarRange_zero, argumentTyping.closed⟩ (parameters.nodup sourceWF) length]
  have baseWF : base.WF env universes := parameters.drop ▸ sourceWF.dropN _ parameters.bound
  have abstraction := sourceWF.mkLambda_trS envWF translated typed identifiers.length parameters.bound
  rw [parameters.drop] at abstraction
  have applied := argumentTyping.apply abstraction.1 abstraction.2
  have beta : BetaReduce ((source.mkLambda identifiers.length parameters.bound body).mkAppList replacements)
      ((body.abstractList identifiers).instantiateRevList replacements) := by
    have lambdas : LambdaBodyN replacements.length
        (source.mkLambda identifiers.length parameters.bound body) (body.abstractList identifiers) := by
      simpa only [← length] using parameters.lambdaBody sourceWF body
    apply BetaReduce.inst_reduce (fn := body.abstractList identifiers) argumentTyping.closed [] lambdas
    simp [Expr.instantiateList_reverse]
  have result := (applied.1.trExpr envWF.ordered baseWF.tr.wf).beta envWF baseWF.tr.wf beta
  have resultClosed : Closed ((body.abstractList identifiers).instantiateRevList replacements) 0 :=
    base.noBV ▸ result.closed
  obtain ⟨resultSemantic, resultTranslated, resultEquality⟩ := result
  have equality := resultEquality.of_r envWF baseWF.tr.wf applied.2
  exact Except.WF.pure ⟨rfl, rfl, ⟨_, resultTranslated, resultEquality⟩, resultClosed,
    resultClosed.looseBVarRange_zero, resultTranslated.fvarsIn, _, resultTranslated,
    equality.hasType.1, equality⟩

theorem replaceParams.prefix_typedRebased
    {env : VEnv} {universes : List Name} {base source target : MLCtx} {identifiers : List FVarId}
    {insertionLift : Lift} (envWF : env.WF) (sourceWF : source.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    {body : Expr} {semantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic (.sort level))
    {replacements : List Expr} {arguments : List VExpr}
    (argumentTyping : TypedParameterArguments env universes base
      (source.mkForall' identifiers.length parameters.bound (.sort level)) replacements arguments (.sort level))
    (length : identifiers.length = replacements.length)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0)
    (nativeEnv : Environment) (state : State) :
    (replaceParams replacements.toArray body (identifiers.map Expr.fvar).toArray nativeEnv state).WF
      fun returned => returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList replacements ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ base.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes base.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length base.vlctx.toCtx resultSemantic (.sort level) ∧
          env.IsDefEq universes.length base.vlctx.toCtx resultSemantic
            (applyParameterArguments (source.mkLambda' identifiers.length parameters.bound semantic) arguments)
            (.sort level) ∧
          TrExprS env universes target.vlctx returned.1 (resultSemantic.lift' insertionLift) ∧
          env.HasType universes.length target.vlctx.toCtx (resultSemantic.lift' insertionLift) (.sort level) ∧
          env.IsDefEq universes.length target.vlctx.toCtx (resultSemantic.lift' insertionLift)
            (VExpr.lift' (applyParameterArguments
              (source.mkLambda' identifiers.length parameters.bound semantic) arguments) insertionLift)
            (.sort level) := by
  exact (replaceParams.prefix_typed envWF sourceWF parameters translated typed argumentTyping length
    nativeEnv state).mono fun returned receipts => by
      obtain ⟨unchanged, equation, _, closed, scope, support, resultSemantic, resultTranslated,
        resultTyped, equality⟩ := receipts
      exact ⟨unchanged, equation, closed, scope, support, resultSemantic, resultTranslated,
        resultTyped, equality, resultTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf,
        resultTyped.weak' envWF.ordered insertion.toCtx, equality.weak' envWF.ordered insertion.toCtx⟩

end Lean4Lean.ElimNestedInductive
