import Lean4Lean.Verify.InductiveParameterPrefixReplacement
import Lean4Lean.Verify.InductiveNestedGuard

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel
open TypeChecker (MLCtx)

theorem TypedParameterArguments.append
    (first : TypedParameterArguments env universes context functionType replacements arguments intermediate)
    (second : TypedParameterArguments env universes context intermediate moreReplacements moreArguments result) :
    TypedParameterArguments env universes context functionType
      (replacements ++ moreReplacements) (arguments ++ moreArguments) result := by
  induction first with
  | nil => exact second
  | cons translated typed _ induction => exact .cons translated typed (induction second)

theorem TypedParameterArguments.weakFV
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' context.vlctx target.vlctx 0 insertionLift 0)
    (parameters : TypedParameterArguments env universes context functionType replacements arguments result) :
    TypedParameterArguments env universes target (functionType.lift' insertionLift) replacements
      (arguments.map (VExpr.lift' · insertionLift)) (result.lift' insertionLift) := by
  induction parameters with
  | nil => exact .nil
  | cons translated typed _ induction =>
    simp only [VExpr.lift', List.map_cons]
    refine .cons (translated.weakFV' envWF.ordered insertion targetWF.tr.wf)
      (typed.weak' envWF.ordered insertion.toCtx) ?_
    simpa only [VExpr.lift'_inst_hi] using induction

theorem ParameterPrefix.insertion (parameters : ParameterPrefix base source identifiers) :
    VLCtx.FVLift' base.vlctx source.vlctx 0 (.skipN .refl identifiers.length) 0 := by
  induction parameters with
  | nil => exact .refl
  | snoc _ induction => simpa using VLCtx.FVLift'.skip_fvar _ _ induction

theorem ParameterPrefix.arguments (parameters : ParameterPrefix base source identifiers)
    (envWF : env.WF) (sourceWF : source.WF env universes) (resultType : VExpr) :
    ∃ arguments, TypedParameterArguments env universes source
      ((source.mkForall' identifiers.length parameters.bound resultType).liftN identifiers.length)
      (identifiers.map Expr.fvar) arguments resultType := by
  induction parameters generalizing resultType with
  | nil => exact ⟨[], by simpa using TypedParameterArguments.nil⟩
  | @snoc previous identifiers identifier name nativeDomain domain binder parameters induction =>
    obtain ⟨arguments, previousArguments⟩ := induction sourceWF.1 (.forallE domain resultType)
    have inserted := previousArguments.weakFV envWF sourceWF
      (VLCtx.FVLift'.skip_fvar _ _ .refl)
    have last : TypedParameterArguments env universes
        (.vlam identifier name nativeDomain domain binder previous)
        ((VExpr.forallE domain resultType).lift' (.skip .refl))
        [.fvar identifier] [.bvar 0] resultType := by
      simp only [VExpr.lift']
      have liftedBody : resultType.lift' (.cons (.skip .refl)) = resultType.liftN 1 1 :=
        VExpr.lift'_consN_skipN (e := resultType) (n := 1) (k := 1)
      rw [← VExpr.lift_eq_lift', liftedBody]
      refine .cons (.fvar (A := domain.lift)
        (by simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]))
        (.bvar .zero) ?_
      simpa only [VExpr.instN_bvar0] using
        (TypedParameterArguments.nil (env := env) (universes := universes)
          (base := MLCtx.vlam identifier name nativeDomain domain binder previous)
          (result := resultType))
    refine ⟨arguments.map (VExpr.lift' · (.skip .refl)) ++ [.bvar 0], ?_⟩
    have combined := inserted.append last
    simpa only [List.map_append, List.map_singleton, List.length_append, List.length_singleton,
      MLCtx.mkForall', VLocalDecl.depth, Lift.skipN, ← VExpr.lift_eq_lift',
      ← VExpr.liftN_succ] using combined

theorem ParameterPrefix.forall_eq (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (domains : source.vlctx.toCtx = target.vlctx.toCtx) (body : VExpr) :
    source.mkForall' identifiers.length parameters.bound body =
      target.mkForall' targetIdentifiers.length targetParameters.bound body := by
  induction parameters generalizing target targetIdentifiers body with
  | nil =>
    cases targetParameters with
    | nil => rfl
    | snoc => simp at length
  | @snoc previous identifiers identifier name nativeDomain domain binder parameters induction =>
    cases targetParameters with
    | nil => simp at length
    | @snoc target targetIdentifiers targetIdentifier targetName targetNativeDomain targetDomain targetBinder targetParameters =>
      have same : domain = targetDomain ∧ previous.vlctx.toCtx = target.vlctx.toCtx := by
        simpa [VLCtx.toCtx] using domains
      obtain ⟨rfl, same⟩ := same
      simpa only [List.length_append, List.length_singleton, MLCtx.mkForall'] using
        induction targetParameters (by simpa using length) same (.forallE domain body)

theorem replaceParams.prefix_typedInto
    {env : VEnv} {universes : List Name} {base source target : MLCtx} {identifiers : List FVarId}
    {insertionLift : Lift} (envWF : env.WF) (sourceWF : source.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : TypedParameterArguments env universes target
      ((source.mkForall' identifiers.length parameters.bound semanticType).lift' insertionLift)
      replacements arguments resultType)
    (length : identifiers.length = replacements.length)
    (nativeEnv : Environment) (state : State) :
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
  have applied := argumentTyping.apply
    (abstraction.1.weakFV' envWF.ordered insertion targetWF.tr.wf)
    (abstraction.2.weak' envWF.ordered insertion.toCtx)
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

theorem replaceParams.prefix_rename_typed
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId}
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (domains : source.vlctx.toCtx = target.vlctx.toCtx)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Environment) (state : State) :
    (replaceParams (targetIdentifiers.map Expr.fvar).toArray body
      (identifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList (targetIdentifiers.map Expr.fvar) ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes target.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length target.vlctx.toCtx resultSemantic semanticType := by
  obtain ⟨arguments, argumentTyping⟩ := targetParameters.arguments envWF targetWF semanticType
  have functionType := parameters.forall_eq targetParameters length domains semanticType
  rw [← functionType, ← length] at argumentTyping
  have typedArguments : TypedParameterArguments env universes target
      ((source.mkForall' identifiers.length parameters.bound semanticType).lift'
        (.skipN .refl targetIdentifiers.length)) (targetIdentifiers.map Expr.fvar) arguments semanticType := by
    have lifted (expression : VExpr) : expression.lift' (.skipN .refl targetIdentifiers.length) =
        expression.liftN targetIdentifiers.length :=
      VExpr.lift'_consN_skipN (e := expression) (n := targetIdentifiers.length) (k := 0)
    rw [lifted]
    simpa only [length] using argumentTyping
  exact (replaceParams.prefix_typedInto envWF sourceWF parameters translated typed targetWF
    targetParameters.insertion typedArguments (by simpa using length) nativeEnv state).mono
    fun _ ⟨unchanged, equation, closed, scope, support, resultSemantic, translation, typing, _⟩ =>
      ⟨unchanged, equation, closed, scope, support, resultSemantic, translation, typing⟩

def TypedParameterOpening (env : VEnv) (universes : List Name) (originalSemantic : VExpr) (numParams : Nat)
    (lctx : LocalContext) (remainder : Expr) (params : Array Expr) : Prop :=
  ∃ source identifiers semantic, source.WF env universes ∧
    ParameterPrefix .nil source identifiers ∧ identifiers.length = numParams ∧
    lctx = source.lctx ∧ params = (identifiers.map Expr.fvar).toArray ∧
    TrExprS env universes source.vlctx remainder semantic ∧
    env.IsType universes.length source.vlctx.toCtx semantic ∧
    ∃ bound : identifiers.length ≤ source.length,
      source.mkForall' identifiers.length bound semantic = originalSemantic

private theorem withParams.loop.typedContext
    {originalSemantic : VExpr}
    (envWF : env.WF) (remaining : Nat) (source : MLCtx) (identifiers : List FVarId)
    (parameters : ParameterPrefix .nil source identifiers) (sourceWF : source.WF env universes)
    (nativeType : Expr) (semantic : VExpr)
    (translated : TrExprS env universes source.vlctx nativeType semantic)
    (typed : env.IsType universes.length source.vlctx.toCtx semantic)
    (reconstruction : source.mkForall' identifiers.length parameters.bound semantic = originalSemantic)
    (next : LocalContext → Expr → Array Expr → M α) (nativeEnv : Environment) (state : State)
    (reserved : ContextReserved source.lctx state.ngen) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state',
      TypedParameterOpening env universes originalSemantic (identifiers.length + remaining) lctx remainder params →
      (next lctx remainder params nativeEnv state').WF post) :
    (withParams.loop next source.lctx nativeType (identifiers.map Expr.fvar).toArray remaining
      nativeEnv state).WF post := by
  induction remaining generalizing source identifiers nativeType semantic state with
  | zero =>
    exact hnext source.lctx nativeType _ state
      ⟨source, identifiers, semantic, sourceWF, parameters, by simp, rfl, rfl,
        translated, typed, parameters.bound, reconstruction⟩
  | succ remaining induction =>
    cases nativeType with
    | forallE name domain body binder =>
      let .forallE (ty' := modelDomain) domainTyped bodyTyped domainTranslated bodyTranslated := translated
      let opened := MLCtx.vlam ⟨state.ngen.curr⟩ name domain modelDomain binder source
      have openedWF : opened.WF env universes :=
        ⟨sourceWF, reserved.fresh sourceWF.tr.1, domainTranslated, domainTyped⟩
      change (withParams.loop next opened.lctx (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        ((identifiers.map Expr.fvar).toArray.push (.fvar ⟨state.ngen.curr⟩)) remaining nativeEnv
        { state with ngen := state.ngen.next }).WF post
      have array : ((identifiers ++ [(⟨state.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray =
          (identifiers.map Expr.fvar).toArray.push (.fvar ⟨state.ngen.curr⟩) := by simp
      rw [← array]
      simp only [Expr.instantiate1_eq]
      refine induction opened (identifiers ++ [(⟨state.ngen.curr⟩ : FVarId)]) (.snoc parameters) openedWF _ _
        (bodyTranslated.inst_fvar envWF.ordered openedWF.tr.wf) bodyTyped
        (by simpa only [List.length_append, List.length_singleton, MLCtx.mkForall'] using reconstruction)
        { state with ngen := state.ngen.next } ?_ ?_
      · exact reserved.push_current name domain binder
      intro lctx remainder params state' receipts
      apply hnext lctx remainder params state'
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm 1] using receipts
    | _ => exact Except.WF.throw

theorem withParams.typedContext
    (envWF : env.WF) (nativeType : Expr) (semantic : VExpr)
    (translated : TrExprS env universes [] nativeType semantic)
    (typed : env.IsType universes.length [] semantic) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (nativeEnv : Environment) (state : State)
    (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state',
      TypedParameterOpening env universes semantic numParams lctx remainder params →
      (next lctx remainder params nativeEnv state').WF post) :
    (withParams nativeType numParams next nativeEnv state).WF post := by
  exact withParams.loop.typedContext envWF numParams .nil [] .nil trivial nativeType semantic translated typed rfl
    next nativeEnv state (ContextReserved.empty state.ngen) post
    (fun lctx remainder params state' receipts => hnext lctx remainder params state' (by simpa using receipts))

theorem withParams.getTypedContext
    (envWF : env.WF) (nativeType : Expr) (semantic : VExpr)
    (translated : TrExprS env universes [] nativeType semantic)
    (typed : env.IsType universes.length [] semantic) (numParams : Nat)
    (nativeEnv : Environment) (state : State) :
    (withParams nativeType numParams (fun lctx remainder params => pure (lctx, remainder, params))
      nativeEnv state).WF fun returned =>
        TypedParameterOpening env universes semantic numParams returned.1.1 returned.1.2.1 returned.1.2.2 := by
  exact withParams.typedContext envWF nativeType semantic translated typed numParams _ nativeEnv state _
    fun _ _ _ _ receipts => Except.WF.pure receipts

private theorem appList_headTyping
    (translated : TrExprS env universes context (function.mkAppList suffix) semantic)
    (typed : env.HasType universes.length context.toCtx semantic semanticType) :
    ∃ functionSemantic functionType, TrExprS env universes context function functionSemantic ∧
      env.HasType universes.length context.toCtx functionSemantic functionType := by
  induction suffix generalizing function semantic semanticType with
  | nil => exact ⟨semantic, semanticType, translated, typed⟩
  | cons argument suffix induction =>
    obtain ⟨_, _, applicationTranslated, _⟩ := induction translated typed
    let .app functionTyped _ functionTranslated _ := applicationTranslated
    exact ⟨_, _, functionTranslated, functionTyped⟩

theorem nestedApp_prefixTyping
    {env : VEnv} {universes : List Name} {context : VLCtx}
    {expression : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes context expression semantic)
    (typed : env.HasType universes.length context.toCtx semantic semanticType)
    (numParams : Nat) (bound : numParams ≤ expression.getAppArgs.size) :
    ∃ prefixSemantic prefixType,
      TrExprS env universes context
        (mkAppRange expression.getAppFn 0 numParams expression.getAppArgs) prefixSemantic ∧
      env.HasType universes.length context.toCtx prefixSemantic prefixType := by
  have length : (expression.getAppArgs.toList.take numParams).length = numParams := by
    simp [List.length_take, Nat.min_eq_left bound]
  rw [Expr.mkAppRange_eq (e := expression.getAppFn) (args := expression.getAppArgs)
    (i := 0) (j := numParams) (l₁ := []) (l₂ := expression.getAppArgs.toList.take numParams)
    (l₃ := expression.getAppArgs.toList.drop numParams) (by simp) rfl (by simpa using length)]
  have reconstructed : (expression.getAppFn.mkAppList (expression.getAppArgs.toList.take numParams)).mkAppList
      (expression.getAppArgs.toList.drop numParams) = expression := by
    rw [← Expr.mkAppList_append, List.take_append_drop, Expr.getAppArgs_eq, List.toList_toArray]
    exact Expr.mkAppList_getAppArgsList expression
  have fullTranslated : TrExprS env universes context
      ((expression.getAppFn.mkAppList (expression.getAppArgs.toList.take numParams)).mkAppList
        (expression.getAppArgs.toList.drop numParams)) semantic := by
    rw [reconstructed]
    exact translated
  exact appList_headTyping fullTranslated typed

theorem isNestedInductiveApp?.typedPrefix
    {env : VEnv} {universes : List Name} {context : VLCtx}
    {expression : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes context expression semantic)
    (typed : env.HasType universes.length context.toCtx semantic semanticType)
    (nativeEnv : Environment) (state : State) :
    (isNestedInductiveApp? expression nativeEnv state).WF fun returned =>
      returned.2 = state ∧ ∀ info, returned.1 = some info →
        NestedAppScope expression info ∧
        ∃ prefixSemantic prefixType,
          TrExprS env universes context
            (mkAppRange expression.getAppFn 0 info.numParams expression.getAppArgs) prefixSemantic ∧
          env.HasType universes.length context.toCtx prefixSemantic prefixType :=
  (isNestedInductiveApp?.scope expression nativeEnv state).mono fun _ receipts =>
    ⟨receipts.1, fun info selected => ⟨receipts.2 info selected,
      nestedApp_prefixTyping translated typed info.numParams (receipts.2 info selected).2.1⟩⟩

theorem isNestedInductiveApp?.typedRebinding
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId} {expression : Expr} {semantic semanticType : VExpr}
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length)
    (domains : source.vlctx.toCtx = target.vlctx.toCtx)
    (translated : TrExprS env universes source.vlctx expression semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Environment) (state : State) :
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
    refine (replaceParams.prefix_rename_typed envWF sourceWF targetWF parameters targetParameters
      length domains prefixTranslated prefixTyped nativeEnv state).bind ?_
    rintro ⟨rebound, current⟩ ⟨unchanged, equation, closed, scope, support, resultSemantic, translated, typed⟩
    change current = state at unchanged
    subst current
    exact Except.WF.pure ⟨rfl, fun result equality => by
      cases equality
      exact ⟨closed, scope, support, info, prefixSemantic, resultSemantic, prefixType,
        scopeReceipt, equation, prefixTranslated, prefixTyped, translated, typed⟩⟩

end Lean4Lean.ElimNestedInductive
