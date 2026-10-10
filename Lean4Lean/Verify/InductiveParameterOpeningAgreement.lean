import Lean4Lean.Verify.InductiveParameterPrefixTyping

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem ParameterPrefix.forall_eq_iff
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    (length : identifiers.length = targetIdentifiers.length) (body targetBody : VExpr) :
    source.mkForall' identifiers.length parameters.bound body =
        target.mkForall' targetIdentifiers.length targetParameters.bound targetBody ↔
      source.vlctx.toCtx = target.vlctx.toCtx ∧ body = targetBody := by
  induction parameters generalizing target targetIdentifiers body targetBody with
  | nil =>
    cases targetParameters with
    | nil => simp
    | snoc => simp at length
  | @snoc previous identifiers identifier name nativeDomain domain binder parameters induction =>
    cases targetParameters with
    | nil => simp at length
    | @snoc target targetIdentifiers targetIdentifier targetName targetNativeDomain targetDomain targetBinder targetParameters =>
      have previousLength : identifiers.length = targetIdentifiers.length := by simpa using length
      simp only [List.length_append, List.length_singleton, MLCtx.mkForall',
        induction targetParameters previousLength, VExpr.forallE.injEq, MLCtx.vlctx,
        VLCtx.toCtx, List.cons.injEq, and_assoc, and_left_comm, and_comm]

def TypedParameterAgreement (env : VEnv) (universes : List Name) (numParams : Nat)
    (sourceContext targetContext : LocalContext) (sourceRemainder targetRemainder : Expr)
    (sourceParams targetParams : Array Expr) : Prop :=
    ∃ source target identifiers targetIdentifiers semantic,
      source.WF env universes ∧ target.WF env universes ∧
      ParameterPrefix .nil source identifiers ∧ ParameterPrefix .nil target targetIdentifiers ∧
      sourceContext = source.lctx ∧ targetContext = target.lctx ∧
      sourceParams = (identifiers.map Expr.fvar).toArray ∧
      targetParams = (targetIdentifiers.map Expr.fvar).toArray ∧
      identifiers.length = numParams ∧ targetIdentifiers.length = numParams ∧
      source.vlctx.toCtx = target.vlctx.toCtx ∧
      TrExprS env universes source.vlctx sourceRemainder semantic ∧
      TrExprS env universes target.vlctx targetRemainder semantic ∧
      env.IsType universes.length source.vlctx.toCtx semantic

theorem TypedParameterOpening.agreement
    (sourceOpening : TypedParameterOpening env universes originalSemantic numParams
      sourceContext sourceRemainder sourceParams)
    (targetOpening : TypedParameterOpening env universes originalSemantic numParams
      targetContext targetRemainder targetParams) :
    TypedParameterAgreement env universes numParams sourceContext targetContext
      sourceRemainder targetRemainder sourceParams targetParams := by
  obtain ⟨source, identifiers, semantic, sourceWF, parameters, sourceLength,
    sourceContextEq, sourceParamsEq, sourceTranslated, sourceTyped, sourceBound, sourceReconstruction⟩ := sourceOpening
  obtain ⟨target, targetIdentifiers, targetSemantic, targetWF, targetParameters, targetLength,
    targetContextEq, targetParamsEq, targetTranslated, _, targetBound, targetReconstruction⟩ := targetOpening
  have reconstructed : source.mkForall' identifiers.length parameters.bound semantic =
      target.mkForall' targetIdentifiers.length targetParameters.bound targetSemantic :=
    sourceReconstruction.trans targetReconstruction.symm
  obtain ⟨domains, sameSemantic⟩ :=
    (parameters.forall_eq_iff targetParameters (sourceLength.trans targetLength.symm)
      semantic targetSemantic).mp reconstructed
  subst targetSemantic
  exact ⟨source, target, identifiers, targetIdentifiers, semantic, sourceWF, targetWF, parameters,
    targetParameters, sourceContextEq, targetContextEq, sourceParamsEq, targetParamsEq,
    sourceLength, targetLength, domains, sourceTranslated, targetTranslated, sourceTyped⟩

theorem withParams.getTypedAgreement
    (envWF : env.WF) (sourceType targetType : Expr) (originalSemantic : VExpr)
    (sourceTranslated : TrExprS env universes [] sourceType originalSemantic)
    (targetTranslated : TrExprS env universes [] targetType originalSemantic)
    (typed : env.IsType universes.length [] originalSemantic) (numParams : Nat)
    (nativeEnv : Kernel.Environment) (state : State) :
    ((do
      let source ← withParams sourceType numParams (fun lctx remainder params => pure (lctx, remainder, params))
      let target ← withParams targetType numParams (fun lctx remainder params => pure (lctx, remainder, params))
      return (source, target) : M ((LocalContext × Expr × Array Expr) × (LocalContext × Expr × Array Expr)))
        nativeEnv state).WF fun returned =>
      TypedParameterOpening env universes originalSemantic numParams
        returned.1.1.1 returned.1.1.2.1 returned.1.1.2.2 ∧
      TypedParameterOpening env universes originalSemantic numParams
        returned.1.2.1 returned.1.2.2.1 returned.1.2.2.2 ∧
      TypedParameterAgreement env universes numParams returned.1.1.1 returned.1.2.1
        returned.1.1.2.1 returned.1.2.2.1 returned.1.1.2.2 returned.1.2.2.2 := by
  refine (withParams.getTypedContext envWF sourceType originalSemantic sourceTranslated typed
    numParams nativeEnv state).bind ?_
  rintro ⟨source, current⟩ sourceOpening
  refine (withParams.getTypedContext envWF targetType originalSemantic targetTranslated typed
    numParams nativeEnv current).bind ?_
  rintro ⟨target, final⟩ targetOpening
  exact .pure ⟨sourceOpening, targetOpening, sourceOpening.agreement targetOpening⟩

theorem TypedParameterAgreement.rebindRemainder
    (envWF : env.WF)
    (agreement : TypedParameterAgreement env universes numParams sourceContext targetContext
      sourceRemainder targetRemainder sourceParams targetParams)
    (nativeEnv : Kernel.Environment) (state : State) :
    (replaceParams targetParams sourceRemainder sourceParams nativeEnv state).WF fun returned =>
      returned.2 = state ∧ Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
      ∃ (target : MLCtx) (semantic : VExpr) (level : VLevel),
        target.WF env universes ∧ targetContext = target.lctx ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        TrExprS env universes target.vlctx returned.1 semantic ∧
        env.HasType universes.length target.vlctx.toCtx semantic (.sort level) := by
  obtain ⟨source, target, identifiers, targetIdentifiers, _, sourceWF, targetWF, parameters,
    targetParameters, _, targetContextEq, sourceParamsEq, targetParamsEq,
    sourceLength, targetLength, domains, sourceTranslated, _, level, sourceTyped⟩ := agreement
  rw [sourceParamsEq, targetParamsEq]
  exact (replaceParams.prefix_rename_typed envWF sourceWF targetWF parameters targetParameters
    (sourceLength.trans targetLength.symm) domains sourceTranslated sourceTyped nativeEnv state).mono
      fun _ ⟨unchanged, _, closed, range, support, semantic, translated, typed⟩ =>
        ⟨unchanged, closed, range, target, semantic, level, targetWF, targetContextEq,
          support, translated, typed⟩

theorem withParams.rebindTypedRemainder
    (envWF : env.WF) (sourceType targetType : Expr) (originalSemantic : VExpr)
    (sourceTranslated : TrExprS env universes [] sourceType originalSemantic)
    (targetTranslated : TrExprS env universes [] targetType originalSemantic)
    (typed : env.IsType universes.length [] originalSemantic) (numParams : Nat)
    (nativeEnv : Kernel.Environment) (state : State) :
    ((do
      let source ← withParams sourceType numParams (fun lctx remainder params => pure (lctx, remainder, params))
      let target ← withParams targetType numParams (fun lctx remainder params => pure (lctx, remainder, params))
      let rebound ← replaceParams target.2.2 source.2.1 source.2.2
      return (target.1, rebound) : M (LocalContext × Expr)) nativeEnv state).WF fun returned =>
      Closed returned.1.2 0 ∧ returned.1.2.looseBVarRange' = 0 ∧
      ∃ (target : MLCtx) (semantic : VExpr) (level : VLevel),
        target.WF env universes ∧ returned.1.1 = target.lctx ∧
        returned.1.2.FVarsIn (· ∈ target.vlctx.fvars) ∧
        TrExprS env universes target.vlctx returned.1.2 semantic ∧
        env.HasType universes.length target.vlctx.toCtx semantic (.sort level) := by
  refine (withParams.getTypedContext envWF sourceType originalSemantic sourceTranslated typed
    numParams nativeEnv state).bind ?_
  rintro ⟨source, current⟩ sourceOpening
  refine (withParams.getTypedContext envWF targetType originalSemantic targetTranslated typed
    numParams nativeEnv current).bind ?_
  rintro ⟨target, middle⟩ targetOpening
  refine ((sourceOpening.agreement targetOpening).rebindRemainder envWF nativeEnv middle).bind ?_
  rintro ⟨rebound, final⟩ ⟨_, closed, range, model, semantic, level, modelWF,
    targetContextEq, support, translated, typed⟩
  exact Except.WF.pure ⟨closed, range, model, semantic, level, modelWF,
    targetContextEq, support, translated, typed⟩

end Lean4Lean.ElimNestedInductive
