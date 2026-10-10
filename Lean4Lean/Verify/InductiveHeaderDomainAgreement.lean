import Lean4Lean.Verify.InductiveParameterDomainTransport
import Lean4Lean.Verify.InductiveHeaderTraces

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix)

def ReducedParameterDomainReceipt (env : VEnv) (universes : List Name)
    (reader : Context) (candidate stored : Expr) (source : List VExpr)
    (storedSemantic candidateSemantic : VExpr) : Prop :=
  ∃ (checker : TypeChecker.VContext) (smaller : VLCtx) (insertion : Lift) (level : VLevel),
    checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel } ∧
    checker.venv = env ∧ checker.lparams = universes ∧ smaller.toCtx = source ∧
    VLCtx.FVLift' smaller checker.vlctx 0 insertion 0 ∧
    TrExprS env universes smaller stored storedSemantic ∧
    TrExprS env universes smaller candidate candidateSemantic ∧
    env.HasType universes.length source storedSemantic (.sort level) ∧
    ({} : TypeChecker.VState).WF checker

theorem ReducedParameterDomainReceipt.accepted
    (receipt : ReducedParameterDomainReceipt env universes reader candidate stored
      source storedSemantic candidateSemantic)
    (accepted : (monadLift (TypeChecker.isDefEq candidate stored) : M Bool) reader = .ok true) :
    ∃ level, env.IsDefEq universes.length source storedSemantic candidateSemantic (.sort level) := by
  obtain ⟨checker, smaller, insertion, level, aligned, environment, levels, sourceContext,
    weakening, storedTranslated, candidateTranslated, storedTyped, initialWF⟩ := receipt
  subst env universes source
  have storedAmbient := storedTranslated.weakFV' checker.Ewf.ordered weakening checker.Δwf
  have candidateAmbient := candidateTranslated.weakFV' checker.Ewf.ordered weakening checker.Δwf
  have storedAmbientTyped := storedTyped.weak' checker.Ewf.ordered weakening.toCtx
  have nativeAccepted : (Prod.fst <$> TypeChecker.isDefEq candidate stored
      checker.toContext ({} : TypeChecker.VState).toState) = .ok true := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.isDefEq candidate stored
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨result, final⟩ := returned
    change Except.ok result = .ok true at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, equality⟩ :=
      TypeChecker.isDefEq.WF candidateAmbient storedAmbient initialWF true final checked
    have sorted := (equality rfl).of_r checker.Ewf checker.Δwf.toCtx storedAmbientTyped
    refine ⟨level, ?_⟩
    apply (VEnv.IsDefEq.weak'_iff checker.Ewf checker.Δwf.toCtx weakening.toCtx).mp
    simpa only [VExpr.lift'] using sorted.symm

inductive CheckedHeaderDomainReceipts (env : VEnv) (universes : List Name) (nparams : Nat) :
    {stats finalStats : InductiveStats} → {type terminal : Expr} →
    {index nindices finalIndices : Nat} → {reader finalReader : Context} →
    CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader →
    List VExpr → List VExpr → List VExpr → List VExpr → Prop where
  | stop (notForall : ∀ name domain body binder, type ≠ Expr.forallE name domain body binder)
      (complete : index = nparams) :
      CheckedHeaderDomainReceipts env universes nparams
        (CheckedHeaderTrace.stop (stats := stats) (nindices := nindices) (ctx := reader) notForall complete)
        source target source target
  | reusedParameter
      (selected : index < nparams) (notFirst : ¬ stats.indConsts.isEmpty = true)
      {storedType : getType stats.params[index]! reader = .ok stored}
      (accepted : (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true)
      (normalized : (monadLift (TypeChecker.whnf (Expr.instantiate1 body stats.params[index]!)) : M Expr)
        reader = .ok normal)
      {trace : CheckedHeaderTrace nparams stats normal (index + 1) nindices reader
        terminal finalStats finalIndices finalReader}
      (domainReceipt : ReducedParameterDomainReceipt env universes reader domain stored
        source storedSemantic candidateSemantic)
      (tail : CheckedHeaderDomainReceipts env universes nparams trace
        (storedSemantic :: source) (candidateSemantic :: target) finalSource finalTarget) :
      CheckedHeaderDomainReceipts env universes nparams
        (CheckedHeaderTrace.reusedParameter (name := name) (bi := binder)
          selected notFirst storedType accepted normalized trace)
        source target finalSource finalTarget
  | index
      (notParameter : ¬ index < nparams)
      (normalized : (monadLift (TypeChecker.whnf (Expr.instantiate1 body (.fvar ⟨reader.ngen.curr⟩))) : M Expr)
        (recursorIndexContext reader name binder (peelTypeAnnotations domain)) = .ok normal)
      {trace : CheckedHeaderTrace nparams stats normal index (nindices + 1)
        (recursorIndexContext reader name binder (peelTypeAnnotations domain))
        terminal finalStats finalIndices finalReader}
      (tail : CheckedHeaderDomainReceipts env universes nparams trace
        source target finalSource finalTarget) :
      CheckedHeaderDomainReceipts env universes nparams
        (CheckedHeaderTrace.index notParameter normalized trace) source target finalSource finalTarget

variable {env : VEnv} {universes : List Name} {nparams : Nat}
  {stats finalStats : InductiveStats} {type terminal : Expr} {index nindices finalIndices : Nat}
  {reader finalReader : Context}
  {trace : CheckedHeaderTrace nparams stats type index nindices reader terminal finalStats finalIndices finalReader}
  {base source target finalSource finalTarget : List VExpr}

theorem CheckedHeaderDomainReceipts.agreement
    (receipts : CheckedHeaderDomainReceipts env universes nparams trace source target finalSource finalTarget)
    (contexts : env.IsDefEqCtx universes.length base source target) :
    env.IsDefEqCtx universes.length base finalSource finalTarget := by
  induction receipts with
  | stop => exact contexts
  | reusedParameter _ _ accepted _ domainReceipt _ induction =>
    obtain ⟨_, equality⟩ := domainReceipt.accepted accepted
    exact induction (.succ contexts equality)
  | index _ _ _ induction => exact induction contexts

theorem CheckedHeaderDomainReceipts.growth
    {trace : CheckedHeaderTrace nparams stats type index nindices reader
      terminal finalStats finalIndices finalReader}
    (receipts : CheckedHeaderDomainReceipts env universes nparams trace source target finalSource finalTarget) :
    finalSource.length = source.length + (nparams - index) ∧
      finalTarget.length = target.length + (nparams - index) := by
  induction receipts with
  | stop _ complete => simp [complete]
  | reusedParameter selected _ _ _ _ _ induction =>
    simp only [List.length_cons] at induction
    omega
  | index _ _ _ induction => exact induction

theorem checkInductiveTypes.loopInd.loop.scopedDomainAgreement
    (nparams fuel : Nat) (stats : InductiveStats) (type : Expr) (index nindices : Nat)
    (next : Expr → InductiveStats → Nat → M Result) (reader : Context) (post : Result → Prop)
    (readerWF : reader.lctx.WF) (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (contexts : env.IsDefEqCtx universes.length base source target)
    (receipts : ∀ terminal finalStats finalIndices current
      (trace : CheckedHeaderTrace nparams stats type index nindices reader
        terminal finalStats finalIndices current),
      CheckedHeaderDomainReceipts env universes nparams trace source target finalSource finalTarget)
    (continuation : ∀ terminal finalStats finalIndices current,
      reader.RecursorScopeFrame current →
      env.IsDefEqCtx universes.length base finalSource finalTarget →
      finalSource.length = source.length + (nparams - index) →
      finalTarget.length = target.length + (nparams - index) →
      (next terminal finalStats finalIndices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats type index nindices fuel next reader).WF post := by
  apply checkInductiveTypes.loopInd.loop.scopedTrace nparams fuel stats type index nindices next
    reader post readerWF reserved
  intro terminal finalStats finalIndices current trace frame
  have model := receipts terminal finalStats finalIndices current trace
  exact continuation terminal finalStats finalIndices current frame (model.agreement contexts)
    model.growth.1 model.growth.2

theorem CheckedHeaderDomainReceipts.rebindPrefix
    {env : VEnv} {universes : List Name} {base source target : MLCtx}
    {identifiers targetIdentifiers : List FVarId}
    (receipts : CheckedHeaderDomainReceipts env universes nparams trace base.vlctx.toCtx base.vlctx.toCtx
      source.vlctx.toCtx target.vlctx.toCtx)
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceParams (targetIdentifiers.map Expr.fvar).toArray body
      (identifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList (targetIdentifiers.map Expr.fvar) ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes target.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length target.vlctx.toCtx resultSemantic semanticType := by
  have contexts := receipts.agreement (base := base.vlctx.toCtx) .zero
  have length : identifiers.length = targetIdentifiers.length := by
    have sameLength := contexts.length_eq
    rw [parameters.toCtx_length, targetParameters.toCtx_length] at sameLength
    omega
  exact ElimNestedInductive.replaceParams.prefix_rename_defeq_typed envWF sourceWF targetWF
    parameters targetParameters length contexts translated typed nativeEnv state

end Lean4Lean.AddInductive
