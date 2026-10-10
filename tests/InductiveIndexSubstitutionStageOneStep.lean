import Lean4Lean.Verify.InductiveIndexSubstitutionStageRebase
import Lean.Util.CollectAxioms

namespace InductiveIndexSubstitutionStageOneStepTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

private def generated (reader : Context) : FVarId := ⟨reader.ngen.curr⟩

private def nextReader (reader : Context) : Context :=
  recursorIndexContext reader `oneIndex .default (.sort .zero)

private def nextVirtual (virtual : VLCtx) (reader : Context) : VLCtx :=
  peeledIndexVirtualContext virtual (generated reader) (.sort .zero) (.sort .zero)

private def normalizationReceipt (reader : Context) : Prop :=
  ((monadLift (TypeChecker.whnf ((Expr.sort .zero).instantiate1 (.fvar (generated reader)))) : M Expr)
    (nextReader reader)) = .ok (.sort .zero)

private def oneStep (reader : Context) : BinderStep :=
  { role := .index, name := `oneIndex, domain := .sort .zero,
    bi := .default, value := .fvar (generated reader) }

private def nativeStageBody (reader : Context) (identifier : FVarId) : Expr :=
  .forallE `formalUse (.bvar 0)
    (.forallE `indexUse (.fvar (generated reader)) (.fvar identifier) .default) .default

private def stageSemantic (argument : VExpr) : VExpr :=
  .forallE (.bvar 0) (.forallE (.bvar 2) argument.lift.lift.lift.lift)

private def stageLevel : VLevel := .imax .zero (.imax .zero .zero)

private theorem nativeSortNormalizationWithPositiveDepth
    (reader : Context) (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    normalizationReceipt reader := by
  unfold normalizationReceipt
  rw [Expr.instantiate1_eq]
  change (Prod.fst <$> (TypeChecker.Methods.withFuel reader.fuel.recDepth).whnf (.sort .zero)
    { env := reader.env, safety := reader.safety, lctx := (nextReader reader).lctx,
      lparams := reader.lparams, fuel := reader.fuel } {}) = .ok (.sort .zero)
  rw [positive]
  rfl

private theorem constructActualIndexOpening
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    PeeledIndexOpening env universes reader virtual `oneIndex (.sort .zero) (.sort .zero)
      .default (.sort .zero) (.sort .zero) (.succ .zero) (.sort .zero) := by
  have domainTranslated : TrExprS env universes virtual (.sort .zero) (.sort .zero) :=
    .sort (by simp [VLevel.ofLevel])
  have domainTyped : env.HasType universes.length virtual.toCtx (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF (by trivial) (by trivial) rfl
  have pushed := translatedIndexContextPush (name := `oneIndex) (bi := .default) (domain := .sort .zero)
    correspondence reserved domainTranslated domainTyped
  have opened : TrExpr env universes (nextVirtual virtual reader)
      ((Expr.sort .zero).instantiate1 (.fvar (generated reader))) (.sort .zero) := by
    rw [Expr.instantiate1_eq]
    exact ⟨.sort .zero, .sort (by simp [VLevel.ofLevel]),
      (show env.HasType universes.length (nextVirtual virtual reader).toCtx
        (.sort .zero) (.sort (.succ .zero)) from .sortDF (by trivial) (by trivial) rfl).toU⟩
  exact ⟨domainTranslated, domainTyped, pushed, opened,
    newlyAllocatedBinderPositioned reader `oneIndex (.sort .zero) .default correspondence.1 reserved,
    Context.RecursorScopeFrame.push reader correspondence.1 reserved `oneIndex .default (.sort .zero)⟩

private theorem constructGenuineOneStepHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {reader : Context} {virtual : VLCtx}
    (parametersEmpty : stats.params.size = 0)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (normalized : normalizationReceipt reader) :
    ∃ trace : RecursorIndexTrace stats (.forallE `oneIndex (.sort .zero) (.sort .zero) .default)
      0 #[] reader (.sort .zero) 0 (#[].push (.fvar (generated reader))) (nextReader reader),
      TranslatedRecursorIndexTrace env universes trace virtual
        (.forallE (.sort .zero) (.sort .zero)) (nextVirtual virtual reader) (.sort .zero) := by
  have opening := constructActualIndexOpening correspondence reserved
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  have notParameter : ¬0 < stats.params.size := by simp [parametersEmpty]
  have nextCorrespondence : TrLCtx env universes (nextReader reader).lctx (nextVirtual virtual reader) :=
    opening.2.2.1
  have tail := RecursorIndexTrace.stop (stats := stats) (index := 0)
    (indices := #[].push (.fvar (generated reader))) (ctx := nextReader reader) notForall
  have translatedTail := TranslatedRecursorIndexTrace.stop (stats := stats) (index := 0)
    (indices := #[].push (.fvar (generated reader))) notForall nextCorrespondence
    (TrExprS.sort (u' := .zero) (by simp [VLevel.ofLevel]))
  have translated : TrExprS env universes virtual
      (.forallE `oneIndex (.sort .zero) (.sort .zero) .default)
      (.forallE (.sort .zero) (.sort .zero)) :=
    .forallE ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      (.sort (by simp [VLevel.ofLevel])) (.sort (by simp [VLevel.ofLevel]))
  refine ⟨.index notParameter normalized tail, ?_⟩
  exact .index (name := `oneIndex) (domain := .sort .zero) (body := .sort .zero)
    (bi := .default) (reader := reader) (index := 0) (indices := #[])
    notParameter normalized tail translated opening
    (.sort (by simp [VLevel.ofLevel]))
    (show env.HasType universes.length (nextVirtual virtual reader).toCtx
      (.sort .zero) (.sort (.succ .zero)) from .sortDF (by trivial) (by trivial) rfl).toU
    translatedTail

private theorem oneActualStoredDomainIsSupported
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (identifier : FVarId) :
    BinderStoredIndexTypeFVarsIn [identifier] (nextReader reader) [oneStep reader] := by
  have opening := constructActualIndexOpening correspondence reserved
  have positioned := opening.2.2.2.2.1
  have declared : BinderStepsIndexDeclared (nextReader reader) [oneStep reader] := by
    intro step member role
    have selected : step = oneStep reader := List.mem_singleton.mp member
    subst step
    exact positioned.declared
  have raw : BinderRawDomainFVarsIn [identifier] [oneStep reader] := by
    intro position step selected
    cases position with
    | zero =>
      have equality : oneStep reader = step := Option.some.inj selected
      subst step
      trivial
    | succ position => simp at selected
  exact raw.storedIndexTypeFVarsIn declared

private theorem actualNewIndexIsFreshInTheBase
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    generated reader ∉ virtual.fvars := by
  have opening := constructActualIndexOpening correspondence reserved
  exact (opening.2.2.1.wf.2.1 (generated reader) [] rfl).1

private theorem selectedLookupSurvivesTheActualIndexPush
    {reader : Context} {virtual : VLCtx} {identifier : FVarId} {argument : VExpr}
    (different : generated reader ≠ identifier)
    (lookup : virtual.find? (.inr identifier) = some (argument, .sort .zero)) :
    (nextVirtual virtual reader).find? (.inr identifier) = some (argument.lift, .sort .zero) := by
  simp [nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next, different, lookup,
    VLocalDecl.depth, VExpr.liftN, VExpr.lift]

private theorem translatedStageUsesTheFormalNewIndexAndSelectedParameter
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (envWF : env.WF) (virtualWF : virtual.WF env universes.length)
    (identifier : FVarId) (different : generated reader ≠ identifier) {argument : VExpr}
    (lookup : virtual.find? (.inr identifier) = some (argument, .sort .zero)) :
    TrExprS env universes ((none, .vlam (.sort .zero)) :: nextVirtual virtual reader)
      (nativeStageBody reader identifier) (stageSemantic argument) ∧
    env.HasType universes.length ((.sort .zero) :: (nextVirtual virtual reader).toCtx)
      (stageSemantic argument) (.sort stageLevel) := by
  have argumentTyped := virtualWF.find?_wf envWF.ordered lookup
  have raisedTyped : env.HasType universes.length
      (.bvar 2 :: .bvar 0 :: .sort .zero :: .sort .zero :: virtual.toCtx)
      argument.lift.lift.lift.lift (.sort .zero) :=
    (((argumentTyped.weak envWF.ordered).weak envWF.ordered).weak envWF.ordered).weak envWF.ordered
  have finalLookup :
      VLCtx.find? ((none, .vlam (.bvar 2)) :: (none, .vlam (.bvar 0)) ::
        (none, .vlam (.sort .zero)) :: nextVirtual virtual reader) (.inr identifier) =
      some (argument.lift.lift.lift.lift, .sort .zero) := by
    simp [nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next, different, lookup,
      VLocalDecl.depth, VExpr.liftN, VExpr.lift]
  have typed : env.HasType universes.length ((.sort .zero) :: (nextVirtual virtual reader).toCtx)
      (stageSemantic argument) (.sort stageLevel) :=
    .forallEDF (.bvar .zero) (.forallEDF (.bvar (.succ (.succ .zero))) raisedTyped)
  refine ⟨?_, typed⟩
  exact .forallE ⟨.zero, .bvar .zero⟩
    ⟨.imax .zero .zero, .forallEDF (.bvar (.succ (.succ .zero))) raisedTyped⟩
    (.bvar rfl) (.forallE ⟨.zero, .bvar (.succ (.succ .zero))⟩
      ⟨.zero, raisedTyped⟩
      (.fvar (A := .sort .zero) (by simp [nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, VExpr.liftN, VExpr.lift]))
      (.fvar finalLookup))

private theorem actualStageBodyClosedAndSupported
    (reader : Context) (identifier : FVarId) (base : List FVarId) (member : identifier ∈ base) :
    Closed (nativeStageBody reader identifier) 1 ∧
    ¬Closed (nativeStageBody reader identifier) 0 ∧
    (nativeStageBody reader identifier).FVarsIn (· ∈ generated reader :: base) := by
  simp [nativeStageBody, Closed, FVarsIn, member]

private theorem exactlyOneIdentifierComesFromTheActualArrayPush
    {reader : Context} {ids : List FVarId}
    (array : (#[].push (.fvar (generated reader))).toList = (#[] : Array Expr).toList ++ ids.map Expr.fvar) :
    ids = [generated reader] := by
  have mapped : ids.map Expr.fvar = [.fvar (generated reader)] := by simpa using array.symm
  cases ids with
  | nil => cases mapped
  | cons identifier remaining =>
    have equalities := List.cons.inj mapped
    have first := Expr.fvar.inj equalities.1
    have tail : remaining = [] := List.map_eq_nil_iff.mp equalities.2
    simp [first, tail]

private theorem actualPushReceiptFixesIndependentNonzeroLiftCutoffs
    {reader : Context} {ids : List FVarId}
    (array : (#[].push (.fvar (generated reader))).toList = (#[] : Array Expr).toList ++ ids.map Expr.fvar) :
    (VExpr.bvar 0).lift' (.consN (.skip .refl) ids.length) = .bvar 0 ∧
    (VExpr.bvar 1).lift' (.consN (.skip .refl) ids.length) = .bvar 2 ∧
    (VExpr.bvar 0).lift' (.consN (.skip (.skip .refl)) ids.length) = .bvar 0 ∧
    (VExpr.bvar 1).lift' (.consN (.skip (.skip .refl)) ids.length) = .bvar 3 ∧
    (VExpr.bvar 0).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons = .bvar 0 ∧
    (VExpr.bvar 1).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons = .bvar 1 ∧
    (VExpr.bvar 2).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons = .bvar 4 ∧
    (VExpr.bvar 1).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons ≠
      (VExpr.bvar 1).lift' (.consN (.skip (.skip .refl)) ids.length) ∧
    (VExpr.bvar 0).lift' (.consN (.skip (.skip .refl)) ids.length) ≠
      (VExpr.bvar 0).lift' (.skip (.skip .refl)) := by
  have idsSingleton := exactlyOneIdentifierComesFromTheActualArrayPush array
  subst ids
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem missingNewIndexOrSelectedParameterCannotSupplyStageSupport
    (reader : Context) (identifier : FVarId) (different : generated reader ≠ identifier) :
    ¬(nativeStageBody reader identifier).FVarsIn (· ∈ [identifier]) ∧
    ¬(nativeStageBody reader identifier).FVarsIn (· ∈ [generated reader]) := by
  simp [nativeStageBody, FVarsIn, different, Ne.symm different]

private theorem genuineOneStepHistoryInvokesTheStageAdapter
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    (parametersEmpty : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (reader : Context)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (envWF : env.WF) (depth : Nat) (positive : reader.fuel.recDepth = depth + 1)
    (identifier : FVarId) (member : identifier ∈ model.vlctx.fvars) {argument : VExpr}
    (lookup : model.vlctx.find? (.inr identifier) = some (argument, .sort .zero)) :
    ∃ (chronological reduced target : MLCtx) (reducedArgument reducedDomain reducedBody : VExpr),
      chronological.lctx = (nextReader reader).lctx ∧
      chronological.vlctx = nextVirtual model.vlctx reader ∧
      SelectedRecursorTelescope env universes (nextReader reader).lctx model [generated reader] reduced ∧
      SelectedRecursorTelescope env universes (nextReader reader).lctx model [generated reader] target ∧
      reduced.vlctx.fvars = generated reader :: model.vlctx.fvars ∧
      target.vlctx.fvars = generated reader :: model.vlctx.fvars ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx)
        (nativeStageBody reader identifier) reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx) reducedBody (.sort stageLevel) ∧
      TrExprS env universes reduced.vlctx
        ((nativeStageBody reader identifier).instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      TrExprS env universes target.vlctx
        ((nativeStageBody reader identifier).instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length target.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort stageLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        ((stageSemantic argument).inst argument.lift) (reducedBody.inst reducedArgument) (.sort stageLevel) ∧
      Closed ((nativeStageBody reader identifier).instantiate1 (.fvar identifier)) 0 ∧
      ((nativeStageBody reader identifier).instantiate1 (.fvar identifier)).FVarsIn
        (· ∈ reduced.vlctx.fvars) := by
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by simpa only [native] using modelWF.tr
  have normalized := nativeSortNormalizationWithPositiveDepth reader depth positive
  obtain ⟨trace, history⟩ := constructGenuineOneStepHistory parametersEmpty correspondence reserved normalized
  have opening := constructActualIndexOpening correspondence reserved
  have frame := opening.2.2.2.2.2
  have nextCorrespondence : TrLCtx env universes (nextReader reader).lctx (nextVirtual model.vlctx reader) :=
    opening.2.2.1
  have fresh := actualNewIndexIsFreshInTheBase correspondence reserved
  have different : generated reader ≠ identifier := by
    intro equality
    exact fresh (equality.symm ▸ member)
  have originalLookup := selectedLookupSurvivesTheActualIndexPush different lookup
  have stageReceipts := translatedStageUsesTheFormalNewIndexAndSelectedParameter envWF modelWF.tr.wf
    identifier different lookup
  have closedSupport := actualStageBodyClosedAndSupported reader identifier model.vlctx.fvars member
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, reducedDomain, _, reducedBody,
    _, chronologicalNative, chronologicalConverted, _, array, reducedTelescope, _, _, _, targetTelescope,
    _, _, _, _, _, _, _, _, _, _, _, _, reducedBodyTranslation, reducedBodyTyping, _, _, _, endpointEquality,
    _, _, _, targetTyping, substitutedClosed, substitutedSupport, _, sourceTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains model modelWF native rfl reserved
      (nextReader reader) (.refl _ nextCorrespondence.1 frame.reserved) envWF model modelWF .refl .refl
      (oneActualStoredDomainIsSupported correspondence reserved identifier)
      (by simp [oneStep, BinderStep.indexValues])
      (by intro candidate candidateMember
          have equality : candidate = identifier := by simpa using candidateMember
          simpa only [equality] using member)
      (by simp) model modelWF 0 .refl
      (by intro candidate candidateMember
          have equality : candidate = generated reader := by simpa using candidateMember
          simpa only [equality] using fresh)
      0 identifier rfl originalLookup stageReceipts.1 stageReceipts.2 closedSupport.1
      (by simpa using closedSupport.2.2)
  have idsSingleton := exactlyOneIdentifierComesFromTheActualArrayPush array
  subst ids
  have contextIdentity (expression : VExpr) : expression.lift' Lift.refl.cons = expression :=
    VExpr.lift'_depth_zero (by rfl)
  have bodyIdentity : reducedBody.lift' Lift.refl.cons.cons = reducedBody :=
    VExpr.lift'_depth_zero (by rfl)
  refine ⟨chronological, reduced, target, reducedArgument, reducedDomain, reducedBody,
    chronologicalNative, chronologicalConverted, reducedTelescope, targetTelescope, ?_, ?_,
    reducedBodyTranslation, reducedBodyTyping, sourceTranslation, ?_, ?_, ?_, substitutedClosed, substitutedSupport⟩
  · simpa using reducedTelescope.extension.virtualFVars
  · simpa using targetTelescope.extension.virtualFVars
  · simpa [bodyIdentity, contextIdentity] using targetTranslation
  · simpa [bodyIdentity, contextIdentity] using targetTyping
  · simpa [contextIdentity] using endpointEquality

private theorem theStoredStepAndArrayReallyContainOneFreshIndex (reader : Context) :
    [oneStep reader][0]? = some (oneStep reader) ∧
    [oneStep reader][1]? = none ∧
    (oneStep reader).role = .index ∧
    BinderStep.indexValues [oneStep reader] = (#[].push (.fvar (generated reader))).toList ∧
    ((#[] : Array Expr).push (.fvar (generated reader))).size = 1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem actualStageSubstitutionKeepsTheNewIndexAndSelectedParameter
    (reader : Context) (identifier : FVarId) :
    (nativeStageBody reader identifier).instantiate1' (.fvar identifier) =
      .forallE `formalUse (.fvar identifier)
        (.forallE `indexUse (.fvar (generated reader)) (.fvar identifier) .default) .default := rfl

private def semanticPosition : VExpr → Nat
  | .bvar position => position
  | _ => 1000

private def runtimeControls : MetaM Unit := do
  let index : FVarId := ⟨`OneStepActualPushIndex⟩
  let parameter : FVarId := ⟨`OneStepRetainedParameter⟩
  let pushed := (#[] : Array Expr).push (.fvar index)
  let removal : Lift := .consN (.skip .refl) pushed.size
  let insertion : Lift := .consN (.skip (.skip .refl)) pushed.size
  let body := Expr.forallE `formalUse (.bvar 0)
    (.forallE `indexUse (.fvar index) (.fvar parameter) .default) .default
  let expected := Expr.forallE `formalUse (.fvar parameter)
    (.forallE `indexUse (.fvar index) (.fvar parameter) .default) .default
  let conditions := [
    (pushed.size == 1 && pushed.toList == [.fvar index], "actual array push contributes exactly one index"),
    (semanticPosition ((VExpr.bvar 0).lift' removal) == 0, "nonzero removal preserves new index slot"),
    (semanticPosition ((VExpr.bvar 1).lift' removal) == 2, "nonzero removal skips one beneath index"),
    (semanticPosition ((VExpr.bvar 0).lift' insertion) == 0, "independent insertion preserves new index slot"),
    (semanticPosition ((VExpr.bvar 1).lift' insertion) == 3, "independent insertion skips two beneath index"),
    (semanticPosition ((VExpr.bvar 0).lift' insertion.cons) == 0, "body lift protects stage formal"),
    (semanticPosition ((VExpr.bvar 1).lift' insertion.cons) == 1, "body lift protects index beneath formal"),
    (semanticPosition ((VExpr.bvar 2).lift' insertion.cons) == 4, "body lift inserts beneath formal and index"),
    (semanticPosition ((VExpr.bvar 1).lift' insertion.cons) != semanticPosition ((VExpr.bvar 1).lift' insertion),
      "plain context lift is wrong for body index coordinate"),
    (semanticPosition ((VExpr.bvar 0).lift' insertion) != semanticPosition ((VExpr.bvar 0).lift' (.skip (.skip .refl))),
      "unprotected insertion is wrong for index slot"),
    (body.instantiate1' (.fvar parameter) == expected, "structural substitution keeps index and selected parameter"),
    (body.instantiate1 (.fvar parameter) == expected, "native substitution keeps index and selected parameter")]
  for (condition, label) in conditions do
    unless condition do throwError "one-step-stage runtime failed: {label}"
  logInfo m!"one-step-stage runtime: {conditions.length} array-push, native/structural substitution and independent nonzero coordinate probes; actual history adapter application uses identity bases"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "one-step-stage audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do throwError "one-step-stage unexpected axiom {axiomName} in {name}"

private def auditExactDependencies (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "one-step-stage exact dependency manifest changed: {name}; got {axioms}"
  logInfo m!"{name}: exact {allowed.length} inherited/native dependencies"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let adapterAllowed := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq]
  let actualControls := [``constructActualIndexOpening, ``constructGenuineOneStepHistory,
    ``oneActualStoredDomainIsSupported, ``actualNewIndexIsFreshInTheBase,
    ``translatedStageUsesTheFormalNewIndexAndSelectedParameter, ``genuineOneStepHistoryInvokesTheStageAdapter]
  for name in actualControls do auditDeclaration name adapterAllowed
  auditDeclaration ``nativeSortNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  let structuralControls := [``selectedLookupSurvivesTheActualIndexPush, ``actualStageBodyClosedAndSupported,
    ``exactlyOneIdentifierComesFromTheActualArrayPush, ``theStoredStepAndArrayReallyContainOneFreshIndex,
    ``actualStageSubstitutionKeepsTheNewIndexAndSelectedParameter,
    ``actualPushReceiptFixesIndependentNonzeroLiftCutoffs, ``missingNewIndexOrSelectedParameterCannotSupplyStageSupport]
  for name in structuralControls do auditDeclaration name logical
  for name in [``generated, ``nextReader, ``nextVirtual, ``normalizationReceipt, ``oneStep,
      ``nativeStageBody, ``stageSemantic, ``stageLevel, ``semanticPosition, ``runtimeControls,
      ``auditDeclaration, ``auditExactDependencies] do auditDeclaration name logical
  auditExactDependencies ``nativeSortNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``genuineOneStepHistoryInvokesTheStageAdapter adapterAllowed
  runtimeControls
  logInfo m!"one-step-stage tests: {actualControls.length + structuralControls.length + 1} proof controls; real index/stop trace and actual array push; real peeled opening and nonvacuous stored declaration; formal/new index/selected parameter body; shared reduced body, suffix support, target native translation/typing and original endpoint agreement; native sort normalization proved at positive depth, identity base application with independent nonzero lift probes tied to pushed suffix receipt"

end InductiveIndexSubstitutionStageOneStepTest
