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

private def pushSortModel (model : MLCtx) (reader : Context) : MLCtx :=
  .vlam (generated reader) `oneIndex (.sort .zero) (.sort .zero) .default model

private def advanceReaderTwice (reader : Context) : Context :=
  { reader with ngen := reader.ngen.next.next }

private def removedMixedBase (model : MLCtx) (reader : Context) : MLCtx :=
  pushSortModel model (advanceReaderTwice reader)

private def originalMixedReader (reader : Context) : Context :=
  nextReader (advanceReaderTwice reader)

private def insertedMixedBase (model : MLCtx) (reader : Context) : MLCtx :=
  pushSortModel (pushSortModel model reader) (nextReader reader)

private theorem pushSortModelIsWellFormed
    {env : VEnv} {universes : List Name} (model : MLCtx) (modelWF : model.WF env universes)
    (reader : Context) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (pushSortModel model reader).WF env universes ∧
    (pushSortModel model reader).lctx = (nextReader reader).lctx ∧
    ContextReserved (nextReader reader).lctx (nextReader reader).ngen := by
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by simpa only [native] using modelWF.tr
  have frame := Context.RecursorScopeFrame.push reader correspondence.1 reserved `oneIndex .default (.sort .zero)
  refine ⟨⟨modelWF, ?_, .sort (by simp [VLevel.ofLevel]),
    .succ .zero, .sortDF (by trivial) (by trivial) rfl⟩, ?_, frame.reserved⟩
  · simpa only [native] using reserved.fresh correspondence.1
  · simp only [pushSortModel, MLCtx.lctx, nextReader, recursorIndexContext, native, generated]

private theorem constructedMixedBaseWeakenings (model : MLCtx) (reader : Context) :
    VLCtx.FVLift' model.vlctx (removedMixedBase model reader).vlctx 0 (.skip .refl) 0 ∧
    VLCtx.FVLift model.vlctx (insertedMixedBase model reader).vlctx 0 2 0 := by
  have removal : IndexMLCtxExtension model [generated (advanceReaderTwice reader)]
      (removedMixedBase model reader) :=
    .push .nil _ `oneIndex (.sort .zero) (.sort .zero) .default
  have insertion : IndexMLCtxExtension model [generated reader, generated (nextReader reader)]
      (insertedMixedBase model reader) :=
    .push (.push .nil _ `oneIndex (.sort .zero) (.sort .zero) .default)
      _ `oneIndex (.sort .zero) (.sort .zero) .default
  exact ⟨removal.weakening.toFVLift', insertion.weakening⟩

private theorem constructedMixedBasesHaveExactSupports (model : MLCtx) (reader : Context) :
    (removedMixedBase model reader).vlctx.fvars = generated (advanceReaderTwice reader) :: model.vlctx.fvars ∧
    (insertedMixedBase model reader).vlctx.fvars =
      generated (nextReader reader) :: generated reader :: model.vlctx.fvars := ⟨rfl, rfl⟩

private theorem constructedMixedBasesHaveIndependentWidths (model : MLCtx) (reader : Context) :
    (removedMixedBase model reader).vlctx.toCtx.length = model.vlctx.toCtx.length + 1 ∧
    (insertedMixedBase model reader).vlctx.toCtx.length = model.vlctx.toCtx.length + 2 ∧
    (removedMixedBase model reader).vlctx.toCtx ≠ model.vlctx.toCtx ∧
    (insertedMixedBase model reader).vlctx.toCtx ≠ (removedMixedBase model reader).vlctx.toCtx := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro equality
    have lengths := congrArg List.length equality
    change model.vlctx.toCtx.length + 1 = model.vlctx.toCtx.length at lengths
    omega
  · intro equality
    have lengths := congrArg List.length equality
    change model.vlctx.toCtx.length + 2 = model.vlctx.toCtx.length + 1 at lengths
    omega

private theorem constructedMixedBasesAreWellFormed
    {env : VEnv} {universes : List Name} (model : MLCtx) (modelWF : model.WF env universes)
    (reader : Context) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (removedMixedBase model reader).WF env universes ∧
    (removedMixedBase model reader).lctx = (originalMixedReader reader).lctx ∧
    ContextReserved (originalMixedReader reader).lctx (originalMixedReader reader).ngen ∧
    (insertedMixedBase model reader).WF env universes ∧
    generated (originalMixedReader reader) ∉ (insertedMixedBase model reader).vlctx.fvars := by
  have advancedReserved : ContextReserved reader.lctx reader.ngen.next.next := by
    intro declaration member
    exact NameGenerator.Reserves.mono (NameGenerator.LE.next.trans NameGenerator.LE.next)
      (reserved declaration member)
  have originalReceipts := pushSortModelIsWellFormed model modelWF (advanceReaderTwice reader)
    native advancedReserved
  have first := pushSortModelIsWellFormed model modelWF reader native reserved
  have second := pushSortModelIsWellFormed (pushSortModel model reader) first.1
    (nextReader reader) first.2.1 first.2.2
  have insertedReserved : ContextReserved (insertedMixedBase model reader).lctx
      (originalMixedReader reader).ngen := by
    intro declaration member
    apply NameGenerator.Reserves.mono NameGenerator.LE.next
    apply second.2.2 declaration
    change declaration ∈ (pushSortModel (pushSortModel model reader) (nextReader reader)).lctx.toList at member
    simpa only [second.2.1] using member
  have fresh := second.1.tr.find?_eq_none.mp (insertedReserved.fresh second.1.tr.1)
  exact ⟨originalReceipts.1, originalReceipts.2.1, originalReceipts.2.2, second.1, fresh⟩

private theorem genuineOneStepHistoryRebasesConstructedMixedBases
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    (parametersEmpty : stats.params.size = 0)
    (seed : MLCtx) (seedWF : seed.WF env universes) (reader : Context)
    (native : seed.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (envWF : env.WF) (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    let smaller := pushSortModel seed reader
    let baseReader := nextReader reader
    let original := removedMixedBase smaller baseReader
    let larger := insertedMixedBase smaller baseReader
    let actualReader := originalMixedReader baseReader
    ∃ (chronological reduced target : MLCtx) (reducedArgument reducedDomain reducedBody : VExpr),
      chronological.vlctx = nextVirtual original.vlctx actualReader ∧
      SelectedRecursorTelescope env universes (nextReader actualReader).lctx smaller
        [generated actualReader] reduced ∧
      SelectedRecursorTelescope env universes (nextReader actualReader).lctx larger
        [generated actualReader] target ∧
      reduced.vlctx.fvars = generated actualReader :: smaller.vlctx.fvars ∧
      target.vlctx.fvars = generated actualReader :: larger.vlctx.fvars ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0 (.cons (.skip (.skip .refl))) 0 ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx)
        (nativeStageBody actualReader (generated reader)) reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx) reducedBody (.sort stageLevel) ∧
      TrExprS env universes reduced.vlctx
        ((nativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort stageLevel) ∧
      TrExprS env universes target.vlctx
        ((nativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        ((reducedBody.lift' (Lift.cons (.skip (.skip .refl))).cons).inst
          (reducedArgument.lift' (.cons (.skip (.skip .refl))))) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.lift' (Lift.cons (.skip (.skip .refl))).cons).inst
          (reducedArgument.lift' (.cons (.skip (.skip .refl))))) (.sort stageLevel) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.inst reducedArgument).lift' (.cons (.skip (.skip .refl)))) (.sort stageLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        ((stageSemantic (.bvar 1)).inst (.bvar 2))
        ((reducedBody.inst reducedArgument).lift' (.cons (.skip .refl))) (.sort stageLevel) ∧
      Closed ((nativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))) 0 ∧
      ((nativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))).FVarsIn
        (· ∈ reduced.vlctx.fvars) := by
  let smaller := pushSortModel seed reader
  let baseReader := nextReader reader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  have retainedReceipts := pushSortModelIsWellFormed seed seedWF reader native reserved
  have mixed := constructedMixedBasesAreWellFormed smaller retainedReceipts.1 baseReader
    retainedReceipts.2.1 retainedReceipts.2.2
  have weakenings := constructedMixedBaseWeakenings smaller baseReader
  have correspondence : TrLCtx env universes actualReader.lctx original.vlctx := by
    simpa only [mixed.2.1] using mixed.1.tr
  have normalized := nativeSortNormalizationWithPositiveDepth actualReader depth positive
  obtain ⟨trace, history⟩ := constructGenuineOneStepHistory parametersEmpty correspondence mixed.2.2.1 normalized
  have opening := constructActualIndexOpening correspondence mixed.2.2.1
  have frame := opening.2.2.2.2.2
  have nextCorrespondence : TrLCtx env universes (nextReader actualReader).lctx
      (nextVirtual original.vlctx actualReader) := opening.2.2.1
  have originalLookup : original.vlctx.find? (.inr (generated reader)) = some (.bvar 1, .sort .zero) := by
    have fresh := mixed.1.tr.wf.2.1 (generated (advanceReaderTwice baseReader)) [] rfl
    have different : generated (advanceReaderTwice baseReader) ≠ generated reader := by
      intro equality
      apply fresh.1
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars, ← equality]
    have selectedLookup : smaller.vlctx.find? (.inr (generated reader)) = some (.bvar 0, .sort .zero) := by
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN]
    exact selectedLookupSurvivesTheActualIndexPush different selectedLookup
  have member : generated reader ∈ smaller.vlctx.fvars := by
    simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars]
  have freshOriginal := actualNewIndexIsFreshInTheBase correspondence mixed.2.2.1
  have different : generated actualReader ≠ generated reader := by
    intro equality
    apply freshOriginal
    change generated actualReader ∈ generated (advanceReaderTwice baseReader) :: smaller.vlctx.fvars
    exact List.mem_cons_of_mem _ (equality.symm ▸ member)
  have finalLookup := selectedLookupSurvivesTheActualIndexPush different originalLookup
  have stageReceipts := translatedStageUsesTheFormalNewIndexAndSelectedParameter envWF mixed.1.tr.wf
    (generated reader) different originalLookup
  have closedSupport := actualStageBodyClosedAndSupported actualReader (generated reader) smaller.vlctx.fvars member
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, reducedDomain, _, reducedBody,
    _, _, chronologicalConverted, _, array, reducedTelescope, _, _, _, targetTelescope,
    _, insertionWeakening, _, _, _, _, _, _, _, _, _, _, reducedBodyTranslation, reducedBodyTyping, _, _,
    sourceTyping, endpointEquality, _, _, _, targetTyping, substitutedClosed, substitutedSupport,
    _, sourceTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains original mixed.1 mixed.2.1 rfl mixed.2.2.1
      (nextReader actualReader) (.refl _ nextCorrespondence.1 frame.reserved) envWF
      smaller retainedReceipts.1 (.skip .refl) weakenings.1
      (oneActualStoredDomainIsSupported correspondence mixed.2.2.1 (generated reader))
      (by simp [oneStep, BinderStep.indexValues])
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      (by simp) larger mixed.2.2.2.1 2 weakenings.2
      (by intro candidate selected
          have equality : candidate = generated actualReader := by simpa using selected
          simpa only [equality] using mixed.2.2.2.2)
      0 (generated reader) rfl finalLookup stageReceipts.1 stageReceipts.2 closedSupport.1
      (by simpa using closedSupport.2.2)
  have idsSingleton := exactlyOneIdentifierComesFromTheActualArrayPush array
  subst ids
  refine ⟨chronological, reduced, target, reducedArgument, reducedDomain, reducedBody,
    chronologicalConverted, reducedTelescope, targetTelescope, ?_, ?_, insertionWeakening,
    reducedBodyTranslation, reducedBodyTyping, sourceTranslation, sourceTyping, targetTranslation,
    targetTyping, ?_, endpointEquality, substitutedClosed, substitutedSupport⟩
  · simpa using reducedTelescope.extension.virtualFVars
  · simpa using targetTelescope.extension.virtualFVars
  · simpa only [VExpr.lift'_inst_hi] using targetTyping

private theorem constructedSelectedStageHasDistinctSourceOriginalAndTargetCoordinates :
    stageSemantic (.bvar 0) = .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 4)) ∧
    stageSemantic (.bvar 1) = .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 5)) ∧
    (stageSemantic (.bvar 0)).lift' (Lift.cons (.skip .refl)).cons = stageSemantic (.bvar 1) ∧
    (stageSemantic (.bvar 0)).lift' (Lift.cons (.skip (.skip .refl))).cons =
      .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6)) ∧
    (stageSemantic (.bvar 0)).inst (.bvar 1) = .forallE (.bvar 1) (.forallE (.bvar 1) (.bvar 3)) ∧
    (stageSemantic (.bvar 1)).inst (.bvar 2) = .forallE (.bvar 2) (.forallE (.bvar 1) (.bvar 4)) ∧
    ((stageSemantic (.bvar 0)).inst (.bvar 1)).lift' (.cons (.skip (.skip .refl))) =
      .forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5)) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .forallE domain body => 1 :: (semanticShape domain ++ semanticShape body)
  | _ => [2]

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
  let sourceBody := stageSemantic (.bvar 0)
  let originalBody := stageSemantic (.bvar 1)
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
    (body.instantiate1 (.fvar parameter) == expected, "native substitution keeps index and selected parameter"),
    (semanticShape sourceBody == semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 4))),
      "retained parameter has reduced body coordinate four"),
    (semanticShape originalBody == semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 5))),
      "removed declaration gives original body coordinate five"),
    (semanticShape (sourceBody.lift' removal.cons) == semanticShape originalBody,
      "actual one-declaration removal lift reconstructs original body"),
    (semanticShape (sourceBody.lift' insertion.cons) ==
      semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6))),
      "independent two-declaration insertion gives target body coordinate six"),
    (semanticShape (sourceBody.inst (.bvar 1)) ==
      semanticShape (.forallE (.bvar 1) (.forallE (.bvar 1) (.bvar 3))),
      "reduced endpoint separates selected parameter and fresh index"),
    (semanticShape (originalBody.inst (.bvar 2)) ==
      semanticShape (.forallE (.bvar 2) (.forallE (.bvar 1) (.bvar 4))),
      "original endpoint reflects removed declaration"),
    (semanticShape ((sourceBody.inst (.bvar 1)).lift' insertion) ==
      semanticShape (.forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5))),
      "target endpoint reflects independent inserted declarations"),
    (semanticShape (sourceBody.lift' insertion.cons) != semanticShape (sourceBody.lift' insertion),
      "plain context lift does not protect body formal"),
    (semanticShape ((sourceBody.inst (.bvar 1)).lift' insertion) !=
      semanticShape ((sourceBody.inst (.bvar 1)).lift' removal),
      "independent insertion cannot be replaced by original removal")]
  for (condition, label) in conditions do
    unless condition do throwError "one-step-stage runtime failed: {label}"
  logInfo m!"one-step-stage runtime: {conditions.length} array-push, native/structural substitution and mixed-base coordinate probes; actual history adapter applications cover identity bases and constructed one-removed/two-inserted bases"

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
    ``translatedStageUsesTheFormalNewIndexAndSelectedParameter, ``genuineOneStepHistoryInvokesTheStageAdapter,
    ``pushSortModelIsWellFormed, ``constructedMixedBasesAreWellFormed,
    ``genuineOneStepHistoryRebasesConstructedMixedBases]
  for name in actualControls do auditDeclaration name adapterAllowed
  auditDeclaration ``nativeSortNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  let structuralControls := [``selectedLookupSurvivesTheActualIndexPush, ``actualStageBodyClosedAndSupported,
    ``exactlyOneIdentifierComesFromTheActualArrayPush, ``theStoredStepAndArrayReallyContainOneFreshIndex,
    ``actualStageSubstitutionKeepsTheNewIndexAndSelectedParameter,
    ``actualPushReceiptFixesIndependentNonzeroLiftCutoffs, ``missingNewIndexOrSelectedParameterCannotSupplyStageSupport,
    ``constructedMixedBaseWeakenings, ``constructedMixedBasesHaveIndependentWidths,
    ``constructedMixedBasesHaveExactSupports, ``constructedSelectedStageHasDistinctSourceOriginalAndTargetCoordinates]
  for name in structuralControls do auditDeclaration name logical
  for name in [``generated, ``nextReader, ``nextVirtual, ``normalizationReceipt, ``oneStep,
      ``nativeStageBody, ``stageSemantic, ``stageLevel, ``semanticPosition, ``semanticShape, ``runtimeControls,
      ``pushSortModel, ``advanceReaderTwice, ``removedMixedBase, ``originalMixedReader, ``insertedMixedBase,
      ``auditDeclaration, ``auditExactDependencies] do auditDeclaration name logical
  auditExactDependencies ``nativeSortNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``genuineOneStepHistoryInvokesTheStageAdapter adapterAllowed
  auditExactDependencies ``genuineOneStepHistoryRebasesConstructedMixedBases adapterAllowed
  runtimeControls
  logInfo m!"one-step-stage tests: {actualControls.length + structuralControls.length + 1} proof controls; real index/stop trace and actual array push; real peeled opening and nonvacuous stored declaration; constructed retained parameter, original one-declaration removal and independent two-declaration target insertion; shared reduced body, suffix support, target native translation/typing and original endpoint agreement; native sort normalization proved at positive depth; both identity and mixed-base applications tied to actual pushed suffix receipt"

end InductiveIndexSubstitutionStageOneStepTest
