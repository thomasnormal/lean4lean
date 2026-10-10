import Lean4Lean.Verify.InductiveIndexSubstitutionStageBinding
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

private def oneIndexType : Expr := .forallE `oneIndex (.sort .zero) (.sort .zero) .default

private def twoIndexType : Expr := .forallE `oneIndex (.sort .zero) oneIndexType .default

private def twoIndexArray (reader : Context) : Array Expr :=
  (#[].push (.fvar (generated reader))).push (.fvar (generated (nextReader reader)))

private def twoIndexSteps (reader : Context) : List BinderStep := [oneStep reader, oneStep (nextReader reader)]

private def twoIndexVirtual (virtual : VLCtx) (reader : Context) : VLCtx :=
  nextVirtual (nextVirtual virtual reader) (nextReader reader)

private def twoIndexNativeStageBody (reader : Context) (identifier : FVarId) : Expr :=
  .forallE `formalUse (.bvar 0)
    (.forallE `firstIndexUse (.fvar (generated reader))
      (.forallE `secondIndexUse (.fvar (generated (nextReader reader))) (.fvar identifier) .default)
      .default) .default

private def twoIndexStageSemantic (argument : VExpr) : VExpr :=
  .forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) argument.lift.lift.lift.lift.lift.lift))

private def twoIndexStageLevel : VLevel := .imax .zero (.imax .zero (.imax .zero .zero))

private theorem nativeForallNormalizationWithPositiveDepth
    (reader : Context) (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    ((monadLift (TypeChecker.whnf (oneIndexType.instantiate1 (.fvar (generated reader)))) : M Expr)
      (nextReader reader)) = .ok oneIndexType := by
  rw [Expr.instantiate1_eq]
  change (Prod.fst <$> (TypeChecker.Methods.withFuel reader.fuel.recDepth).whnf oneIndexType
    { env := reader.env, safety := reader.safety, lctx := (nextReader reader).lctx,
      lparams := reader.lparams, fuel := reader.fuel } {}) = .ok oneIndexType
  rw [positive]
  rfl

private theorem sortForallTranslationAndTyping {env : VEnv} {universes : List Name} (virtual : VLCtx) :
    TrExprS env universes virtual oneIndexType (.forallE (.sort .zero) (.sort .zero)) ∧
    env.HasType universes.length virtual.toCtx (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) := by
  have domainTyped : env.HasType universes.length virtual.toCtx (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF (by trivial) (by trivial) rfl
  have bodyTyped : env.HasType universes.length ((.sort .zero) :: virtual.toCtx)
      (.sort .zero) (.sort (.succ .zero)) := .sortDF (by trivial) (by trivial) rfl
  exact ⟨.forallE ⟨.succ .zero, domainTyped⟩ ⟨.succ .zero, bodyTyped⟩
    (.sort (by simp [VLevel.ofLevel])) (.sort (by simp [VLevel.ofLevel])),
    .forallEDF domainTyped bodyTyped⟩

private theorem constructFirstOfTwoActualIndexOpenings
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    PeeledIndexOpening env universes reader virtual `oneIndex (.sort .zero) oneIndexType
      .default (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) (.succ .zero) (.sort .zero) := by
  have opening := constructActualIndexOpening correspondence reserved
  have translated := sortForallTranslationAndTyping (env := env) (universes := universes)
    (nextVirtual virtual reader)
  refine ⟨opening.1, opening.2.1, opening.2.2.1, ?_, opening.2.2.2.2.1, opening.2.2.2.2.2⟩
  rw [Expr.instantiate1_eq]
  exact ⟨_, translated.1, translated.2.toU⟩

private theorem constructGenuineTwoStepHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {reader : Context} {virtual : VLCtx}
    (parametersEmpty : stats.params.size = 0)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    ∃ trace : RecursorIndexTrace stats twoIndexType 0 #[] reader (.sort .zero) 0
      (twoIndexArray reader) (nextReader (nextReader reader)),
      TranslatedRecursorIndexTrace env universes trace virtual
        (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero)))
        (twoIndexVirtual virtual reader) (.sort .zero) := by
  have firstOpening := constructFirstOfTwoActualIndexOpenings correspondence reserved
  have firstCorrespondence := firstOpening.2.2.1
  have secondOpening := constructActualIndexOpening firstCorrespondence firstOpening.2.2.2.2.2.reserved
  have firstNormalized := nativeForallNormalizationWithPositiveDepth reader depth positive
  have secondNormalized := nativeSortNormalizationWithPositiveDepth (nextReader reader) depth positive
  have notParameter : ¬0 < stats.params.size := by simp [parametersEmpty]
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  have stopped := RecursorIndexTrace.stop (stats := stats) (index := 0)
    (indices := twoIndexArray reader) (ctx := nextReader (nextReader reader)) notForall
  have second := RecursorIndexTrace.index (stats := stats) (name := `oneIndex) (domain := .sort .zero)
    (body := .sort .zero) (bi := .default) (index := 0)
    (indices := #[].push (.fvar (generated reader))) (ctx := nextReader reader)
    notParameter secondNormalized stopped
  have stoppedTranslated := TranslatedRecursorIndexTrace.stop (stats := stats)
    (index := 0) (indices := twoIndexArray reader) notForall secondOpening.2.2.1
    (TrExprS.sort (u' := .zero) (by simp [VLevel.ofLevel]))
  have secondTranslated := TranslatedRecursorIndexTrace.index (name := `oneIndex)
    (domain := .sort .zero) (body := .sort .zero) (bi := .default) (reader := nextReader reader)
    (index := 0) (indices := #[].push (.fvar (generated reader)))
    notParameter secondNormalized stopped (sortForallTranslationAndTyping (nextVirtual virtual reader)).1
    secondOpening (.sort (by simp [VLevel.ofLevel]))
    (show env.HasType universes.length (twoIndexVirtual virtual reader).toCtx
      (.sort .zero) (.sort (.succ .zero)) from .sortDF (by trivial) (by trivial) rfl).toU stoppedTranslated
  have firstTranslated := sortForallTranslationAndTyping (env := env) (universes := universes)
    ((none, .vlam (.sort .zero)) :: virtual)
  have translated : TrExprS env universes virtual twoIndexType
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))) :=
    .forallE ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      ⟨.imax (.succ .zero) (.succ .zero), firstTranslated.2⟩
      (.sort (by simp [VLevel.ofLevel])) firstTranslated.1
  refine ⟨.index notParameter firstNormalized second, ?_⟩
  exact .index (name := `oneIndex) (domain := .sort .zero) (body := oneIndexType)
    (bi := .default) (reader := reader) (index := 0) (indices := #[])
    notParameter firstNormalized second translated firstOpening
    (sortForallTranslationAndTyping (nextVirtual virtual reader)).1
    (sortForallTranslationAndTyping (nextVirtual virtual reader)).2.toU secondTranslated

private theorem twoActualStoredDomainsAreSupported
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (identifier : FVarId) :
    BinderStoredIndexTypeFVarsIn [identifier] (nextReader (nextReader reader)) (twoIndexSteps reader) := by
  have firstOpening := constructActualIndexOpening correspondence reserved
  have secondOpening := constructActualIndexOpening firstOpening.2.2.1 firstOpening.2.2.2.2.2.reserved
  have firstDeclared := firstOpening.2.2.2.2.1.declared.mono firstOpening.2.2.1.1
    secondOpening.2.2.2.2.2
  have declared : BinderStepsIndexDeclared (nextReader (nextReader reader)) (twoIndexSteps reader) := by
    intro step member role
    have alternatives : step = oneStep reader ∨ step = oneStep (nextReader reader) := by
      simpa [twoIndexSteps] using member
    rcases alternatives with equality | equality
    · subst step
      exact firstDeclared
    · subst step
      exact secondOpening.2.2.2.2.1.declared
  have raw : BinderRawDomainFVarsIn [identifier] (twoIndexSteps reader) := by
    intro position step selected
    cases position with
    | zero =>
      have equality : oneStep reader = step := Option.some.inj selected
      subst step
      trivial
    | succ position =>
      cases position with
      | zero =>
        have equality : oneStep (nextReader reader) = step := Option.some.inj selected
        subst step
        trivial
      | succ position => simp [twoIndexSteps] at selected
  exact raw.storedIndexTypeFVarsIn declared

private theorem exactlyTwoIdentifiersComeFromTheActualArrayPushes
    {reader : Context} {ids : List FVarId}
    (array : (twoIndexArray reader).toList = (#[] : Array Expr).toList ++ ids.map Expr.fvar) :
    ids = [generated reader, generated (nextReader reader)] := by
  have mapped : ids.map Expr.fvar = [.fvar (generated reader), .fvar (generated (nextReader reader))] := by
    simpa [twoIndexArray] using array.symm
  have injective : Function.Injective (Expr.fvar : FVarId → Expr) := fun _ _ equality => Expr.fvar.inj equality
  exact (List.map_inj_right injective).mp mapped

private theorem twoFreshIndexNamesAreDistinctFromTheRetainedParameter
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (identifier : FVarId)
    (member : identifier ∈ virtual.fvars) :
    generated reader ≠ identifier ∧ generated (nextReader reader) ≠ identifier ∧
      generated (nextReader reader) ≠ generated reader := by
  have firstOpening := constructActualIndexOpening correspondence reserved
  have firstFresh := actualNewIndexIsFreshInTheBase correspondence reserved
  have secondFresh := actualNewIndexIsFreshInTheBase firstOpening.2.2.1 firstOpening.2.2.2.2.2.reserved
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    exact firstFresh (equality.symm ▸ member)
  · intro equality
    apply secondFresh
    change generated (nextReader reader) ∈ generated reader :: virtual.fvars
    exact List.mem_cons_of_mem _ (equality.symm ▸ member)
  · intro equality
    apply secondFresh
    change generated (nextReader reader) ∈ generated reader :: virtual.fvars
    simp [equality]

private theorem bothActualStoredIndexDeclarationsExist
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ first second : LocalDecl,
      (nextReader (nextReader reader)).lctx.find? (generated reader) = some first ∧
      first.type = .sort .zero ∧
      (nextReader (nextReader reader)).lctx.find? (generated (nextReader reader)) = some second ∧
      second.type = .sort .zero := by
  have firstOpening := constructActualIndexOpening correspondence reserved
  have secondOpening := constructActualIndexOpening firstOpening.2.2.1 firstOpening.2.2.2.2.2.reserved
  obtain ⟨first, firstLookup, _, firstType, _, _⟩ := firstOpening.2.2.2.2.1.declared.mono
    firstOpening.2.2.1.1 secondOpening.2.2.2.2.2
  obtain ⟨second, secondLookup, _, secondType, _, _⟩ := secondOpening.2.2.2.2.1.declared
  exact ⟨first, second, firstLookup, firstType, secondLookup, secondType⟩

private theorem theSecondActualIndexIsFreshInTheIndependentLargerBase
    {env : VEnv} {universes : List Name} (model : MLCtx) (modelWF : model.WF env universes)
    (reader : Context) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    generated (nextReader (originalMixedReader reader)) ∉ (insertedMixedBase model reader).vlctx.fvars := by
  have first := pushSortModelIsWellFormed model modelWF reader native reserved
  have second := pushSortModelIsWellFormed (pushSortModel model reader) first.1
    (nextReader reader) first.2.1 first.2.2
  have insertedReserved : ContextReserved (insertedMixedBase model reader).lctx
      (nextReader (originalMixedReader reader)).ngen := by
    intro declaration member
    apply NameGenerator.Reserves.mono (NameGenerator.LE.next.trans NameGenerator.LE.next)
    apply second.2.2 declaration
    change declaration ∈ (pushSortModel (pushSortModel model reader) (nextReader reader)).lctx.toList at member
    simpa only [second.2.1] using member
  exact second.1.tr.find?_eq_none.mp (insertedReserved.fresh second.1.tr.1)

private theorem translatedStageUsesTheFormalBothNewIndicesAndSelectedParameter
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (envWF : env.WF) (virtualWF : virtual.WF env universes.length)
    (identifier : FVarId) (firstDifferent : generated reader ≠ identifier)
    (secondDifferent : generated (nextReader reader) ≠ identifier)
    (indexDifferent : generated (nextReader reader) ≠ generated reader) {argument : VExpr}
    (lookup : virtual.find? (.inr identifier) = some (argument, .sort .zero)) :
    TrExprS env universes ((none, .vlam (.sort .zero)) :: twoIndexVirtual virtual reader)
      (twoIndexNativeStageBody reader identifier) (twoIndexStageSemantic argument) ∧
    env.HasType universes.length ((.sort .zero) :: (twoIndexVirtual virtual reader).toCtx)
      (twoIndexStageSemantic argument) (.sort twoIndexStageLevel) := by
  have argumentTyped := virtualWF.find?_wf envWF.ordered lookup
  have raisedTyped : env.HasType universes.length
      (.bvar 3 :: .bvar 3 :: .bvar 0 :: .sort .zero :: .sort .zero :: .sort .zero :: virtual.toCtx)
      argument.lift.lift.lift.lift.lift.lift (.sort .zero) :=
    (((((argumentTyped.weak envWF.ordered).weak envWF.ordered).weak envWF.ordered).weak envWF.ordered).weak
      envWF.ordered).weak envWF.ordered
  have finalLookup :
      VLCtx.find? ((none, .vlam (.bvar 3)) :: (none, .vlam (.bvar 3)) :: (none, .vlam (.bvar 0)) ::
        (none, .vlam (.sort .zero)) :: twoIndexVirtual virtual reader) (.inr identifier) =
      some (argument.lift.lift.lift.lift.lift.lift, .sort .zero) := by
    simp [twoIndexVirtual, nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
      firstDifferent, secondDifferent, lookup, VLocalDecl.depth, VExpr.liftN, VExpr.lift]
  have typed : env.HasType universes.length ((.sort .zero) :: (twoIndexVirtual virtual reader).toCtx)
      (twoIndexStageSemantic argument) (.sort twoIndexStageLevel) :=
    .forallEDF (.bvar .zero) (.forallEDF (.bvar (.succ (.succ (.succ .zero))))
      (.forallEDF (.bvar (.succ (.succ (.succ .zero)))) raisedTyped))
  refine ⟨?_, typed⟩
  exact .forallE ⟨.zero, .bvar .zero⟩
    ⟨.imax .zero (.imax .zero .zero), .forallEDF (.bvar (.succ (.succ (.succ .zero))))
      (.forallEDF (.bvar (.succ (.succ (.succ .zero)))) raisedTyped)⟩
    (.bvar rfl) (.forallE ⟨.zero, .bvar (.succ (.succ (.succ .zero)))⟩
      ⟨.imax .zero .zero, .forallEDF (.bvar (.succ (.succ (.succ .zero)))) raisedTyped⟩
      (.fvar (A := .sort .zero) (by simp [twoIndexVirtual, nextVirtual, peeledIndexVirtualContext,
        VLCtx.find?, VLCtx.next, indexDifferent, VLocalDecl.value, VLocalDecl.type,
        VLocalDecl.depth, VExpr.liftN, VExpr.lift]))
      (.forallE ⟨.zero, .bvar (.succ (.succ (.succ .zero)))⟩ ⟨.zero, raisedTyped⟩
        (.fvar (A := .sort .zero) (by simp [twoIndexVirtual, nextVirtual, peeledIndexVirtualContext,
          VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, VExpr.liftN, VExpr.lift]))
        (.fvar finalLookup)))

private theorem actualTwoIndexStageBodyClosedAndSupported
    (reader : Context) (identifier : FVarId) (base : List FVarId) (member : identifier ∈ base) :
    Closed (twoIndexNativeStageBody reader identifier) 1 ∧
    ¬Closed (twoIndexNativeStageBody reader identifier) 0 ∧
    (twoIndexNativeStageBody reader identifier).FVarsIn
      (· ∈ generated (nextReader reader) :: generated reader :: base) := by
  simp [twoIndexNativeStageBody, Closed, FVarsIn, member]

private theorem genuineTwoStepHistoryRebasesConstructedMixedBases
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
    let finalReader := nextReader (nextReader actualReader)
    ∃ (chronological reduced target : MLCtx) (reducedArgument reducedDomain reducedBody : VExpr),
      chronological.vlctx = twoIndexVirtual original.vlctx actualReader ∧
      SelectedRecursorTelescope env universes finalReader.lctx smaller
        [generated actualReader, generated (nextReader actualReader)] reduced ∧
      SelectedRecursorTelescope env universes finalReader.lctx larger
        [generated actualReader, generated (nextReader actualReader)] target ∧
      reduced.vlctx.fvars = generated (nextReader actualReader) :: generated actualReader :: smaller.vlctx.fvars ∧
      target.vlctx.fvars = generated (nextReader actualReader) :: generated actualReader :: larger.vlctx.fvars ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0 (.consN (.skip (.skip .refl)) 2) 0 ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx)
        (twoIndexNativeStageBody actualReader (generated reader)) reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx) reducedBody (.sort twoIndexStageLevel) ∧
      TrExprS env universes reduced.vlctx
        ((twoIndexNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort twoIndexStageLevel) ∧
      TrExprS env universes target.vlctx
        ((twoIndexNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        ((reducedBody.lift' (Lift.consN (.skip (.skip .refl)) 2).cons).inst
          (reducedArgument.lift' (.consN (.skip (.skip .refl)) 2))) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.lift' (Lift.consN (.skip (.skip .refl)) 2).cons).inst
          (reducedArgument.lift' (.consN (.skip (.skip .refl)) 2))) (.sort twoIndexStageLevel) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.inst reducedArgument).lift' (.consN (.skip (.skip .refl)) 2)) (.sort twoIndexStageLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        ((twoIndexStageSemantic (.bvar 1)).inst (.bvar 3))
        ((reducedBody.inst reducedArgument).lift' (.consN (.skip .refl) 2)) (.sort twoIndexStageLevel) ∧
      Closed ((twoIndexNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))) 0 ∧
      ((twoIndexNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))).FVarsIn
        (· ∈ reduced.vlctx.fvars) := by
  let smaller := pushSortModel seed reader
  let baseReader := nextReader reader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  have retained := pushSortModelIsWellFormed seed seedWF reader native reserved
  have mixed := constructedMixedBasesAreWellFormed smaller retained.1 baseReader retained.2.1 retained.2.2
  have weakenings := constructedMixedBaseWeakenings smaller baseReader
  have correspondence : TrLCtx env universes actualReader.lctx original.vlctx := by
    simpa only [mixed.2.1] using mixed.1.tr
  obtain ⟨trace, history⟩ := constructGenuineTwoStepHistory parametersEmpty correspondence mixed.2.2.1 depth positive
  have firstOpening := constructActualIndexOpening correspondence mixed.2.2.1
  have secondOpening := constructActualIndexOpening firstOpening.2.2.1 firstOpening.2.2.2.2.2.reserved
  have originalLookup : original.vlctx.find? (.inr (generated reader)) = some (.bvar 1, .sort .zero) := by
    have fresh := mixed.1.tr.wf.2.1 (generated (advanceReaderTwice baseReader)) [] rfl
    have different : generated (advanceReaderTwice baseReader) ≠ generated reader := by
      intro equality
      apply fresh.1
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars, ← equality]
    have lookup : smaller.vlctx.find? (.inr (generated reader)) = some (.bvar 0, .sort .zero) := by
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN]
    exact selectedLookupSurvivesTheActualIndexPush different lookup
  have member : generated reader ∈ smaller.vlctx.fvars := by
    simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars]
  have originalMember : generated reader ∈ original.vlctx.fvars := by
    change generated reader ∈ generated (advanceReaderTwice baseReader) :: smaller.vlctx.fvars
    exact List.mem_cons_of_mem _ member
  have different := twoFreshIndexNamesAreDistinctFromTheRetainedParameter correspondence mixed.2.2.1
    (generated reader) originalMember
  have firstLookup := selectedLookupSurvivesTheActualIndexPush different.1 originalLookup
  have finalLookup := selectedLookupSurvivesTheActualIndexPush different.2.1 firstLookup
  have stageReceipts := translatedStageUsesTheFormalBothNewIndicesAndSelectedParameter envWF mixed.1.tr.wf
    (generated reader) different.1 different.2.1 different.2.2 originalLookup
  have closedSupport := actualTwoIndexStageBodyClosedAndSupported actualReader (generated reader) smaller.vlctx.fvars member
  have secondFresh := theSecondActualIndexIsFreshInTheIndependentLargerBase smaller retained.1 baseReader
    retained.2.1 retained.2.2
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, reducedDomain, _, reducedBody,
    _, _, chronologicalConverted, _, array, reducedTelescope, _, _, _, targetTelescope,
    _, insertionWeakening, _, _, _, _, _, _, _, _, _, _, reducedBodyTranslation, reducedBodyTyping, _, _,
    sourceTyping, endpointEquality, _, _, _, targetTyping, substitutedClosed, substitutedSupport,
    _, sourceTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains original mixed.1 mixed.2.1 rfl mixed.2.2.1
      (nextReader (nextReader actualReader)) (.refl _ secondOpening.2.2.1.1 secondOpening.2.2.2.2.2.reserved) envWF
      smaller retained.1 (.skip .refl) weakenings.1
      (twoActualStoredDomainsAreSupported correspondence mixed.2.2.1 (generated reader))
      (by simp [twoIndexSteps, twoIndexArray, oneStep, BinderStep.indexValues])
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      (by simp) larger mixed.2.2.2.1 2 weakenings.2
      (by intro candidate selected
          have alternatives : candidate = generated actualReader ∨ candidate = generated (nextReader actualReader) := by
            simpa [twoIndexArray] using selected
          rcases alternatives with equality | equality
          · simpa only [equality] using mixed.2.2.2.2
          · simpa only [equality] using secondFresh)
      0 (generated reader) rfl finalLookup stageReceipts.1 stageReceipts.2 closedSupport.1
      (by simpa [twoIndexArray] using closedSupport.2.2)
  have idsPair := exactlyTwoIdentifiersComeFromTheActualArrayPushes array
  subst ids
  refine ⟨chronological, reduced, target, reducedArgument, reducedDomain, reducedBody,
    chronologicalConverted, reducedTelescope, targetTelescope, ?_, ?_, insertionWeakening,
    reducedBodyTranslation, reducedBodyTyping, sourceTranslation, sourceTyping, targetTranslation,
    targetTyping, ?_, endpointEquality, substitutedClosed, substitutedSupport⟩
  · simpa using reducedTelescope.extension.virtualFVars
  · simpa using targetTelescope.extension.virtualFVars
  · simpa only [VExpr.lift'_inst_hi] using targetTyping

private theorem actualPushReceiptFixesTwoSuffixOrderAndCutoffs
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx} {ids : List FVarId}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (array : (twoIndexArray reader).toList = (#[] : Array Expr).toList ++ ids.map Expr.fvar) :
    ids = [generated reader, generated (nextReader reader)] ∧
    ids.reverse = [generated (nextReader reader), generated reader] ∧ ids ≠ ids.reverse ∧
    (VExpr.bvar 0).lift' (.consN (.skip (.skip .refl)) ids.length) = .bvar 0 ∧
    (VExpr.bvar 1).lift' (.consN (.skip (.skip .refl)) ids.length) = .bvar 1 ∧
    (VExpr.bvar 2).lift' (.consN (.skip .refl) ids.length) = .bvar 3 ∧
    (VExpr.bvar 2).lift' (.consN (.skip (.skip .refl)) ids.length) = .bvar 4 ∧
    (VExpr.bvar 2).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons = .bvar 2 ∧
    (VExpr.bvar 3).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons = .bvar 5 ∧
    (VExpr.bvar 1).lift' (.consN (.skip (.skip .refl)) ids.length) ≠
      (VExpr.bvar 1).lift' (.cons (.skip (.skip .refl))) ∧
    (VExpr.bvar 2).lift' (Lift.consN (.skip (.skip .refl)) ids.length).cons ≠
      (VExpr.bvar 2).lift' (.consN (.skip (.skip .refl)) ids.length) := by
  have pair := exactlyTwoIdentifiersComeFromTheActualArrayPushes array
  subst ids
  have opening := constructActualIndexOpening correspondence reserved
  have secondFresh := actualNewIndexIsFreshInTheBase opening.2.2.1 opening.2.2.2.2.2.reserved
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro equality
    have firstEquality := (List.cons.inj equality).1
    apply secondFresh
    change generated (nextReader reader) ∈ generated reader :: virtual.fvars
    simp [← firstEquality]
  · intro equality
    cases equality
  · intro equality
    cases equality

private theorem twoIndexStageHasDistinctSourceOriginalAndTargetCoordinates :
    twoIndexStageSemantic (.bvar 0) = .forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 6))) ∧
    twoIndexStageSemantic (.bvar 1) = .forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 7))) ∧
    (twoIndexStageSemantic (.bvar 0)).lift' (Lift.consN (.skip .refl) 2).cons =
      twoIndexStageSemantic (.bvar 1) ∧
    (twoIndexStageSemantic (.bvar 0)).lift' (Lift.consN (.skip (.skip .refl)) 2).cons =
      .forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 8))) ∧
    (twoIndexStageSemantic (.bvar 0)).inst (.bvar 2) =
      .forallE (.bvar 2) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 5))) ∧
    (twoIndexStageSemantic (.bvar 1)).inst (.bvar 3) =
      .forallE (.bvar 3) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 6))) ∧
    ((twoIndexStageSemantic (.bvar 0)).inst (.bvar 2)).lift' (.consN (.skip (.skip .refl)) 2) =
      .forallE (.bvar 4) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 7))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem missingEitherIndexOrTheParameterCannotSupplyTwoIndexStageSupport
    (reader : Context) (identifier : FVarId) (firstDifferent : generated reader ≠ identifier)
    (secondDifferent : generated (nextReader reader) ≠ identifier)
    (indexDifferent : generated (nextReader reader) ≠ generated reader) :
    ¬(twoIndexNativeStageBody reader identifier).FVarsIn (· ∈ [identifier, generated reader]) ∧
    ¬(twoIndexNativeStageBody reader identifier).FVarsIn (· ∈ [identifier, generated (nextReader reader)]) ∧
    ¬(twoIndexNativeStageBody reader identifier).FVarsIn (· ∈ [generated reader, generated (nextReader reader)]) := by
  simp [twoIndexNativeStageBody, FVarsIn, firstDifferent, secondDifferent, indexDifferent,
    Ne.symm firstDifferent, Ne.symm secondDifferent, Ne.symm indexDifferent]

private def dependentInnerType : Expr :=
  .forallE `dependentIndex (.bvar 0) (.sort .zero) .default

private def dependentTwoIndexType : Expr :=
  .forallE `oneIndex (.sort .zero) dependentInnerType .default

private def dependentOpenedType (reader : Context) : Expr :=
  .forallE `dependentIndex (.fvar (generated reader)) (.sort .zero) .default

private def dependentFinalReader (reader : Context) : Context :=
  recursorIndexContext (nextReader reader) `dependentIndex .default (.fvar (generated reader))

private def dependentFinalVirtual (virtual : VLCtx) (reader : Context) : VLCtx :=
  peeledIndexVirtualContext (nextVirtual virtual reader) (generated (nextReader reader))
    (.fvar (generated reader)) (.bvar 0)

private def dependentSecondStep (reader : Context) : BinderStep :=
  { role := .index, name := `dependentIndex, domain := .fvar (generated reader),
    bi := .default, value := .fvar (generated (nextReader reader)) }

private def dependentTwoIndexSteps (reader : Context) : List BinderStep :=
  [oneStep reader, dependentSecondStep reader]

private def dependentNativeStageBody (reader : Context) (identifier : FVarId) : Expr :=
  .forallE `formalUse (.bvar 0)
    (.letE `proofUse (.fvar (generated reader)) (.fvar (generated (nextReader reader)))
      (.fvar identifier) true) .default

private def dependentStageSemantic (argument : VExpr) : VExpr :=
  .forallE (.bvar 0) argument.lift.lift.lift.lift

private def dependentStageLevel : VLevel := .imax .zero .zero

private theorem dependentForallTranslationAndTyping
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {domain : Expr}
    (domainTranslation : TrExprS env universes virtual domain (.bvar 0))
    (domainTyping : env.HasType universes.length virtual.toCtx (.bvar 0) (.sort .zero)) :
    TrExprS env universes virtual (.forallE `dependentIndex domain (.sort .zero) .default)
      (.forallE (.bvar 0) (.sort .zero)) ∧
    env.HasType universes.length virtual.toCtx (.forallE (.bvar 0) (.sort .zero))
      (.sort (.imax .zero (.succ .zero))) := by
  have bodyTyped : env.HasType universes.length ((.bvar 0) :: virtual.toCtx)
      (.sort .zero) (.sort (.succ .zero)) := .sortDF (by trivial) (by trivial) rfl
  exact ⟨.forallE ⟨.zero, domainTyping⟩ ⟨.succ .zero, bodyTyped⟩ domainTranslation
    (.sort (by simp [VLevel.ofLevel])), .forallEDF domainTyping bodyTyped⟩

private theorem constructDependentSecondIndexOpening
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    PeeledIndexOpening env universes (nextReader reader) (nextVirtual virtual reader)
      `dependentIndex (.fvar (generated reader)) (.sort .zero) .default
      (.bvar 0) (.sort .zero) .zero (.bvar 0) := by
  have first := constructActualIndexOpening correspondence reserved
  have domainTranslation : TrExprS env universes (nextVirtual virtual reader)
      (.fvar (generated reader)) (.bvar 0) :=
    .fvar (A := .sort .zero) (by simp [nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN])
  have domainTyping : env.HasType universes.length (nextVirtual virtual reader).toCtx
      (.bvar 0) (.sort .zero) := .bvar .zero
  have pushed := translatedIndexContextPush (name := `dependentIndex) (bi := .default)
    (domain := .fvar (generated reader)) first.2.2.1 first.2.2.2.2.2.reserved
    domainTranslation domainTyping
  have opened : TrExpr env universes (dependentFinalVirtual virtual reader)
      ((Expr.sort .zero).instantiate1 (.fvar (generated (nextReader reader)))) (.sort .zero) := by
    rw [Expr.instantiate1_eq]
    exact ⟨.sort .zero, .sort (by simp [VLevel.ofLevel]),
      (show env.HasType universes.length (dependentFinalVirtual virtual reader).toCtx
        (.sort .zero) (.sort (.succ .zero)) from .sortDF (by trivial) (by trivial) rfl).toU⟩
  exact ⟨domainTranslation, domainTyping, pushed, opened,
    newlyAllocatedBinderPositioned (nextReader reader) `dependentIndex (.fvar (generated reader))
      .default first.2.2.1.1 first.2.2.2.2.2.reserved,
    Context.RecursorScopeFrame.push (nextReader reader) first.2.2.1.1 first.2.2.2.2.2.reserved
      `dependentIndex .default (.fvar (generated reader))⟩

private theorem constructDependentFirstIndexOpening
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    PeeledIndexOpening env universes reader virtual `oneIndex (.sort .zero) dependentInnerType
      .default (.sort .zero) (.forallE (.bvar 0) (.sort .zero)) (.succ .zero) (.sort .zero) := by
  have first := constructActualIndexOpening correspondence reserved
  have second := constructDependentSecondIndexOpening correspondence reserved
  have translated := dependentForallTranslationAndTyping second.1 second.2.1
  refine ⟨first.1, first.2.1, first.2.2.1, ?_, first.2.2.2.2.1, first.2.2.2.2.2⟩
  rw [Expr.instantiate1_eq]
  exact ⟨_, translated.1, translated.2.toU⟩

private theorem dependentNativeNormalizationsWithPositiveDepth
    (reader : Context) (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    ((monadLift (TypeChecker.whnf (dependentInnerType.instantiate1 (.fvar (generated reader)))) : M Expr)
      (nextReader reader)) = .ok (dependentOpenedType reader) ∧
    ((monadLift (TypeChecker.whnf ((Expr.sort .zero).instantiate1
      (.fvar (generated (nextReader reader))))) : M Expr)
      (dependentFinalReader reader)) = .ok (.sort .zero) := by
  constructor
  · rw [Expr.instantiate1_eq]
    change (Prod.fst <$> (TypeChecker.Methods.withFuel reader.fuel.recDepth).whnf (dependentOpenedType reader)
      { env := reader.env, safety := reader.safety, lctx := (nextReader reader).lctx,
        lparams := reader.lparams, fuel := reader.fuel } {}) = .ok (dependentOpenedType reader)
    rw [positive]
    rfl
  · rw [Expr.instantiate1_eq]
    change (Prod.fst <$> (TypeChecker.Methods.withFuel reader.fuel.recDepth).whnf (.sort .zero)
      { env := reader.env, safety := reader.safety, lctx := (dependentFinalReader reader).lctx,
        lparams := reader.lparams, fuel := reader.fuel } {}) = .ok (.sort .zero)
    rw [positive]
    rfl

private theorem constructGenuineDependentTwoStepHistory
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {reader : Context} {virtual : VLCtx}
    (parametersEmpty : stats.params.size = 0)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (depth : Nat) (positive : reader.fuel.recDepth = depth + 1) :
    ∃ trace : RecursorIndexTrace stats dependentTwoIndexType 0 #[] reader (.sort .zero) 0
      (twoIndexArray reader) (dependentFinalReader reader),
      TranslatedRecursorIndexTrace env universes trace virtual
        (.forallE (.sort .zero) (.forallE (.bvar 0) (.sort .zero)))
        (dependentFinalVirtual virtual reader) (.sort .zero) := by
  have firstOpening := constructDependentFirstIndexOpening correspondence reserved
  have secondOpening := constructDependentSecondIndexOpening correspondence reserved
  have normalized := dependentNativeNormalizationsWithPositiveDepth reader depth positive
  have notParameter : ¬0 < stats.params.size := by simp [parametersEmpty]
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  have stopped := RecursorIndexTrace.stop (stats := stats) (index := 0)
    (indices := twoIndexArray reader) (ctx := dependentFinalReader reader) notForall
  have second := RecursorIndexTrace.index (stats := stats) (name := `dependentIndex)
    (domain := .fvar (generated reader)) (body := .sort .zero) (bi := .default) (index := 0)
    (indices := #[].push (.fvar (generated reader))) (ctx := nextReader reader)
    notParameter normalized.2 stopped
  have stoppedTranslated := TranslatedRecursorIndexTrace.stop (stats := stats)
    (index := 0) (indices := twoIndexArray reader) notForall secondOpening.2.2.1
    (TrExprS.sort (u' := .zero) (by simp [VLevel.ofLevel]))
  have openedTranslated := dependentForallTranslationAndTyping secondOpening.1 secondOpening.2.1
  have secondTranslated := TranslatedRecursorIndexTrace.index (name := `dependentIndex)
    (domain := .fvar (generated reader)) (body := .sort .zero) (bi := .default) (reader := nextReader reader)
    (index := 0) (indices := #[].push (.fvar (generated reader)))
    notParameter normalized.2 stopped openedTranslated.1 secondOpening
    (.sort (by simp [VLevel.ofLevel]))
    (show env.HasType universes.length (dependentFinalVirtual virtual reader).toCtx
      (.sort .zero) (.sort (.succ .zero)) from .sortDF (by trivial) (by trivial) rfl).toU stoppedTranslated
  have innerTranslated := dependentForallTranslationAndTyping
    (TrExprS.bvar (env := env) (Us := universes) (i := 0)
      (Δ := (none, .vlam (.sort .zero)) :: virtual) (A := .sort .zero) rfl)
    (show env.HasType universes.length ((.sort .zero) :: virtual.toCtx)
      (.bvar 0) (.sort .zero) from .bvar .zero)
  have translated : TrExprS env universes virtual dependentTwoIndexType
      (.forallE (.sort .zero) (.forallE (.bvar 0) (.sort .zero))) :=
    .forallE ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      ⟨.imax .zero (.succ .zero), innerTranslated.2⟩
      (.sort (by simp [VLevel.ofLevel])) innerTranslated.1
  refine ⟨.index notParameter normalized.1 second, ?_⟩
  exact .index (name := `oneIndex) (domain := .sort .zero) (body := dependentInnerType)
    (bi := .default) (reader := reader) (index := 0) (indices := #[])
    notParameter normalized.1 second translated firstOpening openedTranslated.1
    openedTranslated.2.toU secondTranslated

private theorem dependentActualStoredDomainsAreSupported
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (identifier : FVarId) :
    BinderStoredIndexTypeFVarsIn [identifier] (dependentFinalReader reader) (dependentTwoIndexSteps reader) := by
  have first := constructDependentFirstIndexOpening correspondence reserved
  have second := constructDependentSecondIndexOpening correspondence reserved
  have firstDeclared := first.2.2.2.2.1.declared.mono first.2.2.1.1 second.2.2.2.2.2
  have declared : BinderStepsIndexDeclared (dependentFinalReader reader) (dependentTwoIndexSteps reader) := by
    intro step member role
    have alternatives : step = oneStep reader ∨ step = dependentSecondStep reader := by
      simpa [dependentTwoIndexSteps] using member
    rcases alternatives with equality | equality
    · subst step
      exact firstDeclared
    · subst step
      exact second.2.2.2.2.1.declared
  have raw : BinderRawDomainFVarsIn [identifier] (dependentTwoIndexSteps reader) := by
    intro position step selected
    cases position with
    | zero =>
      have equality : oneStep reader = step := Option.some.inj selected
      subst step
      trivial
    | succ position =>
      cases position with
      | zero =>
        have equality : dependentSecondStep reader = step := Option.some.inj selected
        subst step
        simp [dependentTwoIndexSteps, dependentSecondStep, oneStep, BinderStep.indexValues, FVarsIn, Expr.fvarId!]
      | succ position => simp [dependentTwoIndexSteps] at selected
  exact raw.storedIndexTypeFVarsIn declared

private theorem dependentActualStoredDeclarationsExposeTheEarlierIndex
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ first second : LocalDecl,
      (dependentFinalReader reader).lctx.find? (generated reader) = some first ∧
      first.type = .sort .zero ∧
      (dependentFinalReader reader).lctx.find? (generated (nextReader reader)) = some second ∧
      second.type = .fvar (generated reader) := by
  have first := constructDependentFirstIndexOpening correspondence reserved
  have second := constructDependentSecondIndexOpening correspondence reserved
  obtain ⟨firstDecl, firstLookup, _, firstType, _, _⟩ := first.2.2.2.2.1.declared.mono
    first.2.2.1.1 second.2.2.2.2.2
  obtain ⟨secondDecl, secondLookup, _, secondType, _, _⟩ := second.2.2.2.2.1.declared
  exact ⟨firstDecl, secondDecl, firstLookup, firstType, secondLookup, secondType⟩

private theorem translatedDependentStageUsesTheProofValuedSecondIndex
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    (envWF : env.WF) (virtualWF : virtual.WF env universes.length)
    (identifier : FVarId) (firstDifferent : generated reader ≠ identifier)
    (secondDifferent : generated (nextReader reader) ≠ identifier)
    (indexDifferent : generated (nextReader reader) ≠ generated reader) {argument : VExpr}
    (lookup : virtual.find? (.inr identifier) = some (argument, .sort .zero)) :
    TrExprS env universes ((none, .vlam (.sort .zero)) :: dependentFinalVirtual virtual reader)
      (dependentNativeStageBody reader identifier) (dependentStageSemantic argument) ∧
    env.HasType universes.length ((.sort .zero) :: (dependentFinalVirtual virtual reader).toCtx)
      (dependentStageSemantic argument) (.sort dependentStageLevel) := by
  have argumentTyped := virtualWF.find?_wf envWF.ordered lookup
  have raisedTyped : env.HasType universes.length
      (.bvar 0 :: .sort .zero :: .bvar 0 :: .sort .zero :: virtual.toCtx)
      argument.lift.lift.lift.lift (.sort .zero) :=
    (((argumentTyped.weak envWF.ordered).weak envWF.ordered).weak envWF.ordered).weak envWF.ordered
  have proofTyped : env.HasType universes.length
      (.bvar 0 :: .sort .zero :: (dependentFinalVirtual virtual reader).toCtx) (.bvar 2) (.bvar 3) :=
    .bvar (.succ (.succ .zero))
  have finalLookup :
      VLCtx.find? ((none, .vlet (.bvar 3) (.bvar 2)) :: (none, .vlam (.bvar 0)) ::
        (none, .vlam (.sort .zero)) :: dependentFinalVirtual virtual reader) (.inr identifier) =
      some (argument.lift.lift.lift.lift, .sort .zero) := by
    simp [dependentFinalVirtual, nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
      firstDifferent, secondDifferent, lookup, VLocalDecl.depth, VExpr.liftN, VExpr.lift]
  refine ⟨?_, .forallEDF (.bvar .zero) raisedTyped⟩
  exact .forallE ⟨.zero, .bvar .zero⟩ ⟨.zero, raisedTyped⟩ (.bvar rfl)
    (.letE proofTyped
      (.fvar (A := .sort .zero) (by simp [dependentFinalVirtual, nextVirtual,
        peeledIndexVirtualContext, VLCtx.find?, VLCtx.next, indexDifferent,
        VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, VExpr.liftN, VExpr.lift]))
      (.fvar (A := .bvar 3) (by simp [dependentFinalVirtual, peeledIndexVirtualContext,
        VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type,
        VLocalDecl.depth, VExpr.liftN, VExpr.lift]))
      (.fvar finalLookup))

private theorem dependentStageBodyClosedAndSupported
    (reader : Context) (identifier : FVarId) (base : List FVarId) (member : identifier ∈ base) :
    Closed (dependentNativeStageBody reader identifier) 1 ∧
    ¬Closed (dependentNativeStageBody reader identifier) 0 ∧
    (dependentNativeStageBody reader identifier).FVarsIn
      (· ∈ generated (nextReader reader) :: generated reader :: base) := by
  simp [dependentNativeStageBody, Closed, FVarsIn, member]

private theorem dependentStoredDomainRequiresTheEarlierIndex
    (reader : Context) (identifier : FVarId) (different : generated reader ≠ identifier) :
    (dependentSecondStep reader).domain.FVarsIn (· ∈ [generated reader]) ∧
    ¬(dependentSecondStep reader).domain.FVarsIn (· ∈ [identifier]) ∧
    ¬BinderRawDomainFVarsIn [identifier] [dependentSecondStep reader, oneStep reader] := by
  refine ⟨by simp [dependentSecondStep, FVarsIn], by simp [dependentSecondStep, FVarsIn, different], ?_⟩
  intro reversed
  have unsupported := reversed 0 (dependentSecondStep reader) rfl
  simp [dependentSecondStep, BinderStep.indexValues, FVarsIn, different] at unsupported

private theorem genuineDependentTwoStepHistoryRebasesConstructedMixedBases
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
    let finalReader := dependentFinalReader actualReader
    ∃ (chronological reduced target : MLCtx) (reducedArgument reducedDomain reducedBody : VExpr),
      chronological.vlctx = dependentFinalVirtual original.vlctx actualReader ∧
      SelectedRecursorTelescope env universes finalReader.lctx smaller
        [generated actualReader, generated (nextReader actualReader)] reduced ∧
      SelectedRecursorTelescope env universes finalReader.lctx larger
        [generated actualReader, generated (nextReader actualReader)] target ∧
      reduced.vlctx.fvars = generated (nextReader actualReader) :: generated actualReader :: smaller.vlctx.fvars ∧
      target.vlctx.fvars = generated (nextReader actualReader) :: generated actualReader :: larger.vlctx.fvars ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0 (.consN (.skip (.skip .refl)) 2) 0 ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx)
        (dependentNativeStageBody actualReader (generated reader)) reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx) reducedBody (.sort dependentStageLevel) ∧
      TrExprS env universes reduced.vlctx
        ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort dependentStageLevel) ∧
      TrExprS env universes target.vlctx
        ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        ((reducedBody.lift' (Lift.consN (.skip (.skip .refl)) 2).cons).inst
          (reducedArgument.lift' (.consN (.skip (.skip .refl)) 2))) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.lift' (Lift.consN (.skip (.skip .refl)) 2).cons).inst
          (reducedArgument.lift' (.consN (.skip (.skip .refl)) 2))) (.sort dependentStageLevel) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.inst reducedArgument).lift' (.consN (.skip (.skip .refl)) 2)) (.sort dependentStageLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        ((dependentStageSemantic (.bvar 1)).inst (.bvar 3))
        ((reducedBody.inst reducedArgument).lift' (.consN (.skip .refl) 2)) (.sort dependentStageLevel) ∧
      Closed ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))) 0 ∧
      ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))).FVarsIn
        (· ∈ reduced.vlctx.fvars) := by
  let smaller := pushSortModel seed reader
  let baseReader := nextReader reader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  have retained := pushSortModelIsWellFormed seed seedWF reader native reserved
  have mixed := constructedMixedBasesAreWellFormed smaller retained.1 baseReader retained.2.1 retained.2.2
  have weakenings := constructedMixedBaseWeakenings smaller baseReader
  have correspondence : TrLCtx env universes actualReader.lctx original.vlctx := by
    simpa only [mixed.2.1] using mixed.1.tr
  obtain ⟨trace, history⟩ := constructGenuineDependentTwoStepHistory parametersEmpty correspondence
    mixed.2.2.1 depth positive
  have secondOpening := constructDependentSecondIndexOpening correspondence mixed.2.2.1
  have originalLookup : original.vlctx.find? (.inr (generated reader)) = some (.bvar 1, .sort .zero) := by
    have fresh := mixed.1.tr.wf.2.1 (generated (advanceReaderTwice baseReader)) [] rfl
    have different : generated (advanceReaderTwice baseReader) ≠ generated reader := by
      intro equality
      apply fresh.1
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars, ← equality]
    have lookup : smaller.vlctx.find? (.inr (generated reader)) = some (.bvar 0, .sort .zero) := by
      simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN]
    exact selectedLookupSurvivesTheActualIndexPush different lookup
  have member : generated reader ∈ smaller.vlctx.fvars := by
    simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars]
  have originalMember : generated reader ∈ original.vlctx.fvars := by
    change generated reader ∈ generated (advanceReaderTwice baseReader) :: smaller.vlctx.fvars
    exact List.mem_cons_of_mem _ member
  have different := twoFreshIndexNamesAreDistinctFromTheRetainedParameter correspondence mixed.2.2.1
    (generated reader) originalMember
  have finalLookup : (dependentFinalVirtual original.vlctx actualReader).find? (.inr (generated reader)) =
      some (.bvar 3, .sort .zero) := by
    simp [dependentFinalVirtual, nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
      different.1, different.2.1, originalLookup, VLocalDecl.depth, VExpr.liftN]
  have stageReceipts := translatedDependentStageUsesTheProofValuedSecondIndex envWF mixed.1.tr.wf
    (generated reader) different.1 different.2.1 different.2.2 originalLookup
  have closedSupport := dependentStageBodyClosedAndSupported actualReader (generated reader) smaller.vlctx.fvars member
  have secondFresh := theSecondActualIndexIsFreshInTheIndependentLargerBase smaller retained.1 baseReader
    retained.2.1 retained.2.2
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, reducedDomain, _, reducedBody,
    _, _, chronologicalConverted, _, array, reducedTelescope, _, _, _, targetTelescope,
    _, insertionWeakening, _, _, _, _, _, _, _, _, _, _, reducedBodyTranslation, reducedBodyTyping, _, _,
    sourceTyping, endpointEquality, _, _, _, targetTyping, substitutedClosed, substitutedSupport,
    _, sourceTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains original mixed.1 mixed.2.1 rfl mixed.2.2.1
      (dependentFinalReader actualReader) (.refl _ secondOpening.2.2.1.1 secondOpening.2.2.2.2.2.reserved) envWF
      smaller retained.1 (.skip .refl) weakenings.1
      (dependentActualStoredDomainsAreSupported correspondence mixed.2.2.1 (generated reader))
      (by simp [dependentTwoIndexSteps, dependentSecondStep, twoIndexArray, oneStep, BinderStep.indexValues])
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      (by simp) larger mixed.2.2.2.1 2 weakenings.2
      (by intro candidate selected
          have alternatives : candidate = generated actualReader ∨ candidate = generated (nextReader actualReader) := by
            simpa [twoIndexArray] using selected
          rcases alternatives with equality | equality
          · simpa only [equality] using mixed.2.2.2.2
          · simpa only [equality] using secondFresh)
      0 (generated reader) rfl finalLookup stageReceipts.1 stageReceipts.2 closedSupport.1
      (by simpa [twoIndexArray] using closedSupport.2.2)
  have idsPair := exactlyTwoIdentifiersComeFromTheActualArrayPushes array
  subst ids
  refine ⟨chronological, reduced, target, reducedArgument, reducedDomain, reducedBody,
    chronologicalConverted, reducedTelescope, targetTelescope, ?_, ?_, insertionWeakening,
    reducedBodyTranslation, reducedBodyTyping, sourceTranslation, sourceTyping, targetTranslation,
    targetTyping, ?_, endpointEquality, substitutedClosed, substitutedSupport⟩
  · simpa using reducedTelescope.extension.virtualFVars
  · simpa using targetTelescope.extension.virtualFVars
  · simpa only [VExpr.lift'_inst_hi] using targetTyping

private theorem dependentVirtualLookupsDistinguishATypeFromItsProof
    (virtual : VLCtx) (reader : Context)
    (different : generated (nextReader reader) ≠ generated reader) :
    (dependentFinalVirtual virtual reader).find? (.inr (generated reader)) =
      some (.bvar 1, .sort .zero) ∧
    (dependentFinalVirtual virtual reader).find? (.inr (generated (nextReader reader))) =
      some (.bvar 0, .bvar 1) := by
  simp [dependentFinalVirtual, nextVirtual, peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
    different, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth, VExpr.liftN, VExpr.lift]

private theorem dependentStageHasDistinctSourceOriginalAndTargetCoordinates :
    dependentStageSemantic (.bvar 0) = .forallE (.bvar 0) (.bvar 4) ∧
    dependentStageSemantic (.bvar 1) = .forallE (.bvar 0) (.bvar 5) ∧
    (dependentStageSemantic (.bvar 0)).lift' (Lift.consN (.skip .refl) 2).cons =
      dependentStageSemantic (.bvar 1) ∧
    (dependentStageSemantic (.bvar 0)).lift' (Lift.consN (.skip (.skip .refl)) 2).cons =
      .forallE (.bvar 0) (.bvar 6) ∧
    (dependentStageSemantic (.bvar 0)).inst (.bvar 2) = .forallE (.bvar 2) (.bvar 3) ∧
    (dependentStageSemantic (.bvar 1)).inst (.bvar 3) = .forallE (.bvar 3) (.bvar 4) ∧
    ((dependentStageSemantic (.bvar 0)).inst (.bvar 2)).lift' (.consN (.skip (.skip .refl)) 2) =
      .forallE (.bvar 4) (.bvar 5) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem missingEitherIndexOrParameterCannotSupportTheDependentLet
    (reader : Context) (identifier : FVarId) (firstDifferent : generated reader ≠ identifier)
    (secondDifferent : generated (nextReader reader) ≠ identifier)
    (indexDifferent : generated (nextReader reader) ≠ generated reader) :
    ¬(dependentNativeStageBody reader identifier).FVarsIn (· ∈ [identifier, generated reader]) ∧
    ¬(dependentNativeStageBody reader identifier).FVarsIn (· ∈ [identifier, generated (nextReader reader)]) ∧
    ¬(dependentNativeStageBody reader identifier).FVarsIn (· ∈ [generated reader, generated (nextReader reader)]) := by
  simp [dependentNativeStageBody, FVarsIn, firstDifferent, secondDifferent, indexDifferent,
    Ne.symm firstDifferent, Ne.symm secondDifferent, Ne.symm indexDifferent]

private theorem dependentStageSubstitutionPreservesTheProofsActualType
    (reader : Context) (identifier : FVarId) :
    (dependentNativeStageBody reader identifier).instantiate1' (.fvar identifier) =
      .forallE `formalUse (.fvar identifier)
        (.letE `proofUse (.fvar (generated reader)) (.fvar (generated (nextReader reader)))
          (.fvar identifier) true) .default := rfl

private def dependentSeedReader : Context :=
  { env := Lean.Kernel.Environment.empty `DependentStageFixture, lparams := [],
    safety := .safe, allowPrimitive := false, fuel := { recDepth := 1 } }

private def noParameterStats : InductiveStats :=
  { levels := [], resultLevel := .zero, indConsts := #[], params := #[], isNotZero := false }

private theorem emptySeedExercisesTheDependentAdapterWithoutFixturePremises :
    let reader := dependentSeedReader
    let actualReader := originalMixedReader (nextReader reader)
    ∃ (reduced target : MLCtx) (reducedArgument reducedDomain reducedBody : VExpr),
      TrExprS VEnv.empty [] ((none, .vlam reducedDomain) :: reduced.vlctx)
        (dependentNativeStageBody actualReader (generated reader)) reducedBody ∧
      TrExprS VEnv.empty [] reduced.vlctx
        ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        (reducedBody.inst reducedArgument) ∧
      VEnv.empty.HasType 0 reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort dependentStageLevel) ∧
      TrExprS VEnv.empty [] target.vlctx
        ((dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader)))
        ((reducedBody.lift' (Lift.consN (.skip (.skip .refl)) 2).cons).inst
          (reducedArgument.lift' (.consN (.skip (.skip .refl)) 2))) ∧
      VEnv.empty.HasType 0 target.vlctx.toCtx
        ((reducedBody.inst reducedArgument).lift' (.consN (.skip (.skip .refl)) 2)) (.sort dependentStageLevel) := by
  obtain ⟨_, reduced, target, argument, domain, body, _, _, _, _, _, _, translated,
    _, sourceTranslated, sourceTyped, targetTranslated, _, targetTyped, _, _, _⟩ :=
    genuineDependentTwoStepHistoryRebasesConstructedMixedBases (env := VEnv.empty) (universes := [])
      (stats := noParameterStats) rfl .nil trivial dependentSeedReader rfl
      (ContextReserved.empty _) ⟨[], .empty⟩ 0 rfl
  exact ⟨reduced, target, argument, domain, body, translated, sourceTranslated, sourceTyped,
    targetTranslated, targetTyped⟩

private def nativeDependentStageTelescope : Expr :=
  let actualReader := originalMixedReader (nextReader dependentSeedReader)
  (dependentFinalReader actualReader).lctx.mkForall (twoIndexArray actualReader)
    ((dependentNativeStageBody actualReader (generated dependentSeedReader)).instantiate1
      (.fvar (generated dependentSeedReader)))

private theorem actualDependentStageReconstructsOneNativeTelescopeInThreeBases :
    let reader := dependentSeedReader
    let smaller := pushSortModel .nil reader
    let original := removedMixedBase smaller (nextReader reader)
    let larger := insertedMixedBase smaller (nextReader reader)
    let actualReader := originalMixedReader (nextReader reader)
    let endpoint := (dependentNativeStageBody actualReader (generated reader)).instantiate1 (.fvar (generated reader))
    ∃ (reduced target : MLCtx) (originalSemantic sourceSemantic targetSemantic : VExpr),
      (dependentFinalReader actualReader).lctx.BindingScope ∧ reduced.lctx.BindingScope ∧
      target.lctx.BindingScope ∧ endpoint.looseBVarRange' = 0 ∧
      nativeDependentStageTelescope = reduced.lctx.mkForall (twoIndexArray actualReader) endpoint ∧
      nativeDependentStageTelescope = target.lctx.mkForall (twoIndexArray actualReader) endpoint ∧
      TrExprS VEnv.empty [] original.vlctx nativeDependentStageTelescope originalSemantic ∧
      VEnv.empty.IsType 0 original.vlctx.toCtx originalSemantic ∧
      TrExprS VEnv.empty [] smaller.vlctx nativeDependentStageTelescope sourceSemantic ∧
      VEnv.empty.IsType 0 smaller.vlctx.toCtx sourceSemantic ∧
      TrExprS VEnv.empty [] larger.vlctx nativeDependentStageTelescope targetSemantic ∧
      VEnv.empty.IsType 0 larger.vlctx.toCtx targetSemantic ∧
      VEnv.empty.IsDefEqU 0 original.vlctx.toCtx originalSemantic (sourceSemantic.lift' (.skip .refl)) ∧
      VEnv.empty.IsDefEqU 0 larger.vlctx.toCtx (sourceSemantic.lift' (.skip (.skip .refl))) targetSemantic := by
  let reader := dependentSeedReader
  let smaller := pushSortModel .nil reader
  let baseReader := nextReader reader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  have envWF : VEnv.empty.WF := ⟨[], .empty⟩
  have retained := pushSortModelIsWellFormed (env := VEnv.empty) (universes := [])
    .nil trivial reader rfl (ContextReserved.empty _)
  have mixed := constructedMixedBasesAreWellFormed smaller retained.1 baseReader retained.2.1 retained.2.2
  have weakenings := constructedMixedBaseWeakenings smaller baseReader
  have correspondence : TrLCtx VEnv.empty [] actualReader.lctx original.vlctx := by
    simpa only [mixed.2.1] using mixed.1.tr
  obtain ⟨trace, history⟩ := constructGenuineDependentTwoStepHistory (stats := noParameterStats)
    rfl correspondence mixed.2.2.1 0 rfl
  have originalLookup : original.vlctx.find? (.inr (generated reader)) = some (.bvar 1, .sort .zero) := rfl
  have finalLookup : (dependentFinalVirtual original.vlctx actualReader).find? (.inr (generated reader)) =
      some (.bvar 3, .sort .zero) := rfl
  have member : generated reader ∈ smaller.vlctx.fvars := by
    simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars]
  have originalMember : generated reader ∈ original.vlctx.fvars := by
    change generated reader ∈ generated (advanceReaderTwice baseReader) :: smaller.vlctx.fvars
    exact List.mem_cons_of_mem _ member
  have different := twoFreshIndexNamesAreDistinctFromTheRetainedParameter correspondence mixed.2.2.1
    (generated reader) originalMember
  have stageReceipts := translatedDependentStageUsesTheProofValuedSecondIndex envWF mixed.1.tr.wf
    (generated reader) different.1 different.2.1 different.2.2 originalLookup
  have closedSupport := dependentStageBodyClosedAndSupported actualReader (generated reader) smaller.vlctx.fvars member
  have secondFresh := theSecondActualIndexIsFreshInTheIndependentLargerBase smaller retained.1 baseReader
    retained.2.1 retained.2.2
  obtain ⟨chronological, ids, reduced, target, argument, stageBody, extension, reducedTelescope, targetTelescope,
    chronologicalWF, chronologicalNative, chronologicalVirtual, array, reducedWF, targetWF,
    sourceTranslation, sourceTyped, targetTranslation, targetTyped, endpointEquality,
    fullScope, reducedScope, targetScope, endpointScope, sourceBinding, targetBinding,
    originalAbstracted, originalAbstractedTyped, sourceAbstracted, sourceAbstractedTyped,
    targetAbstracted, targetAbstractedTyped, originalAgreement, targetAgreement⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageNativeForall original mixed.1 mixed.2.1 rfl
      mixed.2.2.1 envWF smaller retained.1 (.skip .refl) weakenings.1
      (dependentActualStoredDomainsAreSupported correspondence mixed.2.2.1 (generated reader))
      (by simp [dependentTwoIndexSteps, dependentSecondStep, twoIndexArray, oneStep, BinderStep.indexValues])
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      (by simp) larger mixed.2.2.2.1 2 weakenings.2
      (by intro candidate selected
          have alternatives : candidate = generated actualReader ∨ candidate = generated (nextReader actualReader) := by
            simpa [twoIndexArray] using selected
          rcases alternatives with equality | equality
          · simpa only [equality] using mixed.2.2.2.2
          · simpa only [equality] using secondFresh)
      0 (generated reader) rfl finalLookup stageReceipts.1 stageReceipts.2 closedSupport.1
      (by simpa [twoIndexArray] using closedSupport.2.2)
  have idsPair := exactlyTwoIdentifiersComeFromTheActualArrayPushes array
  subst ids
  refine ⟨reduced, target, _, _, _, fullScope, reducedScope, targetScope, endpointScope,
    ?_, ?_, ?_, originalAbstractedTyped, ?_, sourceAbstractedTyped, ?_, targetAbstractedTyped,
    originalAgreement, targetAgreement⟩
  · exact sourceBinding
  · exact targetBinding
  · exact originalAbstracted
  · exact sourceAbstracted
  · exact targetAbstracted

private theorem emptySelectedTelescopeBindingAddsNoSemanticBinder
    {env : VEnv} {universes : List Name} {model : MLCtx} {body : Expr} {semantic : VExpr}
    (envWF : env.WF) (modelWF : model.WF env universes)
    (translated : TrExprS env universes model.vlctx body semantic)
    (typed : env.IsType universes.length model.vlctx.toCtx semantic) :
    TrExprS env universes model.vlctx (model.lctx.mkForall #[] body) semantic ∧
      env.IsType universes.length model.vlctx.toCtx semantic := by
  have telescope : SelectedRecursorTelescope env universes model.lctx model [] model := .nil
  exact (telescope.scopedTypedAbstractionS envWF modelWF modelWF.bindingScope translated typed).2

private theorem existingIndexPrefixIsNotBoundByAnEmptyActualHistory :
    let reader := dependentSeedReader
    let smaller := pushSortModel .nil reader
    let original := removedMixedBase smaller (nextReader reader)
    let larger := insertedMixedBase smaller (nextReader reader)
    let actualReader := originalMixedReader (nextReader reader)
    let endpoint := (Expr.bvar 0).instantiate1 (.fvar (generated reader))
    ∃ (originalSemantic sourceSemantic targetSemantic : VExpr),
      actualReader.lctx.mkForall #[] endpoint = endpoint ∧
      TrExprS VEnv.empty [] original.vlctx endpoint originalSemantic ∧
      VEnv.empty.IsType 0 original.vlctx.toCtx originalSemantic ∧
      TrExprS VEnv.empty [] smaller.vlctx endpoint sourceSemantic ∧
      VEnv.empty.IsType 0 smaller.vlctx.toCtx sourceSemantic ∧
      TrExprS VEnv.empty [] larger.vlctx endpoint targetSemantic ∧
      VEnv.empty.IsType 0 larger.vlctx.toCtx targetSemantic ∧
      VEnv.empty.IsDefEqU 0 original.vlctx.toCtx originalSemantic (sourceSemantic.lift' (.skip .refl)) ∧
      VEnv.empty.IsDefEqU 0 larger.vlctx.toCtx (sourceSemantic.lift' (.skip (.skip .refl))) targetSemantic := by
  let reader := dependentSeedReader
  let smaller := pushSortModel .nil reader
  let baseReader := nextReader reader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  have envWF : VEnv.empty.WF := ⟨[], .empty⟩
  have retained := pushSortModelIsWellFormed (env := VEnv.empty) (universes := [])
    .nil trivial reader rfl (ContextReserved.empty _)
  have mixed := constructedMixedBasesAreWellFormed smaller retained.1 baseReader retained.2.1 retained.2.2
  have weakenings := constructedMixedBaseWeakenings smaller baseReader
  have correspondence : TrLCtx VEnv.empty [] actualReader.lctx original.vlctx := by
    simpa only [mixed.2.1] using mixed.1.tr
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  let trace := RecursorIndexTrace.stop (stats := noParameterStats) (index := 0)
    (indices := #[.fvar (generated reader)]) (ctx := actualReader) notForall
  have history : TranslatedRecursorIndexTrace VEnv.empty [] trace original.vlctx
      (.sort .zero) original.vlctx (.sort .zero) :=
    .stop notForall correspondence (.sort (by simp [VLevel.ofLevel]))
  have member : generated reader ∈ smaller.vlctx.fvars := by
    simp [smaller, pushSortModel, MLCtx.vlctx, VLCtx.fvars]
  have nativeLookup : actualReader.lctx.find? (generated reader) =
      some (.cdecl 0 (generated reader) `oneIndex (.sort .zero) .default .default) := by
    rw [← mixed.2.1, mixed.1.find?_eq]
    rfl
  have stored : BinderStoredIndexTypeFVarsIn [generated reader] actualReader [oneStep reader] := by
    intro position step declaration selected role lookup
    cases position with
    | zero =>
      have equality : oneStep reader = step := Option.some.inj selected
      subst step
      have equality : LocalDecl.cdecl 0 (generated reader) `oneIndex (.sort .zero) .default .default = declaration :=
        Option.some.inj (nativeLookup.symm.trans lookup)
      subst declaration
      trivial
    | succ position => simp at selected
  have originalLookup : original.vlctx.find? (.inr (generated reader)) = some (.bvar 1, .sort .zero) := rfl
  obtain ⟨chronological, ids, reduced, target, argument, stageBody, extension, reducedTelescope, targetTelescope,
    chronologicalWF, chronologicalNative, chronologicalVirtual, array, reducedWF, targetWF,
    sourceTranslation, sourceTyped, targetTranslation, targetTyped, endpointEquality,
    fullScope, reducedScope, targetScope, endpointScope, sourceBinding, targetBinding,
    originalAbstracted, originalAbstractedTyped, sourceAbstracted, sourceAbstractedTyped,
    targetAbstracted, targetAbstractedTyped, originalAgreement, targetAgreement⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageNativeForall original mixed.1 mixed.2.1 rfl
      mixed.2.2.1 envWF smaller retained.1 (.skip .refl) weakenings.1 stored rfl
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      (by intro candidate selected
          have equality : candidate = generated reader := by simpa using selected
          simpa only [equality] using member)
      larger mixed.2.2.2.1 2 weakenings.2 (by intro candidate selected; simp at selected)
      0 (generated reader) rfl originalLookup
      (TrExprS.bvar (i := 0) (A := .sort .zero) rfl)
      (show VEnv.empty.HasType 0 (.sort .zero :: original.vlctx.toCtx)
        (.bvar 0) (.sort .zero) from .bvar .zero) (by simp [Closed]) (by trivial)
  have idsEmpty : ids = [] := by simpa using array
  subst ids
  have nativeIdentity : actualReader.lctx.mkForall #[] ((Expr.bvar 0).instantiate1 (.fvar (generated reader))) =
      (Expr.bvar 0).instantiate1 (.fvar (generated reader)) :=
    sourceBinding.trans (reducedTelescope.extension.nativeBodyAbstraction reducedWF endpointScope)
  exact ⟨_, _, _, nativeIdentity, nativeIdentity ▸ originalAbstracted, originalAbstractedTyped,
    nativeIdentity ▸ sourceAbstracted, sourceAbstractedTyped, nativeIdentity ▸ targetAbstracted, targetAbstractedTyped,
    originalAgreement, targetAgreement⟩

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

private def twoIndexRuntimeControls : MetaM Unit := do
  let first : FVarId := ⟨`TwoStepFirstActualPushIndex⟩
  let second : FVarId := ⟨`TwoStepSecondActualPushIndex⟩
  let parameter : FVarId := ⟨`TwoStepRetainedParameter⟩
  let pushed : Array Expr := (#[].push (.fvar first)).push (.fvar second)
  let removal : Lift := .consN (.skip .refl) pushed.size
  let insertion : Lift := .consN (.skip (.skip .refl)) pushed.size
  let sourceBody := twoIndexStageSemantic (.bvar 0)
  let originalBody := twoIndexStageSemantic (.bvar 1)
  let nativeBody := Expr.forallE `formalUse (.bvar 0)
    (.forallE `firstIndexUse (.fvar first)
      (.forallE `secondIndexUse (.fvar second) (.fvar parameter) .default) .default) .default
  let expected := Expr.forallE `formalUse (.fvar parameter)
    (.forallE `firstIndexUse (.fvar first)
      (.forallE `secondIndexUse (.fvar second) (.fvar parameter) .default) .default) .default
  let conditions := [
    (pushed.size == 2 && pushed.toList == [.fvar first, .fvar second], "two actual pushes preserve chronological order"),
    (pushed.toList.reverse == [.fvar second, .fvar first] && pushed.toList.reverse != pushed.toList,
      "endpoint order reverses distinct chronological indices"),
    (semanticPosition ((VExpr.bvar 0).lift' insertion) == 0, "target insertion protects second fresh index"),
    (semanticPosition ((VExpr.bvar 1).lift' insertion) == 1, "target insertion protects first fresh index"),
    (semanticPosition ((VExpr.bvar 2).lift' removal) == 3, "original removal occurs beneath both fresh indices"),
    (semanticPosition ((VExpr.bvar 2).lift' insertion) == 4, "target insertion occurs beneath both fresh indices"),
    (semanticPosition ((VExpr.bvar 0).lift' insertion.cons) == 0, "two-index body lift protects formal"),
    (semanticPosition ((VExpr.bvar 2).lift' insertion.cons) == 2, "two-index body lift protects first fresh index"),
    (semanticPosition ((VExpr.bvar 3).lift' insertion.cons) == 5, "two-index body lift inserts after formal and suffix"),
    (semanticPosition ((VExpr.bvar 1).lift' insertion) !=
      semanticPosition ((VExpr.bvar 1).lift' (.cons (.skip (.skip .refl)))),
      "one-index cutoff corrupts first fresh index"),
    (semanticPosition ((VExpr.bvar 2).lift' insertion.cons) != semanticPosition ((VExpr.bvar 2).lift' insertion),
      "plain context map is wrong for body suffix"),
    (semanticShape sourceBody == semanticShape (.forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 6)))),
      "source body mentions formal both indices and retained parameter"),
    (semanticShape originalBody == semanticShape (.forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 7)))),
      "original body reflects one removed declaration"),
    (semanticShape (sourceBody.lift' removal.cons) == semanticShape originalBody,
      "two-index removal reconstructs original body"),
    (semanticShape (sourceBody.lift' insertion.cons) ==
      semanticShape (.forallE (.bvar 0) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 8)))),
      "target body reflects independent two-declaration insertion"),
    (semanticShape (sourceBody.inst (.bvar 2)) ==
      semanticShape (.forallE (.bvar 2) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 5)))),
      "source instantiated endpoint retains both fresh indices"),
    (semanticShape (originalBody.inst (.bvar 3)) ==
      semanticShape (.forallE (.bvar 3) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 6)))),
      "original instantiated endpoint retains both indices beneath removal"),
    (semanticShape ((sourceBody.inst (.bvar 2)).lift' insertion) ==
      semanticShape (.forallE (.bvar 4) (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 7)))),
      "target instantiated endpoint retains both indices beneath insertion"),
    (nativeBody.instantiate1' (.fvar parameter) == expected, "structural substitution preserves both fresh indices"),
    (nativeBody.instantiate1 (.fvar parameter) == expected, "native substitution preserves both fresh indices")]
  for (condition, label) in conditions do
    unless condition do throwError "two-step-stage runtime failed: {label}"
  logInfo m!"two-step-stage runtime: {conditions.length} additional chronological-order, reversed-suffix, cutoff and native/structural substitution probes; previous 21 one-step controls remain"

private def auditFixtureDeclarations (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let fixturePrefix := (``generated).getPrefix
  let mut declarations := 0
  for (name, information) in environment.constants do
    if fixturePrefix.isPrefixOf name then
      if information matches .axiomInfo _ then throwError "index-stage fixture-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"index-stage fixture: {declarations} namespace-owned declarations including generated helpers audited"

private def auditNativeStageBindingModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexSubstitutionStageBinding
    | throwError "index-stage native binding module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index-stage native binding module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == 3 do
    throwError "index-stage native binding declaration manifest changed: expected 3, got {declarations}"
  logInfo m!"index-stage native binding: {declarations} module-owned declarations including generated helpers audited"

private def dependentIndexModel (base : MLCtx) (reader : Context) : MLCtx :=
  .vlam (generated (nextReader reader)) `dependentIndex (.fvar (generated reader)) (.bvar 0) .default
    (pushSortModel base reader)

private def expectedNativeDependentStageTelescope : Expr :=
  .forallE `oneIndex (.sort .zero)
    (.forallE `dependentIndex (.bvar 0)
      (.forallE `formalUse (.fvar (generated dependentSeedReader))
        (.letE `proofUse (.bvar 2) (.bvar 1) (.fvar (generated dependentSeedReader)) true) .default)
      .default) .default

private def nativeStageBindingRuntimeControls : MetaM Unit := do
  let seedReader := dependentSeedReader
  let baseReader := nextReader seedReader
  let smaller := pushSortModel .nil seedReader
  let original := removedMixedBase smaller baseReader
  let larger := insertedMixedBase smaller baseReader
  let actualReader := originalMixedReader baseReader
  let first := generated actualReader
  let second := generated (nextReader actualReader)
  let parameter := generated seedReader
  let finalReader := dependentFinalReader actualReader
  let sourceModel := dependentIndexModel smaller actualReader
  let originalModel := dependentIndexModel original actualReader
  let targetModel := dependentIndexModel larger actualReader
  let array := twoIndexArray actualReader
  let endpoint := (dependentNativeStageBody actualReader parameter).instantiate1 (.fvar parameter)
  let expected := expectedNativeDependentStageTelescope
  let wrongOrder := finalReader.lctx.mkForall #[.fvar second, .fvar first] endpoint
  let sourceBound : 2 ≤ sourceModel.length := by decide
  let originalBound : 2 ≤ originalModel.length := by decide
  let targetBound : 2 ≤ targetModel.length := by decide
  let sourceSemantic := sourceModel.mkForall' 2 sourceBound (.forallE (.bvar 2) (.bvar 3))
  let originalSemantic := originalModel.mkForall' 2 originalBound (.forallE (.bvar 3) (.bvar 4))
  let targetSemantic := targetModel.mkForall' 2 targetBound (.forallE (.bvar 4) (.bvar 5))
  let conditions := [
    (endpoint.looseBVarRange' == 0, "instantiated native body meets structural range-zero scope"),
    (nativeDependentStageTelescope == expected,
      "full native telescope preserves dependent second domain and shifts let proof/type correctly"),
    (expected.looseBVarRange' == 0, "dependent bound telescope has no loose variables"),
    (expected.fvarsList == [parameter, parameter],
      "native binding abstracts only actual indices and retains the selected parameter"),
    (!expected.fvarsList.contains first && !expected.fvarsList.contains second,
      "both selected index IDs are genuinely bound"),
    (sourceModel.lctx.mkForall array endpoint == expected, "contracted source native telescope equals full telescope"),
    (originalModel.lctx.mkForall array endpoint == expected, "chronological original native telescope equals full telescope"),
    (targetModel.lctx.mkForall array endpoint == expected, "independently inserted target native telescope equals full telescope"),
    (sourceModel.mkForall 2 sourceBound endpoint == expected, "source native/model binding equation has exact count two"),
    (originalModel.mkForall 2 originalBound endpoint == expected, "original native/model binding equation has exact count two"),
    (targetModel.mkForall 2 targetBound endpoint == expected, "target native/model binding equation has exact count two"),
    (sourceModel.length == 3 && originalModel.length == 4 && targetModel.length == 5,
      "source/original/target context widths remain genuinely distinct"),
    (sourceModel.fvarRevList 2 sourceBound == [second, first], "source selected fvarRevList reverses chronological array"),
    (originalModel.fvarRevList 2 originalBound == [second, first], "original selected fvarRevList has the same ordered suffix"),
    (targetModel.fvarRevList 2 targetBound == [second, first], "target selected fvarRevList has the same ordered suffix"),
    (semanticShape (sourceSemantic.lift' (.skip .refl)) == semanticShape originalSemantic,
      "after native binding the original abstracted type uses the base removal map"),
    (semanticShape (sourceSemantic.lift' (.skip (.skip .refl))) == semanticShape targetSemantic,
      "after native binding the target abstracted type uses the independent base insertion map"),
    (semanticShape (sourceSemantic.lift' (.consN (.skip .refl) 2)) != semanticShape originalSemantic,
      "keeping an extra context suffix cutoff after binding corrupts original base transport"),
    (semanticShape (sourceSemantic.lift' (.consN (.skip (.skip .refl)) 2)) != semanticShape targetSemantic,
      "keeping an extra context suffix cutoff after binding corrupts target base transport"),
    (wrongOrder != expected, "reversing chronological native binder order changes the dependent telescope"),
    (wrongOrder.fvarsList.contains first, "wrong-order outer proof domain escapes the later first-index binding"),
    (finalReader.lctx.mkForall #[.fvar second] endpoint != expected,
      "omitting first selected binder cannot reconstruct the telescope"),
    ((finalReader.lctx.mkForall #[.fvar second] endpoint).fvarsList.contains first,
      "omitting first binder leaves its dependent proof type unsupported"),
    (finalReader.lctx.mkForall #[] endpoint == endpoint, "empty native array is identity"),
    ((#[.fvar parameter] : Array Expr).toList.drop 1 == [],
      "a retained existing array prefix contributes no newly allocated binding suffix"),
    (original.lctx.mkForall #[.fvar parameter] (.fvar parameter) != .fvar parameter,
      "binding the whole nonempty prefix is not the empty-history suffix identity"),
    (finalReader.lctx.mkForall #[.fvar parameter, .fvar first, .fvar second] endpoint != expected,
      "selected-index binding does not silently bind the retained parameter too")]
  for (condition, label) in conditions do
    unless condition do throwError "native-stage-binding runtime failed: {label}"
  logInfo m!"native-stage-binding runtime: {conditions.length} additional scoped native/model binding, dependency order, exact suffix, retained parameter and distinct-base controls"

private def dependentTwoIndexRuntimeControls : MetaM Unit := do
  let seedReader := dependentSeedReader
  let actualReader := originalMixedReader (nextReader seedReader)
  let first := generated actualReader
  let second := generated (nextReader actualReader)
  let parameter := generated seedReader
  let finalReader := dependentFinalReader actualReader
  let smaller := pushSortModel .nil seedReader
  let original := removedMixedBase smaller (nextReader seedReader)
  let finalVirtual := dependentFinalVirtual original.vlctx actualReader
  let body := dependentNativeStageBody actualReader parameter
  let expected := Expr.forallE `formalUse (.fvar parameter)
    (.letE `proofUse (.fvar first) (.fvar second) (.fvar parameter) true) .default
  let sourceBody := dependentStageSemantic (.bvar 0)
  let originalBody := dependentStageSemantic (.bvar 1)
  let removal : Lift := .consN (.skip .refl) 2
  let insertion : Lift := .consN (.skip (.skip .refl)) 2
  let firstNormalization := ((monadLift (TypeChecker.whnf
    (dependentInnerType.instantiate1 (.fvar first)))) : M Expr) (nextReader actualReader)
  let secondNormalization := ((monadLift (TypeChecker.whnf
    ((Expr.sort .zero).instantiate1 (.fvar second)))) : M Expr) finalReader
  let zeroDepthNormalization := ((monadLift (TypeChecker.whnf
    (dependentInnerType.instantiate1 (.fvar first)))) : M Expr)
    { nextReader actualReader with fuel := { recDepth := 0 } }
  let conditions := [
    (first != second && first != parameter && second != parameter, "all actual allocations have distinct IDs"),
    (match finalReader.lctx.find? first with
      | some declaration => declaration.type == .sort .zero
      | none => false, "first actual stored index is type-valued"),
    (match finalReader.lctx.find? second with
      | some declaration => declaration.type == .fvar first
      | none => false, "second actual stored index is a proof of the first index"),
    ((dependentSecondStep actualReader).domain != .sort .zero,
      "dependent second domain is not the old closed sort domain"),
    ((dependentSecondStep actualReader).domain.fvarsList == [first],
      "dependent domain requires the earlier selected index"),
    (!((dependentSecondStep actualReader).domain.fvarsList.all (· == parameter)),
      "retained base alone cannot support dependent second domain"),
    (BinderStep.indexValues (dependentTwoIndexSteps actualReader) == (twoIndexArray actualReader).toList,
      "dependent actual steps and twice-pushed chronological array agree"),
    ((twoIndexArray actualReader).toList.reverse == [.fvar second, .fvar first],
      "dependent endpoint support reverses actual chronological order"),
    (match finalVirtual.find? (.inr first) with
      | some (value, domain) => semanticShape value == semanticShape (.bvar 1) &&
          semanticShape domain == semanticShape (.sort .zero)
      | none => false, "first virtual index has the expected type-valued lookup"),
    (match finalVirtual.find? (.inr second) with
      | some (value, domain) => semanticShape value == semanticShape (.bvar 0) &&
          semanticShape domain == semanticShape (.bvar 1)
      | none => false, "second virtual index lookup has the shifted first index as type"),
    (match firstNormalization with
      | .ok normalized => normalized == dependentOpenedType actualReader
      | .error _ => false, "first native normalization opens the dependent domain with the actual first ID"),
    (match secondNormalization with
      | .ok normalized => normalized == .sort .zero
      | .error _ => false, "second native normalization stops at sort zero"),
    (match zeroDepthNormalization with
      | .ok _ => false
      | .error _ => true, "zero recursion depth cannot supply the positive-depth normalization receipt"),
    (body.looseBVarRange' == 1, "dependent stage really uses its substitution formal"),
    (body.instantiate1' (.fvar parameter) == expected,
      "structural substitution keeps the proof-valued second index and its actual type"),
    (body.instantiate1 (.fvar parameter) == expected,
      "native substitution keeps the proof-valued second index and its actual type"),
    ((body.instantiate1' (.fvar parameter)).looseBVarRange' == 0,
      "substituted dependent stage is structurally depth-zero closed"),
    (expected.fvarsList == [parameter, first, second, parameter],
      "dependent native let retains both fresh indices and the selected parameter"),
    (!expected.fvarsList.all (· != first), "omitting first index loses let type support"),
    (!expected.fvarsList.all (· != second), "omitting second index loses let value support"),
    (!expected.fvarsList.all (· != parameter), "omitting retained parameter loses stage support"),
    (semanticShape sourceBody == semanticShape (.forallE (.bvar 0) (.bvar 4)),
      "typed native let erases without adding a semantic binder"),
    (semanticShape (sourceBody.lift' removal.cons) == semanticShape originalBody,
      "dependent source body uses the derived removal-one map beneath two indices and the formal"),
    (semanticShape (sourceBody.lift' insertion.cons) == semanticShape (.forallE (.bvar 0) (.bvar 6)),
      "dependent target body uses independent insertion-two beneath indices and formal"),
    (semanticShape (sourceBody.inst (.bvar 2)) == semanticShape (.forallE (.bvar 2) (.bvar 3)),
      "dependent source endpoint substitutes the retained parameter"),
    (semanticShape (originalBody.inst (.bvar 3)) == semanticShape (.forallE (.bvar 3) (.bvar 4)),
      "dependent original endpoint preserves removal coordinates"),
    (semanticShape ((sourceBody.inst (.bvar 2)).lift' insertion) == semanticShape (.forallE (.bvar 4) (.bvar 5)),
      "dependent target endpoint preserves independent insertion coordinates")]
  for (condition, label) in conditions do
    unless condition do throwError "dependent-two-step-stage runtime failed: {label}"
  logInfo m!"dependent-two-step-stage runtime: {conditions.length} additional actual native allocation/normalization, dependent stored-domain, proof-valued let, support and rebasing checks"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let adapterAllowed := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq]
  let abstractionInterfaces := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let bindingAllowed := adapterAllowed ++ abstractionInterfaces
  let abstractionAllowed := adapterAllowed.filter (· != ``Expr.instantiate1_eq) ++ abstractionInterfaces
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
  let twoStepControls := [``sortForallTranslationAndTyping, ``constructFirstOfTwoActualIndexOpenings, ``constructGenuineTwoStepHistory,
    ``twoActualStoredDomainsAreSupported, ``twoFreshIndexNamesAreDistinctFromTheRetainedParameter,
    ``bothActualStoredIndexDeclarationsExist, ``theSecondActualIndexIsFreshInTheIndependentLargerBase,
    ``translatedStageUsesTheFormalBothNewIndicesAndSelectedParameter,
    ``genuineTwoStepHistoryRebasesConstructedMixedBases, ``actualPushReceiptFixesTwoSuffixOrderAndCutoffs]
  for name in twoStepControls do auditDeclaration name adapterAllowed
  let twoStructuralControls := [``exactlyTwoIdentifiersComeFromTheActualArrayPushes,
    ``actualTwoIndexStageBodyClosedAndSupported, ``twoIndexStageHasDistinctSourceOriginalAndTargetCoordinates,
    ``missingEitherIndexOrTheParameterCannotSupplyTwoIndexStageSupport]
  for name in twoStructuralControls do auditDeclaration name logical
  auditDeclaration ``nativeForallNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  let dependentControls := [``dependentForallTranslationAndTyping, ``constructDependentSecondIndexOpening,
    ``constructDependentFirstIndexOpening, ``constructGenuineDependentTwoStepHistory,
    ``dependentActualStoredDomainsAreSupported, ``dependentActualStoredDeclarationsExposeTheEarlierIndex,
    ``translatedDependentStageUsesTheProofValuedSecondIndex,
    ``genuineDependentTwoStepHistoryRebasesConstructedMixedBases,
    ``emptySeedExercisesTheDependentAdapterWithoutFixturePremises]
  for name in dependentControls do auditDeclaration name adapterAllowed
  let dependentStructuralControls := [``dependentStageBodyClosedAndSupported,
    ``dependentStoredDomainRequiresTheEarlierIndex, ``dependentVirtualLookupsDistinguishATypeFromItsProof,
    ``dependentStageHasDistinctSourceOriginalAndTargetCoordinates,
    ``missingEitherIndexOrParameterCannotSupportTheDependentLet,
    ``dependentStageSubstitutionPreservesTheProofsActualType]
  for name in dependentStructuralControls do auditDeclaration name logical
  auditDeclaration ``dependentNativeNormalizationsWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``IndexMLCtxExtension.typedBodyAbstractionS abstractionAllowed
  auditExactDependencies ``SelectedRecursorTelescope.scopedTypedAbstractionS abstractionAllowed
  auditExactDependencies ``TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutionStageNativeForall bindingAllowed
  auditExactDependencies ``actualDependentStageReconstructsOneNativeTelescopeInThreeBases bindingAllowed
  auditExactDependencies ``emptySelectedTelescopeBindingAddsNoSemanticBinder abstractionAllowed
  auditExactDependencies ``existingIndexPrefixIsNotBoundByAnEmptyActualHistory bindingAllowed
  auditNativeStageBindingModule bindingAllowed
  for name in [``generated, ``nextReader, ``nextVirtual, ``normalizationReceipt, ``oneStep,
      ``nativeStageBody, ``stageSemantic, ``stageLevel, ``semanticPosition, ``semanticShape, ``runtimeControls,
      ``pushSortModel, ``advanceReaderTwice, ``removedMixedBase, ``originalMixedReader, ``insertedMixedBase,
      ``oneIndexType, ``twoIndexType, ``twoIndexArray, ``twoIndexSteps, ``twoIndexVirtual,
      ``twoIndexNativeStageBody, ``twoIndexStageSemantic, ``twoIndexStageLevel, ``twoIndexRuntimeControls,
      ``dependentInnerType, ``dependentTwoIndexType, ``dependentOpenedType, ``dependentFinalReader,
      ``dependentFinalVirtual, ``dependentSecondStep, ``dependentTwoIndexSteps, ``dependentNativeStageBody,
      ``dependentStageSemantic, ``dependentStageLevel, ``dependentSeedReader, ``noParameterStats,
      ``dependentTwoIndexRuntimeControls,
      ``nativeDependentStageTelescope, ``dependentIndexModel, ``expectedNativeDependentStageTelescope,
      ``nativeStageBindingRuntimeControls, ``auditNativeStageBindingModule,
      ``auditDeclaration, ``auditExactDependencies, ``auditFixtureDeclarations] do auditDeclaration name logical
  auditExactDependencies ``nativeSortNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``genuineOneStepHistoryInvokesTheStageAdapter adapterAllowed
  auditExactDependencies ``genuineOneStepHistoryRebasesConstructedMixedBases adapterAllowed
  auditExactDependencies ``nativeForallNormalizationWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``genuineTwoStepHistoryRebasesConstructedMixedBases adapterAllowed
  auditExactDependencies ``dependentNativeNormalizationsWithPositiveDepth (logical ++ [``Expr.instantiate1_eq])
  auditExactDependencies ``genuineDependentTwoStepHistoryRebasesConstructedMixedBases adapterAllowed
  auditExactDependencies ``emptySeedExercisesTheDependentAdapterWithoutFixturePremises adapterAllowed
  auditFixtureDeclarations bindingAllowed
  runtimeControls
  twoIndexRuntimeControls
  dependentTwoIndexRuntimeControls
  nativeStageBindingRuntimeControls
  logInfo m!"one-step-stage tests: {actualControls.length + structuralControls.length + 1} proof controls; real index/stop trace and actual array push; real peeled opening and nonvacuous stored declaration; constructed retained parameter, original one-declaration removal and independent two-declaration target insertion; shared reduced body, suffix support, target native translation/typing and original endpoint agreement; native sort normalization proved at positive depth; both identity and mixed-base applications tied to actual pushed suffix receipt"
  logInfo m!"two-step-stage tests: {twoStepControls.length + twoStructuralControls.length + 1} additional proof controls ({actualControls.length + structuralControls.length + twoStepControls.length + twoStructuralControls.length + 2} total); actual index/index/stop history, positive-depth native forall/sort normalization, real peeled openings and two existing stored declarations; chronological IDs from actual array pushes versus reversed selected-telescope endpoint support; both-index stage body, shared existential reduced body, nonidentity cutoff-two source/target native translations/typing and original endpoint agreement"
  logInfo m!"dependent-two-step-stage tests: {dependentControls.length + dependentStructuralControls.length + 1} additional proof controls ({actualControls.length + structuralControls.length + twoStepControls.length + twoStructuralControls.length + dependentControls.length + dependentStructuralControls.length + 3} total); genuine dependent index/index/stop history, actual stored second domain referencing first index, typed proof-valued native let, derived removal-one/insertion-two maps, shared existential reduced body and source/target translation/typing; empty seed and empty environment instantiate the full adapter with no fixture premises"
  logInfo "native-stage-binding tests: three additional fixture proof controls plus three exact module contracts; one native telescope translates strictly and is type-valued in original/removal-one and reduced/insertion-two base contexts, with abstracted semantic agreement at the distinct base maps; body and all three native contexts have derived structural binding scope, chronological selected arrays and dependent binder order; an actual empty history with nonempty retained array prefix binds nothing; no fixture premises, global native range axiom, arbitrary later-context scope or frontend acceptance claim"

end InductiveIndexSubstitutionStageOneStepTest
