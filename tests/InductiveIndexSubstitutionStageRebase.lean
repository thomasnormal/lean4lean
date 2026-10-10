import Lean4Lean.Verify.InductiveIndexSubstitutionStageRebase
import Lean.Util.CollectAxioms

namespace InductiveIndexSubstitutionStageRebaseTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

private theorem actualHistoryStagePreservesEveryReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (smaller : MLCtx) (smallerWF : smaller.WF env universes) (baseLift : Lift)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx model.vlctx 0 baseLift 0)
    {params : List FVarId} {steps : List BinderStep}
    (stored : BinderStoredIndexTypeFVarsIn params current steps)
    (values : BinderStep.indexValues steps = finalIndices.toList)
    (parameters : params ⊆ smaller.vlctx.fvars)
    (prefixRetained : indices.toList.map Expr.fvarId! ⊆ smaller.vlctx.fvars)
    (larger : MLCtx) (largerWF : larger.WF env universes) (inserted : Nat)
    (insertion : VLCtx.FVLift smaller.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier,
      Expr.fvar identifier ∈ finalIndices.toList.drop indices.size → identifier ∉ larger.vlctx.fvars)
    (position : Nat) (identifier : FVarId) (selected : params[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : finalVirtual.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: finalVirtual) body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: finalVirtual.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 1)
    (bodySupport : body.FVarsIn
      (· ∈ ((finalIndices.toList.drop indices.size).map Expr.fvarId!).reverse ++ smaller.vlctx.fvars)) :
    ∃ chronological ids reduced aligned target reducedArgument reducedDomain domainLevel reducedBody,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids reduced ∧
      reduced.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned ∧
      SelectedRecursorTelescope env universes current.lctx larger ids target ∧
      target.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0 (.consN (.skipN .refl inserted) ids.length) 0 ∧
      RetainedFVarPrefix env universes smaller.vlctx larger.vlctx (.skipN .refl inserted) params ∧
      RetainedFVarPrefix env universes reduced.vlctx target.vlctx
        (.consN (.skipN .refl inserted) ids.length) params ∧
      RetainedFVarPrefixAgreement env universes reduced.vlctx chronological.vlctx aligned
        (.consN baseLift ids.length) params ∧
      reduced.vlctx.find? (.inr identifier) = some (reducedArgument, reducedDomain) ∧
      TrExprS env universes reduced.vlctx (.fvar identifier) reducedArgument ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx originalArgumentType
        (reducedDomain.lift' (.consN baseLift ids.length)) (.sort domainLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx originalArgument
        (reducedArgument.lift' (.consN baseLift ids.length)) originalArgumentType ∧
      VLCtx.FVLift' ((none, .vlam reducedDomain) :: reduced.vlctx)
        ((none, .vlam (reducedDomain.lift' (.consN baseLift ids.length))) :: aligned)
        1 (.consN baseLift ids.length) 1 ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam originalArgumentType) :: chronological.vlctx)
        ((none, .vlam (reducedDomain.lift' (.consN baseLift ids.length))) :: aligned) ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedDomain (.sort domainLevel) ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx) body reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx) reducedBody (.sort level) ∧
      env.IsDefEq universes.length (originalArgumentType :: chronological.vlctx.toCtx)
        bodySemantic (reducedBody.lift' (Lift.consN baseLift ids.length).cons) (.sort level) ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedArgument reducedDomain ∧
      env.HasType universes.length reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx (bodySemantic.inst originalArgument)
        ((reducedBody.inst reducedArgument).lift' (.consN baseLift ids.length)) (.sort level) ∧
      TrExprS env universes
        ((none, .vlam (reducedDomain.lift' (.consN (.skipN .refl inserted) ids.length))) :: target.vlctx)
        body (reducedBody.lift' (Lift.consN (.skipN .refl inserted) ids.length).cons) ∧
      env.HasType universes.length
        ((reducedDomain.lift' (.consN (.skipN .refl inserted) ids.length)) :: target.vlctx.toCtx)
        (reducedBody.lift' (Lift.consN (.skipN .refl inserted) ids.length).cons) (.sort level) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedArgument.lift' (.consN (.skipN .refl inserted) ids.length))
        (reducedDomain.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.lift' (Lift.consN (.skipN .refl inserted) ids.length).cons).inst
          (reducedArgument.lift' (.consN (.skipN .refl inserted) ids.length))) (.sort level) ∧
      Closed (body.instantiate1 (.fvar identifier)) 0 ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ reduced.vlctx.fvars) ∧
      TrExprS env universes chronological.vlctx (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      TrExprS env universes reduced.vlctx (body.instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      TrExprS env universes target.vlctx (.fvar identifier)
        (reducedArgument.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      TrExprS env universes target.vlctx (body.instantiate1 (.fvar identifier))
        ((reducedBody.lift' (Lift.consN (.skipN .refl inserted) ids.length).cons).inst
          (reducedArgument.lift' (.consN (.skipN .refl inserted) ids.length))) := by
  exact history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains model modelWF native converted
    reserved current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
    prefixRetained larger largerWF inserted insertion freshBase position identifier selected
    originalLookup bodyTranslated bodyTyped bodyClosed bodySupport

private def emptyNestedBody : Expr :=
  .forallE `outer (.bvar 0) (.forallE `inner (.bvar 1) (.bvar 2) .default) .default

private def emptyNestedSemantic : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))

private def emptyStageLevel (level : VLevel) : VLevel := .imax level (.imax level level)

private theorem emptyNestedBodyProtectsTheFormal :
    Closed emptyNestedBody 1 ∧ ¬Closed emptyNestedBody 0 ∧
    emptyNestedBody.FVarsIn (fun _ => False) := by
  simp [emptyNestedBody, Closed, FVarsIn]

private theorem emptyActualHistoryUsesOneSharedNestedStageBody
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    (model : MLCtx) (modelWF : model.WF env universes) (reader : Context)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (envWF : env.WF) (identifier : FVarId) (member : identifier ∈ model.vlctx.fvars)
    {argument : VExpr} {level : VLevel}
    (lookup : model.vlctx.find? (.inr identifier) = some (argument, .sort level)) :
    ∃ reduced target reducedArgument reducedDomain reducedBody,
      SelectedRecursorTelescope env universes reader.lctx model [] reduced ∧
      SelectedRecursorTelescope env universes reader.lctx model [] target ∧
      TrExprS env universes ((none, .vlam reducedDomain) :: reduced.vlctx) emptyNestedBody reducedBody ∧
      env.HasType universes.length (reducedDomain :: reduced.vlctx.toCtx)
        reducedBody (.sort (emptyStageLevel level)) ∧
      TrExprS env universes reduced.vlctx (emptyNestedBody.instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      TrExprS env universes target.vlctx (emptyNestedBody.instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedBody.inst reducedArgument) (.sort (emptyStageLevel level)) ∧
      env.IsDefEq universes.length model.vlctx.toCtx (emptyNestedSemantic.inst argument)
        (reducedBody.inst reducedArgument) (.sort (emptyStageLevel level)) ∧
      Closed (emptyNestedBody.instantiate1 (.fvar identifier)) 0 ∧
      (emptyNestedBody.instantiate1 (.fvar identifier)).FVarsIn (· ∈ reduced.vlctx.fvars) := by
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  have history := TranslatedRecursorIndexTrace.stop (stats := stats) (index := 0) (indices := #[])
    notForall correspondence (TrExprS.sort (u' := .zero) (by simp [VLevel.ofLevel]))
  have stored : BinderStoredIndexTypeFVarsIn [identifier] reader [] := by
    intro position step declaration selected
    simp at selected
  have translated : TrExprS env universes ((none, .vlam (.sort level)) :: model.vlctx)
      emptyNestedBody emptyNestedSemantic :=
    .forallE ⟨level, .bvar .zero⟩
      ⟨.imax level level, .forallEDF (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))⟩
      (.bvar rfl) (.forallE ⟨level, .bvar (.succ .zero)⟩
        ⟨level, .bvar (.succ (.succ .zero))⟩ (.bvar rfl) (.bvar rfl))
  have typed : env.HasType universes.length (.sort level :: model.vlctx.toCtx)
      emptyNestedSemantic (.sort (emptyStageLevel level)) :=
    .forallEDF (.bvar .zero) (.forallEDF (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero))))
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, reducedDomain, _, reducedBody,
    _, _, chronologicalConverted, _, array, reducedTelescope, _, _, _, targetTelescope, _, _, _, _, _,
    _, _, _, _, _, _, _, reducedBodyTranslation, reducedBodyTyping, _, _, _, endpointEquality,
    _, _, _, targetTyping, substitutedClosed, substitutedSupport, _, sourceTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains model modelWF native rfl reserved
      reader (.refl reader correspondence.1 reserved) envWF model modelWF .refl .refl stored rfl
      (by intro candidate candidateMember
          have candidateEq : candidate = identifier := by simpa using candidateMember
          simpa only [candidateEq] using member)
      (by simp) model modelWF 0 .refl (by simp) 0 identifier rfl lookup
      translated typed emptyNestedBodyProtectsTheFormal.1 (by trivial)
  have idsEmpty : ids = [] := by simpa using array.symm
  subst ids
  have bodyIdentity : reducedBody.lift' Lift.refl.cons = reducedBody :=
    VExpr.lift'_depth_zero (by rfl)
  refine ⟨reduced, target, reducedArgument, reducedDomain, reducedBody,
    reducedTelescope, targetTelescope, reducedBodyTranslation, reducedBodyTyping, sourceTranslation,
    ?_, ?_, ?_, substitutedClosed, substitutedSupport⟩
  · simpa [bodyIdentity] using targetTranslation
  · simpa [bodyIdentity] using targetTyping
  · simpa [chronologicalConverted] using endpointEquality

private def retainedParameter : FVarId := ⟨`IndexSubstitutionRetainedParameter⟩
private def earlierParameter : FVarId := ⟨`IndexSubstitutionEarlierParameter⟩
private def retainedPrefix : FVarId := ⟨`IndexSubstitutionRetainedPrefix⟩
private def firstSuffix : FVarId := ⟨`IndexSubstitutionFirstSuffix⟩
private def secondSuffix : FVarId := ⟨`IndexSubstitutionSecondSuffix⟩
private def discardedInitial : FVarId := ⟨`IndexSubstitutionDiscardedInitial⟩
private def prefixIndices : Array Expr := #[.fvar retainedPrefix]
private def finalIndices : Array Expr := #[.fvar retainedPrefix, .fvar firstSuffix, .fvar secondSuffix]
private def retainedBase : List FVarId := [retainedParameter, earlierParameter, retainedPrefix]
private def endpointSupport : List FVarId :=
  ((finalIndices.toList.drop prefixIndices.size).map Expr.fvarId!).reverse ++ retainedBase

private theorem existingPrefixIsNotPartOfTheSelectedSuffix :
    finalIndices.toList.drop prefixIndices.size = [.fvar firstSuffix, .fvar secondSuffix] ∧
      endpointSupport = [secondSuffix, firstSuffix, retainedParameter, earlierParameter, retainedPrefix] := ⟨rfl, rfl⟩

private theorem suffixReceiptKeepsChronologicalIdentifiers
    {identifiers : List FVarId}
    (array : finalIndices.toList = prefixIndices.toList ++ identifiers.map Expr.fvar) :
    identifiers = [firstSuffix, secondSuffix] := by
  have suffix : identifiers.map Expr.fvar = [.fvar firstSuffix, .fvar secondSuffix] := by
    simpa [finalIndices, prefixIndices] using array.symm
  cases identifiers with
  | nil => cases suffix
  | cons first remaining =>
    cases remaining with
    | nil => cases suffix
    | cons second tail =>
      have equalities := List.cons.inj suffix
      have firstEquality := Expr.fvar.inj equalities.1
      have restEqualities := List.cons.inj equalities.2
      have secondEquality := Expr.fvar.inj restEqualities.1
      have tailEmpty : tail = [] := List.map_eq_nil_iff.mp restEqualities.2
      simp [firstEquality, secondEquality, tailEmpty]

private def dependentBody : Expr :=
  .forallE `suffix (.fvar secondSuffix)
    (.forallE `parameter (.bvar 1)
      (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
        (.app (.fvar retainedParameter) (.app (.bvar 2) (.bvar 1))))) .default) .default

private theorem suffixAndRetainedBaseSupportTheBody : dependentBody.FVarsIn (· ∈ endpointSupport) := by
  simp [dependentBody, FVarsIn, endpointSupport, finalIndices, prefixIndices, retainedBase, Expr.fvarId!]

private theorem bodyHasExactlyTheSubstitutionBinderPremise :
    Closed dependentBody 1 ∧ ¬ Closed dependentBody 0 := by
  simp [dependentBody, Closed]

private theorem missingSuffixCannotSupplyBodySupport :
    ¬ dependentBody.FVarsIn (· ∈ retainedBase) := by
  simp [dependentBody, FVarsIn, retainedBase, retainedParameter, earlierParameter, retainedPrefix,
    firstSuffix, secondSuffix]

private theorem removedInitialCannotSupplyBodySupport :
    ¬ (Expr.app dependentBody (.fvar discardedInitial)).FVarsIn (· ∈ endpointSupport) := by
  simp [dependentBody, FVarsIn, endpointSupport, finalIndices, prefixIndices, retainedBase,
    retainedParameter, earlierParameter, retainedPrefix, firstSuffix, secondSuffix, discardedInitial, Expr.fvarId!]

private theorem bodySubstitutionProtectsItsLocalBinder :
    dependentBody.instantiate1' (.fvar retainedParameter) =
      .forallE `suffix (.fvar secondSuffix)
        (.forallE `parameter (.fvar retainedParameter)
          (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
            (.app (.fvar retainedParameter) (.app (.fvar retainedParameter) (.bvar 1))))) .default) .default := rfl

private theorem selectedParameterPositionIsNotTheIndexPrefixPosition :
    [earlierParameter, retainedParameter][1]? = some retainedParameter ∧
      [earlierParameter, retainedParameter][0]? ≠ some retainedParameter ∧
      [earlierParameter, retainedParameter][2]? = none := by
  simp [earlierParameter, retainedParameter]

private theorem indexSuffixCannotBeSelectedAsARetainedParameter :
    firstSuffix ∉ [earlierParameter, retainedParameter] ∧
      secondSuffix ∉ [earlierParameter, retainedParameter] := by
  simp [firstSuffix, secondSuffix, earlierParameter, retainedParameter]

private theorem endpointLiftCutoffsProtectBothSelectedIndices :
    (VExpr.bvar 0).lift' (.consN (.skip .refl) 2) = .bvar 0 ∧
      (VExpr.bvar 1).lift' (.consN (.skip .refl) 2) = .bvar 1 ∧
      (VExpr.bvar 2).lift' (.consN (.skip .refl) 2) = .bvar 3 ∧
      (VExpr.bvar 0).lift' (.consN (.skipN .refl 3) 2) = .bvar 0 ∧
      (VExpr.bvar 1).lift' (.consN (.skipN .refl 3) 2) = .bvar 1 ∧
      (VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2) = .bvar 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem insertionLiftCannotReplaceTheRemovalReceipt :
    (VExpr.bvar 2).lift' (.consN (.skip .refl) 2) ≠
      (VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2) := by
  intro equality
  cases equality

private def protectedStageSemantic : VExpr := .forallE (.bvar 0) (.forallE (.bvar 3) (.bvar 5))

private def historyRemovalLift : Lift := .consN (.skip .refl) 2

private def historyInsertionLift : Lift := .consN (.skipN .refl 3) 2

private theorem stageFormalAndBothIndicesNeedTheirProtectedBodyLift :
    protectedStageSemantic.lift' historyRemovalLift.cons =
      .forallE (.bvar 0) (.forallE (.bvar 3) (.bvar 6)) ∧
    protectedStageSemantic.lift' historyInsertionLift.cons =
      .forallE (.bvar 0) (.forallE (.bvar 3) (.bvar 8)) ∧
    protectedStageSemantic.lift' historyInsertionLift.cons ≠
      protectedStageSemantic.lift' historyInsertionLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem selectedDomainAndArgumentUsePlainEndpointContextCoordinates :
    (VExpr.bvar 2).lift' historyInsertionLift = .bvar 5 ∧
    (VExpr.bvar 2).lift' historyInsertionLift.cons = .bvar 2 ∧
    (VExpr.bvar 2).lift' historyInsertionLift ≠ (VExpr.bvar 2).lift' historyInsertionLift.cons := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem reducedStageInstantiationCommutesWithIndependentTargetInsertion :
    (protectedStageSemantic.inst (.bvar 2)).lift' historyInsertionLift =
      (protectedStageSemantic.lift' historyInsertionLift.cons).inst
        ((VExpr.bvar 2).lift' historyInsertionLift) ∧
    (protectedStageSemantic.inst (.bvar 2)).lift' historyInsertionLift =
      .forallE (.bvar 5) (.forallE (.bvar 2) (.bvar 7)) ∧
    (protectedStageSemantic.inst (.bvar 2)).lift' historyInsertionLift ≠
      (protectedStageSemantic.inst (.bvar 2)).lift' historyRemovalLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem emptyNestedSubstitutionUsesTheSelectedParameterInEveryFormalOccurrence
    (identifier : FVarId) :
    emptyNestedBody.instantiate1' (.fvar identifier) =
      .forallE `outer (.fvar identifier)
        (.forallE `inner (.fvar identifier) (.fvar identifier) .default) .default := rfl

private theorem unsupportedDomainCannotBeIgnoredByStageBodySupport :
    ¬ (Expr.forallE `unsupported (.fvar discardedInitial) (.bvar 0) .default).FVarsIn
      (· ∈ endpointSupport) := by
  simp [FVarsIn, endpointSupport, finalIndices, prefixIndices, retainedBase, retainedParameter,
    earlierParameter, retainedPrefix, firstSuffix, secondSuffix, discardedInitial, Expr.fvarId!]

private def semanticPosition : VExpr → Nat
  | .bvar position => position
  | _ => 1000

private def runtimeControls : MetaM Unit := do
  let expectedBody := Expr.forallE `suffix (.fvar secondSuffix)
    (.forallE `parameter (.fvar retainedParameter)
      (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
        (.app (.fvar retainedParameter) (.app (.fvar retainedParameter) (.bvar 1))))) .default) .default
  let conditions := [
    (finalIndices.toList.drop prefixIndices.size == [.fvar firstSuffix, .fvar secondSuffix], "chronological suffix"),
    (endpointSupport == [secondSuffix, firstSuffix, retainedParameter, earlierParameter, retainedPrefix], "reversed endpoint support"),
    (endpointSupport.contains retainedPrefix, "retained old prefix"),
    (!endpointSupport.contains discardedInitial, "discarded initial fvar"),
    (dependentBody.instantiate1' (.fvar retainedParameter) == expectedBody, "core binder substitution"),
    (dependentBody.instantiate1 (.fvar retainedParameter) == expectedBody, "native binder substitution"),
    ([earlierParameter, retainedParameter][1]? == some retainedParameter, "nonzero parameter position"),
    ([earlierParameter, retainedParameter][2]? == none, "out-of-range parameter position"),
    (semanticPosition ((VExpr.bvar 0).lift' (.consN (.skip .refl) 2)) == 0, "first removal cutoff"),
    (semanticPosition ((VExpr.bvar 1).lift' (.consN (.skip .refl) 2)) == 1, "second removal cutoff"),
    (semanticPosition ((VExpr.bvar 2).lift' (.consN (.skip .refl) 2)) == 3, "removed parameter position"),
    (semanticPosition ((VExpr.bvar 0).lift' (.consN (.skipN .refl 3) 2)) == 0, "first insertion cutoff"),
    (semanticPosition ((VExpr.bvar 1).lift' (.consN (.skipN .refl 3) 2)) == 1, "second insertion cutoff"),
    (semanticPosition ((VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2)) == 5, "inserted parameter position"),
    (semanticPosition ((VExpr.bvar 2).lift' historyInsertionLift.cons) == 2, "body cons lift is not the argument or domain lift"),
    (emptyNestedBody.instantiate1' (.fvar retainedParameter) ==
      .forallE `outer (.fvar retainedParameter)
        (.forallE `inner (.fvar retainedParameter) (.fvar retainedParameter) .default) .default,
      "actual empty-history body consumes the selected formal beneath two binders"),
    (semanticPosition ((VExpr.bvar 0).lift' historyInsertionLift.cons) == 0, "stage formal remains protected"),
    (semanticPosition ((VExpr.bvar 1).lift' historyInsertionLift.cons) == 1, "newest suffix remains protected beneath formal"),
    (semanticPosition ((VExpr.bvar 2).lift' historyInsertionLift.cons) == 2, "older suffix remains protected beneath formal"),
    (semanticPosition ((VExpr.bvar 3).lift' historyInsertionLift.cons) == 6, "base argument uses independent insertion beneath protected formal and suffix")]
  for (condition, label) in conditions do
    unless condition do throwError "history-stage-rebase runtime failed: {label}"
  logInfo m!"history-stage-rebase runtime: {conditions.length} suffix/support/selection/substitution/formal and independent context cutoff controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "history-stage-rebase declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "history-stage-rebase unexpected axiom {axiomName} in {name}"

private def auditActualHistoryAdapter (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let name := ``TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutionStageOfStoredDomains
  let some information := environment.find? name | throwError "history-stage-rebase adapter absent"
  if information matches .axiomInfo _ then throwError "history-stage-rebase adapter is an axiom"
  unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexSubstitutionStageRebase do
    throwError "history-stage-rebase adapter module provenance changed"
  auditDeclaration name allowed
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "history-stage-rebase inherited/native dependency provenance changed"
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexSubstitutionStageRebase
    | throwError "history-stage-rebase module absent"
  let mut declarations := 0
  for (ownedName, ownedInformation) in environment.constants do
    if environment.getModuleIdxFor? ownedName == some moduleIndex then
      if ownedInformation matches .axiomInfo _ then throwError "history-stage-rebase module-owned axiom {ownedName}"
      auditDeclaration ownedName allowed
      declarations := declarations + 1
  unless declarations == 1 do
    throwError "history-stage-rebase declaration manifest changed: expected 1, got {declarations}"
  logInfo m!"history-stage-rebase adapter: {declarations} module-owned declarations including generated helpers audited; exact eight inherited/native dependencies, three persistent-container interfaces and only native instantiate1 interface"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq]
  let adapterAllowed := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``actualHistoryStagePreservesEveryReceipt adapterAllowed
  auditDeclaration ``emptyActualHistoryUsesOneSharedNestedStageBody adapterAllowed
  let structuralControls := [``existingPrefixIsNotPartOfTheSelectedSuffix,
    ``suffixReceiptKeepsChronologicalIdentifiers, ``suffixAndRetainedBaseSupportTheBody,
    ``bodyHasExactlyTheSubstitutionBinderPremise, ``missingSuffixCannotSupplyBodySupport,
    ``removedInitialCannotSupplyBodySupport, ``bodySubstitutionProtectsItsLocalBinder,
    ``selectedParameterPositionIsNotTheIndexPrefixPosition, ``indexSuffixCannotBeSelectedAsARetainedParameter,
    ``endpointLiftCutoffsProtectBothSelectedIndices, ``insertionLiftCannotReplaceTheRemovalReceipt,
    ``emptyNestedBodyProtectsTheFormal, ``stageFormalAndBothIndicesNeedTheirProtectedBodyLift,
    ``selectedDomainAndArgumentUsePlainEndpointContextCoordinates,
    ``reducedStageInstantiationCommutesWithIndependentTargetInsertion,
    ``emptyNestedSubstitutionUsesTheSelectedParameterInEveryFormalOccurrence,
    ``unsupportedDomainCannotBeIgnoredByStageBodySupport]
  for name in structuralControls do auditDeclaration name logical
  for name in [``emptyNestedBody, ``emptyNestedSemantic, ``emptyStageLevel, ``retainedParameter,
      ``earlierParameter, ``retainedPrefix, ``firstSuffix, ``secondSuffix, ``discardedInitial,
      ``prefixIndices, ``finalIndices, ``retainedBase, ``endpointSupport, ``dependentBody,
      ``protectedStageSemantic, ``historyRemovalLift, ``historyInsertionLift,
      ``semanticPosition, ``runtimeControls, ``auditDeclaration, ``auditActualHistoryAdapter] do
    auditDeclaration name logical
  auditActualHistoryAdapter adapterAllowed
  runtimeControls
  logInfo m!"history-stage-rebase tests: {structuralControls.length + 2} proof controls; all 38 history/parameter/stage receipts forwarded; actual empty translated history uses one shared nested formal body and selected parameter; retained prefix plus two structural suffix IDs; closure/support/domain/selection boundaries; independent removal/insertion and plain-versus-cons body cutoffs"

end InductiveIndexSubstitutionStageRebaseTest
