import Lean4Lean.Verify.InductiveIndexRebase
import Lean.Util.CollectAxioms

namespace InductiveIndexPairSubstitutionRebaseTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

private def pairInstantiate (body : Expr) (outerIdentifier innerIdentifier : FVarId) : Expr :=
  (body.instantiate1 (.fvar innerIdentifier)).instantiate1 (.fvar outerIdentifier)

private def pairSemantic (body outerArgument innerArgument : VExpr) : VExpr :=
  (body.inst innerArgument.lift).inst outerArgument

private theorem actualHistoryPairSubstitutionPreservesEveryReceipt
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
    (outerPosition : Nat) (outerIdentifier : FVarId) (outerSelected : params[outerPosition]? = some outerIdentifier)
    (innerPosition : Nat) (innerIdentifier : FVarId) (innerSelected : params[innerPosition]? = some innerIdentifier)
    {originalOuterArgument originalOuterArgumentType originalInnerArgument originalInnerArgumentType : VExpr}
    (outerLookup : finalVirtual.find? (.inr outerIdentifier) = some (originalOuterArgument, originalOuterArgumentType))
    (innerLookup : finalVirtual.find? (.inr innerIdentifier) = some (originalInnerArgument, originalInnerArgumentType))
    {innerDomain : VExpr}
    (raisedInnerArgumentTyped : env.HasType universes.length
      (originalOuterArgumentType :: finalVirtual.toCtx) originalInnerArgument.lift innerDomain)
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes
      ((none, .vlam innerDomain) :: (none, .vlam originalOuterArgumentType) :: finalVirtual) body bodySemantic)
    (bodyTyped : env.HasType universes.length
      (innerDomain :: originalOuterArgumentType :: finalVirtual.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 2)
    (bodySupport : body.FVarsIn
      (· ∈ ((finalIndices.toList.drop indices.size).map Expr.fvarId!).reverse ++ smaller.vlctx.fvars)) :
    ∃ chronological ids reduced aligned target reducedInnerArgument reducedInnerType reducedOuterArgument reducedOuterType reducedSemantic,
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
      reduced.vlctx.find? (.inr innerIdentifier) = some (reducedInnerArgument, reducedInnerType) ∧
      TrExprS env universes reduced.vlctx (.fvar innerIdentifier) reducedInnerArgument ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedInnerArgument reducedInnerType ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx originalInnerArgument
        (reducedInnerArgument.lift' (.consN baseLift ids.length)) originalInnerArgumentType ∧
      Closed (body.instantiate1 (.fvar innerIdentifier)) 1 ∧
      (body.instantiate1 (.fvar innerIdentifier)).FVarsIn (· ∈ reduced.vlctx.fvars) ∧
      TrExprS env universes ((none, .vlam originalOuterArgumentType) :: chronological.vlctx)
        (body.instantiate1 (.fvar innerIdentifier)) (bodySemantic.inst originalInnerArgument.lift) ∧
      env.HasType universes.length (originalOuterArgumentType :: chronological.vlctx.toCtx)
        (bodySemantic.inst originalInnerArgument.lift) (.sort level) ∧
      reduced.vlctx.find? (.inr outerIdentifier) = some (reducedOuterArgument, reducedOuterType) ∧
      TrExprS env universes reduced.vlctx (.fvar outerIdentifier) reducedOuterArgument ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedOuterArgument reducedOuterType ∧
      Closed (pairInstantiate body outerIdentifier innerIdentifier) 0 ∧
      (pairInstantiate body outerIdentifier innerIdentifier).FVarsIn (· ∈ reduced.vlctx.fvars) ∧
      TrExprS env universes chronological.vlctx (pairInstantiate body outerIdentifier innerIdentifier)
        (pairSemantic bodySemantic originalOuterArgument originalInnerArgument) ∧
      env.HasType universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic originalOuterArgument originalInnerArgument) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic originalOuterArgument originalInnerArgument)
        (pairSemantic bodySemantic (reducedOuterArgument.lift' (.consN baseLift ids.length)) originalInnerArgument) (.sort level) ∧
      TrExprS env universes reduced.vlctx (pairInstantiate body outerIdentifier innerIdentifier) reducedSemantic ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic originalOuterArgument originalInnerArgument)
        (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic (reducedOuterArgument.lift' (.consN baseLift ids.length)) originalInnerArgument)
        (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) ∧
      TrExprS env universes target.vlctx (pairInstantiate body outerIdentifier innerIdentifier)
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) ∧
      env.HasType universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic (reducedOuterArgument.lift' (.consN baseLift ids.length))
          (reducedInnerArgument.lift' (.consN baseLift ids.length))) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic originalOuterArgument originalInnerArgument)
        (pairSemantic bodySemantic (reducedOuterArgument.lift' (.consN baseLift ids.length))
          (reducedInnerArgument.lift' (.consN baseLift ids.length))) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (pairSemantic bodySemantic (reducedOuterArgument.lift' (.consN baseLift ids.length))
          (reducedInnerArgument.lift' (.consN baseLift ids.length)))
        (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) := by
  exact history.selectedTelescopeRebasedSubstitutedPairTypeOfStoredDomains model modelWF native converted
    reserved current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
    prefixRetained larger largerWF inserted insertion freshBase outerPosition outerIdentifier outerSelected
    innerPosition innerIdentifier innerSelected outerLookup innerLookup raisedInnerArgumentTyped
    bodyTranslated bodyTyped bodyClosed bodySupport

private theorem emptyActualHistoryInstantiatesBothFormalBinders
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    (model : MLCtx) (modelWF : model.WF env universes) (reader : Context)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (envWF : env.WF) (outerIdentifier innerIdentifier : FVarId)
    (outerMember : outerIdentifier ∈ model.vlctx.fvars) (innerMember : innerIdentifier ∈ model.vlctx.fvars)
    {outerArgument innerArgument : VExpr} {outerLevel innerLevel : VLevel}
    (outerLookup : model.vlctx.find? (.inr outerIdentifier) = some (outerArgument, .sort outerLevel))
    (innerLookup : model.vlctx.find? (.inr innerIdentifier) = some (innerArgument, .sort innerLevel)) :
    ∃ reduced target semantic,
      SelectedRecursorTelescope env universes reader.lctx model [] reduced ∧
      SelectedRecursorTelescope env universes reader.lctx model [] target ∧
      TrExprS env universes target.vlctx
        (.forallE `pair (.fvar outerIdentifier) (.fvar innerIdentifier) .default) semantic ∧
      env.HasType universes.length target.vlctx.toCtx semantic (.sort (.imax outerLevel innerLevel)) := by
  have correspondence : TrLCtx env universes reader.lctx model.vlctx := by
    simpa only [native] using modelWF.tr
  have notForall : ∀ name domain body bi, Expr.sort .zero ≠ .forallE name domain body bi := by
    intro name domain body binder equality
    cases equality
  have history := TranslatedRecursorIndexTrace.stop (stats := stats) (index := 0) (indices := #[])
    notForall correspondence (TrExprS.sort (u' := .zero) (by simp [VLevel.ofLevel]))
  have stored : BinderStoredIndexTypeFVarsIn [outerIdentifier, innerIdentifier] reader [] := by
    intro position step declaration selected
    simp at selected
  have raisedTyped : env.HasType universes.length (.sort outerLevel :: model.vlctx.toCtx)
      innerArgument.lift (.sort innerLevel) :=
    (modelWF.tr.wf.find?_wf envWF.ordered innerLookup).weak envWF.ordered
  have translated : TrExprS env universes
      ((none, .vlam (.sort innerLevel)) :: (none, .vlam (.sort outerLevel)) :: model.vlctx)
      (.forallE `pair (.bvar 1) (.bvar 1) .default) (.forallE (.bvar 1) (.bvar 1)) :=
    .forallE ⟨outerLevel, .bvar (.succ .zero)⟩ ⟨innerLevel, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl)
  have typed : env.HasType universes.length (.sort innerLevel :: .sort outerLevel :: model.vlctx.toCtx)
      (.forallE (.bvar 1) (.bvar 1)) (.sort (.imax outerLevel innerLevel)) :=
    VEnv.HasType.forallE (.bvar (.succ .zero)) (.bvar (.succ .zero))
  obtain ⟨_, ids, reduced, _, target, _, _, _, _, semantic,
    _, _, _, _, array, reducedTelescope, _, _, _, targetTelescope, _, _, _, _, _,
    _, _, _, _,
    _, _, _, _,
    _, _, _,
    _, _,
    _, _, _,
    _, _, _, _,
    targetTranslation, targetTyping, _, _, _⟩ :=
    history.selectedTelescopeRebasedSubstitutedPairTypeOfStoredDomains model modelWF native rfl reserved
      reader (.refl reader correspondence.1 reserved) envWF model modelWF .refl .refl stored rfl
      (by intro candidate member
          simp at member
          rcases member with rfl | rfl
          · exact outerMember
          · exact innerMember)
      (by simp) model modelWF 0 .refl (by simp) 0 outerIdentifier rfl 1 innerIdentifier rfl
      outerLookup innerLookup raisedTyped translated typed (by simp [Closed]) (by trivial)
  have idsEmpty : ids = [] := by simpa using array.symm
  subst ids
  refine ⟨reduced, target, semantic, reducedTelescope, targetTelescope, ?_, ?_⟩
  · simpa [Expr.instantiate1_eq, Expr.instantiate1'] using targetTranslation
  · simpa using targetTyping

private def outerParameter : FVarId := ⟨`IndexPairSubstitutionOuterParameter⟩
private def innerParameter : FVarId := ⟨`IndexPairSubstitutionInnerParameter⟩
private def earlierParameter : FVarId := ⟨`IndexPairSubstitutionEarlierParameter⟩
private def retainedPrefix : FVarId := ⟨`IndexPairSubstitutionRetainedPrefix⟩
private def firstSuffix : FVarId := ⟨`IndexPairSubstitutionFirstSuffix⟩
private def secondSuffix : FVarId := ⟨`IndexPairSubstitutionSecondSuffix⟩
private def discardedInitial : FVarId := ⟨`IndexPairSubstitutionDiscardedInitial⟩
private def prefixIndices : Array Expr := #[.fvar retainedPrefix]
private def finalIndices : Array Expr := #[.fvar retainedPrefix, .fvar firstSuffix, .fvar secondSuffix]
private def retainedBase : List FVarId := [outerParameter, innerParameter, earlierParameter, retainedPrefix]
private def endpointSupport : List FVarId :=
  ((finalIndices.toList.drop prefixIndices.size).map Expr.fvarId!).reverse ++ retainedBase

private theorem oldPrefixIsExcludedFromChronologicalSuffix :
    finalIndices.toList.drop prefixIndices.size = [.fvar firstSuffix, .fvar secondSuffix] ∧
      endpointSupport = [secondSuffix, firstSuffix, outerParameter, innerParameter, earlierParameter, retainedPrefix] := ⟨rfl, rfl⟩

private theorem historyReceiptFixesBothSuffixIdentifiers
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

private def pairedBody : Expr :=
  .forallE `suffix (.fvar secondSuffix)
    (.forallE `outer (.bvar 2)
      (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
        (.app (.bvar 2) (.app (.bvar 3) (.bvar 1))))) .default) .default

private def intermediateBody : Expr :=
  .forallE `suffix (.fvar secondSuffix)
    (.forallE `outer (.bvar 1)
      (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
        (.app (.fvar innerParameter) (.app (.bvar 2) (.bvar 1))))) .default) .default

private def finalBody : Expr :=
  .forallE `suffix (.fvar secondSuffix)
    (.forallE `outer (.fvar outerParameter)
      (.app (.fvar firstSuffix) (.app (.fvar retainedPrefix)
        (.app (.fvar innerParameter) (.app (.fvar outerParameter) (.bvar 1))))) .default) .default

private theorem suffixAndRetainedBaseSupportBothStages :
    pairedBody.FVarsIn (· ∈ endpointSupport) ∧ intermediateBody.FVarsIn (· ∈ endpointSupport) ∧
      finalBody.FVarsIn (· ∈ endpointSupport) := by
  simp [pairedBody, intermediateBody, finalBody, FVarsIn, endpointSupport, finalIndices, prefixIndices,
    retainedBase, Expr.fvarId!]

private theorem twoBinderClosureCannotBeReplacedByOneBinderClosure :
    Closed pairedBody 2 ∧ ¬ Closed pairedBody 1 ∧ Closed intermediateBody 1 ∧
      ¬ Closed intermediateBody 0 ∧ Closed finalBody 0 := by
  simp [pairedBody, intermediateBody, finalBody, Closed]

private theorem twoNativeStagesProtectTheSelectedLocalBinder :
    pairedBody.instantiate1' (.fvar innerParameter) = intermediateBody ∧
      (pairedBody.instantiate1' (.fvar innerParameter)).instantiate1' (.fvar outerParameter) = finalBody := ⟨rfl, rfl⟩

private theorem swappedSubstitutionOrderCannotProduceTheSameBody :
    (pairedBody.instantiate1' (.fvar outerParameter)).instantiate1' (.fvar innerParameter) ≠ finalBody := by
  simp [pairedBody, finalBody, Expr.instantiate1', Expr.liftLooseBVars', outerParameter, innerParameter]

private theorem missingSuffixCannotSupplyPairSupport : ¬ pairedBody.FVarsIn (· ∈ retainedBase) := by
  simp [pairedBody, FVarsIn, retainedBase, outerParameter, innerParameter, earlierParameter, retainedPrefix,
    firstSuffix, secondSuffix]

private theorem discardedInitialCannotSupplyPairSupport :
    ¬ (Expr.app pairedBody (.fvar discardedInitial)).FVarsIn (· ∈ endpointSupport) := by
  simp [pairedBody, FVarsIn, endpointSupport, finalIndices, prefixIndices, retainedBase, Expr.fvarId!,
    outerParameter, innerParameter, earlierParameter, retainedPrefix, firstSuffix, secondSuffix, discardedInitial]

private theorem twoNonzeroParameterPositionsAreNotTheIndexPrefixPositions :
    [earlierParameter, outerParameter, innerParameter][1]? = some outerParameter ∧
      [earlierParameter, outerParameter, innerParameter][2]? = some innerParameter ∧
      [earlierParameter, outerParameter, innerParameter][1]? ≠ some innerParameter ∧
      [earlierParameter, outerParameter, innerParameter][3]? = none := by
  simp [outerParameter, innerParameter, earlierParameter]

private theorem freshSuffixIdentifiersCannotReplaceSelectedParameters :
    firstSuffix ∉ [earlierParameter, outerParameter, innerParameter] ∧
      secondSuffix ∉ [earlierParameter, outerParameter, innerParameter] := by
  simp [firstSuffix, secondSuffix, earlierParameter, outerParameter, innerParameter]

private theorem endpointCutoffsProtectBothIndicesAndShiftBothArguments :
    (VExpr.bvar 0).lift' (.consN (.skip .refl) 2) = .bvar 0 ∧
      (VExpr.bvar 1).lift' (.consN (.skip .refl) 2) = .bvar 1 ∧
      (VExpr.bvar 2).lift' (.consN (.skip .refl) 2) = .bvar 3 ∧
      (VExpr.bvar 3).lift' (.consN (.skip .refl) 2) = .bvar 4 ∧
      (VExpr.bvar 0).lift' (.consN (.skipN .refl 3) 2) = .bvar 0 ∧
      (VExpr.bvar 1).lift' (.consN (.skipN .refl 3) 2) = .bvar 1 ∧
      (VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2) = .bvar 5 ∧
      (VExpr.bvar 3).lift' (.consN (.skipN .refl 3) 2) = .bvar 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem bothReducedInnerArgumentStillNeedsItsAnonymousOuterLift :
    pairSemantic (.forallE (.bvar 1) (.bvar 1)) (.bvar 4) (.bvar 3) = .forallE (.bvar 4) (.bvar 4) ∧
      ((VExpr.forallE (.bvar 1) (.bvar 1)).inst (.bvar 3)).inst (.bvar 4) ≠ .forallE (.bvar 4) (.bvar 4) := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private def semanticPosition : VExpr → Nat
  | .bvar position => position
  | _ => 1000

private def semanticPairPositions : VExpr → Option (Nat × Nat)
  | .forallE (.bvar outerPosition) (.bvar innerPosition) => some (outerPosition, innerPosition)
  | _ => none

private def runtimeControls : MetaM Unit := do
  let conditions := [
    (finalIndices.toList.drop prefixIndices.size == [.fvar firstSuffix, .fvar secondSuffix], "chronological suffix"),
    (endpointSupport == [secondSuffix, firstSuffix, outerParameter, innerParameter, earlierParameter, retainedPrefix], "reversed endpoint support"),
    (endpointSupport.contains retainedPrefix, "retained old prefix"),
    (!endpointSupport.contains discardedInitial, "discarded initial fvar"),
    (pairedBody.instantiate1' (.fvar innerParameter) == intermediateBody, "core intermediate"),
    (pairedBody.instantiate1 (.fvar innerParameter) == intermediateBody, "native intermediate"),
    ((pairedBody.instantiate1' (.fvar innerParameter)).instantiate1' (.fvar outerParameter) == finalBody, "core final"),
    (pairInstantiate pairedBody outerParameter innerParameter == finalBody, "native final"),
    (pairInstantiate pairedBody innerParameter outerParameter != finalBody, "swapped order"),
    ([earlierParameter, outerParameter, innerParameter][1]? == some outerParameter, "nonzero outer position"),
    ([earlierParameter, outerParameter, innerParameter][2]? == some innerParameter, "nonzero inner position"),
    ([earlierParameter, outerParameter, innerParameter][3]? == none, "out-of-range position"),
    (semanticPosition ((VExpr.bvar 0).lift' (.consN (.skip .refl) 2)) == 0, "first removal cutoff"),
    (semanticPosition ((VExpr.bvar 1).lift' (.consN (.skip .refl) 2)) == 1, "second removal cutoff"),
    (semanticPosition ((VExpr.bvar 2).lift' (.consN (.skip .refl) 2)) == 3, "inner removal position"),
    (semanticPosition ((VExpr.bvar 3).lift' (.consN (.skip .refl) 2)) == 4, "outer removal position"),
    (semanticPosition ((VExpr.bvar 0).lift' (.consN (.skipN .refl 3) 2)) == 0, "first insertion cutoff"),
    (semanticPosition ((VExpr.bvar 1).lift' (.consN (.skipN .refl 3) 2)) == 1, "second insertion cutoff"),
    (semanticPosition ((VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2)) == 5, "inner insertion position"),
    (semanticPosition ((VExpr.bvar 3).lift' (.consN (.skipN .refl 3) 2)) == 6, "outer insertion position"),
    (semanticPairPositions (pairSemantic (.forallE (.bvar 1) (.bvar 1)) (.bvar 4) (.bvar 3)) == some (4, 4), "both semantic argument shifts"),
    (semanticPairPositions (((VExpr.forallE (.bvar 1) (.bvar 1)).inst (.bvar 3)).inst (.bvar 4)) != some (4, 4), "missing raised inner argument"),
    (semanticPairPositions (pairSemantic (.forallE (.bvar 1) (.bvar 1)) (.bvar 3) (.bvar 4)) != some (4, 4), "swapped semantic argument order")]
  for (condition, label) in conditions do
    unless condition do throwError "index-pair-substitution-rebase runtime failed: {label}"
  logInfo m!"index-pair-substitution-rebase runtime: {conditions.length} suffix/two-stage/order/selection/cutoff controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "index-pair-substitution-rebase declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "index-pair-substitution-rebase unexpected axiom {axiomName} in {name}"

private def auditActualHistoryAdapter (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let name := ``TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutedPairTypeOfStoredDomains
  let some information := environment.find? name | throwError "index-pair-substitution-rebase adapter absent"
  if information matches .axiomInfo _ then throwError "index-pair-substitution-rebase adapter is an axiom"
  unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexRebase do
    throwError "index-pair-substitution-rebase adapter module provenance changed"
  auditDeclaration name allowed
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "index-pair-substitution-rebase exact inherited/native dependency manifest changed"
  logInfo "index-pair-substitution-rebase adapter: exact eight-axiom manifest; inherited logic/sorryAx, three persistent-container interfaces, native instantiate1 only"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq]
  let adapterAllowed := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``actualHistoryPairSubstitutionPreservesEveryReceipt adapterAllowed
  auditDeclaration ``emptyActualHistoryInstantiatesBothFormalBinders adapterAllowed
  let structuralControls := [``oldPrefixIsExcludedFromChronologicalSuffix, ``historyReceiptFixesBothSuffixIdentifiers,
    ``suffixAndRetainedBaseSupportBothStages, ``twoBinderClosureCannotBeReplacedByOneBinderClosure,
    ``twoNativeStagesProtectTheSelectedLocalBinder, ``swappedSubstitutionOrderCannotProduceTheSameBody,
    ``missingSuffixCannotSupplyPairSupport, ``discardedInitialCannotSupplyPairSupport,
    ``twoNonzeroParameterPositionsAreNotTheIndexPrefixPositions, ``freshSuffixIdentifiersCannotReplaceSelectedParameters,
    ``endpointCutoffsProtectBothIndicesAndShiftBothArguments, ``bothReducedInnerArgumentStillNeedsItsAnonymousOuterLift]
  for name in structuralControls do auditDeclaration name logical
  auditActualHistoryAdapter adapterAllowed
  runtimeControls
  logInfo m!"index-pair-substitution-rebase tests: {structuralControls.length + 2} proof controls; all 15 history/parameter and 25 pair receipts forwarded; actual empty translated history uses both formal binders; retained prefix plus two chronological suffix IDs; intermediate/final support and closure; order/selection/lift boundaries"

end InductiveIndexPairSubstitutionRebaseTest
