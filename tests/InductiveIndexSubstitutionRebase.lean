import Lean4Lean.Verify.InductiveIndexRebase
import Lean.Util.CollectAxioms

namespace InductiveIndexSubstitutionRebaseTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

private theorem actualHistorySubstitutionPreservesEveryReceipt
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
    ∃ chronological ids reduced aligned target reducedArgument reducedArgumentType reducedSemantic,
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
      reduced.vlctx.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      TrExprS env universes reduced.vlctx (.fvar identifier) reducedArgument ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedArgument reducedArgumentType ∧
      Closed (body.instantiate1 (.fvar identifier)) 0 ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ reduced.vlctx.fvars) ∧
      TrExprS env universes chronological.vlctx (body.instantiate1 (.fvar identifier))
        (bodySemantic.inst originalArgument) ∧
      env.HasType universes.length chronological.vlctx.toCtx (bodySemantic.inst originalArgument) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (bodySemantic.inst originalArgument)
        (bodySemantic.inst (reducedArgument.lift' (.consN baseLift ids.length))) (.sort level) ∧
      TrExprS env universes reduced.vlctx (body.instantiate1 (.fvar identifier)) reducedSemantic ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (bodySemantic.inst originalArgument) (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        (bodySemantic.inst (reducedArgument.lift' (.consN baseLift ids.length)))
        (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) ∧
      TrExprS env universes target.vlctx (body.instantiate1 (.fvar identifier))
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) := by
  exact history.selectedTelescopeRebasedSubstitutedTypeOfStoredDomains model modelWF native converted
    reserved current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
    prefixRetained larger largerWF inserted insertion freshBase position identifier selected
    originalLookup bodyTranslated bodyTyped bodyClosed bodySupport

private theorem emptyActualHistorySubstitutesASelectedParameter
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    (model : MLCtx) (modelWF : model.WF env universes) (reader : Context)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (envWF : env.WF) (identifier : FVarId) (member : identifier ∈ model.vlctx.fvars)
    {argument : VExpr} {level : VLevel}
    (lookup : model.vlctx.find? (.inr identifier) = some (argument, .sort level)) :
    ∃ reduced target semantic,
      SelectedRecursorTelescope env universes reader.lctx model [] reduced ∧
      SelectedRecursorTelescope env universes reader.lctx model [] target ∧
      TrExprS env universes target.vlctx (.fvar identifier) semantic ∧
      env.HasType universes.length target.vlctx.toCtx semantic (.sort level) := by
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
  obtain ⟨_, ids, reduced, _, target, _, _, semantic, _, _, _, _, array,
    reducedTelescope, _, _, _, targetTelescope, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    targetTranslation, targetTyping⟩ :=
    history.selectedTelescopeRebasedSubstitutedTypeOfStoredDomains model modelWF native rfl reserved
      reader (.refl reader correspondence.1 reserved) envWF model modelWF .refl .refl stored rfl
      (by intro candidate candidateMember
          have candidateEq : candidate = identifier := by simpa using candidateMember
          simpa only [candidateEq] using member)
      (by simp) model modelWF 0 .refl (by simp) 0 identifier rfl lookup
      (body := .bvar 0) (bodySemantic := .bvar 0) (.bvar rfl) (.bvar .zero)
      (by simp [Closed]) (by trivial)
  have idsEmpty : ids = [] := by simpa using array.symm
  subst ids
  refine ⟨reduced, target, semantic, reducedTelescope, targetTelescope, ?_, ?_⟩
  · simpa [Expr.instantiate1_eq, Expr.instantiate1'] using targetTranslation
  · simpa using targetTyping

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
    (semanticPosition ((VExpr.bvar 2).lift' (.consN (.skipN .refl 3) 2)) == 5, "inserted parameter position")]
  for (condition, label) in conditions do
    unless condition do throwError "index-substitution-rebase runtime failed: {label}"
  logInfo m!"index-substitution-rebase runtime: {conditions.length} suffix/support/substitution/cutoff controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "index-substitution-rebase declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "index-substitution-rebase unexpected axiom {axiomName} in {name}"

private def auditActualHistoryAdapter (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let name := ``TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutedTypeOfStoredDomains
  let some information := environment.find? name | throwError "index-substitution-rebase adapter absent"
  if information matches .axiomInfo _ then throwError "index-substitution-rebase adapter is an axiom"
  unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexRebase do
    throwError "index-substitution-rebase adapter module provenance changed"
  auditDeclaration name allowed
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "index-substitution-rebase inherited/native dependency provenance changed"
  logInfo m!"index-substitution-rebase adapter: allowed inherited logic/sorryAx, three persistent-container interfaces, and only native instantiate1 interface"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq]
  let adapterAllowed := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``actualHistorySubstitutionPreservesEveryReceipt adapterAllowed
  auditDeclaration ``emptyActualHistorySubstitutesASelectedParameter adapterAllowed
  let structuralControls := [``existingPrefixIsNotPartOfTheSelectedSuffix,
    ``suffixReceiptKeepsChronologicalIdentifiers, ``suffixAndRetainedBaseSupportTheBody,
    ``bodyHasExactlyTheSubstitutionBinderPremise, ``missingSuffixCannotSupplyBodySupport,
    ``removedInitialCannotSupplyBodySupport, ``bodySubstitutionProtectsItsLocalBinder,
    ``selectedParameterPositionIsNotTheIndexPrefixPosition, ``indexSuffixCannotBeSelectedAsARetainedParameter,
    ``endpointLiftCutoffsProtectBothSelectedIndices, ``insertionLiftCannotReplaceTheRemovalReceipt]
  for name in structuralControls do auditDeclaration name logical
  auditActualHistoryAdapter adapterAllowed
  runtimeControls
  logInfo m!"index-substitution-rebase tests: {structuralControls.length + 2} proof controls; full forwarding of 15 history/parameter receipts and 14 substituted-type receipts; actual empty translated history; retained prefix plus two suffix IDs; closure/support/selection boundaries; distinct nonzero endpoint cutoffs"

end InductiveIndexSubstitutionRebaseTest
