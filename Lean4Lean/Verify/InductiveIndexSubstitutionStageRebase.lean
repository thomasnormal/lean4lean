import Lean4Lean.Verify.InductiveIndexRebase
import Lean4Lean.Verify.InductiveParameterSubstitutionStage

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutionStageOfStoredDomains
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
      Expr.fvar identifier ∈ finalIndices.toList.drop indices.size →
      identifier ∉ larger.vlctx.fvars)
    (position : Nat) (identifier : FVarId) (selected : params[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : finalVirtual.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes ((none, .vlam originalArgumentType) :: finalVirtual) body bodySemantic)
    (bodyTyped : env.HasType universes.length (originalArgumentType :: finalVirtual.toCtx) bodySemantic (.sort level))
    (bodyClosed : Closed body 1)
    (bodySupport : body.FVarsIn
      (· ∈ ((finalIndices.toList.drop indices.size).map Expr.fvarId!).reverse ++
        smaller.vlctx.fvars)) :
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
      VLCtx.FVLift' reduced.vlctx target.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 ∧
      RetainedFVarPrefix env universes smaller.vlctx larger.vlctx
        (.skipN .refl inserted) params ∧
      RetainedFVarPrefix env universes reduced.vlctx target.vlctx
        (.consN (.skipN .refl inserted) ids.length) params ∧
      RetainedFVarPrefixAgreement env universes reduced.vlctx chronological.vlctx aligned
        (.consN baseLift ids.length) params ∧
      reduced.vlctx.find? (.inr identifier) = some (reducedArgument, reducedDomain) ∧
      TrExprS env universes reduced.vlctx (.fvar identifier) reducedArgument ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        originalArgumentType (reducedDomain.lift' (.consN baseLift ids.length)) (.sort domainLevel) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx
        originalArgument (reducedArgument.lift' (.consN baseLift ids.length)) originalArgumentType ∧
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
  obtain ⟨chronological, ids, reduced, aligned, target, chronologicalWF, chronologicalNative,
    chronologicalVirtual, extension, array, reducedTelescope, reducedWF, contraction, contexts,
    targetTelescope, targetWF, insertionWeakening, baseParameters, endpointParameters,
    chronologicalParameters⟩ :=
    history.selectedTelescopeRebasedOfStoredDomains model modelWF native converted reserved
      current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
      prefixRetained larger largerWF inserted insertion freshBase
  have suffix : finalIndices.toList.drop indices.size = ids.map Expr.fvar := by
    rw [array, ← Array.length_toList, List.drop_left]
  have reducedFVars : reduced.vlctx.fvars = ids.reverse ++ smaller.vlctx.fvars :=
    reducedTelescope.extension.virtualFVars
  have reducedBodySupport : body.FVarsIn (· ∈ reduced.vlctx.fvars) := by
    simpa only [reducedFVars, suffix, List.map_map, Function.comp_def, Expr.fvarId!, List.map_id'] using bodySupport
  have originalLookup' : chronological.vlctx.find? (.inr identifier) =
      some (originalArgument, originalArgumentType) := by
    simpa only [chronologicalVirtual] using originalLookup
  have bodyTranslated' : TrExprS env universes
      ((none, .vlam originalArgumentType) :: chronological.vlctx) body bodySemantic := by
    simpa only [chronologicalVirtual] using bodyTranslated
  have bodyTyped' : env.HasType universes.length
      (originalArgumentType :: chronological.vlctx.toCtx) bodySemantic (.sort level) := by
    simpa only [chronologicalVirtual] using bodyTyped
  obtain ⟨reducedArgument, reducedDomain, domainLevel, reducedBody, reducedLookup, argumentTranslation,
    domainEquality, argumentEquality, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality,
    targetBodyTranslation, targetBodyTyped, targetArgumentTyped, targetEndpointTyped, substitutedClosed,
    substitutedSupport, originalInstantiatedTranslation, reducedInstantiatedTranslation,
    targetArgumentTranslation, targetInstantiatedTranslation⟩ :=
    chronologicalParameters.instantiateStageIsTypeRebased envWF contraction contexts insertionWeakening
      targetWF.tr.wf position identifier selected originalLookup' bodyTranslated' bodyTyped'
      bodyClosed reducedBodySupport
  exact ⟨chronological, ids, reduced, aligned, target, reducedArgument, reducedDomain, domainLevel,
    reducedBody, chronologicalWF, chronologicalNative, chronologicalVirtual, extension, array,
    reducedTelescope, reducedWF, contraction, contexts, targetTelescope, targetWF, insertionWeakening,
    baseParameters, endpointParameters, chronologicalParameters, reducedLookup, argumentTranslation,
    domainEquality, argumentEquality, bodyWeakening, bodyContexts, reducedDomainTyped, reducedBodyTranslation,
    reducedBodyTyped, bodyEquality, reducedArgumentTyped, reducedEndpointTyped, endpointEquality,
    targetBodyTranslation, targetBodyTyped, targetArgumentTyped, targetEndpointTyped, substitutedClosed,
    substitutedSupport, originalInstantiatedTranslation, reducedInstantiatedTranslation,
    targetArgumentTranslation, targetInstantiatedTranslation⟩

end Lean4Lean.AddInductive
