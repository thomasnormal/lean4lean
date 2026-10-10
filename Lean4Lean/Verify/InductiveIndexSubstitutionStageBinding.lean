import Lean4Lean.Verify.InductiveIndexSubstitutionStageRebase

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem IndexMLCtxExtension.typedBodyAbstractionS
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {body : Expr} {semantic : VExpr}
    (translated : TrExprS env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    TrExprS env universes initial.vlctx
        (final.lctx.mkForall (ids.map Expr.fvar).toArray body)
        (final.mkForall' ids.length extension.bound semantic) ∧
      env.IsType universes.length initial.vlctx.toCtx
        (final.mkForall' ids.length extension.bound semantic) := by
  have closed : body.looseBVarRange' = 0 :=
    (final.noBV ▸ translated.closed).looseBVarRange_zero
  rw [extension.nativeBodyAbstraction modelWF closed]
  simpa only [extension.drop_eq] using
    modelWF.mkForall_trS envWF translated typed ids.length extension.bound

theorem SelectedRecursorTelescope.scopedTypedAbstractionS
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (fullScope : full.BindingScope)
    {body : Expr} {semantic : VExpr}
    (translated : TrExprS env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    full.mkForall (ids.map Expr.fvar).toArray body =
        final.lctx.mkForall (ids.map Expr.fvar).toArray body ∧
      TrExprS env universes initial.vlctx (full.mkForall (ids.map Expr.fvar).toArray body)
        (final.mkForall' ids.length telescope.extension.bound semantic) ∧
      env.IsType universes.length initial.vlctx.toCtx
        (final.mkForall' ids.length telescope.extension.bound semantic) := by
  have binding := telescope.nativeBindingEquation initialWF fullScope translated
  obtain ⟨abstracted, abstractedTyped⟩ := telescope.extension.typedBodyAbstractionS
    envWF (telescope.context initialWF) translated typed
  exact ⟨binding, binding.symm ▸ abstracted, abstractedTyped⟩

theorem TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutionStageNativeForall
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (envWF : env.WF)
    (smaller : MLCtx) (smallerWF : smaller.WF env universes) (baseLift : Lift)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx model.vlctx 0 baseLift 0)
    {params : List FVarId} {steps : List BinderStep}
    (stored : BinderStoredIndexTypeFVarsIn params finalReader steps)
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
    ∃ (chronological : MLCtx) (ids : List FVarId) (reduced target : MLCtx)
        (reducedArgument reducedBody : VExpr)
        (chronologicalExtension : IndexMLCtxExtension model ids chronological)
        (reducedTelescope : SelectedRecursorTelescope env universes finalReader.lctx smaller ids reduced)
        (targetTelescope : SelectedRecursorTelescope env universes finalReader.lctx larger ids target),
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      reduced.WF env universes ∧ target.WF env universes ∧
      TrExprS env universes reduced.vlctx (body.instantiate1 (.fvar identifier))
        (reducedBody.inst reducedArgument) ∧
      env.HasType universes.length reduced.vlctx.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
      TrExprS env universes target.vlctx (body.instantiate1 (.fvar identifier))
        ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx (bodySemantic.inst originalArgument)
        ((reducedBody.inst reducedArgument).lift' (.consN baseLift ids.length)) (.sort level) ∧
      finalReader.lctx.BindingScope ∧ reduced.lctx.BindingScope ∧ target.lctx.BindingScope ∧
      (body.instantiate1 (.fvar identifier)).looseBVarRange' = 0 ∧
      finalReader.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)) =
        reduced.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)) ∧
      finalReader.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)) =
        target.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)) ∧
      TrExprS env universes model.vlctx
        (finalReader.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)))
        (chronological.mkForall' ids.length chronologicalExtension.bound (bodySemantic.inst originalArgument)) ∧
      env.IsType universes.length model.vlctx.toCtx
        (chronological.mkForall' ids.length chronologicalExtension.bound (bodySemantic.inst originalArgument)) ∧
      TrExprS env universes smaller.vlctx
        (finalReader.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)))
        (reduced.mkForall' ids.length reducedTelescope.extension.bound (reducedBody.inst reducedArgument)) ∧
      env.IsType universes.length smaller.vlctx.toCtx
        (reduced.mkForall' ids.length reducedTelescope.extension.bound (reducedBody.inst reducedArgument)) ∧
      TrExprS env universes larger.vlctx
        (finalReader.lctx.mkForall (ids.map Expr.fvar).toArray (body.instantiate1 (.fvar identifier)))
        (target.mkForall' ids.length targetTelescope.extension.bound
          ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length))) ∧
      env.IsType universes.length larger.vlctx.toCtx
        (target.mkForall' ids.length targetTelescope.extension.bound
          ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length))) ∧
      env.IsDefEqU universes.length model.vlctx.toCtx
        (chronological.mkForall' ids.length chronologicalExtension.bound (bodySemantic.inst originalArgument))
        ((reduced.mkForall' ids.length reducedTelescope.extension.bound
          (reducedBody.inst reducedArgument)).lift' baseLift) ∧
      env.IsDefEqU universes.length larger.vlctx.toCtx
        ((reduced.mkForall' ids.length reducedTelescope.extension.bound
          (reducedBody.inst reducedArgument)).lift' (.skipN .refl inserted))
        (target.mkForall' ids.length targetTelescope.extension.bound
          ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length))) := by
  have frame := history.scope reserved
  obtain ⟨chronological, ids, reduced, _, target, reducedArgument, _, _, reducedBody,
    chronologicalWF, chronologicalNative, chronologicalVirtual, extension, array,
    reducedTelescope, reducedWF, _, _, targetTelescope, targetWF, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, sourceTyped, endpointEquality, _, _, _,
    targetTyped, _, _, originalTranslation, reducedTranslation, _, targetTranslation⟩ :=
    history.selectedTelescopeRebasedSubstitutionStageOfStoredDomains model modelWF native converted reserved
      finalReader (.refl _ frame.wf frame.reserved) envWF smaller smallerWF baseLift baseWeakening
      stored values parameters prefixRetained larger largerWF inserted insertion freshBase
      position identifier selected originalLookup bodyTranslated bodyTyped bodyClosed bodySupport
  have fullScope : finalReader.lctx.BindingScope := chronologicalNative ▸ chronologicalWF.bindingScope
  have targetTranslation' : TrExprS env universes target.vlctx (body.instantiate1 (.fvar identifier))
      ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length)) := by
    simpa only [VExpr.lift'_inst_hi] using targetTranslation
  have targetTyped' : env.HasType universes.length target.vlctx.toCtx
      ((reducedBody.inst reducedArgument).lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) := by
    simpa only [VExpr.lift'_inst_hi] using targetTyped
  obtain ⟨originalAbstracted, originalAbstractedTyped⟩ := extension.typedBodyAbstractionS
    envWF chronologicalWF originalTranslation ⟨level, endpointEquality.hasType.1⟩
  obtain ⟨sourceBinding, sourceAbstracted, sourceAbstractedTyped⟩ :=
    reducedTelescope.scopedTypedAbstractionS envWF smallerWF fullScope reducedTranslation ⟨level, sourceTyped⟩
  obtain ⟨targetBinding, targetAbstracted, targetAbstractedTyped⟩ :=
    targetTelescope.scopedTypedAbstractionS envWF largerWF fullScope targetTranslation' ⟨level, targetTyped'⟩
  rw [chronologicalNative] at originalAbstracted
  have sourceInOriginal := sourceAbstracted.weakFV' envWF.ordered baseWeakening modelWF.tr.wf
  have sourceInTarget := sourceAbstracted.weakFV' envWF.ordered insertion.toFVLift' largerWF.tr.wf
  have originalAgreement := originalAbstracted.uniq envWF (.refl envWF.ordered modelWF.tr.wf) sourceInOriginal
  have targetAgreement := sourceInTarget.uniq envWF (.refl envWF.ordered largerWF.tr.wf) targetAbstracted
  exact ⟨chronological, ids, reduced, target, reducedArgument, reducedBody,
    extension, reducedTelescope, targetTelescope, chronologicalWF, chronologicalNative,
    chronologicalVirtual, array, reducedWF, targetWF, reducedTranslation, sourceTyped,
    targetTranslation', targetTyped', endpointEquality, fullScope, reducedWF.bindingScope, targetWF.bindingScope,
    (reduced.noBV ▸ reducedTranslation.closed).looseBVarRange_zero, sourceBinding, targetBinding,
    originalAbstracted, originalAbstractedTyped,
    sourceAbstracted, sourceAbstractedTyped, targetAbstracted, targetAbstractedTyped,
    originalAgreement, targetAgreement⟩

end Lean4Lean.AddInductive
