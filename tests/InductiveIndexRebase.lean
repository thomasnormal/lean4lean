import Lean4Lean.Verify.InductiveIndexRebase

namespace InductiveIndexRebaseTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

private theorem rebaseReceiptComposes
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller larger : MLCtx} {ids removedIds : List FVarId}
    {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (removal : IndexMLCtxExtension smaller removedIds initial)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids)
    (largerWF : larger.WF env universes)
    (insertion : VLCtx.FVLift smaller.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ reduced aligned target,
      SelectedRecursorTelescope env universes full smaller ids reduced ∧
      reduced.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx aligned 0
        (.consN (.skipN .refl removedIds.length) ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned ∧
      SelectedRecursorTelescope env universes full larger ids target ∧
      target.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 := by
  exact telescope.rebase envWF initialWF removal supported largerWF insertion freshBase

private theorem selectedTelescopeBodyRebaseComposes
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller larger : MLCtx} {ids removedIds : List FVarId}
    {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (removal : IndexMLCtxExtension smaller removedIds initial)
    (selectedSupport : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids)
    (largerWF : larger.WF env universes)
    (insertion : VLCtx.FVLift smaller.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars)
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes final.vlctx body bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level))
    (bodyClosed : Closed body 0)
    (bodySupport : body.FVarsIn (· ∈ ids.reverse ++ smaller.vlctx.fvars)) :
    ∃ reduced aligned target reducedSemantic,
      SelectedRecursorTelescope env universes full smaller ids reduced ∧
      reduced.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx aligned 0
        (.consN (.skipN .refl removedIds.length) ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned ∧
      SelectedRecursorTelescope env universes full larger ids target ∧
      target.WF env universes ∧
      VLCtx.FVLift' reduced.vlctx target.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 ∧
      TrExprS env universes reduced.vlctx body reducedSemantic ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length final.vlctx.toCtx bodySemantic
        (reducedSemantic.lift' (.consN (.skipN .refl removedIds.length) ids.length))
        (.sort level) ∧
      TrExprS env universes target.vlctx body
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) := by
  exact telescope.rebaseBodyIsType envWF initialWF removal selectedSupport largerWF insertion
    freshBase bodyTranslated bodyTyped bodyClosed bodySupport

private theorem actualHistoryRebaseReceiptComposes
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
      identifier ∉ larger.vlctx.fvars) :
    ∃ chronological ids reduced aligned target,
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
        (.consN baseLift ids.length) params := by
  exact history.selectedTelescopeRebasedOfStoredDomains model modelWF native converted reserved
    current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
    prefixRetained larger largerWF inserted insertion freshBase

private theorem actualHistoryBodyRebaseReceiptComposes
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
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (bodyTranslated : TrExprS env universes finalVirtual body bodySemantic)
    (bodyTyped : env.HasType universes.length finalVirtual.toCtx bodySemantic (.sort level))
    (bodyClosed : Closed body 0)
    (bodySupport : body.FVarsIn
      (· ∈ ((finalIndices.toList.drop indices.size).map Expr.fvarId!).reverse ++
        smaller.vlctx.fvars)) :
    ∃ chronological ids reduced aligned target reducedSemantic,
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
      TrExprS env universes reduced.vlctx body reducedSemantic ∧
      env.HasType universes.length reduced.vlctx.toCtx reducedSemantic (.sort level) ∧
      env.IsDefEq universes.length chronological.vlctx.toCtx bodySemantic
        (reducedSemantic.lift' (.consN baseLift ids.length)) (.sort level) ∧
      TrExprS env universes target.vlctx body
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) ∧
      env.HasType universes.length target.vlctx.toCtx
        (reducedSemantic.lift' (.consN (.skipN .refl inserted) ids.length)) (.sort level) := by
  exact history.selectedTelescopeRebasedBodyOfStoredDomains model modelWF native converted reserved
    current frame envWF smaller smallerWF baseLift baseWeakening stored values parameters
    prefixRetained larger largerWF inserted insertion freshBase bodyTranslated bodyTyped bodyClosed
    bodySupport

end InductiveIndexRebaseTest
