import Lean4Lean.Verify.CanonicalBoolPassSupport
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean.Util.CollectAxioms

namespace InductiveRecursorEndpointSelectedDomainTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (alignment : ∀ ids, IndexMLCtxExtension initial ids final →
      (recursorTypeBinders stats infos 0).toList = ids.map Expr.fvar) :
    RecursorSelectedDomainSupport canonicalBoolModel [`u] stats infos 0 finalReader.lctx initial :=
  endpoint.selectedDomainSupport alignment

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final) :
    ∃ parentModel parentIds minorIds,
      IndexMLCtxExtension initial parentIds parentModel ∧
      IndexMLCtxExtension parentModel minorIds final ∧
      IndexMLCtxExtension initial (parentIds ++ minorIds) final :=
  endpoint.passExtensions

example {stats : InductiveStats} {infos : Array RecInfo}
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (distinct : major ≠ motive) :
    (recursorTypeBinders stats infos 0).toList ≠
      [major, motive, minorFalse, minorTrue].map Expr.fvar :=
  canonicalBoolRecursorBinderOrderBoundary params infosEq motiveEq minorsEq indicesEq majorEq distinct

example {motive minorFalse minorTrue major : FVarId} :
    [motive, minorFalse, minorTrue, major].Perm
      [major, motive, minorFalse, minorTrue] :=
  canonicalBoolRecursorBinderOrderPermutation

private def splitId : FVarId := ⟨`RecursorReceiptSplitId⟩
private def splitModel : MLCtx :=
  .vlam splitId `split (.sort .zero) (.sort .zero) .default .nil
private def splitExtension : IndexMLCtxExtension (.nil : MLCtx) [splitId] splitModel :=
  .push .nil splitId `split (.sort .zero) (.sort .zero) .default

example : ∃ middle,
    IndexMLCtxExtension (.nil : MLCtx) [] middle ∧
      IndexMLCtxExtension middle [splitId] splitModel :=
  splitExtension.split rfl

example : ∃ middle,
    IndexMLCtxExtension (.nil : MLCtx) [splitId] middle ∧
      IndexMLCtxExtension middle [] splitModel :=
  splitExtension.split rfl

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped :=
  endpoint.rebaseBinderOrder canonicalBoolModel.wf grouped order alignment

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      ∀ identifier, identifier ∈ grouped →
        ∃ physicalIndex projectedIndex name domain binder semantic,
          finalReader.lctx.find? identifier =
            some (.cdecl physicalIndex identifier name domain binder .default) ∧
          final.lctx.find? identifier =
            some (.cdecl projectedIndex identifier name domain binder .default) ∧
          TrExprS canonicalBoolModel [`u] final.vlctx domain semantic ∧
          canonicalBoolModel.IsType 1 final.vlctx.toCtx semantic := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  refine ⟨chronological, receipt, ?_⟩
  intro identifier member
  exact receipt.finalDomainSupport finalWF finalNative identifier member

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    {body : Expr} (bodyClosed : body.looseBVarRange' = 0) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      finalReader.lctx.mkForall (grouped.map Expr.fvar).toArray body =
      final.lctx.mkForall (grouped.map Expr.fvar).toArray body := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  refine ⟨chronological, receipt, ?_⟩
  simpa only [finalNative] using receipt.groupedBindingEquation finalWF finalNative bodyClosed

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "endpoint selected-domain support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "endpoint selected-domain support proof missing: {name}"
  if proof.hasSorry then
    throwError "endpoint selected-domain support has an admission: {name}"

run_meta
  auditTheorem ``RecursorInfoModelEndpoint.selectedDomainSupport
  auditTheorem ``RecursorInfoModelEndpoint.passExtensions
  auditTheorem ``IndexMLCtxExtension.split
  auditTheorem ``SelectedRecursorTelescope.domainReceiptWithSuffix
  auditTheorem ``RecursorInfoModelEndpoint.rebaseBinderOrder
  auditTheorem ``RecursorBinderRebaseReceipt.finalDomainSupport
  auditTheorem ``RecursorBinderRebaseReceipt.groupedBindingEquation
  auditTheorem ``canonicalBoolRecursorBinderOrderBoundary
  auditTheorem ``canonicalBoolRecursorBinderOrderPermutation
  logInfo "endpoint selected-domain, split/rebase, and allocation-order boundaries are theorem-backed"

end InductiveRecursorEndpointSelectedDomainTest
