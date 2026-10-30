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

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      recursorRawType stats infos 0 finalReader.lctx =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray (recursorTypeBody infos 0) := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  refine ⟨chronological, receipt, ?_⟩
  simpa only [finalNative] using receipt.rawTypeFinalEquation finalWF finalNative bodyClosed

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    (bodySupport : RecursorTypeBodyApplicationSupport canonicalBoolModel [`u] infos 0 final.vlctx)
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      ∃ bodySemantic, ∃ level : VLevel,
        TrExprS canonicalBoolModel [`u] final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
        canonicalBoolModel.HasType [`u].length final.vlctx.toCtx bodySemantic (.sort level) ∧
        recursorRawType stats infos 0 finalReader.lctx =
          final.lctx.mkForall (grouped.map Expr.fvar).toArray (recursorTypeBody infos 0) := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  refine ⟨chronological, receipt, ?_⟩
  simpa only [finalNative] using
    receipt.finalBodyApplicationReceipt finalWF finalNative bodySupport bodyClosed

example {infos : Array RecInfo} {final : MLCtx} {elimLevel : Level}
    {motive major : FVarId}
    {semanticElimLevel : VLevel}
    (finalWF : final.WF canonicalBoolModel [`u])
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (majorEvidence : ∃ index name domain binder,
      final.lctx.find? major =
        some (.cdecl index major name domain binder .default))
    (motiveEvidence : ∃ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) ∧
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)))
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    RecursorTypeBodyApplicationSupport canonicalBoolModel [`u] infos 0 final.vlctx := by
  exact canonicalBoolRecursorTypeBodyApplicationSupport canonicalBoolModel.wf finalWF
    motiveEq indicesEq majorEq majorEvidence motiveEvidence mapped minorSemantics
    generatedRuleSemantics iotaSoundness

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    {motive major : FVarId} {semanticElimLevel : VLevel}
    (majorMember : major ∈ grouped) (motiveMember : motive ∈ grouped)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (motiveShape : ∀ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) →
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)))
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    RecursorTypeBodyApplicationSupport canonicalBoolModel [`u] infos 0 final.vlctx := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have majorEvidence : ∃ index name domain binder,
      final.lctx.find? major =
        some (.cdecl index major name domain binder .default) := by
    obtain ⟨_, projectedIndex, name, domain, binder, _, _, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF finalNative major majorMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup⟩
  have motiveEvidence : ∃ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) ∧
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)) := by
    obtain ⟨_, projectedIndex, name, domain, binder, _, _, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF finalNative motive motiveMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup,
      motiveShape projectedIndex name domain binder finalLookup⟩
  exact canonicalBoolRecursorTypeBodyApplicationSupport canonicalBoolModel.wf finalWF
    motiveEq indicesEq majorEq majorEvidence motiveEvidence mapped minorSemantics
    generatedRuleSemantics iotaSoundness

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
  auditTheorem ``RecursorBinderRebaseReceipt.rawTypeFinalEquation
  auditTheorem ``RecursorBinderRebaseReceipt.finalBodyApplicationReceipt
  auditTheorem ``canonicalBoolRecursorTypeBodyApplicationSupport
  auditTheorem ``canonicalBoolRecursorBinderOrderBoundary
  auditTheorem ``canonicalBoolRecursorBinderOrderPermutation
  logInfo "endpoint selected-domain, split/rebase, and allocation-order boundaries are theorem-backed"

end InductiveRecursorEndpointSelectedDomainTest
