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

example {initial final : MLCtx} {motive minorFalse minorTrue major : FVarId}
    (known : IndexMLCtxExtension initial [major, motive, minorFalse, minorTrue] final) :
    ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue] :=
  canonicalBoolAllocationOfKnownExtension known

example {full : LocalContext} {initial final : MLCtx}
    {motive minorFalse minorTrue major : FVarId}
    (chronological : SelectedRecursorTelescope canonicalBoolModel [`u] full initial
      [major, motive, minorFalse, minorTrue] final)
    (distinct : major ≠ motive) :
    ¬ SelectedRecursorTelescope canonicalBoolModel [`u] full initial
      [motive, minorFalse, minorTrue, major] final :=
  canonicalBoolGroupedTelescopeImpossible chronological distinct

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[]) (majorEq : info.major = .fvar major)
    (allocation : ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue]) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0
        finalReader.lctx initial final chronological
          [motive, minorFalse, minorTrue, major] :=
  endpoint.canonicalBoolRebaseBinderOrder canonicalBoolModel.wf params infosEq motiveEq
    minorsEq indicesEq majorEq allocation

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[]) (majorEq : info.major = .fvar major)
    (known : IndexMLCtxExtension initial [major, motive, minorFalse, minorTrue] final) :
    ∃ chronological,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological [motive, minorFalse, minorTrue, major] :=
  endpoint.canonicalBoolRebaseBinderOrderOfKnownExtension canonicalBoolModel.wf params infosEq
    motiveEq minorsEq indicesEq majorEq known

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[]) (majorEq : info.major = .fvar major)
    (allocation : ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue])
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    ∃ chronological bodySemantic level,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological [motive, minorFalse, minorTrue, major] ∧
      TrExprS canonicalBoolModel [`u] final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 finalReader.lctx =
        final.lctx.mkForall
          ([motive, minorFalse, minorTrue, major].map Expr.fvar).toArray
          (recursorTypeBody infos 0) :=
  endpoint.canonicalBoolRebasedFinalBodyApplicationReceipt canonicalBoolModel.wf
    params infosEq motiveEq minorsEq indicesEq majorEq allocation source mapped
    minorSemantics generatedRuleSemantics iotaSoundness

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
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0)
    (support : RecursorGroupedTypeTranslationSupport canonicalBoolModel [`u]
      finalReader.lctx initial grouped (recursorTypeBody infos 0)) :
    ∃ chronological bodySemantic level,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      TrExprS canonicalBoolModel [`u] initial.vlctx
        (recursorRawType stats infos 0 finalReader.lctx) bodySemantic ∧
      canonicalBoolModel.HasType 1 initial.vlctx.toCtx bodySemantic (.sort level) := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  obtain ⟨bodySemantic, level, translated, typed⟩ :=
    receipt.rawTypeTranslationFromGroupedSupport finalWF finalNative bodyClosed support
  exact ⟨chronological, bodySemantic, level, receipt, translated, typed⟩

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain canonicalBoolModel [`u]
      finalReader.lctx initial.vlctx (recursorTypeBody infos 0) grouped) :
    ∃ chronological bodySemantic level,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      TrExprS canonicalBoolModel [`u] initial.vlctx
        (recursorRawType stats infos 0 finalReader.lctx) bodySemantic ∧
      canonicalBoolModel.HasType 1 initial.vlctx.toCtx bodySemantic (.sort level) ∧
      TrExprS canonicalBoolModel [`u] final.vlctx
        (recursorRawType stats infos 0 finalReader.lctx)
        (bodySemantic.liftN (final.length - initial.length)) ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx
        (bodySemantic.liftN (final.length - initial.length)) (.sort level) := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  obtain ⟨bodySemantic, level, translated, typed, translatedFinal, typedFinal⟩ :=
    endpoint.rawTypeAtFinalFromGroupedChain receipt canonicalBoolModel.wf finalWF finalNative
      bodyClosed chain
  exact ⟨chronological, bodySemantic, level, receipt, translated, typed, translatedFinal, typedFinal⟩

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain canonicalBoolModel [`u]
      finalReader.lctx initial.vlctx (recursorTypeBody infos 0) grouped) :
    RecursorTypeModelReceipt canonicalBoolModel [`u] stats infos 0 finalReader initial final := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  exact endpoint.recursorTypeFromGroupedChain receipt canonicalBoolModel.wf finalWF finalNative
    bodyClosed chain

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    (bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain canonicalBoolModel [`u]
      finalReader.lctx initial.vlctx (recursorTypeBody infos 0) grouped) :
    ∃ chronological bodySemantic level,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      TrExprS canonicalBoolModel [`u] initial.vlctx
        (recursorRawType stats infos 0 finalReader.lctx) bodySemantic ∧
      canonicalBoolModel.HasType 1 initial.vlctx.toCtx bodySemantic (.sort level) := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder canonicalBoolModel.wf
    grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  obtain ⟨bodySemantic, level, translated, typed⟩ :=
    receipt.rawTypeTranslationFromGroupedChain finalWF finalNative bodyClosed chain
  exact ⟨chronological, bodySemantic, level, receipt, translated, typed⟩

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

example {stats : InductiveStats} {infos : Array RecInfo} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    {elimLevel : Level} {motive major : FVarId} {semanticElimLevel : VLevel}
    (receipt : RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 full
      initial final chronological grouped)
    (finalWF : final.WF canonicalBoolModel [`u]) (native : final.lctx = full)
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
    ∃ bodySemantic level,
      TrExprS canonicalBoolModel [`u] final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 full =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos 0) := by
  exact receipt.canonicalBoolFinalBodyApplicationReceipt canonicalBoolModel.wf finalWF native rfl
    majorMember motiveMember motiveEq indicesEq majorEq motiveShape mapped minorSemantics
    generatedRuleSemantics iotaSoundness

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader : Context} {infos : Array RecInfo} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    {motive major : FVarId} {semanticElimLevel : VLevel}
    (receipt : RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 full
      initial final chronological grouped)
    (typeReceipt : RecursorTypeModelReceipt canonicalBoolModel [`u] stats infos 0
      reader initial final)
    (readerNative : reader.lctx = full)
    (finalWF : final.WF canonicalBoolModel [`u]) (native : final.lctx = full)
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
    (iotaSoundness : IotaSoundness)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = [`u])
    (empty : initial.vlctx = []) :
    ∃ bodySemantic level constant,
      TrExprS canonicalBoolModel [`u] final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 reader.lctx =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray (recursorTypeBody infos 0) ∧
      TrConstVal .safe canonicalBoolModel
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          reader.lctx isK false 0 rules)) constant ∧
      constant.toVConstant.WF canonicalBoolModel := by
  exact receipt.canonicalBoolDeclaredRecursorReceipt typeReceipt readerNative
    canonicalBoolModel.wf finalWF native majorMember motiveMember motiveEq indicesEq majorEq
    motiveShape mapped minorSemantics generatedRuleSemantics iotaSoundness
    lparams isK rules levels empty

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (initialWF : initial.WF canonicalBoolModel [`u])
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport canonicalBoolModel [`u] stats infos 0
      finalReader.lctx initial)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    {motive major : FVarId}
    (majorMember : major ∈ grouped) (motiveMember : motive ∈ grouped)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = [`u])
    (empty : initial.vlctx = [])
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (minorSemantics : MinorSemantics)
    (generatedRuleSemantics : GeneratedRuleSemantics)
    (iotaSoundness : IotaSoundness) :
    ∃ chronological bodySemantic level constant,
      RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      TrExprS canonicalBoolModel [`u] final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 finalReader.lctx =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos 0) ∧
      TrConstVal .safe canonicalBoolModel
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          finalReader.lctx isK false 0 rules)) constant ∧
      constant.toVConstant.WF canonicalBoolModel := by
  exact endpoint.canonicalBoolDeclaredRecursorReceipt canonicalBoolModel.wf initialWF
    parameterFree bound source mapped support grouped order alignment majorMember motiveMember
    motiveEq indicesEq majorEq lparams isK rules levels empty minorSemantics
    generatedRuleSemantics iotaSoundness

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (initialWF : initial.WF canonicalBoolModel [`u])
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport canonicalBoolModel [`u] stats infos 0
      finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = [`u])
    (empty : initial.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel infos
      lparams finalReader.lctx isK false 0 rules) :
    ∃ constant,
      registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt canonicalBoolModel [`u] stats infos 0 finalReader initial final ∧
      TrConstVal .safe canonicalBoolModel (.recInfo recursor) constant ∧
      constant.toVConstant.WF canonicalBoolModel := by
  exact endpoint.registeredRecursorFromDomains canonicalBoolModel.wf initialWF parameterFree bound
    source mapped support lparams isK rules levels empty lookup metadata

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (initialWF : initial.WF canonicalBoolModel [`u])
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel [`u] elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport canonicalBoolModel [`u] stats infos 0
      finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = [`u])
    (empty : initial.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel infos
      lparams finalReader.lctx isK false 0 rules)
    (fresh : (canonicalBoolModel : VEnv).constants (mkRecName types[0]!.name) = none) :
    ∃ constant extended,
      registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt canonicalBoolModel [`u] stats infos 0 finalReader initial final ∧
      TrConstVal .safe canonicalBoolModel (.recInfo recursor) constant ∧
      constant.toVConstant.WF canonicalBoolModel ∧
      canonicalBoolModel.addConstructorHeaders [constant] = some extended ∧ extended.WF := by
  exact endpoint.registeredRecursorInsertionFromDomains canonicalBoolModel.wf initialWF
    parameterFree bound source mapped support lparams isK rules levels empty lookup metadata fresh

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
      receipt.dependencyAwareRebase.finalDomainSupport canonicalBoolModel.wf finalWF
        finalNative major majorMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup⟩
  have motiveEvidence : ∃ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) ∧
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)) := by
    obtain ⟨_, projectedIndex, name, domain, binder, _, _, finalLookup, _, _⟩ :=
      receipt.dependencyAwareRebase.finalDomainSupport canonicalBoolModel.wf finalWF
        finalNative motive motiveMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup,
      motiveShape projectedIndex name domain binder finalLookup⟩
  exact canonicalBoolRecursorTypeBodyApplicationSupport canonicalBoolModel.wf finalWF
    motiveEq indicesEq majorEq majorEvidence motiveEvidence mapped minorSemantics
    generatedRuleSemantics iotaSoundness

example {stats : InductiveStats} {infos : Array RecInfo} {parent : Nat}
    {full : LocalContext} {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF canonicalBoolModel [`u]) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped) {nativeDecl : LocalDecl}
    (nativeLookup : full.find? identifier = some nativeDecl) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      nativeDecl = .cdecl physicalIndex identifier name domain binder .default ∧
      final.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) ∧
      TrExprS canonicalBoolModel [`u] final.vlctx domain semantic ∧
      canonicalBoolModel.IsType 1 final.vlctx.toCtx semantic :=
  receipt.finalDomainSupportOfNativeDecl finalWF native identifier member nativeLookup

example {stats : InductiveStats} {infos : Array RecInfo} {parent : Nat}
    {full : LocalContext} {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF canonicalBoolModel [`u]) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped) {domain : Expr}
    (domainLookup : ∃ index name binder,
      final.lctx.find? identifier =
        some (.cdecl index identifier name domain binder .default))
    (closed : Closed domain 0)
    (free : FVarsIn (· ∈ initial.vlctx.fvars) domain) :
    ∃ semantic, TrExprS canonicalBoolModel [`u] initial.vlctx domain semantic :=
  receipt.initialDomainTranslationOfFinal canonicalBoolModel.wf finalWF native identifier member
    domainLookup closed free

example {stats : InductiveStats} {infos : Array RecInfo} {parent : Nat}
    {full : LocalContext} {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt canonicalBoolModel [`u] stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF canonicalBoolModel [`u]) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped) {domain : Expr}
    (domainLookup : ∃ index name binder,
      final.lctx.find? identifier =
        some (.cdecl index identifier name domain binder .default))
    (closed : Closed domain 0)
    (free : FVarsIn (· ∈ initial.vlctx.fvars) domain) :
    ∃ semantic level,
      TrExprS canonicalBoolModel [`u] initial.vlctx domain semantic ∧
      canonicalBoolModel.HasType 1 initial.vlctx.toCtx semantic (.sort level) :=
  receipt.initialDomainTranslationAndTypeOfFinal canonicalBoolModel.wf finalWF native
    identifier member domainLookup closed free

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
  auditTheorem ``IndexMLCtxExtension.eq_ids_of_same_final
  auditTheorem ``SelectedRecursorTelescope.domainReceiptWithSuffix
  auditTheorem ``RecursorInfoModelEndpoint.rebaseBinderOrder
  auditTheorem ``RecursorBinderRebaseReceipt.dependencyAwareRebase
  auditTheorem ``DependencyAwareVirtualContextRebase.finalDomainSupport
  auditTheorem ``RecursorBinderRebaseReceipt.finalDomainSupport
  auditTheorem ``RecursorBinderRebaseReceipt.finalDomainSupportOfNativeDecl
  auditTheorem ``RecursorBinderRebaseReceipt.initialDomainTranslationOfFinal
  auditTheorem ``RecursorBinderRebaseReceipt.initialDomainTranslationAndTypeOfFinal
  auditTheorem ``RecursorBinderRebaseReceipt.finalDomainSupportOfSourceMajor
  auditTheorem ``RecursorBinderRebaseReceipt.finalDomainSupportOfSourceMotive
  auditTheorem ``RecursorBinderRebaseReceipt.groupedBindingEquation
  auditTheorem ``RecursorBinderRebaseReceipt.rawTypeFinalEquation
  auditTheorem ``RecursorBinderRebaseReceipt.rawTypeTranslationFromGroupedSupport
  auditTheorem ``RecursorBinderRebaseReceipt.rawTypeTranslationFromGroupedChain
  auditTheorem ``RecursorInfoModelEndpoint.rawTypeAtFinalFromGroupedChain
  auditTheorem ``RecursorInfoModelEndpoint.recursorTypeFromGroupedChain
  auditTheorem ``RecursorBinderRebaseReceipt.finalBodyApplicationReceipt
  auditTheorem ``canonicalBoolRecursorTypeBodyApplicationSupport
  auditTheorem ``RecursorBinderRebaseReceipt.canonicalBoolFinalBodyApplicationReceipt
  auditTheorem ``RecursorBinderRebaseReceipt.canonicalBoolDeclaredRecursorReceipt
  auditTheorem ``RecursorInfoModelEndpoint.canonicalBoolDeclaredRecursorReceipt
  auditTheorem ``RecursorInfoModelEndpoint.registeredRecursorFromDomains
  auditTheorem ``RecursorInfoModelEndpoint.registeredRecursorInsertionFromDomains
  auditTheorem ``canonicalBoolRecursorBinderOrderBoundary
  auditTheorem ``canonicalBoolRecursorBinderOrderPermutation
  auditTheorem ``canonicalBoolAllocationOfKnownExtension
  auditTheorem ``SelectedRecursorTelescope.no_reordered_ids
  auditTheorem ``canonicalBoolGroupedTelescopeImpossible
  auditTheorem ``RecursorInfoModelEndpoint.canonicalBoolRebaseBinderOrder
  auditTheorem ``RecursorInfoModelEndpoint.canonicalBoolRebaseBinderOrderOfKnownExtension
  auditTheorem ``RecursorInfoModelEndpoint.canonicalBoolRebasedFinalBodyApplicationReceipt
  logInfo "endpoint selected-domain, split/rebase, and allocation-order boundaries are theorem-backed"

end InductiveRecursorEndpointSelectedDomainTest
