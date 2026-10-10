import Lean4Lean.Verify.InductiveCtorFieldTranslationCPS
import Lean4Lean.Verify.InductiveIHTranslationCPS
import Lean4Lean.Verify.InductiveMinorTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem CtorFieldOpening.application {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semanticDomain bodySemantic peeled convertedBody : VExpr} {level : VLevel}
    (opening : CtorFieldOpening env universes reader virtual name domain body bi
      semanticDomain bodySemantic level peeled convertedBody)
    (envWF : env.WF) {value : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual value semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue
      (.forallE semanticDomain bodySemantic)) :
    TrExprS env universes
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
        (.app value (.fvar ⟨reader.ngen.curr⟩)) (.app semanticValue.lift (.bvar 0)) ∧
      env.HasType universes.length
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
        (.app semanticValue.lift (.bvar 0)) convertedBody := by
  have nextWF := opening.context.wf
  have weakening : VLCtx.FVLift virtual
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled) 0 1 0 :=
    .skip_fvar _ _ .refl
  have valueTranslated := translated.weakFV envWF.ordered weakening nextWF
  have valueTyped : env.HasType universes.length
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
      semanticValue.lift (.forallE semanticDomain.lift (bodySemantic.liftN 1 1)) := by
    simpa only [peeledIndexVirtualContext, VLCtx.toCtx, VExpr.lift, VExpr.liftN]
      using typed.weak envWF.ordered (B := peeled)
  have argumentTranslated : TrExprS env universes
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
      (.fvar ⟨reader.ngen.curr⟩) (.bvar 0) :=
    .fvar (A := peeled.lift) (by
      simp [peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type])
  have argumentTyped : env.HasType universes.length
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
      (.bvar 0) semanticDomain.lift :=
    (opening.domainEquality.weak envWF.ordered (B := peeled)).symm.defeq (.bvar .zero)
  have applicationTyped : env.HasType universes.length
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
      (.app semanticValue.lift (.bvar 0)) bodySemantic := by
    simpa only [VExpr.instN_bvar0] using valueTyped.app argumentTyped
  exact ⟨.app valueTyped argumentTyped valueTranslated argumentTranslated,
    applicationTyped.defeqU_r envWF nextWF.toCtx opening.bodyEquality.symm⟩

theorem TranslatedRecursorCtorFieldTrace.application
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) {head : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual (mkAppN head fields) semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue semantic) :
    ∃ finalValue,
      TrExprS env universes finalVirtual (mkAppN head finalFields) finalValue ∧
        env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic := by
  induction history generalizing semanticValue with
  | stop => exact ⟨semanticValue, translated, typed⟩
  | field _ _ _ _ opening _ tailInduction =>
    obtain ⟨applicationTranslated, applicationTyped⟩ := opening.application envWF translated typed
    exact tailInduction (by simpa only [mkAppN_indexPush] using applicationTranslated) applicationTyped

theorem CtorFieldModelEndpoint.application
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    {initial fieldModel : MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial fieldModel semantic)
    (envWF : env.WF) {head : Expr} {headSemantic : VExpr}
    (headTranslated : TrExprS env universes initial.vlctx head headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic) :
    ∃ value terminalSemantic,
      TrExprS env universes fieldModel.vlctx (mkAppN head fields) value ∧
      TrExprS env universes fieldModel.vlctx terminal terminalSemantic ∧
      env.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic := by
  obtain ⟨_, finalSemantic, history, _, _, converted, _⟩ := endpoint
  obtain ⟨value, translated, typed⟩ := history.application envWF headTranslated headTyped
  exact ⟨value, finalSemantic, by simpa only [converted] using translated,
    by simpa only [converted] using history.finalTranslation.2,
    by simpa only [converted] using typed⟩

theorem IndexMLCtxExtension.selectedBindingAtLaterContext
    {env : VEnv} {universes : List Name} {initial fieldModel hypothesisModel : MLCtx}
    {ids : List FVarId} {fieldReader hypothesisReader : Context}
    (extension : IndexMLCtxExtension initial ids fieldModel)
    (fieldWF : fieldModel.WF env universes) (hypothesisWF : hypothesisModel.WF env universes)
    (fieldNative : fieldModel.lctx = fieldReader.lctx)
    (hypothesisNative : hypothesisModel.lctx = hypothesisReader.lctx)
    (frame : fieldReader.RecursorScopeFrame hypothesisReader)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes fieldModel.vlctx body bodySemantic) :
    hypothesisReader.lctx.mkForall (ids.map Expr.fvar).toArray body =
      fieldReader.lctx.mkForall (ids.map Expr.fvar).toArray body := by
  have closed : body.looseBVarRange' = 0 :=
    (fieldModel.noBV ▸ translated.closed).looseBVarRange_zero
  have distinct : ids.Nodup := by
    have selected := fieldWF.fvarRevList_nodup ids.length extension.bound
    rw [extension.selection] at selected
    exact List.nodup_reverse.mp selected
  have lookups : ∀ selected ∈ ids,
      hypothesisModel.lctx.find? selected = fieldModel.lctx.find? selected := by
    intro selected member
    have present : selected ∈ fieldModel.vlctx.fvars := by
      have suffix := MLCtx.fvarRevList_prefix fieldModel (n := ids.length) (hn := extension.bound)
      rw [extension.selection] at suffix
      exact suffix.subset (List.mem_reverse.mpr member)
    cases oldLookup : fieldModel.lctx.find? selected with
    | none => exact False.elim ((fieldWF.tr.find?_eq_none.mp oldLookup) present)
    | some declaration =>
      have originalLookup : fieldReader.lctx.find? selected = some declaration := by
        simpa only [fieldNative] using oldLookup
      have laterLookup := frame.oldLookup (fieldNative ▸ fieldWF.tr.1) originalLookup
      simpa only [← hypothesisNative] using laterLookup
  simpa only [fieldNative, hypothesisNative] using
    mkForall_congr_selected ids hypothesisWF.bindingScope fieldWF.bindingScope closed distinct lookups

theorem CtorFieldModelEndpoint.minorBodyTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields : Array Expr} {reader fieldReader : Context}
    {trace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    {initial fieldModel : MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial fieldModel semantic)
    (envWF : env.WF)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ bodySemantic level,
      TrExprS env universes fieldModel.vlctx
        (recursorMinorBody stats infos constructor terminal fields) bodySemantic ∧
      env.HasType universes.length fieldModel.vlctx.toCtx bodySemantic (.sort level) := by
  obtain ⟨value, terminalSemantic, valueTranslated, terminalTranslated, valueTyped⟩ :=
    endpoint.application envWF headTranslated headTyped
  obtain ⟨motiveSemantic, level, motiveTranslated, motiveTyped⟩ :=
    motiveSupport terminalSemantic terminalTranslated
  refine ⟨.app motiveSemantic value, level, ?_, ?_⟩
  · exact TrExprS.app motiveTyped valueTyped motiveTranslated valueTranslated
  · simpa only [VExpr.inst] using motiveTyped.app valueTyped

theorem CtorFieldModelEndpoint.minorDomainTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursiveFields infos 0 #[]
      fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ domainSemantic level,
      TrExprS env universes initial.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)
        domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx domainSemantic (.sort level) := by
  obtain ⟨bodySemantic, bodyLevel, bodyTranslated, bodyTyped⟩ :=
    endpoint.minorBodyTranslation envWF headTranslated headTyped motiveSupport
  obtain ⟨hypothesisIds, hypothesisExtension, _⟩ := history.extension
  have hypothesisWF := history.context.1
  have translatedLater := bodyTranslated.weakFV envWF.ordered hypothesisExtension.weakening
    hypothesisWF.tr.wf
  have typedLater := bodyTyped.weakN envWF.ordered hypothesisExtension.weakening.toCtx
  obtain ⟨innerSemantic, innerTranslated, innerTyped⟩ := history.typedHypothesisAbstraction envWF
    ⟨_, translatedLater, typedLater.toU⟩ ⟨bodyLevel, typedLater⟩
  have endpointCopy := endpoint
  obtain ⟨_, _, _, fieldWF, fieldNative, _, fieldIds, fieldExtension, selected⟩ := endpointCopy
  have arrays : fields = (fieldIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  have fieldFrame := hypothesisTrace.scope (fieldNative ▸ fieldWF.tr.1) reserved
  have outerEquality := fieldExtension.selectedBindingAtLaterContext fieldWF hypothesisWF
    fieldNative history.context.2.1 fieldFrame innerTranslated
  have outerFieldsEquality : hypothesisReader.lctx.mkForall fields
      (hypothesisReader.lctx.mkForall hypotheses
        (recursorMinorBody stats infos constructor terminal fields)) =
      fieldReader.lctx.mkForall fields (hypothesisReader.lctx.mkForall hypotheses
        (recursorMinorBody stats infos constructor terminal fields)) := by
    simpa only [arrays] using outerEquality
  obtain ⟨domainSemantic, domainTranslated, level, domainTyped⟩ :=
    endpoint.typedFieldAbstraction envWF innerTranslated innerTyped
  obtain ⟨strictSemantic, strictTranslated, equality⟩ := domainTranslated
  refine ⟨strictSemantic, level, ?_,
    domainTyped.defeqU_l envWF modelWF.tr.wf.toCtx equality.symm⟩
  simpa only [recursorMinorDomain, outerFieldsEquality] using strictTranslated

theorem CtorFieldModelEndpoint.liftedMinorDomainTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursiveFields infos 0 #[]
      fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal) :
    ∃ domainSemantic level,
      TrExprS env universes initial.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)
        domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx domainSemantic (.sort level) ∧
      TrExprS env universes hypothesisModel.vlctx
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)
        (domainSemantic.liftN (fields.size + hypotheses.size)) ∧
      env.HasType universes.length hypothesisModel.vlctx.toCtx
        (domainSemantic.liftN (fields.size + hypotheses.size)) (.sort level) := by
  obtain ⟨domainSemantic, level, translated, typed⟩ := endpoint.minorDomainTranslation history
    envWF modelWF reserved headTranslated headTyped motiveSupport
  obtain ⟨_, _, _, _, _, _, fieldIds, fieldExtension, selectedFields⟩ := endpoint
  obtain ⟨hypothesisIds, hypothesisExtension, selectedHypotheses⟩ := history.extension
  have combined := fieldExtension.trans hypothesisExtension
  have fieldCount : fields.size = fieldIds.length := by
    simpa only [Array.length_toList, List.length_map] using congrArg List.length selectedFields
  have hypothesisCount : hypotheses.size = hypothesisIds.length := by
    simpa only [Array.toList_empty, List.nil_append, Array.length_toList, List.length_map]
      using congrArg List.length selectedHypotheses
  refine ⟨domainSemantic, level, translated, typed, ?_, ?_⟩
  · simpa only [List.length_append, fieldCount, hypothesisCount] using
      translated.weakFV envWF.ordered combined.weakening history.context.1.tr.wf
  · simpa only [List.length_append, fieldCount, hypothesisCount, VExpr.liftN] using
      typed.weakN envWF.ordered combined.weakening.toCtx

structure RecursorMinorOpening (env : VEnv) (universes : List Name) (reader : Context)
    (virtual : VLCtx) (parentName : Name) (constructor : Constructor) (domain : Expr)
    (rawSemantic peeled : VExpr) (level : VLevel) : Prop where
  domainTranslated : TrExprS env universes virtual domain rawSemantic
  domainTyped : env.HasType universes.length virtual.toCtx rawSemantic (.sort level)
  peeledTranslated : TrExprS env universes virtual (peelTypeAnnotations domain) peeled
  domainEquality : env.IsDefEq universes.length virtual.toCtx rawSemantic peeled (.sort level)
  context : TrLCtx env universes (recursorMinorContext reader parentName constructor domain).lctx
    (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
  positioned : BinderPositionedAt (recursorMinorContext reader parentName constructor domain)
    (.fvar ⟨reader.ngen.curr⟩) (recursorMinorName parentName constructor)
    (peelTypeAnnotations domain) .default reader.lctx.decls.size
  scope : reader.RecursorScopeFrame (recursorMinorContext reader parentName constructor domain)

theorem translatedMinorOpening_ofDomain {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {parentName : Name} {constructor : Constructor}
    {domain : Expr} {rawSemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual domain rawSemantic)
    (typed : env.HasType universes.length virtual.toCtx rawSemantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled, RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level := by
  have spine := TypedAnnotationSpine.ofTrExprS envWF correspondence.wf.toCtx
    constants uniform translated typed
  obtain ⟨peeled, peeledTranslated, domainEquality⟩ :=
    spine.peelTypeAnnotations definitions envWF.ordered
  have nextCorrespondence := translatedIndexContextPush
    (name := recursorMinorName parentName constructor) (bi := .default)
    correspondence reserved peeledTranslated domainEquality.hasType.2
  exact ⟨peeled, translated, typed, peeledTranslated, domainEquality, nextCorrespondence,
    newlyAllocatedBinderPositioned reader (recursorMinorName parentName constructor)
      domain .default correspondence.1 reserved,
    Context.RecursorScopeFrame.push reader correspondence.1 reserved
      (recursorMinorName parentName constructor) .default (peelTypeAnnotations domain)⟩

theorem CtorFieldModelEndpoint.minorOpening
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {constructor : Constructor} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields hypotheses : Array Expr} {reader fieldReader hypothesisReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats constructor.type 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    {hypothesisTrace : RecursorIHTrace stats recursiveFields infos 0 #[]
      fieldReader hypotheses hypothesisReader}
    {initial fieldModel hypothesisModel : MLCtx} {semantic headSemantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes fieldTrace initial fieldModel semantic)
    (history : TranslatedRecursorIHTrace env universes hypothesisTrace fieldModel hypothesisModel)
    (parentName : Name)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (modelWF : initial.WF env universes)
    (reserved : ContextReserved fieldReader.lctx fieldReader.ngen)
    (headTranslated : TrExprS env universes initial.vlctx
      (mkAppN (.const constructor.name stats.levels) stats.params) headSemantic)
    (headTyped : env.HasType universes.length initial.vlctx.toCtx headSemantic semantic)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos fieldModel.vlctx terminal)
    (annotations : IndexAnnotationSupport env universes hypothesisReader
      (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)) :
    ∃ rawSemantic peeled level,
      RecursorMinorOpening env universes hypothesisReader hypothesisModel.vlctx parentName constructor
        (recursorMinorDomain stats infos constructor terminal fields hypotheses hypothesisReader)
        rawSemantic peeled level := by
  obtain ⟨rawSemantic, rawLevel, _, _, rawTranslated, rawTyped⟩ :=
    endpoint.liftedMinorDomainTranslation history envWF modelWF reserved
      headTranslated headTyped motiveSupport
  obtain ⟨level, typed, uniform⟩ := annotations hypothesisModel.vlctx _ history.context.2.2
    rawTranslated ⟨rawLevel, rawTyped⟩
  have fieldFrame := hypothesisTrace.scope (endpoint.context.2.1 ▸ endpoint.context.1.tr.1) reserved
  obtain ⟨peeled, receipt⟩ := translatedMinorOpening_ofDomain envWF constants definitions
    history.context.2.2 fieldFrame.reserved rawTranslated typed uniform
  exact ⟨_, peeled, level, receipt⟩

def recursorMinorMLCtx (reader : Context) (model : MLCtx) (parentName : Name)
    (constructor : Constructor) (domain : Expr) (peeled : VExpr) : MLCtx :=
  .vlam ⟨reader.ngen.curr⟩ (recursorMinorName parentName constructor) (peelTypeAnnotations domain)
    peeled .default model

theorem RecursorMinorOpening.mixedContext {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {parentName : Name} {constructor : Constructor}
    {domain : Expr} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorMinorMLCtx reader model parentName constructor domain peeled).WF env universes ∧
      (recursorMinorMLCtx reader model parentName constructor domain peeled).lctx =
        (recursorMinorContext reader parentName constructor domain).lctx ∧
      (recursorMinorMLCtx reader model parentName constructor domain peeled).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨modelWF, ?_, ?_, ?_⟩
    · rw [native]
      exact reserved.fresh (native ▸ modelWF.tr.1)
    · simpa only [converted] using opening.peeledTranslated
    · exact ⟨level, by simpa only [converted] using opening.domainEquality.hasType.2⟩
  · simp only [recursorMinorMLCtx, MLCtx.lctx, recursorMinorContext, recursorIndexContext, native]
  · simp only [recursorMinorMLCtx, MLCtx.vlctx, peeledIndexVirtualContext, converted]

theorem RecursorMinorOpening.extension {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {parentName : Name} {constructor : Constructor}
    {domain : Expr} {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level) (model : MLCtx) :
    IndexMLCtxExtension model [⟨reader.ngen.curr⟩]
      (recursorMinorMLCtx reader model parentName constructor domain peeled) :=
  IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ (recursorMinorName parentName constructor)
    (peelTypeAnnotations domain) peeled .default

end Lean4Lean.AddInductive
