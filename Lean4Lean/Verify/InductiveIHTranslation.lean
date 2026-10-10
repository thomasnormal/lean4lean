import Lean4Lean.Verify.InductiveUArgTranslationCPS
import Lean4Lean.Verify.InductiveIHTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def IHMotiveApplicationSupport (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (infos : Array RecInfo) (virtual : VLCtx) (terminal : Expr) : Prop :=
  ∀ terminalSemantic, TrExprS env universes virtual terminal terminalSemantic →
    ∃ motiveSemantic level,
      TrExprS env universes virtual
        (mkAppN infos[(getIIndices stats terminal).1]!.motive (getIIndices stats terminal).2)
        motiveSemantic ∧
      env.HasType universes.length virtual.toCtx motiveSemantic
        (.forallE terminalSemantic (.sort level))

theorem UArgModelEndpoint.ihBodyTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments argumentReader}
    {initial argumentModel : MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal) :
    ∃ bodySemantic level,
      TrExprS env universes argumentModel.vlctx
        (recursorIHBody stats infos argument terminal arguments) bodySemantic ∧
      env.HasType universes.length argumentModel.vlctx.toCtx bodySemantic (.sort level) := by
  obtain ⟨value, terminalSemantic, valueTranslated, terminalTranslated, valueTyped⟩ :=
    endpoint.application envWF
  obtain ⟨motiveSemantic, level, motiveTranslated, motiveTyped⟩ :=
    motiveSupport terminalSemantic terminalTranslated
  refine ⟨.app motiveSemantic value, level, ?_, ?_⟩
  · exact TrExprS.app motiveTyped valueTyped motiveTranslated valueTranslated
  · simpa only [VExpr.inst] using motiveTyped.app valueTyped

theorem UArgModelEndpoint.ihDomainTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments argumentReader}
    {initial argumentModel : MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF) (modelWF : initial.WF env universes)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal) :
    ∃ domainSemantic level,
      TrExprS env universes initial.vlctx
        (recursorIHDomain stats infos argument terminal arguments argumentReader) domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx domainSemantic (.sort level) := by
  obtain ⟨bodySemantic, bodyLevel, bodyTranslated, bodyTyped⟩ :=
    endpoint.ihBodyTranslation envWF motiveSupport
  obtain ⟨abstracted, domainTranslated, level, domainTyped⟩ := endpoint.typedArgumentAbstraction
    envWF ⟨bodySemantic, bodyTranslated, bodyTyped.toU⟩ ⟨bodyLevel, bodyTyped⟩
  obtain ⟨strictSemantic, strictTranslated, equality⟩ := domainTranslated
  exact ⟨strictSemantic, level, strictTranslated,
    domainTyped.defeqU_l envWF modelWF.tr.wf.toCtx equality.symm⟩

structure RecursorIHOpening (env : VEnv) (universes : List Name) (reader : Context)
    (virtual : VLCtx) (argument domain : Expr) (rawSemantic peeled : VExpr) (level : VLevel) : Prop where
  domainTranslated : TrExprS env universes virtual domain rawSemantic
  domainTyped : env.HasType universes.length virtual.toCtx rawSemantic (.sort level)
  peeledTranslated : TrExprS env universes virtual (peelTypeAnnotations domain) peeled
  domainEquality : env.IsDefEq universes.length virtual.toCtx rawSemantic peeled (.sort level)
  context : TrLCtx env universes (recursorIHContext reader argument domain).lctx
    (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
  positioned : BinderPositionedAt (recursorIHContext reader argument domain)
    (.fvar ⟨reader.ngen.curr⟩) (recursorIHName reader argument) (peelTypeAnnotations domain)
    .default reader.lctx.decls.size
  scope : reader.RecursorScopeFrame (recursorIHContext reader argument domain)

theorem translatedIHOpening_ofDomain {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {argument domain : Expr}
    {rawSemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual domain rawSemantic)
    (typed : env.HasType universes.length virtual.toCtx rawSemantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled, RecursorIHOpening env universes reader virtual argument domain rawSemantic peeled level := by
  have spine := TypedAnnotationSpine.ofTrExprS envWF correspondence.wf.toCtx
    constants uniform translated typed
  obtain ⟨peeled, peeledTranslated, domainEquality⟩ :=
    spine.peelTypeAnnotations definitions envWF.ordered
  have nextCorrespondence := translatedIndexContextPush
    (name := recursorIHName reader argument) (bi := .default)
    correspondence reserved peeledTranslated domainEquality.hasType.2
  exact ⟨peeled, translated, typed, peeledTranslated, domainEquality, nextCorrespondence,
    newlyAllocatedBinderPositioned reader (recursorIHName reader argument) domain .default
      correspondence.1 reserved,
    Context.RecursorScopeFrame.push reader correspondence.1 reserved
      (recursorIHName reader argument) .default (peelTypeAnnotations domain)⟩

theorem UArgModelEndpoint.ihOpening
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument terminal : Expr} {arguments : Array Expr} {reader argumentReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments argumentReader}
    {initial argumentModel : MLCtx}
    (endpoint : UArgModelEndpoint env universes opening initial argumentModel)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (modelWF : initial.WF env universes) (native : initial.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (motiveSupport : IHMotiveApplicationSupport env universes stats infos argumentModel.vlctx terminal)
    (annotations : IndexAnnotationSupport env universes reader
      (recursorIHDomain stats infos argument terminal arguments argumentReader)) :
    ∃ rawSemantic peeled level,
      RecursorIHOpening env universes reader initial.vlctx argument
        (recursorIHDomain stats infos argument terminal arguments argumentReader)
        rawSemantic peeled level := by
  obtain ⟨rawSemantic, rawLevel, rawTranslated, rawTyped⟩ :=
    endpoint.ihDomainTranslation envWF modelWF motiveSupport
  have correspondence : TrLCtx env universes reader.lctx initial.vlctx := by
    simpa only [native] using modelWF.tr
  obtain ⟨level, typed, uniform⟩ :=
    annotations initial.vlctx rawSemantic correspondence rawTranslated ⟨rawLevel, rawTyped⟩
  obtain ⟨peeled, receipt⟩ := translatedIHOpening_ofDomain envWF constants definitions
    correspondence reserved rawTranslated typed uniform
  exact ⟨rawSemantic, peeled, level, receipt⟩

def recursorIHMLCtx (reader : Context) (model : MLCtx) (argument domain : Expr)
    (peeled : VExpr) : MLCtx :=
  .vlam ⟨reader.ngen.curr⟩ (recursorIHName reader argument) (peelTypeAnnotations domain)
    peeled .default model

theorem RecursorIHOpening.mixedContext {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {argument domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorIHOpening env universes reader virtual argument domain rawSemantic peeled level)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorIHMLCtx reader model argument domain peeled).WF env universes ∧
      (recursorIHMLCtx reader model argument domain peeled).lctx =
        (recursorIHContext reader argument domain).lctx ∧
      (recursorIHMLCtx reader model argument domain peeled).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨modelWF, ?_, ?_, ?_⟩
    · rw [native]
      exact reserved.fresh (native ▸ modelWF.tr.1)
    · simpa only [converted] using opening.peeledTranslated
    · exact ⟨level, by simpa only [converted] using opening.domainEquality.hasType.2⟩
  · simp only [recursorIHMLCtx, MLCtx.lctx, recursorIHContext, recursorIndexContext, native]
  · simp only [recursorIHMLCtx, MLCtx.vlctx, peeledIndexVirtualContext, converted]

theorem RecursorIHOpening.extension {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {argument domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorIHOpening env universes reader virtual argument domain rawSemantic peeled level)
    (model : MLCtx) :
    IndexMLCtxExtension model [⟨reader.ngen.curr⟩]
      (recursorIHMLCtx reader model argument domain peeled) :=
  IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ (recursorIHName reader argument)
    (peelTypeAnnotations domain) peeled .default

end Lean4Lean.AddInductive
