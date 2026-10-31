import Lean4Lean.Verify.CanonicalBoolRecursorSupport
import Lean4Lean.Verify.InductiveNativePassTrace
import Lean4Lean.Verify.PrimitiveInductivePreprocessing

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem canonicalBoolMinorPassSupport
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats
      #[{name := ``Bool, type := .sort (.succ .zero),
          ctors := [⟨``Bool.false, .const ``Bool []⟩,
            ⟨``Bool.true, .const ``Bool []⟩]}] 0 infos reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorPassTranslationSupport canonicalBoolModel [`u] trace := by
  cases trace with
  | stop complete => exact .stop complete
  | step bound head tail =>
    refine .step bound head tail ?_ ?_
    · simpa only using
        (canonicalBoolMinorTraceSupport (trace := head) params levels indConsts nindices boolIndices
          motives motiveSupport)
    · cases tail with
      | stop complete => exact .stop complete
      | step bound2 constructors2 tail2 =>
        have impossible : ¬ (0 + 1 < (#[(
          { name := ``Bool, type := .sort (.succ .zero),
            ctors := [⟨``Bool.false, .const ``Bool []⟩,
              ⟨``Bool.true, .const ``Bool []⟩] } : InductiveType)] : Array InductiveType).size) := by
          decide
        exact (impossible bound2).elim

/- The source-level Bool support only needs the motive witness at its concrete
   initial model.  Every field endpoint is then an extension of that model,
   so `canonicalBoolMotiveSupportOfExtension` supplies the IH callback without
   asking for a witness at arbitrary model inputs. -/
theorem canonicalBoolMinorSourceSupportOfMotive
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    (constructorType : constructor.type = .const ``Bool [])
    (constructorName : constructor.name = ``Bool.false ∨ constructor.name = ``Bool.true)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (model : MLCtx) (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    MinorSourceTranslationSupport canonicalBoolModel [`u] source model := by
  exact canonicalBoolMinorSourceSupport constructorType constructorName params levels indConsts
    nindices boolIndices ⟨motive, motiveEq⟩ source model modelWF native (by
      intro terminal finalIndex fields recursiveFields fieldReader semantic fieldTrace fieldModel endpoint
      obtain ⟨fieldIds, fieldExtension⟩ := endpoint.modelExtension
      exact canonicalBoolMotiveSupportOfExtension fieldExtension endpoint.context.1 (by
        cases fieldTrace
        rfl) boolIndices motiveEq motiveTranslated motiveTyped)

/- Translate the concrete two-constructor Bool minor trace from one parent
   model.  The first constructor produces the model extension used by the
   second constructor; the parent motive is weakened through that exact
   extension before the second source is translated. -/
theorem canonicalBoolMinorTraceTranslatedOfMotive
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context} {model : MLCtx}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (infoBound : 0 < infos.size)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    ∃ finalModel, TranslatedRecursorMinorTrace canonicalBoolModel [`u] trace model finalModel := by
  cases trace with
  | @step infos0 finalInfos0 constructor constructors reader0 domainReader0 finalReader0 domain0 source tail =>
    cases tail with
    | @step infos1 finalInfos1 constructor2 constructors2 reader1 domainReader1 finalReader1 domain1 source2 tail2 =>
      cases tail2
      obtain ⟨middleModel, headStep⟩ := source.translatedStep ``Bool canonicalBoolModel.wf
        canonicalBoolModel.constants canonicalBoolModel.definitions (by simpa [params])
        model modelWF native reserved (canonicalBoolMinorSourceSupportOfMotive rfl (Or.inl rfl)
          params levels indConsts nindices boolIndices source model modelWF native motiveEq
          motiveTranslated motiveTyped)
      obtain ⟨_, headExtension⟩ := headStep.extension
      have middleWF := headStep.context.1
      have middleNative := headStep.context.2
      have motiveEq2 : (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))[0]!.motive =
          .fvar motive := by
        rw [recursorMinorUpdate.selected 0 infos _ infoBound, motiveEq]
      have motiveTranslated2 := motiveTranslated.weakFV canonicalBoolModel.wf.ordered
        headExtension.weakening middleWF.tr.wf
      have motiveTyped2 := by
        simpa only [List.length_cons, List.length_nil] using
          motiveTyped.weakN canonicalBoolModel.wf.ordered headExtension.weakening.toCtx
      have domainFrame := source.scope (native ▸ modelWF.tr.1) reserved
      have pushed := Context.RecursorScopeFrame.push domainReader0 domainFrame.wf domainFrame.reserved
        (recursorMinorName ``Bool {name := ``Bool.false, type := .const ``Bool []}) .default
        (peelTypeAnnotations domain0)
      obtain ⟨finalModel, tailStep⟩ := source2.translatedStep ``Bool canonicalBoolModel.wf
        canonicalBoolModel.constants canonicalBoolModel.definitions (by simpa [params])
        middleModel middleWF middleNative pushed.reserved
        (canonicalBoolMinorSourceSupportOfMotive rfl (Or.inr rfl) params levels indConsts nindices
          boolIndices source2 middleModel middleWF middleNative motiveEq2 motiveTranslated2 motiveTyped2)
      have finalWF := tailStep.context.1
      have finalNative := tailStep.context.2
      have stopHistory : TranslatedRecursorMinorTrace canonicalBoolModel [`u]
          (.stop : RecursorMinorTrace stats ``Bool 0
            (recursorMinorUpdate 0 (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))
              (.fvar ⟨domainReader1.ngen.curr⟩)) []
            (recursorMinorContext domainReader1 ``Bool
              {name := ``Bool.true, type := .const ``Bool []} domain1)
            (recursorMinorUpdate 0 (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))
              (.fvar ⟨domainReader1.ngen.curr⟩))
            (recursorMinorContext domainReader1 ``Bool
              {name := ``Bool.true, type := .const ``Bool []} domain1))
          finalModel finalModel :=
        .stop finalWF finalNative
      have inner : TranslatedRecursorMinorTrace canonicalBoolModel [`u]
          (.step source2 (.stop)) middleModel finalModel :=
        .step source2 (.stop) tailStep stopHistory
      exact ⟨finalModel, .step source (.step source2 (.stop)) headStep inner⟩

/- The parent-history consumer supplies the concrete model and motive receipt
   required by the two-constructor trace translator.  The generic minor-pass
   callback remains separate because its contract quantifies over arbitrary
   model inputs. -/
theorem canonicalBoolMinorTraceTranslatedOfParentHistory
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ finalModel, TranslatedRecursorMinorTrace canonicalBoolModel [`u]
      minorTrace parentModel finalModel := by
  obtain ⟨motive, level, motiveEq, motiveTranslated, motiveTyped⟩ :=
    canonicalBoolParentHistoryMotiveReceipt parentTrace parentHistory normalization params indConsts
  have infoBound : 0 < infos.size := by
    have counts := parentTrace.counts
    have infoSize : infos.size = 1 := by
      simpa only [Array.size_empty, Array.size_singleton, Nat.sub_zero, Nat.zero_add] using counts
    omega
  obtain ⟨parentWF, parentNative, _⟩ := parentHistory.context
  exact canonicalBoolMinorTraceTranslatedOfMotive minorTrace params levels indConsts nindices
    boolIndices parentWF parentNative reserved infoBound motiveEq motiveTranslated motiveTyped

/- The concrete Bool minor pass has one translated minor trace followed by the
   forced stop.  This packages the parent-history consumer at the pass level
   without manufacturing the generic arbitrary-model support callback. -/
theorem canonicalBoolMinorPassTranslatedOfParentHistory
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats #[canonicalBoolType] 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ finalModel, TranslatedRecursorMinorPass canonicalBoolModel [`u]
      minorTrace parentModel finalModel := by
  unfold canonicalBoolType at minorTrace
  cases minorTrace with
  | stop complete =>
    exact (complete (by decide)).elim
  | step bound head tail =>
    cases tail with
    | stop complete =>
      obtain ⟨middleModel, headHistory⟩ :=
        canonicalBoolMinorTraceTranslatedOfParentHistory parentTrace parentHistory head
          normalization params levels indConsts nindices boolIndices reserved
      exact ⟨middleModel, .step bound head (.stop complete) headHistory
        (.stop complete headHistory.context.1 headHistory.context.2.1)⟩
    | step bound2 _ _ =>
      have impossible : ¬ (1 : Nat) < #[canonicalBoolType].size := by decide
      exact (impossible bound2).elim

end Lean4Lean.AddInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem canonicalBoolMinorPassSupport_of_types
    {stats : InductiveStats} {types : Array InductiveType}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (typesEq : types = #[canonicalBoolType])
    (trace : RecursorMinorPassTrace stats types 0 infos reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorPassTranslationSupport canonicalBoolModel [`u] trace := by
  subst types
  unfold canonicalBoolType at trace
  exact canonicalBoolMinorPassSupport trace params levels indConsts nindices boolIndices motives motiveSupport

theorem canonicalBoolNullaryFalseStepAllocation
    {stats : InductiveStats} {infos : Array RecInfo}
    {reader domainReader : Context} {domain : Expr}
    {initial final : MLCtx}
    {source : RecursorMinorDomainSource stats infos
      ({name := ``Bool.false, type := .const ``Bool []} : Constructor)
      reader domain domainReader}
    (step : MinorModelStep canonicalBoolModel [`u] ``Bool source initial final) :
    IndexMLCtxExtension initial [⟨domainReader.ngen.curr⟩] final := by
  rcases step with ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, modelWF, native⟩
  cases fieldTrace
  cases hypothesisTrace
  case stop =>
    have fieldModelEq : fieldModel = initial := by
      obtain ⟨_, _, _, _, _, _, ids, extension, selected⟩ := endpoint
      cases extension with
      | nil => rfl
      | push earlier id name domain semantic bi => simp at selected
    have hypothesisModelEq : hypothesisModel = fieldModel := by
      obtain ⟨ids, extension, selected⟩ := history.extension
      cases extension with
      | nil => rfl
      | push earlier id name domain semantic bi => simp at selected
    subst fieldModel
    subst hypothesisModel
    exact finalEq ▸ opening.extension initial
  case step bound source tail =>
    have impossible : ¬ (0 : Nat) < (#[] : Array Expr).size := by decide
    exact (impossible bound).elim

theorem canonicalBoolNullaryTrueStepAllocation
    {stats : InductiveStats} {infos : Array RecInfo}
    {reader domainReader : Context} {domain : Expr}
    {initial final : MLCtx}
    {source : RecursorMinorDomainSource stats infos
      ({name := ``Bool.true, type := .const ``Bool []} : Constructor)
      reader domain domainReader}
    (step : MinorModelStep canonicalBoolModel [`u] ``Bool source initial final) :
    IndexMLCtxExtension initial [⟨domainReader.ngen.curr⟩] final := by
  rcases step with ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, modelWF, native⟩
  cases fieldTrace
  cases hypothesisTrace
  case stop =>
    have fieldModelEq : fieldModel = initial := by
      obtain ⟨_, _, _, _, _, _, ids, extension, selected⟩ := endpoint
      cases extension with
      | nil => rfl
      | push earlier id name domain semantic bi => simp at selected
    have hypothesisModelEq : hypothesisModel = fieldModel := by
      obtain ⟨ids, extension, selected⟩ := history.extension
      cases extension with
      | nil => rfl
      | push earlier id name domain semantic bi => simp at selected
    subst fieldModel
    subst hypothesisModel
    exact finalEq ▸ opening.extension initial
  case step bound source tail =>
    have impossible : ¬ (0 : Nat) < (#[] : Array Expr).size := by decide
    exact (impossible bound).elim

/- A nullary Bool constructor has no field or IH binders.  Its native minor
   domain therefore reduces to the parent motive applied to the constructor
   value.  Keep this source shape separate from the translated model receipt:
   it identifies the declaration type before any chronological-to-grouped
   transport is attempted. -/
theorem canonicalBoolMinorSourceDomainShape
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    (constructorType : constructor.type = .const ``Bool [])
    (params : stats.params = #[]) (levels : stats.levels = [])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader) :
    domain = .app infos[0]!.motive (.const constructor.name []) := by
  rcases constructor with ⟨constructorName', constructorType'⟩
  simp only at constructorType source ⊢
  cases constructorType
  rcases source with ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, domainEq⟩
  cases fieldTrace with
  | stop terminalNotForall =>
    cases hypothesisTrace with
    | stop complete =>
      rw [domainEq, recursorMinorDomain, recursorMinorBody]
      simp only [params, levels, boolIndices, mkAppN, Array.foldl_empty]
      have emptyForall : ∀ body : Expr, LocalContext.mkForall reader.lctx #[] body = body := by
        intro body
        simp only [Lean.LocalContext.mkForall, Lean.LocalContext.mkBinding,
          Array.size_empty, Nat.foldRev_zero, Expr.abstractRange_eq]
        have abstractEmpty : body.abstract #[] = body := by
          have h := Expr.abstract_eq body []
          simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil body 0)
        rw [abstractEmpty]
      rw [emptyForall, emptyForall]
    | step bound source tail => simpa using bound

/- The concrete two-constructor trace records the exact native cdecls for both
   minor binders.  The first declaration is carried through the second
   constructor's scope frame, while the second is the final frame's newest
   declaration.  Their types are the motive applications established above;
   the result is native provenance for later dependency-aware grouped
   transport, not a reordered model extension. -/
theorem canonicalBoolMinorTraceDomainReceipts
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (_indConsts : stats.indConsts = #[.const ``Bool []]) (_nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (infoBound : 0 < infos.size)
    {motive : FVarId} (motiveEq : infos[0]!.motive = .fvar motive)
    (readerWF : reader.lctx.WF)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ (minorFalse minorTrue : FVarId) (falseDecl trueDecl : LocalDecl),
      finalReader.lctx.find? minorFalse = some falseDecl ∧
      finalReader.lctx.find? minorTrue = some trueDecl ∧
      falseDecl.fvarId = minorFalse ∧ trueDecl.fvarId = minorTrue ∧
      falseDecl.type = .app infos[0]!.motive (.const ``Bool.false []) ∧
      trueDecl.type = .app infos[0]!.motive (.const ``Bool.true []) := by
  cases trace with
  | @step infos0 finalInfos0 constructor constructors reader0 domainReader0 finalReader0 domain0 source tail =>
    cases tail with
    | @step infos1 finalInfos1 constructor2 constructors2 reader1 domainReader1 finalReader1 domain1 source2 tail2 =>
      cases tail2
      have falseShape := canonicalBoolMinorSourceDomainShape (constructorType := rfl)
        params levels boolIndices source
      have trueShape := canonicalBoolMinorSourceDomainShape (constructorType := rfl)
        params levels boolIndices source2
      have motivePreserved :
          (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))[0]!.motive =
            infos[0]!.motive := by
        rw [recursorMinorUpdate.selected 0 infos _ infoBound]
      rw [motivePreserved] at trueShape
      have firstFrame := source.scope readerWF reserved
      have falsePush := Context.RecursorScopeFrame.push domainReader0 firstFrame.wf firstFrame.reserved
        (recursorMinorName ``Bool {name := ``Bool.false, type := .const ``Bool []}) .default
        (peelTypeAnnotations domain0)
      let falseDecl := LocalDecl.cdecl domainReader0.lctx.decls.size
        ⟨domainReader0.ngen.curr⟩
        (recursorMinorName ``Bool {name := ``Bool.false, type := .const ``Bool []})
        (peelTypeAnnotations domain0) .default .default
      have falseMem : falseDecl ∈ (recursorMinorContext domainReader0 ``Bool
          {name := ``Bool.false, type := .const ``Bool []} domain0).lctx.toList := by
        simp only [falseDecl, recursorMinorContext, recursorIndexContext,
          LocalContext.mkLocalDecl_toList, List.mem_cons]
        simp
      have falseLookup : (recursorMinorContext domainReader0 ``Bool
          {name := ``Bool.false, type := .const ``Bool []} domain0).lctx.find?
          falseDecl.fvarId = some falseDecl := falsePush.wf.find?_of_mem falseMem
      have secondFrame := source2.scope falsePush.wf falsePush.reserved
      have truePush := Context.RecursorScopeFrame.push domainReader1 secondFrame.wf secondFrame.reserved
        (recursorMinorName ``Bool {name := ``Bool.true, type := .const ``Bool []}) .default
        (peelTypeAnnotations domain1)
      have falseFinalLookup := (secondFrame.trans truePush).oldLookup falsePush.wf falseLookup
      let trueDecl := LocalDecl.cdecl domainReader1.lctx.decls.size
        ⟨domainReader1.ngen.curr⟩
        (recursorMinorName ``Bool {name := ``Bool.true, type := .const ``Bool []})
        (peelTypeAnnotations domain1) .default .default
      have trueMem : trueDecl ∈ (recursorMinorContext domainReader1 ``Bool
          {name := ``Bool.true, type := .const ``Bool []} domain1).lctx.toList := by
        simp only [trueDecl, recursorMinorContext, recursorIndexContext,
          LocalContext.mkLocalDecl_toList, List.mem_cons]
        simp
      have trueLookup : (recursorMinorContext domainReader1 ``Bool
          {name := ``Bool.true, type := .const ``Bool []} domain1).lctx.find?
          trueDecl.fvarId = some trueDecl := truePush.wf.find?_of_mem trueMem
      have falseType : falseDecl.type = .app infos[0]!.motive (.const ``Bool.false []) := by
        simp only [falseDecl, LocalDecl.type, falseShape]
        rw [motiveEq]
        rfl
      have trueType : trueDecl.type = .app infos[0]!.motive (.const ``Bool.true []) := by
        simp only [trueDecl, LocalDecl.type, trueShape]
        rw [motiveEq]
        rfl
      refine ⟨⟨domainReader0.ngen.curr⟩, ⟨domainReader1.ngen.curr⟩,
        falseDecl, trueDecl, ?_, ?_, ?_, ?_, falseType, trueType⟩
      · simpa only [falseDecl, LocalDecl.fvarId, recursorMinorContext,
          recursorIndexContext, Expr.fvarId!, Lean.mkFVar] using falseFinalLookup
      · simpa only [trueDecl, LocalDecl.fvarId, recursorMinorContext,
          recursorIndexContext, Expr.fvarId!, Lean.mkFVar] using trueLookup
      · rfl
      · rfl

theorem canonicalBoolMinorTraceAllocationOfMotive
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context} {model : MLCtx}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (infoBound : 0 < infos.size)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    ∃ finalModel, ∃ minorFalse minorTrue : FVarId,
      TranslatedRecursorMinorTrace canonicalBoolModel [`u] trace model finalModel ∧
      IndexMLCtxExtension model [minorFalse, minorTrue] finalModel ∧
      finalInfos[0]!.minors = (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) := by
  cases trace with
  | @step infos0 finalInfos0 constructor constructors reader0 domainReader0 finalReader0 domain0 source tail =>
    cases tail with
    | @step infos1 finalInfos1 constructor2 constructors2 reader1 domainReader1 finalReader1 domain1 source2 tail2 =>
      cases tail2
      obtain ⟨middleModel, headStep⟩ := source.translatedStep ``Bool canonicalBoolModel.wf
        canonicalBoolModel.constants canonicalBoolModel.definitions (by simpa [params])
        model modelWF native reserved (canonicalBoolMinorSourceSupportOfMotive rfl (Or.inl rfl)
          params levels indConsts nindices boolIndices source model modelWF native motiveEq
          motiveTranslated motiveTyped)
      let minorFalse : FVarId := ⟨domainReader0.ngen.curr⟩
      have headExtension : IndexMLCtxExtension model [minorFalse] middleModel := by
        simpa only [minorFalse] using canonicalBoolNullaryFalseStepAllocation headStep
      have middleWF := headStep.context.1
      have middleNative := headStep.context.2
      have motiveEq2 : (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))[0]!.motive =
          .fvar motive := by
        rw [recursorMinorUpdate.selected 0 infos _ infoBound, motiveEq]
      have motiveTranslated2 := motiveTranslated.weakFV canonicalBoolModel.wf.ordered
        headExtension.weakening middleWF.tr.wf
      have motiveTyped2 := by
        simpa only [List.length_cons, List.length_nil] using
          motiveTyped.weakN canonicalBoolModel.wf.ordered headExtension.weakening.toCtx
      have domainFrame := source.scope (native ▸ modelWF.tr.1) reserved
      have pushed := Context.RecursorScopeFrame.push domainReader0 domainFrame.wf domainFrame.reserved
        (recursorMinorName ``Bool {name := ``Bool.false, type := .const ``Bool []}) .default
        (peelTypeAnnotations domain0)
      obtain ⟨finalModel, tailStep⟩ := source2.translatedStep ``Bool canonicalBoolModel.wf
        canonicalBoolModel.constants canonicalBoolModel.definitions (by simpa [params])
        middleModel middleWF middleNative pushed.reserved
        (canonicalBoolMinorSourceSupportOfMotive rfl (Or.inr rfl) params levels indConsts nindices
          boolIndices source2 middleModel middleWF middleNative motiveEq2 motiveTranslated2 motiveTyped2)
      let minorTrue : FVarId := ⟨domainReader1.ngen.curr⟩
      have tailExtension : IndexMLCtxExtension middleModel [minorTrue] finalModel := by
        simpa only [minorTrue] using canonicalBoolNullaryTrueStepAllocation tailStep
      have finalWF := tailStep.context.1
      have finalNative := tailStep.context.2
      have stopHistory : TranslatedRecursorMinorTrace canonicalBoolModel [`u]
          (.stop : RecursorMinorTrace stats ``Bool 0
            (recursorMinorUpdate 0 (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))
              (.fvar ⟨domainReader1.ngen.curr⟩)) []
            (recursorMinorContext domainReader1 ``Bool
              {name := ``Bool.true, type := .const ``Bool []} domain1)
            (recursorMinorUpdate 0 (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩))
              (.fvar ⟨domainReader1.ngen.curr⟩))
            (recursorMinorContext domainReader1 ``Bool
              {name := ``Bool.true, type := .const ``Bool []} domain1))
          finalModel finalModel :=
        .stop finalWF finalNative
      have inner : TranslatedRecursorMinorTrace canonicalBoolModel [`u]
          (.step source2 (.stop)) middleModel finalModel :=
        .step source2 (.stop) tailStep stopHistory
      have infoBound2 : 0 <
          (recursorMinorUpdate 0 infos (.fvar ⟨domainReader0.ngen.curr⟩)).size := by
        simpa only [recursorMinorUpdate.size] using infoBound
      have minorsEq :
          (recursorMinorUpdate 0 (recursorMinorUpdate 0 infos
            (.fvar ⟨domainReader0.ngen.curr⟩)) (.fvar ⟨domainReader1.ngen.curr⟩))[0]!.minors =
            (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) := by
        rw [recursorMinorUpdate.selected 0 _ _ infoBound2,
          recursorMinorUpdate.selected 0 infos _ infoBound]
      refine ⟨finalModel, minorFalse, minorTrue,
        .step source (.step source2 (.stop)) headStep inner,
        headExtension.trans tailExtension, minorsEq⟩

/- The concrete Bool pass allocation is the parent major/motive extension
   followed by the two nullary constructor binders. -/
theorem canonicalBoolMinorPassAllocationOfParentHistory
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats #[canonicalBoolType] 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ (major motive minorFalse minorTrue : FVarId),
      infos[0]!.major = .fvar major ∧ infos[0]!.motive = .fvar motive ∧
      finalInfos[0]!.minors = (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) ∧
      ∃ finalModel, IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel := by
  obtain ⟨major, motive, majorEq, motiveEq, _, parentExt, parentIdsEq⟩ :=
    canonicalBoolParentHistoryAllocation parentTrace parentHistory normalization params indConsts
  rw [parentIdsEq] at parentExt
  have infoBound : 0 < infos.size := by
    have counts := parentTrace.counts
    have infoSize : infos.size = 1 := by
      simpa only [Array.size_empty, Array.size_singleton, Nat.sub_zero, Nat.zero_add] using counts
    omega
  unfold canonicalBoolType at minorTrace
  cases minorTrace with
  | stop complete =>
    exact (complete (by decide)).elim
  | step bound head tail =>
    cases tail with
    | stop complete =>
      have motiveReceipt : ∃ motiveLevel,
          TrExprS canonicalBoolModel [`u] parentModel.vlctx
            (.fvar motive) (.bvar 0) ∧
          canonicalBoolModel.HasType 1 parentModel.vlctx.toCtx (.bvar 0)
            (.forallE (.const ``Bool []) (.sort motiveLevel)) := by
        obtain ⟨motive0, motiveLevel, motiveEq0, motiveTranslated0, motiveTyped0⟩ :=
          canonicalBoolParentHistoryMotiveReceipt parentTrace parentHistory normalization params indConsts
        have motiveIds : (Expr.fvar motive0 : Expr) = .fvar motive :=
          motiveEq0.symm.trans motiveEq
        cases motiveIds
        exact ⟨motiveLevel, motiveTranslated0, motiveTyped0⟩
      obtain ⟨motiveLevel, motiveTranslated, motiveTyped⟩ := motiveReceipt
      obtain ⟨minorModel, minorFalse, minorTrue, _, minorExt, minorsEq⟩ :=
        canonicalBoolMinorTraceAllocationOfMotive head params levels indConsts nindices
          boolIndices parentHistory.context.1 parentHistory.context.2.1 reserved infoBound motiveEq
          motiveTranslated motiveTyped
      refine ⟨major, motive, minorFalse, minorTrue, majorEq, motiveEq, minorsEq, ?_⟩
      exact ⟨minorModel, parentExt.trans minorExt⟩
    | step bound2 _ _ =>
      have impossible : ¬ (1 : Nat) < #[canonicalBoolType].size := by decide
      exact (impossible bound2).elim


/- The one-type Bool minor pass updates only the minor array.  Its final slot
   therefore preserves the parent major, motive, and indices exactly. -/
theorem canonicalBoolMinorPassInfoPreservation
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {parentReader finalReader : Context}
    (minorTrace : RecursorMinorPassTrace stats #[canonicalBoolType] 0 infos parentReader finalInfos finalReader)
    (infoBound : 0 < infos.size) :
    finalInfos[0]!.major = infos[0]!.major ∧
    finalInfos[0]!.motive = infos[0]!.motive ∧
    finalInfos[0]!.indices = infos[0]!.indices := by
  unfold canonicalBoolType at minorTrace
  cases minorTrace with
  | stop complete => exact (complete (by decide)).elim
  | step bound head tail =>
    cases tail with
    | stop complete =>
      cases head with
      | step source tail =>
        cases tail with
        | step source2 tail2 =>
          cases tail2
          simp [recursorMinorUpdate, getElem!_pos, infoBound, Array.getElem_modify]
    | step bound2 _ _ =>
      have impossible : ¬ (1 : Nat) < #[canonicalBoolType].size := by decide
      exact (impossible bound2).elim

end Lean4Lean.AddInductive
