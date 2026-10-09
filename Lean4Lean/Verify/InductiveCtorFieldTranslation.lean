import Lean4Lean.Verify.InductiveMotiveContextTranslation
import Lean4Lean.Verify.InductiveCtorFieldTrace

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem IndexMLCtxExtension.nativeBodyAbstraction
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (modelWF : final.WF env universes) {body : Expr}
    (closed : body.looseBVarRange' = 0) :
    final.lctx.mkForall (ids.map Expr.fvar).toArray body =
      final.mkForall ids.length extension.bound body := by
  exact modelWF.mkForall_eq ids.length extension.bound
    (by simp only [List.map_reverse, extension.selection]) closed

theorem IndexMLCtxExtension.typedBodyAbstraction
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {body : Expr} {semantic : VExpr}
    (translated : TrExpr env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    TrExpr env universes initial.vlctx
        (final.lctx.mkForall (ids.map Expr.fvar).toArray body)
        (final.mkForall' ids.length extension.bound semantic) ∧
      env.IsType universes.length initial.vlctx.toCtx
        (final.mkForall' ids.length extension.bound semantic) := by
  have closed : body.looseBVarRange' = 0 :=
    (final.noBV ▸ translated.closed).looseBVarRange_zero
  rw [extension.nativeBodyAbstraction modelWF closed]
  simpa only [extension.drop_eq] using
    modelWF.mkForall_tr envWF translated typed ids.length extension.bound

theorem IndexMLCtxExtension.typedBodyAbstractionAtFinal
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {body : Expr} {semantic : VExpr}
    (translated : TrExpr env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    TrExpr env universes final.vlctx
        (final.lctx.mkForall (ids.map Expr.fvar).toArray body)
        ((final.mkForall' ids.length extension.bound semantic).liftN ids.length) ∧
      env.IsType universes.length final.vlctx.toCtx
        ((final.mkForall' ids.length extension.bound semantic).liftN ids.length) := by
  obtain ⟨abstracted, level, abstractedTyped⟩ :=
    extension.typedBodyAbstraction envWF modelWF translated typed
  refine ⟨abstracted.weakFV envWF extension.weakening modelWF.tr.wf, level, ?_⟩
  simpa only [VExpr.liftN] using
    abstractedTyped.weakN envWF.ordered extension.weakening.toCtx

structure CtorFieldOpening (env : VEnv) (universes : List Name) (reader : Context)
    (virtual : VLCtx) (name : Name) (domain body : Expr) (bi : BinderInfo)
    (semanticDomain bodySemantic : VExpr) (level : VLevel)
    (peeled convertedBody : VExpr) : Prop where
  domainTranslated : TrExprS env universes virtual (peelTypeAnnotations domain) peeled
  domainEquality : env.IsDefEq universes.length virtual.toCtx semanticDomain peeled (.sort level)
  context : TrLCtx env universes
    (recursorIndexContext reader name bi (peelTypeAnnotations domain)).lctx
    (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
  bodyTranslated : TrExprS env universes
    (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
    (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) convertedBody
  bodyEquality : env.IsDefEqU universes.length
    (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
    convertedBody bodySemantic
  positioned : BinderPositionedAt (recursorIndexContext reader name bi (peelTypeAnnotations domain))
    (.fvar ⟨reader.ngen.curr⟩) name (peelTypeAnnotations domain) bi reader.lctx.decls.size
  scope : reader.RecursorScopeFrame (recursorIndexContext reader name bi (peelTypeAnnotations domain))

theorem translatedForallCtorFieldOpening {env : VEnv} {universes : List Name}
    {virtual : VLCtx} {reader : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semanticDomain bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual (.forallE name domain body bi)
      (.forallE semanticDomain bodySemantic))
    (domainTyped : env.HasType universes.length virtual.toCtx semanticDomain (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled convertedBody, CtorFieldOpening env universes reader virtual name domain body bi
      semanticDomain bodySemantic level peeled convertedBody := by
  cases translated with
  | forallE _ _ domainTranslated bodyTranslated =>
    have spine := TypedAnnotationSpine.ofTrExprS envWF correspondence.wf.toCtx constants
      uniform domainTranslated domainTyped
    obtain ⟨peeled, convertedBody, peeledTranslated, domainEquality, _, convertedTranslation,
      convertedEquality⟩ :=
      spine.anonymousBodyStrongTranslation envWF definitions correspondence.wf bodyTranslated
    have nextCorrespondence := translatedIndexContextPush (name := name) (bi := bi)
      correspondence reserved peeledTranslated domainEquality.hasType.2
    refine ⟨peeled, convertedBody, peeledTranslated, domainEquality, nextCorrespondence,
      ?_, convertedEquality, ?_, ?_⟩
    · rw [Expr.instantiate1_eq]
      exact convertedTranslation.inst_fvar envWF.ordered nextCorrespondence.wf
    · exact newlyAllocatedBinderPositioned reader name domain bi correspondence.1 reserved
    · exact Context.RecursorScopeFrame.push reader correspondence.1 reserved name bi
        (peelTypeAnnotations domain)

def ctorFieldMLCtx (reader : Context) (model : MLCtx) (name : Name)
    (domain : Expr) (peeled : VExpr) (bi : BinderInfo) : MLCtx :=
  .vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled bi model

theorem CtorFieldOpening.mixedContext {env : VEnv} {universes : List Name}
    {virtual : VLCtx} {reader : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semanticDomain bodySemantic peeled convertedBody : VExpr} {level : VLevel}
    (opening : CtorFieldOpening env universes reader virtual name domain body bi
      semanticDomain bodySemantic level peeled convertedBody)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (ctorFieldMLCtx reader model name domain peeled bi).WF env universes ∧
      (ctorFieldMLCtx reader model name domain peeled bi).lctx =
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)).lctx ∧
      (ctorFieldMLCtx reader model name domain peeled bi).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨modelWF, ?_, ?_, ?_⟩
    · rw [native]
      exact reserved.fresh (native ▸ modelWF.tr.1)
    · simpa only [converted] using opening.domainTranslated
    · exact ⟨level, by simpa only [converted] using opening.domainEquality.hasType.2⟩
  · simp only [ctorFieldMLCtx, MLCtx.lctx, recursorIndexContext, native]
  · simp only [ctorFieldMLCtx, MLCtx.vlctx, peeledIndexVirtualContext, converted]

inductive CtorFieldTraceAnnotationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} :
    {source : Expr} → {index : Nat} → {fields recursiveFields : Array Expr} → {reader : Context} →
    {terminal : Expr} → {finalIndex : Nat} → {finalFields finalRecursive : Array Expr} →
    {finalReader : Context} →
    RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader → Prop where
  | stop {source : Expr} {index : Nat} {fields recursiveFields : Array Expr} {reader : Context}
      (terminal : ∀ name domain body bi, source ≠ .forallE name domain body bi) :
      CtorFieldTraceAnnotationSupport env universes (.stop (index := index) (fields := fields)
        (recursiveFields := recursiveFields) (reader := reader) terminal)
  | parameter {name : Name} {domain body parameter terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
      {reader finalReader : Context}
      (selected : stats.params[index]? = some parameter)
      (tail : RecursorCtorFieldTrace stats (body.instantiate1 parameter) (index + 1)
        fields recursiveFields reader terminal finalIndex finalFields finalRecursive finalReader)
      (supported : CtorFieldTraceAnnotationSupport env universes tail) :
      CtorFieldTraceAnnotationSupport env universes
        (.parameter (name := name) (domain := domain) (binderInfo := bi) selected tail)
  | field {name : Name} {domain body terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
      {reader finalReader : Context} {recursive : Option Nat}
      (selected : stats.params[index]? = none)
      (classified : isRecArg stats domain
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)) = .ok recursive)
      (tail : RecursorCtorFieldTrace stats (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))
        (index + 1) (fields.push (.fvar ⟨reader.ngen.curr⟩))
        (if recursive.isSome then recursiveFields.push (.fvar ⟨reader.ngen.curr⟩) else recursiveFields)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        terminal finalIndex finalFields finalRecursive finalReader)
      (headSupported : IndexAnnotationSupport env universes reader domain)
      (tailSupported : CtorFieldTraceAnnotationSupport env universes tail) :
      CtorFieldTraceAnnotationSupport env universes (.field selected classified tail)

inductive TranslatedRecursorCtorFieldTrace (env : VEnv) (universes : List Name)
    {stats : InductiveStats} :
    {source : Expr} → {index : Nat} → {fields recursiveFields : Array Expr} → {reader : Context} →
    {terminal : Expr} → {finalIndex : Nat} → {finalFields finalRecursive : Array Expr} →
    {finalReader : Context} →
    RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader →
        VLCtx → VExpr → VLCtx → VExpr → Prop where
  | stop {source : Expr} {index : Nat} {fields recursiveFields : Array Expr} {reader : Context}
      {virtual : VLCtx} {semantic : VExpr}
      (terminal : ∀ name domain body bi, source ≠ .forallE name domain body bi)
      (correspondence : TrLCtx env universes reader.lctx virtual)
      (translated : TrExprS env universes virtual source semantic) :
      TranslatedRecursorCtorFieldTrace env universes (.stop (index := index) (fields := fields)
        (recursiveFields := recursiveFields) (reader := reader) terminal)
        virtual semantic virtual semantic
  | field {name : Name} {domain body terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {fields recursiveFields finalFields finalRecursive : Array Expr}
      {reader finalReader : Context} {recursive : Option Nat}
      {virtual finalVirtual : VLCtx}
      {semanticDomain bodySemantic peeled convertedBody finalSemantic : VExpr} {level : VLevel}
      (selected : stats.params[index]? = none)
      (classified : isRecArg stats domain
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)) = .ok recursive)
      (tail : RecursorCtorFieldTrace stats (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))
        (index + 1) (fields.push (.fvar ⟨reader.ngen.curr⟩))
        (if recursive.isSome then recursiveFields.push (.fvar ⟨reader.ngen.curr⟩) else recursiveFields)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        terminal finalIndex finalFields finalRecursive finalReader)
      (translated : TrExprS env universes virtual (.forallE name domain body bi)
        (.forallE semanticDomain bodySemantic))
      (opening : CtorFieldOpening env universes reader virtual name domain body bi
        semanticDomain bodySemantic level peeled convertedBody)
      (translatedTail : TranslatedRecursorCtorFieldTrace env universes tail
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled) convertedBody
        finalVirtual finalSemantic) :
      TranslatedRecursorCtorFieldTrace env universes (.field selected classified tail)
        virtual (.forallE semanticDomain bodySemantic) finalVirtual finalSemantic

theorem RecursorCtorFieldTrace.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual : VLCtx} {semantic : VExpr}
    (trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (annotations : CtorFieldTraceAnnotationSupport env universes trace) :
    ∃ finalVirtual finalSemantic,
      TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic := by
  induction trace generalizing virtual semantic with
  | stop terminal => exact ⟨virtual, semantic, .stop terminal correspondence translated⟩
  | parameter selected tail tailInduction =>
    obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp selected
    exact False.elim (Nat.not_lt_of_ge fieldOnly bound)
  | @field name domain body bi index finalIndex fields recursiveFields finalFields finalRecursive
      reader finalReader terminal recursive selected classified tail tailInduction =>
    cases annotations with
    | stop notForall => exact False.elim (notForall name domain body bi rfl)
    | parameter parameterSelected _ _ =>
      obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp parameterSelected
      exact False.elim (Nat.not_lt_of_ge fieldOnly bound)
    | field _ supportedClassification _ headSupported tailSupported =>
      have sameRecursive := Except.ok.inj (classified.symm.trans supportedClassification)
      cases sameRecursive
      have original := translated
      cases translated with
      | forallE domainIsType _ domainTranslated _ =>
        obtain ⟨level, domainTyped, uniform⟩ :=
          headSupported virtual _ correspondence domainTranslated domainIsType
        obtain ⟨peeled, convertedBody, opening⟩ := translatedForallCtorFieldOpening envWF constants
          definitions correspondence reserved original domainTyped uniform
        obtain ⟨finalVirtual, finalSemantic, translatedTail⟩ := tailInduction
          (Nat.le_trans fieldOnly (Nat.le_add_right index 1)) opening.context
          opening.scope.reserved opening.bodyTranslated tailSupported
        exact ⟨finalVirtual, finalSemantic,
          .field selected classified tail original opening translatedTail⟩

theorem TranslatedRecursorCtorFieldTrace.finalTranslation {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic) :
    TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic := by
  induction history with
  | stop _ correspondence translated => exact ⟨correspondence, translated⟩
  | field _ _ _ _ _ _ tailInduction => exact tailInduction

theorem TranslatedRecursorCtorFieldTrace.scope {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) : reader.RecursorScopeFrame finalReader := by
  induction history with
  | stop _ correspondence _ => exact .refl _ correspondence.1 reserved
  | field _ _ _ _ opening _ tailInduction =>
    exact opening.scope.trans (tailInduction opening.scope.reserved)

theorem TranslatedRecursorCtorFieldTrace.mixedContext {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalFields.toList = fields.toList ++ ids.map Expr.fvar := by
  induction history generalizing model with
  | stop => exact ⟨model, [], modelWF, native, converted, .nil,
      by simp only [List.map_nil, List.append_nil]⟩
  | @field name domain body terminal bi index finalIndex fields recursiveFields finalFields
      finalRecursive reader finalReader recursive virtual finalVirtual semanticDomain bodySemantic
      peeled convertedBody finalSemantic level selected classified tail translated opening
      translatedTail tailInduction =>
    obtain ⟨nextWF, nextNative, nextConverted⟩ :=
      opening.mixedContext model modelWF native converted reserved
    obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
      tailInduction (ctorFieldMLCtx reader model name domain peeled bi)
        nextWF nextNative nextConverted opening.scope.reserved
    refine ⟨finalModel, ⟨reader.ngen.curr⟩ :: ids, finalWF, finalNative, finalConverted, ?_, ?_⟩
    · exact (IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ name
        (peelTypeAnnotations domain) peeled bi).trans extension
    · simpa only [Array.toList_push, List.map_cons, List.append_assoc,
        List.singleton_append] using array

theorem TranslatedRecursorCtorFieldTrace.typedAbstraction {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index #[] recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {body : Expr} {bodySemantic : VExpr}
    (bodyTranslated : TrExpr env universes finalVirtual body bodySemantic)
    (bodyTyped : env.IsType universes.length finalVirtual.toCtx bodySemantic) :
    ∃ abstracted level,
      TrExpr env universes finalVirtual (finalReader.lctx.mkForall finalFields body) abstracted ∧
        env.HasType universes.length finalVirtual.toCtx abstracted (.sort level) := by
  obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
    history.mixedContext model modelWF native converted reserved
  have selected : finalFields = (ids.map Expr.fvar).toArray := by
    rw [Array.toList_empty, List.nil_append] at array
    rw [← array, Array.toArray_toList]
  have translatedInModel : TrExpr env universes finalModel.vlctx body bodySemantic := by
    simpa only [finalConverted] using bodyTranslated
  have typedInModel : env.IsType universes.length finalModel.vlctx.toCtx bodySemantic := by
    simpa only [finalConverted] using bodyTyped
  obtain ⟨translated, level, typed⟩ :=
    extension.typedBodyAbstractionAtFinal envWF finalWF translatedInModel typedInModel
  exact ⟨_, level, by simpa only [selected, finalNative, finalConverted] using translated,
    by simpa only [finalConverted] using typed⟩

end Lean4Lean.AddInductive
