import Lean4Lean.Verify.InductiveIndexTraceTranslationFacts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem mkRecInfos.loopArgs1.translatedTrace {ResultType : Type}
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {semantic : VExpr}
    (stats : InductiveStats) (source : Expr) (index : Nat) (indices : Array Expr)
    (fuel : Nat) (next : Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (supports : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader
        terminal finalIndex finalIndices current),
      IndexTraceAnnotationSupport env universes trace ∧
        IndexTraceNormalizationSupport env universes trace)
    (nextWF : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader
        terminal finalIndex finalIndices current) finalVirtual finalSemantic,
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic →
      TrLCtx env universes current.lctx finalVirtual →
      TrExprS env universes finalVirtual terminal finalSemantic →
      reader.RecursorScopeFrame current → (next finalIndices current).WF post) :
    (mkRecInfos.loopArgs1 stats source index indices fuel next reader).WF post := by
  apply mkRecInfos.loopArgs1.scopedTrace stats source index indices fuel next reader post
    correspondence.1 reserved
  intro terminal finalIndex finalIndices current trace frame
  obtain ⟨annotations, normalizations⟩ := supports terminal finalIndex finalIndices current trace
  obtain ⟨finalVirtual, finalSemantic, history⟩ := trace.translated envWF constants definitions
    indexOnly correspondence reserved translated annotations normalizations
  obtain ⟨finalCorrespondence, terminalTranslation⟩ := history.finalTranslation
  exact nextWF terminal finalIndex finalIndices current trace finalVirtual finalSemantic
    history finalCorrespondence terminalTranslation frame

theorem mkRecInfos.loopArgs1.translatedTrace_ofSortTelescope {ResultType : Type}
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {semantic : VExpr}
    (stats : InductiveStats) (source : Expr) (index : Nat) (indices : Array Expr)
    (fuel : Nat) (next : Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic) (telescope : SortTelescope source)
    (annotations : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader
        terminal finalIndex finalIndices current), IndexTraceAnnotationSupport env universes trace)
    (nextWF : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader
        terminal finalIndex finalIndices current) finalVirtual finalSemantic,
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic →
      TrLCtx env universes current.lctx finalVirtual →
      TrExprS env universes finalVirtual terminal finalSemantic →
      reader.RecursorScopeFrame current → (next finalIndices current).WF post) :
    (mkRecInfos.loopArgs1 stats source index indices fuel next reader).WF post := by
  apply mkRecInfos.loopArgs1.translatedTrace stats source index indices fuel next reader post
    envWF constants definitions indexOnly correspondence reserved translated _ nextWF
  intro terminal finalIndex finalIndices current trace
  exact ⟨annotations terminal finalIndex finalIndices current trace,
    trace.normalizationSupport_ofSortTelescope telescope⟩

theorem mkRecInfos.loopArgs1.getTranslatedTrace
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {semantic : VExpr}
    (stats : InductiveStats) (source : Expr) (index : Nat) (indices : Array Expr)
    (fuel : Nat) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (supports : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader
        terminal finalIndex finalIndices current),
      IndexTraceAnnotationSupport env universes trace ∧
        IndexTraceNormalizationSupport env universes trace) :
    (mkRecInfos.loopArgs1 stats source index indices fuel
      (fun values => do return (values, ← readThe Context)) reader).WF fun result =>
      ∃ terminal finalVirtual finalSemantic,
        ∃ trace : RecursorIndexTrace stats source index indices reader terminal index result.1 result.2,
        TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
        TrLCtx env universes result.2.lctx finalVirtual ∧
        TrExprS env universes finalVirtual terminal finalSemantic ∧
        reader.RecursorScopeFrame result.2 := by
  refine mkRecInfos.loopArgs1.translatedTrace stats source index indices fuel
    (fun values => do return (values, ← readThe Context)) reader _
    envWF constants definitions indexOnly correspondence reserved translated supports ?_
  intro terminal finalIndex finalIndices current trace finalVirtual finalSemantic history
    finalCorrespondence terminalTranslation frame
  have unchanged := history.indexUnchanged
  subst finalIndex
  exact .pure ⟨terminal, finalVirtual, finalSemantic, trace, history,
    finalCorrespondence, terminalTranslation, frame⟩

end Lean4Lean.AddInductive
