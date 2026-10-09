import Lean4Lean.Verify.InductiveMotiveBindingFacts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem IndexMLCtxExtension.typedAbstraction {env : VEnv} {universes : List Name}
    {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ semantic level,
      TrExprS env universes final.vlctx
          (final.mkForall ids.length extension.bound (.sort elimLevel)) semantic ∧
        env.HasType universes.length final.vlctx.toCtx semantic (.sort level) := by
  have elimTyped : env.HasType universes.length final.vlctx.toCtx
      (.sort semanticElimLevel) (.sort (.succ semanticElimLevel)) :=
    .sort (VLevel.WF.of_ofLevel mapped)
  obtain ⟨translated, level, typed⟩ := modelWF.mkForall_trS envWF (.sort mapped)
    ⟨.succ semanticElimLevel, elimTyped⟩ ids.length extension.bound
  have initialTranslated : TrExprS env universes initial.vlctx
      (final.mkForall ids.length extension.bound (.sort elimLevel))
      (final.mkForall' ids.length extension.bound (.sort semanticElimLevel)) := by
    simpa only [extension.drop_eq] using translated
  have initialTyped : env.HasType universes.length initial.vlctx.toCtx
      (final.mkForall' ids.length extension.bound (.sort semanticElimLevel)) (.sort level) := by
    simpa only [extension.drop_eq] using typed
  exact ⟨_, level,
    initialTranslated.weakFV envWF.ordered extension.weakening modelWF.tr.wf,
    by simpa only [VExpr.liftN] using initialTyped.weakN envWF.ordered extension.weakening.toCtx⟩

def RecursorMotiveDomainTranslation (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (parent : Nat) (indices : Array Expr) (reader : Context)
    (virtual : VLCtx) (peeled : VExpr) (elimLevel : Level) (semantic : VExpr)
    (level : VLevel) : Prop :=
  TrExprS env universes (recursorMajorVirtualContext stats parent indices reader virtual peeled)
      (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))) semantic ∧
    env.HasType universes.length
      (recursorMajorVirtualContext stats parent indices reader virtual peeled).toCtx
      semantic (.sort level)

theorem TranslatedRecursorIndexTrace.motiveDomainTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {source terminal : Expr} {index finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    {rawSemantic peeled : VExpr} {majorLevel : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices indexReader
      finalVirtual rawSemantic peeled majorLevel)
    (envWF : env.WF) (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ motiveSemantic motiveLevel,
      RecursorMotiveDomainTranslation env universes stats parent indices indexReader
        finalVirtual peeled elimLevel motiveSemantic motiveLevel := by
  obtain ⟨indexModel, ids, indexWF, indexNative, indexConverted, extension, arrays⟩ :=
    history.mixedContext model modelWF native converted reserved
  have selected : indices.toList = ids.map Expr.fvar := by
    simpa only [Array.toList_empty, List.nil_append] using arrays
  have indexReserved := (history.scope reserved).reserved
  obtain ⟨majorWF, _, majorConverted⟩ :=
    opening.mixedContext indexModel indexWF indexNative indexConverted indexReserved
  have majorExtension := extension.push ⟨indexReader.ngen.curr⟩ `t
    (recursorMajorDomain stats parent indices) peeled .default
  obtain ⟨motiveSemantic, motiveLevel, translated, typed⟩ :=
    majorExtension.typedAbstraction envWF majorWF mapped
  have binding := opening.motiveBindingEquation extension indexWF indexNative indexConverted
    indexReserved selected elimLevel
  dsimp only [recursorMajorMLCtx] at majorConverted binding
  refine ⟨motiveSemantic, motiveLevel, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton, majorConverted, ← binding] using translated
  · simpa only [majorConverted] using typed

end Lean4Lean.AddInductive
