import Lean4Lean.Verify.InductiveMajorContextTranslation
import Lean4Lean.Verify.InductiveRecursorIndexTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem translatedConstantHeader {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {name : Name} {nativeLevels : List Level} {semanticLevels : List VLevel}
    {constant : VConstant} {headerSemantic : VExpr}
    (envWF : env.WF) (contextWF : OnCtx virtual.toCtx (env.IsType universes.length))
    (lookup : env.constants name = some constant)
    (levels : nativeLevels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : nativeLevels.length = constant.uvars)
    (alignment : env.IsDefEqU universes.length virtual.toCtx
      (constant.type.instL semanticLevels) headerSemantic) :
    TrExprS env universes virtual (.const name nativeLevels) (.const name semanticLevels) ∧
      env.HasType universes.length virtual.toCtx (.const name semanticLevels) headerSemantic := by
  have typed := VEnv.HasType.const (Γ := virtual.toCtx) lookup
    (VLevel.WF.of_mapM_ofLevel levels) ((List.mapM_eq_some.mp levels).length_eq.symm.trans arity)
  exact ⟨.const lookup levels arity, typed.defeqU_r envWF contextWF alignment⟩

theorem TranslatedRecursorIndexTrace.constantApplication
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index #[] reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (readerWF : reader.lctx.WF)
    {name : Name} {nativeLevels : List Level} {semanticLevels : List VLevel} {constant : VConstant}
    (lookup : env.constants name = some constant)
    (levels : nativeLevels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : nativeLevels.length = constant.uvars)
    (alignment : env.IsDefEqU universes.length virtual.toCtx
      (constant.type.instL semanticLevels) semantic) :
    ∃ finalValue, TrExprS env universes finalVirtual (mkAppN (.const name nativeLevels) finalIndices) finalValue ∧
      env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic := by
  have correspondence := history.initialCorrespondence readerWF
  obtain ⟨translated, typed⟩ := translatedConstantHeader envWF correspondence.wf.toCtx
    lookup levels arity alignment
  exact history.application envWF
    (by simpa only [mkAppN, Array.foldl_empty] using translated) typed

theorem withLocalDecl.majorTranslation {ResultType : Type}
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : TrLCtx env universes
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx
      (recursorMajorVirtualContext stats parent indices reader virtual peeled) →
      (next (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))).WF post) :
    (withLocalDecl `t .default (recursorMajorDomain stats parent indices) next reader).WF post :=
  nextWF opening.2.2.2.2.2.1

theorem mkRecInfos.getTranslatedMajorSources {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2) :
    (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoMajorSources env universes stats types elimLevel reader result.1 result.2 := by
  intro result success
  obtain ⟨frame, counts, sources⟩ := mkRecInfos.getTranslatedIndexSources stats types elimLevel reader
    envWF constants definitions indexOnly readerWF reserved
    (fun captured actual => (support captured actual).1) result success
  exact ⟨frame, counts, sources.majorTranslated envWF constants definitions indexOnly
    (support result success).2⟩

theorem mkRecInfos.scopedTranslatedMajorSources {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoMajorSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun infos => do return (infos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedMajorSources stats types elimLevel reader
    envWF constants definitions indexOnly readerWF reserved support).bind ?_
  rintro ⟨infos, current⟩ ⟨frame, _, sources⟩
  exact nextWF infos current frame sources

end Lean4Lean.AddInductive
