import Lean4Lean.Verify.InductiveRecursorIndexTranslationFacts
import Lean4Lean.Verify.InductiveCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private readWF bindWF from Lean4Lean.Verify.InductiveStats

theorem mkRecInfos.scopedTranslatedIndexSources {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel
        reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoIndexSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  let collect : Array RecInfo → M (Array RecInfo × Context) :=
    fun infos => do return (infos, ← readThe Context)
  rw [mkRecInfos.morphism stats types elimLevel next collect
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  have observed : (mkRecInfos stats types elimLevel collect reader).WF fun result =>
      mkRecInfos stats types elimLevel collect reader = .ok result ∧
      reader.RecursorScopeFrame result.2 ∧
      RecursorInfoIndexSources stats types elimLevel reader result.1 result.2 := by
    intro result success
    obtain ⟨frame, _, sources⟩ :=
      mkRecInfos.getIndexSources stats types elimLevel reader readerWF reserved result success
    exact ⟨success, frame, sources⟩
  refine observed.bind ?_
  rintro ⟨infos, current⟩ ⟨success, frame, sources⟩
  exact nextWF infos current frame
    (sources.translated envWF constants definitions indexOnly (support _ success))

theorem mkRecInfos.getTranslatedIndexSources {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel
        reader result.1 result.2) :
    (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoIndexSources env universes stats types elimLevel reader result.1 result.2 := by
  intro result success
  obtain ⟨frame, counts, sources⟩ :=
    mkRecInfos.getIndexSources stats types elimLevel reader readerWF reserved result success
  exact ⟨frame, counts,
    sources.translated envWF constants definitions indexOnly (support result success)⟩

theorem mkRecInfos.registeredTranslatedIndexSources {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel
        reader result.1 result.2) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      TranslatedRecursorInfoIndexSources env universes stats types elimLevel
        reader result.2.1 result.2.2 ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have translatedSources :
      (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
        TranslatedRecursorInfoIndexSources env universes stats types elimLevel
          reader result.2.1 result.2.2 := by
    unfold mkRecInfos.scopeRegistration
    refine mkRecInfos.scopedTranslatedIndexSources stats types elimLevel _ reader _
      envWF constants definitions indexOnly readerWF reserved support ?_
    intro infos current _ sources
    apply readWF
    apply bindWF
    intro registeredEnv
    exact .pure sources
  intro result success
  obtain ⟨frame, counts, _, registeredWF, retained, metadata, rhsScope⟩ :=
    mkRecInfos.registeredIndexSources stats types elimLevel lparams isK isUnsafe reader
      readerWF reserved nativeEnvWF result success
  exact ⟨frame, counts, translatedSources result success,
    registeredWF, retained, metadata, rhsScope⟩

end Lean4Lean.AddInductive
