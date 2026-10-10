import Lean4Lean.Verify.InductiveRecursorTypeTranslation
import Lean4Lean.Verify.InductiveRecursorImplicitTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def RecursorTypeModelReceipt (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (reader : Context) (initial final : MLCtx) : Prop :=
  ∃ semantic level,
    TrExprS env universes initial.vlctx (recursorRawType stats infos parent reader.lctx) semantic ∧
    TrExprS env universes initial.vlctx
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) semantic ∧
    env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) ∧
    TrExprS env universes final.vlctx (recursorRawType stats infos parent reader.lctx)
      (semantic.liftN (final.length - initial.length)) ∧
    TrExprS env universes final.vlctx
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false)
      (semantic.liftN (final.length - initial.length)) ∧
    env.HasType universes.length final.vlctx.toCtx
      (semantic.liftN (final.length - initial.length)) (.sort level)

theorem RecursorTypeModelReceipt.sourceFVars
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    Expr.FVarsIn (· ∈ initial.vlctx.fvars) (recursorRawType stats infos parent reader.lctx) ∧
      Expr.FVarsIn (· ∈ initial.vlctx.fvars)
        ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) := by
  obtain ⟨_, _, raw, stored, _⟩ := receipt
  exact ⟨raw.fvarsIn, stored.fvarsIn⟩

theorem RecursorTypeModelReceipt.sourceClosed
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    (recursorRawType stats infos parent reader.lctx).looseBVarRange' = 0 ∧
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false).looseBVarRange' = 0 := by
  obtain ⟨_, _, raw, stored, _⟩ := receipt
  exact ⟨(initial.noBV ▸ raw.closed).looseBVarRange_zero,
    (initial.noBV ▸ stored.closed).looseBVarRange_zero⟩

theorem RecursorTypeModelReceipt.metadataType
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name)
    (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) ∧
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK isUnsafe parent rules).type (semantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (semantic.liftN (final.length - initial.length)) (.sort level) := by
  obtain ⟨semantic, level, _, stored, typed, _, currentStored, currentTyped⟩ := receipt
  exact ⟨semantic, level, stored, typed, currentStored, currentTyped⟩

theorem RecursorInfoModelEndpoint.recursorType
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final := by
  obtain ⟨semantic, level, raw, typed⟩ := endpoint.rawTypeTranslation
    envWF initialWF parameterFree parent support
  obtain ⟨currentRaw, currentTyped⟩ := endpoint.liftTypeTranslation envWF raw typed
  exact ⟨semantic, level, raw, raw.inferImplicit 1000 false, typed,
    currentRaw, currentRaw.inferImplicit 1000 false, currentTyped⟩

theorem mkRecInfos.getTranslatedRecursorTypes
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (typeSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorRawTypeTranslationSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats result.1 parent result.2 model finalModel := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact endpoint.recursorType envWF modelWF fieldOnly parent
    (typeSupport result success finalModel endpoint parent bound)

theorem mkRecInfos.scopedTranslatedRecursorTypes {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (typeSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorRawTypeTranslationSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport typeSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, receipts⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint receipts

end Lean4Lean.AddInductive
