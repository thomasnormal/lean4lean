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

theorem RecursorTypeModelReceipt.metadataTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name)
    (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes initial.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length initial.vlctx.toCtx semantic := by
  have metadata := receipt.metadataType types elimLevel lparams isK isUnsafe rules
  refine ⟨metadata.choose, metadata.choose_spec.choose_spec.1, ?_⟩
  exact ⟨metadata.choose_spec.choose, metadata.choose_spec.choose_spec.2.1⟩

theorem RecursorTypeModelReceipt.storedTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    ∃ semantic,
      TrExprS env universes initial.vlctx
        ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length initial.vlctx.toCtx semantic := by
  obtain ⟨semantic, level, _, stored, typed, _⟩ := receipt
  exact ⟨semantic, stored, ⟨level, typed⟩⟩

theorem RecursorTypeModelReceipt.initialStoredWF
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (constant : VConstVal)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (constantUvars : constant.uvars = universes.length)
    (constantType : TrExprS env universes initial.vlctx
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) constant.type)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  obtain ⟨semantic, level, _, stored, typed, _⟩ := receipt
  have contextEquality : VLCtx.IsDefEq env universes.length initial.vlctx initial.vlctx :=
    VLCtx.IsDefEq.refl envWF.ordered initialWF.tr.wf
  obtain ⟨_, translatedEquality⟩ :=
    TrExprS.uniq (henv := envWF) contextEquality stored constantType
  have constantTyped := typed.defeqU_l envWF initialWF.tr.wf.toCtx translatedEquality.toU
  change env.IsType constant.uvars [] constant.type
  rw [constantUvars]
  exact ⟨level, empty ▸ constantTyped⟩

theorem RecursorTypeModelReceipt.initialStoredWF_of_closedTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (constant : VConstVal)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (constantUvars : constant.uvars = universes.length)
    (storedTranslated : TrExprS env universes []
      ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) constant.type)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  apply receipt.initialStoredWF constant envWF initialWF constantUvars
    (empty := empty)
  have initialLength : initial.vlctx.toCtx.length = 0 := by simp [empty]
  simpa only [initialLength, VExpr.liftN_zero] using storedTranslated.weakFV envWF.ordered
    (VLCtx.FVLift.from_nil initial.noBV) initialWF.tr.wf

theorem RecursorTypeModelReceipt.initialStoredWF_of_recursorTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (constant : VConstVal) (info : RecursorVal)
    (native : TrConstVal .safe env (.recInfo info) constant)
    (levels : info.levelParams = universes)
    (type : info.type =
      (recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  apply receipt.initialStoredWF_of_closedTranslation constant envWF initialWF
    (empty := empty)
  · rw [← levels]
    exact native.1.2.1.symm
  · rw [← levels, ← type]
    exact native.1.2.2

theorem RecursorTypeModelReceipt.initialStoredWF_of_declaredRecursor
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (constant : VConstVal) (lparams : List Name) (isK isUnsafe : Bool)
    (rules : List RecursorRule)
    (native : TrConstVal .safe env
      (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
        isK isUnsafe parent rules)) constant)
    (levels : (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
      isK isUnsafe parent rules).levelParams = universes)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  apply receipt.initialStoredWF_of_recursorTranslation constant
    (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
      isK isUnsafe parent rules) native levels
    (declareRecursors.metadataVal_type stats types elimLevel infos lparams reader.lctx
      isK isUnsafe parent rules) envWF initialWF empty

theorem RecursorTypeModelReceipt.initialStoredWFOfDeclaredRecursors
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {reader : Context} {initial final : MLCtx}
    (receipts : ∀ parent, parent < types.size →
      RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (constants : ∀ parent, parent < types.size → VConstVal)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (native : ∀ parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK isUnsafe parent rules)) (constants parent bound))
    (levels : ∀ parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (empty : initial.vlctx.toCtx = []) :
    ∀ parent (bound : parent < types.size), (constants parent bound).toVConstant.WF env := by
  intro parent bound
  exact (receipts parent bound).initialStoredWF_of_declaredRecursor (constants parent bound)
    lparams isK isUnsafe rules (native parent bound) (levels parent bound) envWF initialWF empty

/-- An empty native translation context lets the receipt supply the model constant itself.
An empty `toCtx` alone would still permit native free variables from let bindings. -/
theorem RecursorTypeModelReceipt.existsDeclaredRecursor
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = []) :
    ∃ constant : VConstVal,
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK false parent rules)) constant ∧ constant.toVConstant.WF env := by
  obtain ⟨semantic, level, translated, typed, _⟩ :=
    receipt.metadataType types elimLevel lparams isK false rules
  let constant : VConstVal :=
    { name := mkRecName types[parent]!.name, uvars := universes.length, type := semantic }
  refine ⟨constant, ⟨⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
  · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
      declareRecursors.metadataVal]
  · exact congrArg List.length levels
  · change TrExprS env (getRecLevelParams elimLevel lparams) []
      (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
        isK false parent rules).type semantic
    rw [levels]
    simpa only [empty] using translated
  · change env.IsType universes.length [] semantic
    exact ⟨level, by simpa only [empty, VLCtx.toCtx] using typed⟩

theorem RecursorTypeModelReceipt.rawTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    ∃ semantic,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent reader.lctx) semantic ∧
      env.IsType universes.length initial.vlctx.toCtx semantic := by
  obtain ⟨semantic, level, raw, _, typed, _⟩ := receipt
  exact ⟨semantic, raw, ⟨level, typed⟩⟩

theorem RecursorTypeModelReceipt.finalRawTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent reader.lctx) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  obtain ⟨semantic, level, _, _, _, raw, _, typed⟩ := receipt
  exact ⟨semantic.liftN (final.length - initial.length), raw, ⟨level, typed⟩⟩

theorem RecursorTypeModelReceipt.finalStoredTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        ((recursorRawType stats infos parent reader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  obtain ⟨semantic, level, _, _, _, _, stored, typed⟩ := receipt
  exact ⟨semantic.liftN (final.length - initial.length), stored, ⟨level, typed⟩⟩

theorem RecursorTypeModelReceipt.finalMetadataTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {reader : Context} {initial final : MLCtx}
    (receipt : RecursorTypeModelReceipt env universes stats infos parent reader initial final)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name)
    (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams reader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  have metadata := receipt.metadataType types elimLevel lparams isK isUnsafe rules
  refine ⟨metadata.choose.liftN (final.length - initial.length),
    metadata.choose_spec.choose_spec.2.2.1, ?_⟩
  exact ⟨metadata.choose_spec.choose, metadata.choose_spec.choose_spec.2.2.2⟩

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

theorem RecursorInfoModelEndpoint.finalMetadataTypehood
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorType envWF initialWF parameterFree parent support).finalMetadataTypehood
    types elimLevel lparams isK isUnsafe rules

theorem RecursorInfoModelEndpoint.finalRawTypehood
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
    ∃ semantic,
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorType envWF initialWF parameterFree parent support).finalRawTypehood

theorem RecursorInfoModelEndpoint.finalStoredTypehood
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
    ∃ semantic,
      TrExprS env universes final.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorType envWF initialWF parameterFree parent support).finalStoredTypehood

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
