import Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS
import Lean4Lean.Verify.InductiveRecursorApplicationTranslation
import Lean4Lean.Verify.InductiveGeneratedRuleResult

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)
open private readWF bindWF from Lean4Lean.Verify.InductiveStats

def RecursorSelectedDomainSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (full : LocalContext) (initial : MLCtx) : Prop :=
  ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
    ∃ projected, SelectedRecursorTelescope env universes full initial ids projected

/- The translated parent/minor endpoint already contains a model extension for
   every allocated recursor binder.  Once native allocation order is aligned
   with `recursorTypeBinders`, that extension itself supplies the semantic
   selected-domain telescope.  Keep the alignment as a premise: the endpoint
   does not manufacture a native binder-order equation. -/
theorem RecursorInfoModelEndpoint.selectedDomainSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx} {parent : Nat}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (alignment : ∀ ids, IndexMLCtxExtension initial ids final →
      (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar) :
    RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial := by
  obtain ⟨ids, extension⟩ := endpoint.extension
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have telescope : SelectedRecursorTelescope env universes finalReader.lctx initial ids final := by
    simpa only [finalNative] using extension.selectedTelescope finalWF
  exact ⟨ids, alignment ids extension, final, telescope⟩

/- The endpoint's extension is chronological: all parent-pass allocations are
   completed before the minor pass starts.  Expose both phases separately so
   a caller can compare native allocation order with the recursor-type binder
   order instead of silently treating the aggregate list as canonical. -/
theorem RecursorInfoModelEndpoint.passExtensions
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final) :
    ∃ parentModel parentIds minorIds,
      IndexMLCtxExtension initial parentIds parentModel ∧
      IndexMLCtxExtension parentModel minorIds final ∧
      IndexMLCtxExtension initial (parentIds ++ minorIds) final := by
  rcases endpoint with ⟨parentInfos, parentReader, parentModel, parentTrace, minorTrace,
    parentHistory, minorHistory⟩
  obtain ⟨parentIds, parentExtension⟩ := parentHistory.extension
  obtain ⟨minorIds, minorExtension⟩ := minorHistory.extension
  exact ⟨parentModel, parentIds, minorIds, parentExtension, minorExtension,
    parentExtension.trans minorExtension⟩

/- For canonical Bool, native parent allocation is major-then-motive, while
   the recursor type groups motive/minors before major.  Keep this shape
   obstruction explicit: selected-domain support needs a reordering/rebase
   theorem, not an unproved identification of the chronological extension. -/
theorem canonicalBoolRecursorBinderOrderBoundary
    {stats : InductiveStats} {infos : Array RecInfo}
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (distinct : major ≠ motive) :
    (recursorTypeBinders stats infos 0).toList ≠
      [major, motive, minorFalse, minorTrue].map Expr.fvar := by
  intro alignment
  have order : [motive, minorFalse, minorTrue, major] =
      [major, motive, minorFalse, minorTrue] := by
    simpa [recursorTypeBinders, params, infosEq, motiveEq, minorsEq, indicesEq, majorEq]
      using alignment
  have head := congrArg List.head? order
  have motiveMajor : motive = major := by simpa using head
  exact distinct motiveMajor.symm

/- Once selected-domain support is available, its semantic content can be
   consumed one binder at a time.  This packages the exact chronological
   prefix model, native cdecl provenance, translated domain, and domain
   typehood for every selected recursor binder.  Native metadata by itself
   supplies only the cdecl provenance; the telescope receipt is the missing
   semantic premise at the canonical frontend boundary. -/
theorem RecursorSelectedDomainSupport.domainReceipts
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext} {initial : MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent full initial) :
    ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
      ∃ projected, SelectedRecursorTelescope env universes full initial ids projected ∧
        ∀ identifier, identifier ∈ ids →
          ∃ preIds suffix model physicalIndex name domain binder semantic,
            ids = preIds ++ identifier :: suffix ∧
            SelectedRecursorTelescope env universes full initial preIds model ∧
            full.find? identifier =
              some (.cdecl physicalIndex identifier name domain binder .default) ∧
            model.lctx.find? identifier = none ∧
            TrExprS env universes model.vlctx domain semantic ∧
            env.IsType universes.length model.vlctx.toCtx semantic := by
  obtain ⟨ids, selected, projected, telescope⟩ := support
  refine ⟨ids, selected, projected, telescope, ?_⟩
  intro identifier member
  exact telescope.domainReceipt identifier member

def RecursorFinalTypehood (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (finalReader : Context) (finalModel : MLCtx)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) : Prop :=
  ∀ parent, parent < types.size →
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic)

def RecursorInitialTypehood (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (finalReader : Context) (initialModel : MLCtx)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) : Prop :=
  ∀ parent, parent < types.size →
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic)

theorem RecursorSelectedDomainSupport.rawTypeSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo} {parent : Nat}
    {original current : Context} {initial : MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent current.lctx initial)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (fullScope : current.lctx.BindingScope) (bound : parent < infos.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    RecursorRawTypeTranslationSupport env universes stats infos parent current.lctx initial := by
  obtain ⟨ids, selected, projected, telescope⟩ := support
  refine ⟨ids, selected, ⟨projected, telescope⟩, ?_⟩
  intro projected projectedTelescope
  exact projectedTelescope.bodyApplicationSupport envWF initialWF fullScope bound selected source mapped

theorem RecursorInfoModelEndpoint.recursorTypeFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final := by
  have fullScope : finalReader.lctx.BindingScope := by
    simpa only [endpoint.context.2.1] using endpoint.context.1.bindingScope
  have infoBound : parent < infos.size := by simpa only [endpoint.infoSize] using bound
  exact endpoint.recursorType envWF initialWF parameterFree parent
    (support.rawTypeSupport envWF initialWF fullScope infoBound source mapped)

/-- Combine the selected-domain application receipt with the exact model constant
    used by native recursor registration.  This is the semantic boundary needed
    by callers that have established the recursor type support but have not yet
    assembled the whole registration CPS.  In particular, the theorem keeps
    the native index source, elimination-level mapping, and empty initial model
    context visible instead of manufacturing a model constant from a weaker
    typehood statement. -/
theorem RecursorInfoModelEndpoint.declaredRecursorFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = []) :
    ∃ (constant : VConstVal),
      RecursorTypeModelReceipt env universes stats infos parent finalReader initial final ∧
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          finalReader.lctx isK false parent rules)) constant ∧
      constant.toVConstant.WF env := by
  have receipt := endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound
    source mapped support
  obtain ⟨constant, translated, wellFormed⟩ :=
    receipt.existsDeclaredRecursor (types := types) lparams isK rules levels empty
  exact ⟨constant, receipt, translated, wellFormed⟩

theorem RecursorInfoModelEndpoint.finalStoredTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support).finalStoredTypehood

theorem RecursorInfoModelEndpoint.finalRawTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support).finalRawTypehood

theorem RecursorInfoModelEndpoint.finalMetadataTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support)
    |>.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules

theorem RecursorInfoModelEndpoint.initialTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
      lparams isK isUnsafe rules := by
  intro parent bound
  have receipt := endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound
    (sources parent bound) mapped (supports parent bound)
  exact ⟨receipt.rawTypehood, receipt.storedTypehood,
    receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩

theorem RecursorInfoModelEndpoint.initialStoredWF_of_declaredRecursorFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constant : VConstVal) (lparams : List Name) (isK isUnsafe : Bool)
    (rules : List RecursorRule)
    (native : TrConstVal .safe env
      (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules)) constant)
    (levels : (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
      isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support)
    |>.initialStoredWF_of_declaredRecursor constant lparams isK isUnsafe rules native levels
      envWF initialWF empty

theorem RecursorInfoModelEndpoint.initialStoredWFOfDeclaredRecursorsFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constants : ∀ parent, parent < types.size → VConstVal)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (native : ∀ parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules)) (constants parent bound))
    (levels : ∀ parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) :
    ∀ parent (bound : parent < types.size), (constants parent bound).toVConstant.WF env := by
  intro parent bound
  exact endpoint.initialStoredWF_of_declaredRecursorFromDomains envWF initialWF parameterFree parent
    bound (sources parent bound) mapped (supports parent bound) (constants parent bound) lparams
    isK isUnsafe rules (native parent bound) (levels parent bound) empty

theorem RecursorInfoModelEndpoint.finalTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
      lparams isK isUnsafe rules := by
  intro parent bound
  exact ⟨endpoint.finalRawTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound),
    endpoint.finalStoredTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound),
    endpoint.finalMetadataTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound)
      lparams isK isUnsafe rules⟩

theorem mkRecInfos.getTranslatedAppliedRecursorTypes
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
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
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact endpoint.recursorTypeFromDomains envWF modelWF fieldOnly parent bound
    (sources.2 parent bound) mapped (domainSupport result success finalModel endpoint parent bound)

theorem mkRecInfos.getTranslatedAppliedInitialStoredWFOfDeclaredRecursors
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (recursorConstant : ∀ (_finalInfos : Array RecInfo) (_finalReader : Context) (_finalModel : MLCtx)
      parent, parent < types.size → VConstVal)
    (recursorNative : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (finalModel : MLCtx)
      parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel finalInfos lparams
          finalReader.lctx isK isUnsafe parent rules))
        (recursorConstant finalInfos finalReader finalModel parent bound))
    (recursorLevels : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (_finalModel : MLCtx)
      parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : model.vlctx.toCtx = []) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∀ bound, (recursorConstant result.1 result.2 finalModel parent bound).toVConstant.WF env := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent parentBound bound
  exact (receipts parent parentBound).initialStoredWF_of_declaredRecursor
    (recursorConstant result.1 result.2 finalModel parent bound) lparams isK isUnsafe rules
    (recursorNative result.1 result.2 finalModel parent bound)
    (recursorLevels result.1 result.2 finalModel parent bound) envWF modelWF empty

theorem mkRecInfos.getTranslatedAppliedFinalStoredTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats result.1 parent result.2.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalStoredTypehood

theorem mkRecInfos.getTranslatedAppliedFinalRawTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats result.1 parent result.2.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalRawTypehood

theorem mkRecInfos.getTranslatedAppliedFinalMetadataTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel result.1 lparams result.2.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalMetadataTypehood types elimLevel lparams isK isUnsafe rules

theorem mkRecInfos.scopedTranslatedAppliedFinalMetadataTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalMetadataTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, metadataTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint metadataTypehood

theorem mkRecInfos.scopedTranslatedAppliedFinalStoredTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats finalInfos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalStoredTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, storedTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint storedTypehood

theorem mkRecInfos.scopedTranslatedAppliedFinalRawTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats finalInfos parent finalReader.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalRawTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, rawTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint rawTypehood

theorem mkRecInfos.getTranslatedAppliedFinalTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        RecursorFinalTypehood env universes stats types elimLevel result.1 result.2
          finalModel lparams isK isUnsafe rules := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.finalTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem RecursorInfoModelEndpoint.initialAndFinalTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
        lparams isK isUnsafe rules ∧
      RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
        lparams isK isUnsafe rules := by
  exact ⟨endpoint.initialTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
      lparams isK isUnsafe rules,
    endpoint.finalTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
      lparams isK isUnsafe rules⟩

theorem mkRecInfos.getTranslatedAppliedInitialTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.initialTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem mkRecInfos.getTranslatedAppliedInitialAndFinalTypehood
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.1 result.2
            finalModel lparams isK isUnsafe rules) := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.initialAndFinalTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem mkRecInfos.scopedTranslatedAppliedFinalTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
        finalModel lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedInitialTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
        model lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedInitialTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedInitialAndFinalTypehood {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedInitialAndFinalTypehood stats types elimLevel reader envWF
    constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
    domainSupport lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedRecursorTypes {ResultType : Type}
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
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
  refine (mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, receipts⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint receipts

theorem mkRecInfos.registeredTranslatedAppliedRecursorTypes
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        ∀ parent, parent < types.size →
          RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have translatedApplied :
      (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
        reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
        ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
          result.2.1 result.2.2 model finalModel ∧
          ∀ parent, parent < types.size →
            RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel := by
    unfold mkRecInfos.scopeRegistration
    refine mkRecInfos.scopedTranslatedAppliedRecursorTypes stats types elimLevel _ reader _ envWF
      constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
      domainSupport ?_
    intro finalInfos finalReader finalModel frame counts endpoint receipts
    apply readWF
    apply bindWF
    intro registeredEnv
    exact .pure ⟨frame, counts, finalModel, endpoint, receipts⟩
  intro result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨frame, counts, registeredWF, retained, metadata, rhsScope⟩ :=
    mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe reader
      readerWF reserved nativeEnvWF result success
  obtain ⟨_, _, finalModel, endpoint, receipts⟩ := translatedApplied result success
  exact ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩

/-- Construct translated model constants for the recursors actually stored by registration.
This supplies their type receipts; rule semantics and model insertion remain separate. -/
theorem mkRecInfos.registeredTranslatedAppliedDeclaredRecursors
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : model.vlctx = []) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        ∀ parent, parent < types.size →
          RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK false result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      ∀ parent, parent < types.size → ∃ (info : RecursorVal) (constant : VConstVal),
        result.1.find? (mkRecName types[parent]!.name) = some (.recInfo info) ∧
        TrConstVal .safe env (.recInfo info) constant ∧ constant.toVConstant.WF env := by
  refine (mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK false reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport).mono ?_
  rintro result ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained,
    metadata, rhsScope⟩
  refine ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained,
    metadata, rhsScope, ?_⟩
  intro parent bound
  obtain ⟨rules, _, lookup⟩ := metadata parent bound
  obtain ⟨constant, translated, wellFormed⟩ :=
    (receipts parent bound).existsDeclaredRecursor lparams isK rules levels empty
  exact ⟨_, constant, lookup, translated, wellFormed⟩

theorem mkRecInfos.registeredTranslatedAppliedInitialAndFinalTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.2.1 result.2.2
            model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.2.1 result.2.2
            finalModel lparams isK isUnsafe rules)) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have registered := mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport
  intro result success
  obtain ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩ :=
    registered result success
  have initial : RecursorInitialTypehood env universes stats types elimLevel result.2.1 result.2.2
      model lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.rawTypehood, receipt.storedTypehood,
      receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  have final : RecursorFinalTypehood env universes stats types elimLevel result.2.1 result.2.2
      finalModel lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.finalRawTypehood, receipt.finalStoredTypehood,
      receipt.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  exact ⟨frame, counts, ⟨finalModel, endpoint, initial, final⟩,
    registeredWF, retained, metadata, rhsScope⟩

theorem mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine (mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨registeredEnv, finalInfos, finalReader⟩
    ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope

/- Registration can consume closed rule semantics while a later RHS consumer
   keeps a richer per-rule result.  The result relation is abstract here so
   this CPS layer does not depend on the concrete generated-body package. -/
theorem RecursorRuleRhsScope.impRegistrationRuleSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic) :
    List.Forall₂ (fun entry rule => ∃ semantic, TrExprS env universes [] rule.rhs semantic)
      (ctors.zipIdx initial) rules := by
  exact List.Forall₂.imp (fun entry rule receipt => head entry rule receipt) hscope

theorem mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults
    {ResultType : Type} {env : VEnv} {universes : List Name}
    {RuleResult : Array RecInfo → Context → Constructor → Expr → RecursorRule → Prop}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (resultHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RuleResult finalInfos finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            RuleResult finalInfos finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader next post envWF constants definitions fieldOnly model modelWF native
    reserved nativeEnvWF mapped parentSupport minorSupport domainSupport ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope
  have results : ∀ parent, parent < types.size → ∃ recursor,
      registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          finalInfos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          RuleResult finalInfos finalReader ctor minor rule := by
    intro parent hparent
    obtain ⟨recursor, hlookup, hentries⟩ := rhsScope parent hparent
    refine ⟨recursor, hlookup, ?_⟩
    intro index ctor hctor
    obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hentries index ctor hctor
    exact ⟨rule, minor, hrule, hminor,
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        hreceipt hreceipt.fvars.counts.receipt,
      resultHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        hreceipt hreceipt.fvars.counts.receipt⟩
  have completeRuleSemantics := rhsScope.completeRuleSemantics metadata.metadata.orderedRules
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics

/- Instantiate the registration CPS boundary with the named generated
   constructor-RHS package.  The closed callback and generated callback are
   paired at each indexed receipt; the continuation receives complete
   stored-rule semantic coverage derived from that same indexed package. -/
theorem mkRecInfos.registeredScopedGeneratedRuleResultCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  exact mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults
    (RuleResult := fun finalInfos finalReader ctor minor rule =>
      GeneratedRecursorRuleResult env universes stats
        (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
        finalReader ctor minor rule)
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
      registeredWF retained metadata rhsScope _results _completeRuleSemantics =>
      have completeRuleResults := rhsScope.completeRuleResultSemanticsIndexed
        metadata.metadata.orderedRules
        (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
          ⟨closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt,
            generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt⟩)
      have completeRuleSemantics := rhsScope.completeRuleSemanticsFromIndexed
        metadata.metadata.orderedRules
        (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
          ⟨closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt,
            generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt⟩)
      nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
        registeredWF retained metadata rhsScope completeRuleResults completeRuleSemantics)

/- Extend the generated-rule CPS boundary with the paired base/target iota
   endpoint.  The existing generated package remains available to the
   continuation; the additional indexed callback is obtained by projecting
   `GeneratedRecursorRuleIotaKind.baseAndTargetResults` from that same package. -/
theorem mkRecInfos.registeredScopedGeneratedRuleIotaCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic,
    hgenerated.iotaKind.baseAndTargetResults⟩

/- Keep the generated result and its paired base/target iota endpoint together
   in the registration CPS continuation.  The iota projection is derived from
   the exact generated witness supplied by the same indexed callback. -/
theorem mkRecInfos.registeredScopedGeneratedRuleIotaBaseAndTargetResultsCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic,
    hgenerated.iotaKind.baseAndTargetResults⟩

/- Keep the generated result and its paired base/target iota endpoint together
   in the registration CPS continuation.  The iota projection is derived from
   the exact generated witness supplied by the same indexed callback. -/
theorem mkRecInfos.registeredScopedGeneratedRuleResultAndIotaCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic, hgenerated,
    hgenerated.iotaKind.baseAndTargetResults⟩

theorem mkRecInfos.registeredScopedGeneratedRuleResultAndIotaBaseAndTargetResultsCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic, hgenerated,
    hgenerated.iotaKind.baseAndTargetResults⟩

theorem mkRecInfos.registeredScopedTranslatedAppliedInitialAndFinalTypehood
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
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
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine (mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader next post envWF constants definitions fieldOnly model modelWF native
    reserved nativeEnvWF mapped parentSupport minorSupport domainSupport ?_)
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope
  have initial : RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
      model lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.rawTypehood, receipt.storedTypehood,
      receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  have final : RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
      finalModel lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.finalRawTypehood, receipt.finalStoredTypehood,
      receipt.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint ⟨initial, final⟩
    registeredWF retained metadata rhsScope

end Lean4Lean.AddInductive
