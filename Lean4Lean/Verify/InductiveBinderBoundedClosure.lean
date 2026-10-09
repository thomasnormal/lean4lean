import Lean4Lean.Verify.InductiveBoundedHeaderClosure
import Lean4Lean.Verify.InductiveBinderClosure

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem CheckedHeaderSupportSources.wrappedBinderClosure_of_bvarRangeFits
    {nparams : Nat} {types : Array InductiveType} {stats : InductiveStats}
    {original checkedRoot recursorRoot current : Context} {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types)
    (support : BinderValuesBefore recursorRoot recursorRoot.lctx.decls.size stats.params.toList)
    (hwf : recursorRoot.lctx.WF) (fits : HeaderSourceBVarRangeFits types) :
    RecursorBinderClosure stats types checkedRoot current infos :=
  headers.wrappedBinderClosure sources htypes support hwf (headers.sourceClosed_of_bvarRangeFits fits)

theorem mkRecInfos.scopedWrappedBinderClosure_of_bvarRangeFits
    (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current →
      RecursorIndexCounts stats types infos → RecursorBinderClosure stats types checkedRoot current infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedWrappedBinderClosure nparams stats types elimLevel next original checkedRoot ctx post
    headers htypes hwf hreserved support (headers.sourceClosed_of_bvarRangeFits fits) hnext

theorem mkRecInfos.getWrappedBinderClosure_of_bvarRangeFits
    (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧
      RecursorIndexCounts stats types result.1 ∧ RecursorBinderClosure stats types checkedRoot result.2 result.1 :=
  mkRecInfos.getWrappedBinderClosure nparams stats types elimLevel original checkedRoot ctx
    headers htypes hwf hreserved support (headers.sourceClosed_of_bvarRangeFits fits)

theorem mkRecInfos.registeredWrappedBinderClosure_of_bvarRangeFits
    (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSupportSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF)
    (support : BinderValuesBefore ctx ctx.lctx.decls.size stats.params.toList)
    (fits : HeaderSourceBVarRangeFits types) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 ∧ RecursorBinderClosure stats types checkedRoot result.2.2 result.2.1 :=
  mkRecInfos.registeredWrappedBinderClosure nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes hwf hreserved henv support (headers.sourceClosed_of_bvarRangeFits fits)

theorem checkInductiveTypes.safeRegisteredWrappedBinderClosure_of_bvarRangeFits
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (fits : HeaderSourceBVarRangeFits types) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 types result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources nparams types ctx result.1 checkedRoot ∧
        RecursorBinderClosure result.1 types checkedRoot result.2.2.2 result.2.2.1 :=
  checkInductiveTypes.safeRegisteredBinderClosure nparams types numNested elimLevel lparams isK ctx
    htypes.normalizedHeaders hwf hreserved (fun _ _ headers => headers.wrappedFVarsIn htypes)
    (fun _ _ headers => headers.wrappedClosed_of_bvarRangeFits htypes fits)

end Lean4Lean.AddInductive
