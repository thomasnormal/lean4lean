import Lean4Lean.Verify.InductiveWrappedSpines

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def WrappedHeaderTelescope (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → ∃ normalized, WrappedSortTelescope types[parent]!.type normalized

theorem WrappedHeaderTelescope.normalizedHeaders {types : Array InductiveType}
    (htypes : WrappedHeaderTelescope types) : NormalizedHeaderTelescope types := by
  intro parent hparent
  obtain ⟨normalized, hwrapped⟩ := htypes parent hparent
  exact ⟨normalized, hwrapped.normalized⟩

theorem CheckedHeaderSources.wrappedTelescopeIndexCounts {nparams : Nat} {types : Array InductiveType}
    {stats : InductiveStats} {original checkedRoot recursorRoot current : Context} {elimLevel : Level}
    {infos : Array RecInfo} (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : WrappedHeaderTelescope types) : RecursorIndexCounts stats types infos :=
  headers.normalizedTelescopeIndexCounts sources htypes.normalizedHeaders

theorem mkRecInfos.registeredWrappedAlignedIndices (nparams : Nat) (stats : InductiveStats)
    (types : Array InductiveType) (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.2.1 result.2.2 ∧
      result.1.constants.WF ∧ (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧ LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      RecursorIndexCounts stats types result.2.1 :=
  mkRecInfos.registeredNormalizedAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes.normalizedHeaders hwf hreserved henv

theorem checkInductiveTypes.safeRegisteredWrappedIndexCounts (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (elimLevel : Level) (lparams : List Name) (isK : Bool) (ctx : Context)
    (htypes : WrappedHeaderTelescope types) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result => RecursorIndexCounts result.1 types result.2.2.1 :=
  checkInductiveTypes.safeRegisteredNormalizedIndexCounts nparams types numNested elimLevel lparams
    isK ctx htypes.normalizedHeaders hwf hreserved

end Lean4Lean.AddInductive
