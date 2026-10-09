import Lean4Lean.Verify.ExprBoundedRange
import Lean4Lean.Verify.InductiveHeaderClosureGuard
import Lean4Lean.Verify.InductiveBinderClosed

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

theorem checkType_closed_of_bvarRangeFits {value inferred : Expr} {predicate : FVarId → Prop}
    {context : Context} {state nextState : State}
    (within : value.FVarsIn predicate) (fits : BVarRangeFits value)
    (success : checkType value context state = .ok (inferred, nextState)) : value.Closed 0 := by
  have guard := checkType_hasLooseBVars_eq_false success
  simp only [Expr.hasLooseBVars, fits.rangeAccurate, decide_eq_false_iff_not, Nat.not_lt] at guard
  exact within.closed_of_looseBVarRange'_le guard

theorem checkType_run_closed_of_bvarRangeFits {value inferred : Expr} {predicate : FVarId → Prop}
    {env : Environment} {safety : DefinitionSafety} {lctx : LocalContext}
    {lparams : List Name} {fuel : FuelConfig}
    (within : value.FVarsIn predicate) (fits : BVarRangeFits value)
    (success : M.run env safety lctx lparams fuel (checkType value) = .ok inferred) :
    value.Closed 0 := by
  have guard := checkType_run_hasLooseBVars_eq_false success
  simp only [Expr.hasLooseBVars, fits.rangeAccurate, decide_eq_false_iff_not, Nat.not_lt] at guard
  exact within.closed_of_looseBVarRange'_le guard

end TypeChecker

namespace AddInductive

def HeaderSourceBVarRangeFits (types : Array InductiveType) : Prop :=
  ∀ parent, parent < types.size → BVarRangeFits types[parent]!.type

theorem CheckedHeaderSource.sourceClosed_of_bvarRangeFits {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (fits : BVarRangeFits types[parent]!.type) : types[parent]!.type.Closed 0 :=
  source.sourceClosed_of_rangeAccurate fits.rangeAccurate

theorem CheckedHeaderSource.normalizedClosed_of_bvarRangeFits {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    {wrapped normalized : Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (fits : BVarRangeFits types[parent]!.type)
    (hwrapped : WrappedSortTelescope types[parent]!.type wrapped)
    (hnormalized : NormalizedSortTelescope types[parent]!.type normalized) :
    normalized.Closed 0 :=
  source.normalizedClosed_of_wrapped (source.sourceClosed_of_bvarRangeFits fits) hwrapped hnormalized

theorem CheckedHeaderSources.sourceClosed_of_bvarRangeFits {nparams : Nat}
    {types : Array InductiveType} {original current : Context} {stats : InductiveStats}
    (headers : CheckedHeaderSources nparams types original stats current)
    (fits : HeaderSourceBVarRangeFits types) : HeaderSourceClosed types :=
  fun parent hparent => (headers.2 parent hparent).sourceClosed_of_bvarRangeFits (fits parent hparent)

theorem CheckedHeaderSupportSources.sourceClosed_of_bvarRangeFits {nparams : Nat}
    {types : Array InductiveType} {original current : Context} {stats : InductiveStats}
    (headers : CheckedHeaderSupportSources nparams types original stats current)
    (fits : HeaderSourceBVarRangeFits types) : HeaderSourceClosed types :=
  headers.toSources.sourceClosed_of_bvarRangeFits fits

theorem CheckedHeaderSupportSources.wrappedClosed_of_bvarRangeFits {nparams : Nat}
    {types : Array InductiveType} {original current : Context} {stats : InductiveStats}
    (headers : CheckedHeaderSupportSources nparams types original stats current)
    (htypes : WrappedHeaderTelescope types) (fits : HeaderSourceBVarRangeFits types) :
    NormalizedHeaderClosed types :=
  headers.wrappedClosed htypes (headers.sourceClosed_of_bvarRangeFits fits)

end AddInductive
end Lean4Lean
