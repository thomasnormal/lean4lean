import Lean4Lean.Verify.CanonicalBoolPassSupport
import Lean.Util.CollectAxioms

namespace InductiveRecursorEndpointSelectedDomainTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final)
    (alignment : ∀ ids, IndexMLCtxExtension initial ids final →
      (recursorTypeBinders stats infos 0).toList = ids.map Expr.fvar) :
    RecursorSelectedDomainSupport canonicalBoolModel [`u] stats infos 0 finalReader.lctx initial :=
  endpoint.selectedDomainSupport alignment

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {reader finalReader : Context} {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint canonicalBoolModel [`u] stats types elimLevel
      reader infos finalReader initial final) :
    ∃ parentModel parentIds minorIds,
      IndexMLCtxExtension initial parentIds parentModel ∧
      IndexMLCtxExtension parentModel minorIds final ∧
      IndexMLCtxExtension initial (parentIds ++ minorIds) final :=
  endpoint.passExtensions

example {stats : InductiveStats} {infos : Array RecInfo}
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (distinct : major ≠ motive) :
    (recursorTypeBinders stats infos 0).toList ≠
      [major, motive, minorFalse, minorTrue].map Expr.fvar :=
  canonicalBoolRecursorBinderOrderBoundary params infosEq motiveEq minorsEq indicesEq majorEq distinct

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "endpoint selected-domain support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "endpoint selected-domain support proof missing: {name}"
  if proof.hasSorry then
    throwError "endpoint selected-domain support has an admission: {name}"

run_meta
  auditTheorem ``RecursorInfoModelEndpoint.selectedDomainSupport
  auditTheorem ``RecursorInfoModelEndpoint.passExtensions
  auditTheorem ``canonicalBoolRecursorBinderOrderBoundary
  logInfo "endpoint selected-domain and allocation-order boundaries are theorem-backed"

end InductiveRecursorEndpointSelectedDomainTest
