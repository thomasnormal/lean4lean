import Lean4Lean.Verify.CanonicalBoolRecursorSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolRecursorSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)

example {stats : InductiveStats} {reader : Context}
    {trace : RecursorIndexTrace stats (.sort (.succ .zero)) 0 #[] reader
      (.sort (.succ .zero)) 0 #[] reader}
    (head : stats.indConsts[0]! = .const ``Bool [])
    (params : stats.params = #[]) :
    ParentModelTranslationSupport canonicalBoolModel [`u] stats 0 trace :=
  canonicalBoolStopParentSupport head params

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorTraceTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorTraceSupport trace params levels indConsts nindices boolIndices motives motiveSupport

example {stats : InductiveStats} {infos : Array RecInfo}
    {terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context} {model fieldModel : MLCtx}
    {semantic motiveSemantic : VExpr} {motive : FVarId}
    {level : VLevel}
    {fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint canonicalBoolModel [`u]
      fieldTrace model fieldModel semantic)
    (fieldsEq : fields = #[])
    (terminalEq : terminal = .const ``Bool [])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal := by
  exact canonicalBoolCtorFieldEndpointIHMotiveApplicationSupport endpoint fieldsEq terminalEq
    boolIndices motiveEq motiveTranslated motiveTyped

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool support has an admission: {name}"

run_meta
  for theoremName in [``canonicalBoolStopParentSupport,
      ``canonicalBoolMinorSourceSupport,
      ``canonicalBoolMinorTraceSupport,
      ``canonicalBoolCtorFieldEndpointIHMotiveApplicationSupport] do
    auditTheorem theoremName
  logInfo "canonical Bool parent stop and two-constructor minor support are theorem-backed"

end CanonicalBoolRecursorSupportTest
