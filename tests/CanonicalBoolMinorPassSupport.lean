import Lean4Lean.Verify.CanonicalBoolMinorPassSupport
import Lean.Util.CollectAxioms

namespace CanonicalBoolMinorPassSupportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorPassTrace stats
      #[{name := ``Bool, type := .sort (.succ .zero),
          ctors := [⟨``Bool.false, .const ``Bool []⟩,
            ⟨``Bool.true, .const ``Bool []⟩]}] 0 infos reader finalInfos finalReader)
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
    MinorPassTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorPassSupport trace params levels indConsts nindices boolIndices motives motiveSupport

example {stats : InductiveStats} {types : Array InductiveType}
    {infos finalInfos : Array RecInfo} {reader finalReader : Context}
    (typesEq : types = #[canonicalBoolType])
    (trace : RecursorMinorPassTrace stats types 0 infos reader finalInfos finalReader)
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
    MinorPassTranslationSupport canonicalBoolModel [`u] trace :=
  canonicalBoolMinorPassSupport_of_types typesEq trace params levels indConsts nindices boolIndices
    motives motiveSupport

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context} {model : MLCtx}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (infoBound : 0 < infos.size)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    ∃ finalModel, TranslatedRecursorMinorTrace canonicalBoolModel [`u] trace model finalModel :=
  canonicalBoolMinorTraceTranslatedOfMotive trace params levels indConsts nindices boolIndices
    modelWF native reserved infoBound motiveEq motiveTranslated motiveTyped

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ finalModel, TranslatedRecursorMinorTrace canonicalBoolModel [`u]
      minorTrace parentModel finalModel :=
  canonicalBoolMinorTraceTranslatedOfParentHistory parentTrace parentHistory minorTrace
    normalization params levels indConsts nindices boolIndices reserved

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats #[canonicalBoolType] 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ finalModel, TranslatedRecursorMinorPass canonicalBoolModel [`u]
      minorTrace parentModel finalModel :=
  canonicalBoolMinorPassTranslatedOfParentHistory parentTrace parentHistory minorTrace
    normalization params levels indConsts nindices boolIndices reserved

example {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    (constructorType : constructor.type = .const ``Bool [])
    (constructorName : constructor.name = ``Bool.false ∨ constructor.name = ``Bool.true)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (model : MLCtx) (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    {motive : FVarId} {motiveSemantic : VExpr} {level : VLevel}
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    MinorSourceTranslationSupport canonicalBoolModel [`u] source model :=
  canonicalBoolMinorSourceSupportOfMotive constructorType constructorName params levels
    indConsts nindices boolIndices source model modelWF native motiveEq motiveTranslated motiveTyped

example {stats : InductiveStats} {infos : Array RecInfo}
    {reader domainReader : Context} {domain : Expr} {initial final : MLCtx}
    {source : RecursorMinorDomainSource stats infos
      ({name := ``Bool.false, type := .const ``Bool []} : Constructor)
      reader domain domainReader}
    (step : MinorModelStep canonicalBoolModel [`u] ``Bool source initial final) :
    IndexMLCtxExtension initial [⟨domainReader.ngen.curr⟩] final :=
  canonicalBoolNullaryFalseStepAllocation step

example {stats : InductiveStats} {infos : Array RecInfo}
    {reader domainReader : Context} {domain : Expr} {initial final : MLCtx}
    {source : RecursorMinorDomainSource stats infos
      ({name := ``Bool.true, type := .const ``Bool []} : Constructor)
      reader domain domainReader}
    (step : MinorModelStep canonicalBoolModel [`u] ``Bool source initial final) :
    IndexMLCtxExtension initial [⟨domainReader.ngen.curr⟩] final :=
  canonicalBoolNullaryTrueStepAllocation step

example {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader parentReader finalReader : Context} {model parentModel : MLCtx}
    {elimLevel : Level}
    (parentTrace : RecursorParentPassTrace stats #[canonicalBoolType] elimLevel 0 #[] reader infos parentReader)
    (parentHistory : TranslatedRecursorParentPass canonicalBoolModel [`u]
      parentTrace model parentModel)
    (minorTrace : RecursorMinorPassTrace stats #[canonicalBoolType] 0 infos parentReader finalInfos finalReader)
    (normalization : ((monadLift (TypeChecker.whnf (.sort (.succ .zero))) : M Expr) reader) =
      .ok (.sort (.succ .zero)))
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (reserved : ContextReserved parentReader.lctx parentReader.ngen) :
    ∃ (major motive minorFalse minorTrue : FVarId),
      infos[0]!.major = .fvar major ∧ infos[0]!.motive = .fvar motive ∧
      finalInfos[0]!.minors =
        (infos[0]!.minors.push (.fvar minorFalse)).push (.fvar minorTrue) ∧
      ∃ finalModel, IndexMLCtxExtension model [major, motive, minorFalse, minorTrue] finalModel :=
  canonicalBoolMinorPassAllocationOfParentHistory parentTrace parentHistory minorTrace
    normalization params levels indConsts nindices boolIndices reserved

private def auditTheorem (name : Name) : MetaM Unit := do
  let information ← getConstInfo name
  if information matches .axiomInfo _ then
    throwError "canonical Bool minor pass support is primitive: {name}"
  let some proof := information.value? (allowOpaque := true) |
    throwError "canonical Bool minor pass support proof missing: {name}"
  if proof.hasSorry then
    throwError "canonical Bool minor pass support has an admission: {name}"

run_meta
  for theoremName in [``canonicalBoolMinorPassSupport,
      ``canonicalBoolMinorPassSupport_of_types,
      ``canonicalBoolMinorSourceSupportOfMotive,
      ``canonicalBoolMinorTraceTranslatedOfMotive,
      ``canonicalBoolMinorTraceTranslatedOfParentHistory,
      ``canonicalBoolMinorPassTranslatedOfParentHistory,
      ``canonicalBoolNullaryFalseStepAllocation,
      ``canonicalBoolNullaryTrueStepAllocation,
      ``canonicalBoolMinorTraceAllocationOfMotive,
      ``canonicalBoolMinorPassAllocationOfParentHistory] do
    auditTheorem theoremName
  logInfo "canonical Bool minor pass support is theorem-backed"

end CanonicalBoolMinorPassSupportTest
