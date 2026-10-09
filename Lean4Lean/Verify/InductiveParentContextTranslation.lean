import Lean4Lean.Verify.InductiveMotiveContextTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

def recursorMotiveMLCtx (stats : InductiveStats) (parent : Nat) (indices : Array Expr)
    (reader : Context) (elimLevel : Level) (name : Name) (semantic : VExpr)
    (model : MLCtx) : MLCtx :=
  let majorReader := recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)
  .vlam ⟨majorReader.ngen.curr⟩ name
    (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩) majorReader)
    semantic .default model

theorem RecursorMotiveOpening.mixedContext
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {peeled semantic : VExpr} {level : VLevel} {elimLevel : Level} {name : Name}
    (opening : RecursorMotiveOpening env universes stats parent indices reader virtual peeled
      elimLevel name semantic level)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx =
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx)
    (converted : model.vlctx = recursorMajorVirtualContext stats parent indices reader virtual peeled) :
    (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).WF env universes ∧
      (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).lctx =
        (recursorMotiveContext stats parent indices reader elimLevel name).lctx ∧
      (recursorMotiveMLCtx stats parent indices reader elimLevel name semantic model).vlctx =
        recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic := by
  have fresh := (opening.2.1.wf.2.1 _ _ rfl).1
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨modelWF, ?_, ?_, level, ?_⟩
    · exact modelWF.tr.find?_eq_none.2 (converted.symm ▸ fresh)
    · exact converted.symm ▸ opening.1.1
    · exact converted.symm ▸ opening.1.2
  · simp only [recursorMotiveMLCtx, MLCtx.lctx, recursorMotiveContext, recursorIndexContext, native]
  · simp only [recursorMotiveMLCtx, MLCtx.vlctx, recursorMotiveVirtualContext, converted]

def RecursorParentModelStep (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (parent : Nat)
    (indices : Array Expr) (indexReader : Context) (indexVirtual : VLCtx)
    (initial final : MLCtx) (ids : List FVarId) : Prop :=
  ∃ rawSemantic peeled majorLevel motiveSemantic motiveLevel,
    RecursorMajorOpening env universes stats parent indices indexReader indexVirtual
      rawSemantic peeled majorLevel ∧
    RecursorMotiveOpening env universes stats parent indices indexReader indexVirtual peeled
      elimLevel (recursorMotiveName types parent) motiveSemantic motiveLevel ∧
    final.WF env universes ∧
    final.lctx =
      (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)).lctx ∧
    final.vlctx = recursorMotiveVirtualContext stats parent indices indexReader indexVirtual
      peeled elimLevel motiveSemantic ∧
    IndexMLCtxExtension initial ids final ∧
    ids.map Expr.fvar = indices.toList ++
      [.fvar ⟨indexReader.ngen.curr⟩,
        .fvar ⟨(recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats parent indices)).ngen.curr⟩]

theorem RecursorParentModelStep.model
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) :
    final.WF env universes ∧ final.lctx =
      (recursorMotiveContext stats parent indices indexReader elimLevel (recursorMotiveName types parent)).lctx := by
  obtain ⟨_, _, _, _, _, _, _, modelWF, native, _⟩ := step
  exact ⟨modelWF, native⟩

theorem RecursorParentModelStep.extension
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {indices : Array Expr} {indexReader : Context} {indexVirtual : VLCtx}
    {initial final : MLCtx} {ids : List FVarId}
    (step : RecursorParentModelStep env universes stats types elimLevel parent indices indexReader
      indexVirtual initial final ids) : IndexMLCtxExtension initial ids final := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, extension, _⟩ := step
  exact extension

theorem RecursorMajorOpening.parentModelStep
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {indices : Array Expr}
    {indexReader : Context} {indexVirtual : VLCtx} {rawSemantic peeled : VExpr} {majorLevel : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices indexReader indexVirtual
      rawSemantic peeled majorLevel)
    {initial indexModel : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids indexModel)
    (modelWF : indexModel.WF env universes)
    (native : indexModel.lctx = indexReader.lctx) (converted : indexModel.vlctx = indexVirtual)
    (reserved : ContextReserved indexReader.lctx indexReader.ngen)
    (selected : indices.toList = ids.map Expr.fvar) (envWF : env.WF)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ finalModel allocated,
      RecursorParentModelStep env universes stats types elimLevel parent indices indexReader indexVirtual
        initial finalModel allocated := by
  obtain ⟨majorWF, majorNative, majorConverted⟩ :=
    opening.mixedContext indexModel modelWF native converted reserved
  have majorExtension := extension.push ⟨indexReader.ngen.curr⟩ `t
    (recursorMajorDomain stats parent indices) peeled .default
  obtain ⟨motiveSemantic, motiveLevel, translated, typed⟩ :=
    majorExtension.typedAbstraction envWF majorWF mapped
  have binding := opening.motiveBindingEquation extension modelWF native converted reserved selected elimLevel
  have motiveDomain : RecursorMotiveDomainTranslation env universes stats parent indices indexReader
      indexVirtual peeled elimLevel motiveSemantic motiveLevel := by
    dsimp only [recursorMajorMLCtx] at majorConverted binding
    refine ⟨?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton, majorConverted, ← binding] using translated
    · simpa only [majorConverted] using typed
  have motiveOpening := motiveDomain.opening opening (recursorMotiveName types parent)
  obtain ⟨finalWF, finalNative, finalConverted⟩ := motiveOpening.mixedContext
    (recursorMajorMLCtx stats parent indices indexReader indexModel peeled)
    majorWF majorNative majorConverted
  have finalExtension := majorExtension.push
    ⟨(recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices)).ngen.curr⟩
    (recursorMotiveName types parent)
    (recursorMotiveDomain elimLevel indices (.fvar ⟨indexReader.ngen.curr⟩)
      (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent indices)))
    motiveSemantic .default
  refine ⟨_, _, rawSemantic, peeled, majorLevel, motiveSemantic, motiveLevel, opening, motiveOpening,
    finalWF, finalNative, finalConverted, finalExtension, ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, ← selected,
    List.append_assoc, List.singleton_append]

theorem TranslatedRecursorIndexTrace.parentModelStep
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader indexReader : Context} {virtual indexVirtual : VLCtx}
    {semantic finalSemantic headSemantic : VExpr} {majorLevel : VLevel}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic indexVirtual finalSemantic)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
    (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
    (finalSort : finalSemantic = .sort majorLevel)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) majorLevel)
    {elimLevel : Level} {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    ∃ finalModel allocated,
      RecursorParentModelStep env universes stats types elimLevel parent indices indexReader indexVirtual
        model finalModel allocated := by
  obtain ⟨rawSemantic, peeled, opening⟩ := history.majorOpening envWF constants definitions indexOnly
    reserved headTranslated headTyped finalSort uniform
  obtain ⟨indexModel, ids, indexWF, indexNative, indexConverted, extension, arrays⟩ :=
    history.mixedContext model modelWF native converted reserved
  exact opening.parentModelStep extension indexWF indexNative indexConverted
    (history.scope reserved).reserved
    (by simpa only [Array.toList_empty, List.nil_append] using arrays) envWF mapped

end Lean4Lean.AddInductive
