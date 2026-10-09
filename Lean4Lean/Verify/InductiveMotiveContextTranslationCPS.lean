import Lean4Lean.Verify.InductiveMajorContextTranslationCPS
import Lean4Lean.Verify.InductiveMotiveContextTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def recursorMotiveContext (stats : InductiveStats) (parent : Nat) (indices : Array Expr)
    (reader : Context) (elimLevel : Level) (name : Name) : Context :=
  let majorReader := recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)
  recursorIndexContext majorReader name .default
    (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩) majorReader)

def recursorMotiveVirtualContext (stats : InductiveStats) (parent : Nat) (indices : Array Expr)
    (reader : Context) (virtual : VLCtx) (peeled : VExpr) (elimLevel : Level)
    (semantic : VExpr) : VLCtx :=
  let majorReader := recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)
  (some (⟨majorReader.ngen.curr⟩,
      (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩) majorReader).fvarsList),
    .vlam semantic) :: recursorMajorVirtualContext stats parent indices reader virtual peeled

def RecursorMotiveOpening (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (parent : Nat) (indices : Array Expr) (reader : Context)
    (virtual : VLCtx) (peeled : VExpr) (elimLevel : Level) (name : Name)
    (semantic : VExpr) (level : VLevel) : Prop :=
  RecursorMotiveDomainTranslation env universes stats parent indices reader virtual peeled
      elimLevel semantic level ∧
  TrLCtx env universes (recursorMotiveContext stats parent indices reader elimLevel name).lctx
    (recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic) ∧
  BinderPositionedAt (recursorMotiveContext stats parent indices reader elimLevel name)
    (.fvar ⟨(recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).ngen.curr⟩)
    name (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)))
    .default (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx.decls.size ∧
  (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).RecursorScopeFrame
    (recursorMotiveContext stats parent indices reader elimLevel name)

theorem RecursorMotiveDomainTranslation.opening
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled semantic : VExpr} {majorLevel level : VLevel}
    {elimLevel : Level}
    (translated : RecursorMotiveDomainTranslation env universes stats parent indices reader virtual peeled
      elimLevel semantic level)
    (major : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled majorLevel)
    (name : Name) :
    RecursorMotiveOpening env universes stats parent indices reader virtual peeled elimLevel name semantic level := by
  obtain ⟨_, _, _, _, _, correspondence, _, frame⟩ := major
  refine ⟨translated, ?_, ?_, ?_⟩
  · exact translatedIndexContextPush (name := name) (bi := .default)
      correspondence frame.reserved translated.1 translated.2
  · exact newlyAllocatedBinderPositioned _ name _ .default correspondence.1 frame.reserved
  · exact Context.RecursorScopeFrame.push _ correspondence.1 frame.reserved name .default _

def ParentRecursorMotiveModelSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (parent : Nat) (info : RecInfo) (current : Context) : Prop :=
  ∀ entry normalized terminal finalIndex indexReader virtual semantic finalVirtual finalSemantic
      headSemantic rawSemantic peeled level,
    original.RecursorScopeFrame entry →
    ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized →
    ∀ trace : RecursorIndexTrace stats normalized 0 #[] entry
      terminal finalIndex info.indices indexReader,
    info.major = .fvar ⟨indexReader.ngen.curr⟩ →
    info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
      (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ →
    (recursorIndexContext
      (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices))
      (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel info.indices info.major
        (recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats parent info.indices)))).RecursorScopeFrame current →
    TrLCtx env universes entry.lctx virtual →
    TrExprS env universes virtual normalized semantic →
    TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic →
    TrExprS env universes virtual stats.indConsts[parent]! headSemantic →
    env.HasType universes.length virtual.toCtx headSemantic semantic →
    finalSemantic = .sort level →
    RecursorMajorOpening env universes stats parent info.indices indexReader
      finalVirtual rawSemantic peeled level →
    ∃ base : TypeChecker.MLCtx,
      base.WF env universes ∧ base.lctx = entry.lctx ∧ base.vlctx = virtual

def RecursorMotiveModelsSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  ∀ parent, parent < types.size →
    ParentRecursorMotiveModelSupport env universes stats types elimLevel
      original parent infos[parent]! current

inductive TranslatedRecursorInfoMotiveSource (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (original : Context) (info : RecInfo) (current : Context) : Prop where
  | mk {entry indexReader : Context} {normalized terminal : Expr} {finalIndex : Nat}
      {virtual finalVirtual : VLCtx} {semantic finalSemantic headSemantic rawSemantic peeled motiveSemantic : VExpr}
      {level motiveLevel : VLevel}
      (entryFrame : original.RecursorScopeFrame entry)
      (initialNormalization :
        ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized)
      (trace : RecursorIndexTrace stats normalized 0 #[] entry
        terminal finalIndex info.indices indexReader)
      (major : info.major = .fvar ⟨indexReader.ngen.curr⟩)
      (motive : info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩)
      (currentFrame : (recursorIndexContext
        (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent info.indices))
        (recursorMotiveName types parent) .default
        (recursorMotiveDomain elimLevel info.indices info.major
          (recursorIndexContext indexReader `t .default
            (recursorMajorDomain stats parent info.indices)))).RecursorScopeFrame current)
      (initialCorrespondence : TrLCtx env universes entry.lctx virtual)
      (initialTranslation : TrExprS env universes virtual normalized semantic)
      (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
      (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
      (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
      (finalSort : finalSemantic = .sort level)
      (majorOpening : RecursorMajorOpening env universes stats parent info.indices indexReader
        finalVirtual rawSemantic peeled level)
      (motiveOpening : RecursorMotiveOpening env universes stats parent info.indices indexReader
        finalVirtual peeled elimLevel (recursorMotiveName types parent) motiveSemantic motiveLevel) :
      TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current

theorem TranslatedRecursorInfoMotiveSource.toMajorSource
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMotiveSource env universes stats types elimLevel
      parent original info current) :
    TranslatedRecursorInfoMajorSource env universes stats types elimLevel parent original info current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history
      headTranslated headTyped finalSort majorOpening _ =>
    exact .mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history
      headTranslated headTyped finalSort majorOpening

theorem TranslatedRecursorInfoMajorSource.motiveTranslated
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {semanticElimLevel : VLevel} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel
      parent original info current)
    (envWF : env.WF) (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : ParentRecursorMotiveModelSupport env universes stats types elimLevel
      original parent info current) :
    TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history
      headTranslated headTyped finalSort majorOpening =>
    obtain ⟨base, baseWF, native, converted⟩ := support _ _ _ _ _ _ _ _ _ _ _ _ _
      entryFrame initialNormalization trace major motive currentFrame correspondence translated history
      headTranslated headTyped finalSort majorOpening
    obtain ⟨motiveSemantic, motiveLevel, domain⟩ := history.motiveDomainTranslation majorOpening
      envWF base baseWF native converted entryFrame.reserved mapped
    exact .mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history
      headTranslated headTyped finalSort majorOpening (domain.opening majorOpening _)

def TranslatedRecursorInfoMotiveSources (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original infos[parent]! current

theorem TranslatedRecursorInfoMajorSources.motiveTranslated
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {semanticElimLevel : VLevel}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoMajorSources env universes stats types elimLevel original infos current)
    (envWF : env.WF) (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorMotiveModelsSupport env universes stats types elimLevel original infos current) :
    TranslatedRecursorInfoMotiveSources env universes stats types elimLevel original infos current :=
  ⟨sources.1, fun parent bound => (sources.2 parent bound).motiveTranslated envWF mapped (support parent bound)⟩

theorem TranslatedRecursorInfoMotiveSources.toMajorSources
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoMotiveSources env universes stats types elimLevel original infos current) :
    TranslatedRecursorInfoMajorSources env universes stats types elimLevel original infos current :=
  ⟨sources.1, fun parent bound => (sources.2 parent bound).toMajorSource⟩

theorem TranslatedRecursorInfoMotiveSource.motiveReaderReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMotiveSource env universes stats types elimLevel parent original info current) :
    ∃ indexReader virtual peeled semantic level,
      info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ ∧
      RecursorMotiveOpening env universes stats parent info.indices indexReader virtual peeled
        elimLevel (recursorMotiveName types parent) semantic level := by
  cases source with
  | mk _ _ _ major motive _ _ _ _ _ _ _ _ opening =>
    exact ⟨_, _, _, _, _, major, motive, opening⟩

theorem withLocalDecl.motiveTranslation {ResultType : Type}
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {peeled semantic : VExpr} {level : VLevel} {elimLevel : Level} {name : Name}
    (opening : RecursorMotiveOpening env universes stats parent indices reader virtual peeled
      elimLevel name semantic level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : TrLCtx env universes (recursorMotiveContext stats parent indices reader elimLevel name).lctx
      (recursorMotiveVirtualContext stats parent indices reader virtual peeled elimLevel semantic) →
      (next (.fvar ⟨(recursorIndexContext reader `t .default
          (recursorMajorDomain stats parent indices)).ngen.curr⟩)
        (recursorMotiveContext stats parent indices reader elimLevel name)).WF post) :
    (withLocalDecl name .default
      (recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)))
      next (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))).WF post :=
  nextWF opening.2.1

theorem mkRecInfos.getTranslatedMotiveSources {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader result.1 result.2) :
    (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      TranslatedRecursorInfoMotiveSources env universes stats types elimLevel reader result.1 result.2 := by
  intro result success
  obtain ⟨frame, counts, sources⟩ := mkRecInfos.getTranslatedMajorSources stats types elimLevel reader
    envWF constants definitions indexOnly readerWF reserved
    (fun captured actual => ⟨(support captured actual).1, (support captured actual).2.1⟩) result success
  exact ⟨frame, counts, sources.motiveTranslated envWF mapped (support result success).2.2⟩

theorem mkRecInfos.scopedTranslatedMotiveSources {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : (mkRecInfos stats types elimLevel
      (fun infos => do return (infos, ← readThe Context)) reader).WF fun result =>
      RecursorIndexSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMajorSourcesTranslationSupport env universes stats types elimLevel reader result.1 result.2 ∧
      RecursorMotiveModelsSupport env universes stats types elimLevel reader result.1 result.2)
    (nextWF : ∀ infos current, reader.RecursorScopeFrame current →
      TranslatedRecursorInfoMotiveSources env universes stats types elimLevel reader infos current →
      (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun infos => do return (infos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedMotiveSources stats types elimLevel reader
    envWF constants definitions indexOnly readerWF reserved mapped support).bind ?_
  rintro ⟨infos, current⟩ ⟨frame, _, sources⟩
  exact nextWF infos current frame sources

end Lean4Lean.AddInductive
