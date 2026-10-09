import Lean4Lean.Verify.InductiveIndexTraceTranslationFacts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def ParentRecursorIndexTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (parent : Nat) (info : RecInfo) (current : Context) : Prop :=
  ∀ entry normalized terminal finalIndex indexReader,
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
    ∃ virtual semantic,
      TrLCtx env universes entry.lctx virtual ∧
      TrExprS env universes virtual normalized semantic ∧
      IndexTraceAnnotationSupport env universes trace ∧
      IndexTraceNormalizationSupport env universes trace

def RecursorIndexSourcesTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  ∀ parent, parent < types.size →
    ParentRecursorIndexTranslationSupport env universes stats types elimLevel
      original parent infos[parent]! current

inductive TranslatedRecursorInfoIndexSource (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (original : Context) (info : RecInfo) (current : Context) : Prop where
  | mk {entry indexReader : Context} {normalized terminal : Expr} {finalIndex : Nat}
      {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
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
      (history : TranslatedRecursorIndexTrace env universes trace virtual semantic
        finalVirtual finalSemantic) :
      TranslatedRecursorInfoIndexSource env universes stats types elimLevel
        parent original info current

def TranslatedRecursorInfoIndexSources (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original infos[parent]! current

theorem RecursorInfoIndexSource.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : ParentRecursorIndexTranslationSupport env universes stats types elimLevel
      original parent info current) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexReader,
    entryFrame, initialNormalization, trace, major, motive, currentFrame⟩ := source
  obtain ⟨virtual, semantic, correspondence, translated, annotations, normalizations⟩ :=
    support entry normalized terminal finalIndex indexReader
      entryFrame initialNormalization trace major motive currentFrame
  obtain ⟨finalVirtual, finalSemantic, history⟩ := trace.translated envWF constants definitions
    (by omega) correspondence entryFrame.reserved translated annotations normalizations
  exact .mk entryFrame initialNormalization trace major motive currentFrame
    correspondence translated history

theorem RecursorInfoIndexSources.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : RecursorInfoIndexSources stats types elimLevel original infos current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : RecursorIndexSourcesTranslationSupport env universes stats types elimLevel
      original infos current) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current := by
  refine ⟨sources.1, ?_⟩
  intro parent bound
  exact (sources.2 parent bound).translated envWF constants definitions indexOnly
    (support parent bound)

theorem TranslatedRecursorInfoIndexSource.toSource {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    RecursorInfoIndexSource stats types elimLevel parent original info current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame _ _ _ =>
    exact ⟨_, _, _, _, _, entryFrame, initialNormalization, trace, major, motive, currentFrame⟩

theorem TranslatedRecursorInfoIndexSources.toSources {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel
      original infos current) : RecursorInfoIndexSources stats types elimLevel original infos current :=
  ⟨sources.1, fun parent bound => (sources.2 parent bound).toSource⟩

theorem TranslatedRecursorInfoIndexSource.mono {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current next : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current)
    (frame : current.RecursorScopeFrame next) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info next := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history =>
    exact .mk entryFrame initialNormalization trace major motive (currentFrame.trans frame)
      correspondence translated history

theorem TranslatedRecursorInfoIndexSource.withMinors {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) (minors : Array Expr) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original { info with minors } current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history =>
    exact .mk entryFrame initialNormalization trace major motive currentFrame
      correspondence translated history

theorem TranslatedRecursorInfoIndexSources.mono {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current next : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel
      original infos current) (frame : current.RecursorScopeFrame next) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos next :=
  ⟨sources.1, fun parent bound => (sources.2 parent bound).mono frame⟩

theorem TranslatedRecursorInfoIndexSources.modifyMinors {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel
      original infos current) (parent : Nat) (minor : Expr) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original
      (infos.modify parent fun info => { info with minors := info.minors.push minor }) current := by
  refine ⟨by simpa only [Array.size_modify] using sources.1, ?_⟩
  intro index bound
  have infoBound : index < infos.size := by rw [sources.1]; exact bound
  have modifiedBound : index <
      (infos.modify parent fun info => { info with minors := info.minors.push minor }).size := by
    simpa only [Array.size_modify] using infoBound
  by_cases sameParent : index = parent
  · subst index
    simpa only [getElem!_pos, infoBound, modifiedBound, Array.getElem_modify, ↓reduceIte] using
      (sources.2 parent bound).withMinors (infos[parent]!.minors.push minor)
  · simpa only [getElem!_pos, infoBound, modifiedBound, Array.getElem_modify,
      if_neg (Ne.symm sameParent)] using sources.2 index bound

end Lean4Lean.AddInductive
