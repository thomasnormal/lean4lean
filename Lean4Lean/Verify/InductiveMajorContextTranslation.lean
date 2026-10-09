import Lean4Lean.Verify.InductiveIndexApplicationTranslation
import Lean4Lean.Verify.InductiveRecursorIndexTranslationFacts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def recursorMajorVirtualContext (stats : InductiveStats) (parent : Nat)
    (indices : Array Expr) (reader : Context) (virtual : VLCtx) (semantic : VExpr) : VLCtx :=
  (some (⟨reader.ngen.curr⟩, (recursorMajorDomain stats parent indices).fvarsList),
    .vlam semantic) :: virtual

def RecursorMajorOpening (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (parent : Nat) (indices : Array Expr) (reader : Context) (virtual : VLCtx)
    (rawSemantic peeled : VExpr) (level : VLevel) : Prop :=
  TrExprS env universes virtual
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) rawSemantic ∧
  env.HasType universes.length virtual.toCtx rawSemantic (.sort level) ∧
  TrExprS env universes virtual (recursorMajorDomain stats parent indices) peeled ∧
  env.IsDefEq universes.length virtual.toCtx rawSemantic peeled (.sort level) ∧
  env.HasType universes.length virtual.toCtx peeled (.sort level) ∧
  TrLCtx env universes
    (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx
    (recursorMajorVirtualContext stats parent indices reader virtual peeled) ∧
  BinderPositionedAt
    (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))
    (.fvar ⟨reader.ngen.curr⟩) `t (recursorMajorDomain stats parent indices) .default
    reader.lctx.decls.size ∧
  reader.RecursorScopeFrame
    (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices))

theorem TranslatedRecursorIndexTrace.majorOpening
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {source terminal : Expr} {finalIndex : Nat} {indices : Array Expr}
    {reader indexReader : Context} {virtual finalVirtual : VLCtx}
    {semantic finalSemantic headSemantic : VExpr} {level : VLevel}
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
    (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
    (finalSort : finalSemantic = .sort level)
    (uniform : UniformAnnotationUniverse universes
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) level) :
    ∃ rawSemantic peeled,
      RecursorMajorOpening env universes stats parent indices indexReader finalVirtual
        rawSemantic peeled level := by
  have initialApplication : TrExprS env universes virtual
      (mkAppN stats.indConsts[parent]! #[]) headSemantic := by
    simpa only [mkAppN, Array.foldl_empty] using headTranslated
  obtain ⟨rawSemantic, rawTranslated, rawTyped⟩ :=
    history.application envWF initialApplication headTyped
  have parametersEmpty := Array.eq_empty_of_size_eq_zero indexOnly
  have fullTranslated : TrExprS env universes finalVirtual
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) rawSemantic := by
    simpa only [parametersEmpty, mkAppN, Array.foldl_empty] using rawTranslated
  have fullTyped : env.HasType universes.length finalVirtual.toCtx rawSemantic (.sort level) :=
    finalSort ▸ rawTyped
  have correspondence := history.finalTranslation.1
  have finalReserved := (history.scope reserved).reserved
  have spine := TypedAnnotationSpine.ofTrExprS envWF correspondence.wf.toCtx
    constants uniform fullTranslated fullTyped
  obtain ⟨peeled, peeledTranslated, converted⟩ :=
    spine.peelTypeAnnotations definitions envWF.ordered
  have pushed := translatedIndexContextPush (name := `t) (bi := .default)
    correspondence finalReserved peeledTranslated converted.hasType.2
  refine ⟨rawSemantic, peeled, fullTranslated, fullTyped, peeledTranslated, converted,
    converted.hasType.2, ?_, ?_, ?_⟩
  · exact pushed
  · exact newlyAllocatedBinderPositioned indexReader `t _ .default correspondence.1 finalReserved
  · exact Context.RecursorScopeFrame.push indexReader correspondence.1 finalReserved `t .default
      (recursorMajorDomain stats parent indices)

def ParentRecursorMajorTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (parent : Nat) (info : RecInfo) (current : Context) : Prop :=
  ∀ entry normalized terminal finalIndex indexReader virtual semantic finalVirtual finalSemantic,
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
    ∃ headSemantic level,
      TrExprS env universes virtual stats.indConsts[parent]! headSemantic ∧
      env.HasType universes.length virtual.toCtx headSemantic semantic ∧
      finalSemantic = .sort level ∧
      UniformAnnotationUniverse universes
        (mkAppN (mkAppN stats.indConsts[parent]! stats.params) info.indices) level

inductive TranslatedRecursorInfoMajorSource (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (parent : Nat) (original : Context) (info : RecInfo) (current : Context) : Prop where
  | mk {entry indexReader : Context} {normalized terminal : Expr} {finalIndex : Nat}
      {virtual finalVirtual : VLCtx} {semantic finalSemantic headSemantic rawSemantic peeled : VExpr}
      {level : VLevel}
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
        finalVirtual finalSemantic)
      (headTranslated : TrExprS env universes virtual stats.indConsts[parent]! headSemantic)
      (headTyped : env.HasType universes.length virtual.toCtx headSemantic semantic)
      (finalSort : finalSemantic = .sort level)
      (opening : RecursorMajorOpening env universes stats parent info.indices indexReader
        finalVirtual rawSemantic peeled level) :
      TranslatedRecursorInfoMajorSource env universes stats types elimLevel
        parent original info current

theorem TranslatedRecursorInfoIndexSource.majorTranslated
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : ParentRecursorMajorTranslationSupport env universes stats types elimLevel
      original parent info current) :
    TranslatedRecursorInfoMajorSource env universes stats types elimLevel
      parent original info current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history =>
    obtain ⟨headSemantic, level, headTranslated, headTyped, finalSort, uniform⟩ :=
      support _ _ _ _ _ _ _ _ _ entryFrame initialNormalization trace major motive currentFrame
        correspondence translated history
    obtain ⟨rawSemantic, peeled, opening⟩ := history.majorOpening envWF constants definitions
      indexOnly entryFrame.reserved headTranslated headTyped finalSort uniform
    exact .mk entryFrame initialNormalization trace major motive currentFrame correspondence
      translated history headTranslated headTyped finalSort opening

theorem TranslatedRecursorInfoMajorSource.toIndexSource
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel
      parent original info current) :
    TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current := by
  cases source with
  | mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history _ _ _ _ =>
    exact .mk entryFrame initialNormalization trace major motive currentFrame correspondence translated history

def RecursorMajorSourcesTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  ∀ parent, parent < types.size →
    ParentRecursorMajorTranslationSupport env universes stats types elimLevel
      original parent infos[parent]! current

def TranslatedRecursorInfoMajorSources (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original : Context) (infos : Array RecInfo) (current : Context) : Prop :=
  infos.size = types.size ∧ ∀ parent, parent < types.size →
    TranslatedRecursorInfoMajorSource env universes stats types elimLevel
      parent original infos[parent]! current

theorem TranslatedRecursorInfoIndexSources.majorTranslated
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel
      original infos current)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size = 0)
    (support : RecursorMajorSourcesTranslationSupport env universes stats types elimLevel
      original infos current) :
    TranslatedRecursorInfoMajorSources env universes stats types elimLevel original infos current :=
  ⟨sources.1, fun parent bound =>
    (sources.2 parent bound).majorTranslated envWF constants definitions indexOnly (support parent bound)⟩

theorem TranslatedRecursorInfoMajorSources.toIndexSources
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoMajorSources env universes stats types elimLevel
      original infos current) :
    TranslatedRecursorInfoIndexSources env universes stats types elimLevel original infos current :=
  ⟨sources.1, fun parent bound => (sources.2 parent bound).toIndexSource⟩

theorem TranslatedRecursorInfoMajorSource.majorReaderReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoMajorSource env universes stats types elimLevel
      parent original info current) :
    ∃ indexReader finalVirtual rawSemantic peeled level,
      info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      TrLCtx env universes indexReader.lctx finalVirtual ∧
      RecursorMajorOpening env universes stats parent info.indices indexReader
        finalVirtual rawSemantic peeled level := by
  cases source with
  | mk _ _ _ major _ _ _ _ history _ _ _ opening =>
    exact ⟨_, _, _, _, _, major, history.finalTranslation.1, opening⟩

end Lean4Lean.AddInductive
