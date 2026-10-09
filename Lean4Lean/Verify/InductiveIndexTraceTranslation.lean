import Lean4Lean.Verify.InductiveIndexOpeningTranslation
import Lean4Lean.Verify.RecursorInfoIndices

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def IndexAnnotationSupport (env : VEnv) (universes : List Name) (reader : Context)
    (domain : Expr) : Prop :=
  ∀ virtual semanticDomain,
    TrLCtx env universes reader.lctx virtual →
    TrExprS env universes virtual domain semanticDomain →
    env.IsType universes.length virtual.toCtx semanticDomain →
    ∃ level, env.HasType universes.length virtual.toCtx semanticDomain (.sort level) ∧
      UniformAnnotationUniverse universes domain level

def IndexNormalizationSupport (env : VEnv) (universes : List Name) (reader : Context)
    (opened normalized : Expr) : Prop :=
  ∀ virtual semantic,
    TrLCtx env universes reader.lctx virtual →
    TrExpr env universes virtual opened semantic →
    ∃ normalizedSemantic, TrExprS env universes virtual normalized normalizedSemantic ∧
      env.IsDefEqU universes.length virtual.toCtx normalizedSemantic semantic

inductive IndexTraceAnnotationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} :
    {source : Expr} → {index : Nat} → {indices : Array Expr} → {reader : Context} →
    {terminal : Expr} → {finalIndex : Nat} → {finalIndices : Array Expr} → {finalReader : Context} →
    RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader → Prop where
  | stop {source : Expr} {index : Nat} {indices : Array Expr} {reader : Context}
      (notForall : ∀ name domain body bi, source ≠ .forallE name domain body bi) :
      IndexTraceAnnotationSupport env universes (.stop (index := index) (indices := indices)
        (ctx := reader) notForall)
  | parameter {name : Name} {domain body normalized terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
      (parameter : index < stats.params.size)
      (normalization : ((monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr)
        reader) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized (index + 1) indices reader
        terminal finalIndex finalIndices finalReader)
      (supported : IndexTraceAnnotationSupport env universes tail) :
      IndexTraceAnnotationSupport env universes (.parameter (name := name) (domain := domain)
        (bi := bi) parameter normalization tail)
  | index {name : Name} {domain body normalized terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
      (notParameter : ¬ index < stats.params.size)
      (normalization : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))) : M Expr)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized index (indices.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        terminal finalIndex finalIndices finalReader)
      (headSupported : IndexAnnotationSupport env universes reader domain)
      (tailSupported : IndexTraceAnnotationSupport env universes tail) :
      IndexTraceAnnotationSupport env universes (.index notParameter normalization tail)

inductive IndexTraceNormalizationSupport (env : VEnv) (universes : List Name)
    {stats : InductiveStats} :
    {source : Expr} → {index : Nat} → {indices : Array Expr} → {reader : Context} →
    {terminal : Expr} → {finalIndex : Nat} → {finalIndices : Array Expr} → {finalReader : Context} →
    RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader → Prop where
  | stop {source : Expr} {index : Nat} {indices : Array Expr} {reader : Context}
      (notForall : ∀ name domain body bi, source ≠ .forallE name domain body bi) :
      IndexTraceNormalizationSupport env universes (.stop (index := index) (indices := indices)
        (ctx := reader) notForall)
  | parameter {name : Name} {domain body normalized terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
      (parameter : index < stats.params.size)
      (normalization : ((monadLift (TypeChecker.whnf (body.instantiate1 stats.params[index]!)) : M Expr)
        reader) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized (index + 1) indices reader
        terminal finalIndex finalIndices finalReader)
      (supported : IndexTraceNormalizationSupport env universes tail) :
      IndexTraceNormalizationSupport env universes (.parameter (name := name) (domain := domain)
        (bi := bi) parameter normalization tail)
  | index {name : Name} {domain body normalized terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
      (notParameter : ¬ index < stats.params.size)
      (normalization : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))) : M Expr)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized index (indices.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        terminal finalIndex finalIndices finalReader)
      (headSupported : IndexNormalizationSupport env universes
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) normalized)
      (tailSupported : IndexTraceNormalizationSupport env universes tail) :
      IndexTraceNormalizationSupport env universes (.index notParameter normalization tail)

inductive TranslatedRecursorIndexTrace (env : VEnv) (universes : List Name)
    {stats : InductiveStats} :
    {source : Expr} → {index : Nat} → {indices : Array Expr} → {reader : Context} →
    {terminal : Expr} → {finalIndex : Nat} → {finalIndices : Array Expr} → {finalReader : Context} →
    RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader →
      VLCtx → VExpr → VLCtx → VExpr → Prop where
  | stop {source : Expr} {index : Nat} {indices : Array Expr} {reader : Context}
      {virtual : VLCtx} {semantic : VExpr}
      (notForall : ∀ name domain body bi, source ≠ .forallE name domain body bi)
      (correspondence : TrLCtx env universes reader.lctx virtual)
      (translated : TrExprS env universes virtual source semantic) :
      TranslatedRecursorIndexTrace env universes (.stop (index := index) (indices := indices)
        (ctx := reader) notForall) virtual semantic virtual semantic
  | index {name : Name} {domain body normalized terminal : Expr} {bi : BinderInfo}
      {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
      {virtual finalVirtual : VLCtx} {semanticDomain bodySemantic peeled normalizedSemantic finalSemantic : VExpr}
      {level : VLevel}
      (notParameter : ¬ index < stats.params.size)
      (normalization : ((monadLift (TypeChecker.whnf (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))) : M Expr)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))) = .ok normalized)
      (tail : RecursorIndexTrace stats normalized index (indices.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIndexContext reader name bi (peelTypeAnnotations domain))
        terminal finalIndex finalIndices finalReader)
      (translated : TrExprS env universes virtual (.forallE name domain body bi)
        (.forallE semanticDomain bodySemantic))
      (opening : PeeledIndexOpening env universes reader virtual name domain body bi
        semanticDomain bodySemantic level peeled)
      (normalizedTranslation : TrExprS env universes
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled) normalized normalizedSemantic)
      (normalizedEquality : env.IsDefEqU universes.length
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
        normalizedSemantic bodySemantic)
      (translatedTail : TranslatedRecursorIndexTrace env universes tail
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled) normalizedSemantic
        finalVirtual finalSemantic) :
      TranslatedRecursorIndexTrace env universes (.index notParameter normalization tail)
        virtual (.forallE semanticDomain bodySemantic) finalVirtual finalSemantic

theorem RecursorIndexTrace.translated {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual : VLCtx} {semantic : VExpr}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (annotations : IndexTraceAnnotationSupport env universes trace)
    (normalizations : IndexTraceNormalizationSupport env universes trace) :
    ∃ finalVirtual finalSemantic,
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic := by
  induction trace generalizing virtual semantic with
  | stop notForall =>
    exact ⟨virtual, semantic, .stop notForall correspondence translated⟩
  | parameter parameter normalization tail tailInduction =>
    exact False.elim (Nat.not_lt_of_ge indexOnly parameter)
  | @index name domain body bi index indices reader normalized terminal finalIndex finalIndices finalReader
      notParameter normalization tail tailInduction =>
    cases annotations with
    | stop notForall => exact False.elim (notForall name domain body bi rfl)
    | parameter parameter _ _ _ => exact False.elim (Nat.not_lt_of_ge indexOnly parameter)
    | index _ supportedNormalization _ headSupported tailSupported =>
      have sameNormalized := Except.ok.inj (normalization.symm.trans supportedNormalization)
      cases sameNormalized
      cases normalizations with
      | stop notForall => exact False.elim (notForall name domain body bi rfl)
      | parameter parameter _ _ _ => exact False.elim (Nat.not_lt_of_ge indexOnly parameter)
      | index _ supportedNormalization _ normalizationSupported tailNormalizationSupported =>
        have sameNormalized := Except.ok.inj (normalization.symm.trans supportedNormalization)
        cases sameNormalized
        have original := translated
        cases translated with
        | forallE domainIsType bodyIsType domainTranslation bodyTranslation =>
          obtain ⟨level, domainTyped, uniform⟩ :=
            headSupported virtual _ correspondence domainTranslation domainIsType
          obtain ⟨peeled, opening⟩ := translatedForallIndexOpening envWF constants definitions
            correspondence reserved original domainTyped uniform
          obtain ⟨normalizedSemantic, normalizedTranslation, normalizedEquality⟩ :=
            normalizationSupported _ _ opening.2.2.1 opening.2.2.2.1
          obtain ⟨finalVirtual, finalSemantic, translatedTail⟩ := tailInduction indexOnly
            opening.2.2.1 opening.2.2.2.2.2.reserved normalizedTranslation
            tailSupported tailNormalizationSupported
          exact ⟨finalVirtual, finalSemantic, .index notParameter normalization tail original opening
            normalizedTranslation normalizedEquality translatedTail⟩

end Lean4Lean.AddInductive
