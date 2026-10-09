import Lean4Lean.Verify.InductiveIndexOpeningTranslation
import Lean4Lean.Verify.InductiveBinderAllocations
import Lean4Lean.Verify.InductiveIndexTraceTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private recursorIndexSize from Lean4Lean.Verify.InductiveBinderAllocations

theorem SortTelescope.normalizedTranslation {env : VEnv} {universes : List Name}
    {virtualContext : VLCtx} {ctx : Context} {body normalized : Expr}
    {value : Expr} {semantic : VExpr}
    (bodyTelescope : SortTelescope body)
    (normalizedResult : ((monadLift (TypeChecker.whnf (body.instantiate1 value)) : M Expr) ctx) =
      .ok normalized)
    (translation : TrExpr env universes virtualContext (body.instantiate1 value) semantic) :
    ∃ normalizedSemantic, TrExprS env universes virtualContext normalized normalizedSemantic ∧
      env.IsDefEqU universes.length virtualContext.toCtx normalizedSemantic semantic := by
  have unchanged := (bodyTelescope.instantiate1 value).whnf ctx normalized normalizedResult
  subst normalized
  exact translation

theorem RecursorIndexTrace.normalizationSupport_ofSortTelescope
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (telescope : SortTelescope source) : IndexTraceNormalizationSupport env universes trace := by
  induction trace with
  | stop notForall => exact .stop notForall
  | @parameter name domain body bi index indices reader normalized terminal finalIndex finalIndices finalReader
      parameter normalization tail ih =>
    cases telescope with
    | forallE _ _ _ bodyTelescope =>
      have nextTelescope := (bodyTelescope.whnfStep name domain bi stats.params[index]!
        reader normalized normalization).1
      exact .parameter parameter normalization tail (ih nextTelescope)
  | @index name domain body bi index indices reader normalized terminal finalIndex finalIndices finalReader
      notParameter normalization tail ih =>
    cases telescope with
    | forallE _ _ _ bodyTelescope =>
      have nextTelescope := (bodyTelescope.whnfStep name domain bi (.fvar ⟨reader.ngen.curr⟩)
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)) normalized normalization).1
      refine .index notParameter normalization tail ?_ (ih nextTelescope)
      intro virtual semantic _ translation
      exact bodyTelescope.normalizedTranslation normalization translation

theorem TranslatedRecursorIndexTrace.initialTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic) :
    TrExprS env universes virtual source semantic := by
  cases history with
  | stop _ _ translated => exact translated
  | index _ _ _ translated _ _ _ _ => exact translated

theorem TranslatedRecursorIndexTrace.initialCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (readerWF : reader.lctx.WF) : TrLCtx env universes reader.lctx virtual := by
  cases history with
  | stop _ correspondence _ => exact correspondence
  | index _ _ _ _ opening _ _ _ =>
    have pushedList := opening.2.2.1.2
    simp only [recursorIndexContext, LocalContext.mkLocalDecl_toList] at pushedList
    cases pushedList with
    | cons original _ => exact ⟨readerWF, original⟩

theorem TranslatedRecursorIndexTrace.finalTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic) :
    TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic := by
  induction history with
  | stop _ correspondence translated => exact ⟨correspondence, translated⟩
  | index _ _ _ _ _ _ _ _ ih => exact ih

theorem TranslatedRecursorIndexTrace.indexUnchanged
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic) :
    finalIndex = index := by
  induction history with
  | stop => rfl
  | index _ _ _ _ _ _ _ _ ih => exact ih

theorem TranslatedRecursorIndexTrace.scope
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) : reader.RecursorScopeFrame finalReader := by
  induction history with
  | stop _ correspondence _ => exact .refl _ correspondence.1 reserved
  | index _ _ _ _ opening _ _ _ ih =>
    have frame := opening.2.2.2.2.2
    exact frame.trans (ih frame.reserved)

theorem TranslatedRecursorIndexTrace.allocations
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ steps : List BinderStep,
      finalIndices.toList = indices.toList ++ steps.map BinderStep.value ∧
      (∀ step ∈ steps, step.role = .index) ∧
      BinderIndexAllocations finalReader reader.lctx.decls.size steps := by
  induction history with
  | stop => exact ⟨[], (List.append_nil _).symm, by simp, True.intro⟩
  | @index name domain body normalized terminal bi index finalIndex indices finalIndices reader finalReader
      virtual finalVirtual semanticDomain bodySemantic peeled normalizedSemantic finalSemantic level
      notParameter normalization tail translated opening normalizedTranslation normalizedEquality translatedTail ih =>
    have frame := opening.2.2.2.2.2
    obtain ⟨steps, arrays, roles, allocated⟩ := ih frame.reserved
    let step : BinderStep := { role := .index, name, domain, bi, value := .fvar ⟨reader.ngen.curr⟩ }
    refine ⟨step :: steps, ?_, ?_, ?_⟩
    · simpa only [step, List.map_cons, Array.toList_push, List.append_assoc,
        List.singleton_append] using arrays
    · intro selected member
      obtain rfl | member := List.mem_cons.mp member
      · rfl
      · exact roles selected member
    · change BinderPositionedAt finalReader (.fvar ⟨reader.ngen.curr⟩) name
        (peelTypeAnnotations domain) bi reader.lctx.decls.size ∧
          BinderIndexAllocations finalReader (reader.lctx.decls.size + 1) steps
      exact ⟨opening.2.2.2.2.1.mono frame.wf (translatedTail.scope frame.reserved),
        by simpa only [recursorIndexSize] using allocated⟩

end Lean4Lean.AddInductive
