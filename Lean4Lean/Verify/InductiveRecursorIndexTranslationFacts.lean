import Lean4Lean.Verify.InductiveRecursorIndexTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem TranslatedRecursorIndexTrace.majorMotiveScope
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader indexReader current : Context} {virtual finalVirtual : VLCtx}
    {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader
      terminal finalIndex finalIndices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (types : Array InductiveType) (elimLevel : Level) (parent : Nat) (major : Expr)
    (finalFrame : (recursorIndexContext
      (recursorIndexContext indexReader `t .default (recursorMajorDomain stats parent finalIndices))
      (recursorMotiveName types parent) .default
      (recursorMotiveDomain elimLevel finalIndices major
        (recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats parent finalIndices)))).RecursorScopeFrame current) :
    indexReader.RecursorScopeFrame current := by
  have indexScope := history.scope reserved
  have majorScope := Context.RecursorScopeFrame.push indexReader
    history.finalTranslation.1.1 indexScope.reserved `t .default
    (recursorMajorDomain stats parent finalIndices)
  let majorReader := recursorIndexContext indexReader `t .default
    (recursorMajorDomain stats parent finalIndices)
  have motiveScope := Context.RecursorScopeFrame.push majorReader majorScope.wf majorScope.reserved
    (recursorMotiveName types parent) .default
    (recursorMotiveDomain elimLevel finalIndices major majorReader)
  exact majorScope.trans (motiveScope.trans finalFrame)

theorem TranslatedRecursorIndexTrace.allocationsInContinuation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader indexReader current : Context} {virtual finalVirtual : VLCtx}
    {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader
      terminal finalIndex finalIndices indexReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (scope : indexReader.RecursorScopeFrame current) :
    ∃ steps : List BinderStep,
      finalIndices.toList = indices.toList ++ steps.map BinderStep.value ∧
      (∀ step ∈ steps, step.role = .index) ∧
      BinderIndexAllocations indexReader reader.lctx.decls.size steps ∧
      BinderIndexAllocations current reader.lctx.decls.size steps := by
  obtain ⟨steps, arrays, roles, allocations⟩ := history.allocations reserved
  exact ⟨steps, arrays, roles, allocations,
    allocations.mono history.finalTranslation.1.1 scope⟩

theorem BinderStep.indexValues_eq_map_of_indices {steps : List BinderStep}
    (roles : ∀ step ∈ steps, step.role = .index) :
    BinderStep.indexValues steps = steps.map BinderStep.value := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    simp only [BinderStep.indexValues, roles step List.mem_cons_self, ↓reduceIte, List.map_cons]
    rw [ih fun selected member => roles selected (List.mem_cons_of_mem step member)]

theorem TranslatedRecursorInfoIndexSource.historyToCurrent
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    ∃ entry normalized terminal indexReader virtual semantic finalVirtual finalSemantic,
      ∃ trace : RecursorIndexTrace stats normalized 0 #[] entry
        terminal 0 info.indices indexReader,
      original.RecursorScopeFrame entry ∧
      ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
      TrLCtx env universes indexReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic ∧
      entry.RecursorScopeFrame indexReader ∧
      indexReader.RecursorScopeFrame current ∧
      info.major = .fvar ⟨indexReader.ngen.curr⟩ ∧
      info.motive = .fvar ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats parent info.indices)).ngen.curr⟩ := by
  cases source with
  | @mk entry indexReader normalized terminal finalIndex virtual finalVirtual semantic finalSemantic
      entryFrame initialNormalization trace major motive currentFrame _ _ history =>
    have unchanged := history.indexUnchanged
    subst finalIndex
    obtain ⟨finalCorrespondence, terminalTranslation⟩ := history.finalTranslation
    exact ⟨entry, normalized, terminal, indexReader, virtual, semantic, finalVirtual,
      finalSemantic, trace, entryFrame, initialNormalization, history, finalCorrespondence,
      terminalTranslation, history.scope entryFrame.reserved,
      history.majorMotiveScope entryFrame.reserved types elimLevel parent info.major currentFrame,
      major, motive⟩

theorem TranslatedRecursorInfoIndexSource.allocationReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    ∃ entry normalized terminal indexReader virtual semantic finalVirtual finalSemantic,
      ∃ trace : RecursorIndexTrace stats normalized 0 #[] entry
        terminal 0 info.indices indexReader,
      original.RecursorScopeFrame entry ∧
      ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) entry) = .ok normalized ∧
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
      TrLCtx env universes indexReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic ∧
      indexReader.RecursorScopeFrame current ∧
      ∃ steps : List BinderStep,
        info.indices.toList = steps.map BinderStep.value ∧
        (∀ step ∈ steps, step.role = .index) ∧
        BinderIndexAllocations indexReader entry.lctx.decls.size steps ∧
        BinderIndexAllocations current entry.lctx.decls.size steps := by
  obtain ⟨entry, normalized, terminal, indexReader, virtual, semantic, finalVirtual,
    finalSemantic, trace, entryFrame, initialNormalization, history, finalCorrespondence,
    terminalTranslation, _, currentScope, _, _⟩ := source.historyToCurrent
  obtain ⟨steps, arrays, roles, indexAllocations, currentAllocations⟩ :=
    history.allocationsInContinuation entryFrame.reserved currentScope
  exact ⟨entry, normalized, terminal, indexReader, virtual, semantic, finalVirtual,
    finalSemantic, trace, entryFrame, initialNormalization, history, finalCorrespondence,
    terminalTranslation, currentScope, steps, by simpa only [Array.toList_empty,
      List.nil_append] using arrays, roles, indexAllocations, currentAllocations⟩

theorem TranslatedRecursorInfoIndexSource.allocations
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    ∃ entry indexReader steps,
      original.RecursorScopeFrame entry ∧
      info.indices.toList = steps.map BinderStep.value ∧
      (∀ step ∈ steps, step.role = .index) ∧
      BinderIndexAllocations indexReader entry.lctx.decls.size steps ∧
      BinderIndexAllocations current entry.lctx.decls.size steps := by
  obtain ⟨entry, _, _, indexReader, _, _, _, _, _, entryFrame, _, _, _, _, _,
    steps, arrays, roles, indexAllocations, currentAllocations⟩ := source.allocationReceipt
  exact ⟨entry, indexReader, steps, entryFrame, arrays, roles, indexAllocations,
    currentAllocations⟩

theorem TranslatedRecursorInfoIndexSource.indexIdsNodup
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    (info.indices.toList.map Expr.fvarId!).Nodup := by
  obtain ⟨_, _, steps, _, arrays, roles, _, currentAllocations⟩ := source.allocations
  have values := BinderStep.indexValues_eq_map_of_indices roles
  rw [arrays, ← values]
  exact currentAllocations.indexIdsNodup

theorem TranslatedRecursorInfoIndexSource.indexPositioned
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) (ordinal : Nat) (value : Expr)
    (selected : info.indices.toList[ordinal]? = some value) :
    ∃ (entry indexReader : Context) (steps : List BinderStep) (step : BinderStep),
      original.RecursorScopeFrame entry ∧
      info.indices.toList = steps.map BinderStep.value ∧
      step ∈ steps ∧ step.role = .index ∧ step.value = value ∧
      BinderPositionedAt indexReader value step.name step.localDomain step.bi
        (entry.lctx.decls.size + ordinal) ∧
      BinderPositionedAt current value step.name step.localDomain step.bi
        (entry.lctx.decls.size + ordinal) := by
  obtain ⟨entry, _, _, indexReader, _, _, _, _, _, entryFrame, _, _,
    finalCorrespondence, _, currentScope, steps, arrays, roles, indexAllocations, _⟩ :=
    source.allocationReceipt
  have values := BinderStep.indexValues_eq_map_of_indices roles
  have selectedStep : (BinderStep.indexValues steps)[ordinal]? = some value := by
    rw [values, ← arrays]
    exact selected
  obtain ⟨step, member, role, valueEquality, positioned⟩ :=
    indexAllocations.positioned selectedStep
  have currentPositioned := positioned.mono finalCorrespondence.1 currentScope
  exact ⟨entry, indexReader, steps, step, entryFrame, arrays, member, role, valueEquality,
    by simpa only [valueEquality] using positioned,
    by simpa only [valueEquality] using currentPositioned⟩

theorem TranslatedRecursorInfoIndexSource.majorLookup
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    ∃ decl, current.lctx.find? info.major.fvarId! = some decl ∧ decl.toExpr = info.major ∧
      decl.type = recursorMajorDomain stats parent info.indices :=
  source.toSource.majorLookup

theorem TranslatedRecursorInfoIndexSource.declared
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original current : Context} {info : RecInfo}
    (source : TranslatedRecursorInfoIndexSource env universes stats types elimLevel
      parent original info current) :
    RecursorFieldsDeclared current.lctx ((info.indices.push info.major).push info.motive) :=
  source.toSource.declared

theorem TranslatedRecursorInfoIndexSources.indexIdsNodup
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level}
    {original current : Context} {infos : Array RecInfo}
    (sources : TranslatedRecursorInfoIndexSources env universes stats types elimLevel
      original infos current) (parent : Nat) (bound : parent < types.size) :
    (infos[parent]!.indices.toList.map Expr.fvarId!).Nodup :=
  (sources.2 parent bound).indexIdsNodup

end Lean4Lean.AddInductive
