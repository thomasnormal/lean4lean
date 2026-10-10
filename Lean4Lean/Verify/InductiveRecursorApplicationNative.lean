import Lean4Lean.Verify.InductiveRecursorApplicationFacts
import Lean4Lean.Verify.RecursorInfoIndices
import Lean4Lean.Verify.RecursorFieldDistinct

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem RecursorIndexTrace.distinct {stats : InductiveStats} {type terminal : Expr}
    {index finalIndex : Nat} {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats type index indices reader terminal finalIndex finalIndices finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen)
    (declared : RecursorFieldsDeclared reader.lctx indices) (distinct : indices.toList.Nodup) :
    finalIndices.toList.Nodup := by
  revert readerWF reserved declared distinct
  induction trace with
  | stop => intro readerWF reserved declared distinct; exact distinct
  | parameter _ _ _ tailInduction => exact tailInduction
  | @index name domain body bi index indices reader normalized terminal finalIndex finalIndices finalReader
      parameter normalizedEq tail tailInduction =>
    intro readerWF reserved declared distinct
    have frame := Context.RecursorScopeFrame.push reader readerWF reserved name bi (peelTypeAnnotations domain)
    exact tailInduction frame.wf frame.reserved
      (declared.push ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) bi)
      (declared.nodup_push readerWF reserved distinct)

theorem Context.RecursorScopeFrame.bindingScopeBefore {original current : Context}
    (frame : original.RecursorScopeFrame current) (originalWF : original.lctx.WF)
    (scope : current.lctx.BindingScope) : original.lctx.BindingScope := by
  intro identifier declaration lookup
  exact scope identifier declaration (frame.oldLookup originalWF lookup)

theorem RecursorFieldsDeclared.binderShape {lctx : LocalContext} {arguments : Array Expr}
    (declared : RecursorFieldsDeclared lctx arguments) : BinderArrayFVars arguments := by
  intro expression member
  obtain ⟨declaration, _, expressionEq, _⟩ := declared expression (Array.mem_toList_iff.mp member)
  exact ⟨declaration.fvarId, expressionEq.symm⟩

theorem RecursorFieldsDeclared.selectedBindings {lctx : LocalContext} {arguments : Array Expr}
    (declared : RecursorFieldsDeclared lctx arguments) (nativeWF : lctx.WF) :
    SelectedCDeclBindings lctx (binderArrayIds arguments) := by
  intro identifier member
  obtain ⟨expression, member, identifierEq⟩ := List.mem_map.mp member
  obtain ⟨declaration, lookup, expressionEq, valueNone, _⟩ :=
    declared.lookup nativeWF expression (Array.mem_toList_iff.mp member)
  cases declaration with
  | cdecl index selected name domain binder kind =>
    have selectedEq : selected = identifier := by
      exact (congrArg Expr.fvarId! expressionEq).trans identifierEq
    subst identifier
    exact ⟨index, name, domain, binder, kind, by simpa only [← expressionEq] using lookup⟩
  | ldecl index selected name domain value nondependent kind =>
    cases nondependent <;> cases valueNone

theorem BinderArrayFVars.idsDistinct {arguments : Array Expr} (shape : BinderArrayFVars arguments)
    (distinct : arguments.toList.Nodup) : (binderArrayIds arguments).Nodup := by
  have arrayEq := shape.array_eq
  rw [arrayEq] at distinct
  have mapped : ((binderArrayIds arguments).map Expr.fvar).Nodup := by
    simpa only [binderArrayIds, List.toList_toArray, List.map_map] using distinct
  exact (List.pairwise_map.mp mapped).imp (fun different equality => different (congrArg Expr.fvar equality))

theorem SelectedCDeclBindings.agreementAcross {original current : Context} {ids : List FVarId}
    (bindings : SelectedCDeclBindings original.lctx ids)
    (frame : original.RecursorScopeFrame current) (originalWF : original.lctx.WF) :
    SelectedCDeclBindingAgreement original.lctx current.lctx ids := by
  intro identifier member
  obtain ⟨index, name, domain, binder, kind, lookup⟩ := bindings identifier member
  exact ⟨index, index, name, domain, binder, kind, kind, lookup, frame.oldLookup originalWF lookup⟩

theorem peelTypeAnnotations_mkForall_selected_nonempty {lctx : LocalContext} {body : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) (nonempty : ids ≠ []) :
    peelTypeAnnotations (lctx.mkForall (ids.map Expr.fvar).toArray body) =
      lctx.mkForall (ids.map Expr.fvar).toArray body := by
  rw [mkForall_selected_fold ids scope closed distinct bindings]
  cases ids with
  | nil => exact False.elim (nonempty rfl)
  | cons identifier ids =>
    obtain ⟨index, name, domain, binder, kind, lookup⟩ := bindings identifier (by simp only [List.mem_cons_self])
    simp only [List.foldr_cons, LocalContext.mkBindingList1, lookup, Expr.abstractList,
      Bool.false_eq_true, if_false]
    rfl

theorem RecursorInfoIndexSource.motiveLookupAtCurrent
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (scope : current.lctx.BindingScope) :
    ∃ physicalIndex identifier,
      current.lctx.find? info.motive.fvarId! = some (.cdecl physicalIndex identifier
        (recursorMotiveName types parent)
        (current.lctx.mkForall info.indices (current.lctx.mkForall #[info.major] (.sort elimLevel)))
        .default .default) ∧ Expr.fvar identifier = info.motive := by
  obtain ⟨entry, normalized, terminal, finalIndex, indexReader, entryFrame,
    normalizedEq, indicesTrace, majorEq, motiveEq, finalFrame⟩ := source
  have indexFrame := indicesTrace.scope entryFrame.wf entryFrame.reserved
  have indexDeclared : RecursorFieldsDeclared indexReader.lctx info.indices :=
    indicesTrace.declared (fun expression member => by simp only [Array.not_mem_empty] at member)
  have indicesDistinct := indicesTrace.distinct entryFrame.wf entryFrame.reserved
    (fun expression member => by simp only [Array.not_mem_empty] at member)
    (by simp only [List.nodup_nil])
  let majorReader := recursorIndexContext indexReader `t .default
    (recursorMajorDomain stats parent info.indices)
  have majorFrame : indexReader.RecursorScopeFrame majorReader :=
    Context.RecursorScopeFrame.push indexReader indexFrame.wf indexFrame.reserved _ _ _
  let motiveReader := recursorIndexContext majorReader (recursorMotiveName types parent) .default
    (recursorMotiveDomain elimLevel info.indices info.major majorReader)
  have motiveFrame : majorReader.RecursorScopeFrame motiveReader :=
    Context.RecursorScopeFrame.push majorReader majorFrame.wf majorFrame.reserved _ _ _
  have majorToCurrent : majorReader.RecursorScopeFrame current := motiveFrame.trans finalFrame
  have majorScope := majorToCurrent.bindingScopeBefore majorFrame.wf scope
  let arguments := info.indices.push info.major
  have argumentDeclared : RecursorFieldsDeclared majorReader.lctx arguments := by
    simpa only [arguments, majorEq] using
      indexDeclared.push ⟨indexReader.ngen.curr⟩ `t (recursorMajorDomain stats parent info.indices) .default
  have argumentsDistinct : arguments.toList.Nodup := by
    simpa only [arguments, majorEq] using
      indexDeclared.nodup_push indexFrame.wf indexFrame.reserved indicesDistinct
  have shape := argumentDeclared.binderShape
  let ids := binderArrayIds arguments
  have idsDistinct : ids.Nodup := shape.idsDistinct argumentsDistinct
  have bindings : SelectedCDeclBindings majorReader.lctx ids := argumentDeclared.selectedBindings majorFrame.wf
  have agreement := bindings.agreementAcross majorToCurrent majorFrame.wf
  have selectedArray : arguments = (ids.map Expr.fvar).toArray := shape.array_eq
  have nonempty : ids ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [ids, binderArrayIds, arguments, Array.toList_push, List.length_map,
      List.length_append, List.length_singleton, List.length_nil] at lengths
    omega
  have argumentAppend : info.indices ++ #[info.major] = arguments := by
    simp only [arguments, Array.push_eq_append]
  have originalFlat : majorReader.lctx.mkForall info.indices
      (majorReader.lctx.mkForall #[info.major] (.sort elimLevel)) =
      majorReader.lctx.mkForall arguments (.sort elimLevel) := by
    have equation := mkForall_append_array_cdecl (body := .sort elimLevel)
      info.indices #[info.major] majorScope (by rfl)
      (by simpa only [argumentAppend] using shape)
      (by simpa only [argumentAppend] using idsDistinct)
      (by simpa only [argumentAppend] using bindings)
    simpa only [argumentAppend] using equation
  have currentFlat : current.lctx.mkForall info.indices
      (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
      current.lctx.mkForall arguments (.sort elimLevel) := by
    have equation := mkForall_append_array_cdecl (body := .sort elimLevel)
      info.indices #[info.major] scope (by rfl)
      (by simpa only [argumentAppend] using shape)
      (by simpa only [argumentAppend] using idsDistinct)
      (by simpa only [argumentAppend] using agreement.right)
    simpa only [argumentAppend] using equation
  have flatAgreement : majorReader.lctx.mkForall arguments (.sort elimLevel) =
      current.lctx.mkForall arguments (.sort elimLevel) := by
    simpa only [← selectedArray] using
      mkForall_congr_selected_cdecl (body := .sort elimLevel)
        ids majorScope scope (by rfl) idsDistinct agreement
  have unpeeled : peelTypeAnnotations (majorReader.lctx.mkForall arguments (.sort elimLevel)) =
      majorReader.lctx.mkForall arguments (.sort elimLevel) := by
    simpa only [← selectedArray] using
      peelTypeAnnotations_mkForall_selected_nonempty (body := .sort elimLevel)
        ids majorScope (by rfl) idsDistinct bindings nonempty
  have domainEq : recursorMotiveDomain elimLevel info.indices info.major majorReader =
      current.lctx.mkForall info.indices (current.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    rw [recursorMotiveDomain, originalFlat, unpeeled, flatAgreement, ← currentFlat]
  let declaration := LocalDecl.cdecl majorReader.lctx.decls.size ⟨majorReader.ngen.curr⟩
    (recursorMotiveName types parent)
    (recursorMotiveDomain elimLevel info.indices info.major majorReader) .default .default
  have member : declaration ∈ motiveReader.lctx.toList := by
    simp only [motiveReader, recursorIndexContext, LocalContext.mkLocalDecl_toList, List.mem_cons]
    exact Or.inl rfl
  have allocatedLookup := motiveFrame.wf.find?_of_mem member
  have currentLookup := finalFrame.oldLookup motiveFrame.wf allocatedLookup
  refine ⟨majorReader.lctx.decls.size, ⟨majorReader.ngen.curr⟩, ?_, motiveEq.symm⟩
  simpa only [declaration, LocalDecl.fvarId, domainEq, motiveEq, Expr.fvarId!] using currentLookup

end Lean4Lean.AddInductive
