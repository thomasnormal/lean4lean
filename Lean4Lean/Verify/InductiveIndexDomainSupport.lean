import Lean4Lean.Verify.InductiveIndexBinderOrder
import Lean4Lean.Verify.InductiveIndexBaseStrengthening

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

theorem BinderStoredIndexTypeFVarsIn.selectedDomains
    {params base : List FVarId} {current : Context} {steps : List BinderStep}
    (receipt : BinderStoredIndexTypeFVarsIn params current steps) (parameters : params ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base
      ((BinderStep.indexValues steps).map Expr.fvarId!) := by
  intro selectedPrefix identifier suffix split physicalIndex name domain binder lookup selected member
  obtain ⟨position, step, selectedAt, selectedRole, selectedId, prefixEq⟩ :=
    BinderStep.indexIds_split split
  let declaration := LocalDecl.cdecl physicalIndex identifier name domain binder .default
  have stepLookup : current.lctx.find? step.value.fvarId! = some declaration := by
    simpa only [selectedId] using lookup
  have supported := receipt position step declaration selectedAt selectedRole stepLookup
  have retained : selected ∈ params ++ selectedPrefix := by
    simpa only [declaration, LocalDecl.type, prefixEq] using (fvarsIn_iff.mp supported).1 selected member
  rcases List.mem_append.mp retained with parameter | earlier
  · exact List.mem_append_right _ (parameters parameter)
  · exact List.mem_append_left _ earlier

theorem BinderRawDomainFVarsIn.selectedDomains
    {params base : List FVarId} {current : Context} {steps : List BinderStep}
    (within : BinderRawDomainFVarsIn params steps)
    (declared : BinderStepsIndexDeclared current steps) (parameters : params ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base
      ((BinderStep.indexValues steps).map Expr.fvarId!) :=
  (within.storedIndexTypeFVarsIn declared).selectedDomains parameters

theorem SelectedRecursorDomainFVars.dropPrefix
    {full : LocalContext} {base largerBase earlier selected : List FVarId}
    (supported : SelectedRecursorDomainFVars full base (earlier ++ selected))
    (retained : earlier ⊆ largerBase) (baseRetained : base ⊆ largerBase) :
    SelectedRecursorDomainFVars full largerBase selected := by
  intro selectedPrefix identifier suffix split physicalIndex name domain binder lookup dependency member
  have totalSplit : earlier ++ selected = (earlier ++ selectedPrefix) ++ identifier :: suffix := by
    simp only [split, List.append_assoc]
  have allowed := supported (earlier ++ selectedPrefix) identifier suffix totalSplit
    physicalIndex name domain binder lookup member
  rcases List.mem_append.mp allowed with prefixMember | baseMember
  · rcases List.mem_append.mp prefixMember with oldMember | selectedMember
    · exact List.mem_append_right _ (retained oldMember)
    · exact List.mem_append_left _ selectedMember
  · exact List.mem_append_right _ (baseRetained baseMember)

theorem ParentBinderIntegrity.selectedIndexDomains
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedRoot current : Context} {info : RecInfo} {base : List FVarId}
    (receipt : ParentBinderIntegrity stats types parent checkedRoot current info)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base (info.indices.toList.map Expr.fvarId!) := by
  obtain ⟨_, _, generated, _, _, _, _, _,
    _, _, _, _, _, _, _, generatedIndices,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, stored⟩ := receipt
  simpa only [generatedIndices] using stored.selectedDomains parameters

theorem RecursorBinderIntegrity.selectedIndexDomains
    {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo} {base : List FVarId}
    (receipt : RecursorBinderIntegrity stats types checkedRoot current infos)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    ∀ parent, parent < types.size →
      SelectedRecursorDomainFVars current.lctx base (infos[parent]!.indices.toList.map Expr.fvarId!) :=
  fun parent bound => (receipt.2 parent bound).selectedIndexDomains parameters

theorem TranslatedRecursorIndexTrace.selectedTelescopeStrengthenedOfStoredDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (smaller : MLCtx) (smallerWF : smaller.WF env universes) (baseLift : Lift)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx model.vlctx 0 baseLift 0)
    {params : List FVarId} {steps : List BinderStep}
    (stored : BinderStoredIndexTypeFVarsIn params current steps)
    (values : BinderStep.indexValues steps = finalIndices.toList)
    (parameters : params ⊆ smaller.vlctx.fvars)
    (prefixRetained : indices.toList.map Expr.fvarId! ⊆ smaller.vlctx.fvars) :
    ∃ chronological ids transported aligned,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned := by
  obtain ⟨allocated, array, _, _⟩ := history.allocations reserved
  have prefixArray : finalIndices.toList = indices.toList ++ finalIndices.toList.drop indices.size := by
    rw [array, ← Array.length_toList, List.drop_left]
  have allSupport := stored.selectedDomains parameters
  rw [values, prefixArray, List.map_append] at allSupport
  have selectedSupport := allSupport.dropPrefix prefixRetained (fun _ member => member)
  exact history.selectedTelescopeStrengthened model modelWF native converted reserved current frame envWF
    smaller smallerWF baseLift baseWeakening selectedSupport

end Lean4Lean.AddInductive
