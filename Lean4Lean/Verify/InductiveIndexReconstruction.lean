import Lean4Lean.Verify.InductiveRecursiveFamilyInputs
import Lean4Lean.Verify.InductiveIndexSubstitutionStageBinding

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

/-- Closing an index suffix leaves its actual first declaration as the outer
Pi. This is an equation about the generated telescope, without typing inputs. -/
theorem IndexMLCtxExtension.mkForall'_outer
    {model final : MLCtx} {ids : List FVarId}
    {identifier : FVarId} {name : Name} {domain : Expr} {semantic : VExpr} {binder : BinderInfo}
    (extension : IndexMLCtxExtension (.vlam identifier name domain semantic binder model) ids final)
    (body : VExpr) :
    final.mkForall' (ids.length + 1) (by rw [extension.length_eq]; simp only [MLCtx.length]; omega) body =
      .forallE semantic (final.mkForall' ids.length extension.bound body) := by
  induction extension generalizing body with
  | nil => rfl
  | push earlier identifier name domain semantic binder induction =>
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc, MLCtx.mkForall'] using
      induction (.forallE semantic body)

/-- Reclose the actual peeled index declarations. The source signature is
definitionally equal to that telescope even when annotation peeling and body
normalization change its native domains. No literal source/domain agreement
or strengthening of an uninhabited context is assumed. -/
theorem TranslatedRecursorIndexTrace.reconstructedModel
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (sourceTyped : env.IsType universes.length virtual.toCtx semantic) :
    ∃ (finalModel : MLCtx) (ids : List FVarId) (extension : IndexMLCtxExtension model ids finalModel),
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      env.IsType universes.length finalVirtual.toCtx finalSemantic ∧
      env.IsDefEqU universes.length model.vlctx.toCtx semantic
        (finalModel.mkForall' ids.length extension.bound finalSemantic) := by
  induction history generalizing model with
  | stop =>
    exact ⟨model, [], .nil, modelWF, native, converted,
      by simp only [List.map_nil, List.append_nil], sourceTyped,
      by obtain ⟨_, typed⟩ := sourceTyped; simpa only [converted, List.length_nil, MLCtx.mkForall'] using typed.toU⟩
  | @index name domain body normalized terminal bi index finalIndex indices finalIndices reader finalReader
      virtual finalVirtual semanticDomain bodySemantic peeled normalizedSemantic finalSemantic level
      notParameter normalization tail translated opening normalizedTranslation normalizedEquality
      translatedTail induction =>
    let nextModel := MLCtx.vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled bi model
    have nextWF : nextModel.WF env universes := by
      refine ⟨modelWF, ?_, ?_, ?_⟩
      · rw [native]; exact reserved.fresh (native ▸ modelWF.tr.1)
      · simpa only [converted] using opening.1
      · exact ⟨level, by simpa only [converted] using opening.2.1.hasType.2⟩
    have nextNative : nextModel.lctx =
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)).lctx := by
      simp only [nextModel, MLCtx.lctx, recursorIndexContext, native]
    have nextConverted : nextModel.vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled := by
      simp only [nextModel, MLCtx.vlctx, peeledIndexVirtualContext, converted]
    have bodyTyped : env.IsType universes.length (peeled :: virtual.toCtx) bodySemantic := by
      cases translated with
      | forallE _ bodyTyped _ _ =>
        exact bodyTyped.defeqDFC envWF.ordered (.succ .zero opening.2.1)
    have normalizedTyped := bodyTyped.defeqU_l envWF opening.2.2.1.wf.toCtx normalizedEquality.symm
    obtain ⟨finalModel, ids, extension, finalWF, finalNative, finalConverted, array,
      finalTyped, equality⟩ := induction nextModel nextWF nextNative nextConverted
        opening.2.2.2.2.2.reserved normalizedTyped
    let extended := (IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ name
      (peelTypeAnnotations domain) peeled bi).trans extension
    refine ⟨finalModel, ⟨reader.ngen.curr⟩ :: ids, extended, finalWF, finalNative, finalConverted,
      ?_, finalTyped, ?_⟩
    · simpa only [Array.toList_push, List.map_cons, List.append_assoc,
        List.singleton_append] using array
    · have equality' : env.IsDefEqU universes.length (peeled :: virtual.toCtx) normalizedSemantic
          (finalModel.mkForall' ids.length extension.bound finalSemantic) := by
        simpa only [nextConverted, peeledIndexVirtualContext, VLCtx.toCtx] using equality
      have bodyEquality := normalizedEquality.symm.trans envWF opening.2.2.1.wf.toCtx equality'
      obtain ⟨bodyLevel, bodyTyped⟩ := bodyTyped
      have bodyEquality := opening.2.1.symm.defeqDF_l envWF.ordered
        (bodyEquality.of_l envWF opening.2.2.1.wf.toCtx bodyTyped)
      have closedEquality := VEnv.IsDefEq.forallEDF opening.2.1 bodyEquality
      have outer := extension.mkForall'_outer finalSemantic
      simpa only [List.length_cons, outer, converted] using closedEquality.toU

/-- A partial-family input can use the reconstructed, actually selected index
signature. Strict translation uniqueness aligns its semantic source with the
trace; the new expected type is derived rather than supplied by the caller. -/
theorem FamilyIndexInput.reconstruct
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source sortTerminal terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr} {model : MLCtx}
    {trace : RecursorIndexTrace stats source index indices reader sortTerminal finalIndex finalIndices finalReader}
    (input : FamilyIndexInput env universes model stats terminal source)
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ (finalModel : MLCtx) (ids : List FVarId),
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes finalReader.lctx model ids finalModel ∧
      Nonempty (FamilyIndexInput env universes model stats terminal
        (finalReader.lctx.mkForall (ids.map Expr.fvar).toArray sortTerminal)) := by
  have sourceTranslation : TrExprS env universes model.vlctx source semantic :=
    converted.symm ▸ history.initialTranslation
  have sourceEquality := input.sourceTranslated.uniq envWF (.refl envWF.ordered modelWF.tr.wf)
    sourceTranslation
  have sourceTyped := (input.typed.isType envWF modelWF.tr.wf.toCtx).defeqU_l
    envWF modelWF.tr.wf.toCtx sourceEquality
  obtain ⟨finalModel, ids, extension, finalWF, finalNative, finalConverted, array,
    finalTyped, equality⟩ := history.reconstructedModel envWF model modelWF native converted reserved
      (converted ▸ sourceTyped)
  have finalTranslation : TrExprS env universes finalModel.vlctx sortTerminal finalSemantic :=
    finalConverted.symm ▸ history.finalTranslation.2
  obtain ⟨translated, _⟩ := extension.typedBodyAbstractionS envWF finalWF finalTranslation
    (finalConverted.symm ▸ finalTyped)
  refine ⟨finalModel, ids, finalWF, finalNative, finalConverted, array,
    finalNative ▸ extension.selectedTelescope finalWF, ⟨?_⟩⟩
  exact ⟨_, finalNative ▸ translated, input.value, input.translated,
    input.typed.defeqU_r envWF modelWF.tr.wf.toCtx
      (sourceEquality.trans envWF modelWF.tr.wf.toCtx equality)⟩

end Lean4Lean.AddInductive
