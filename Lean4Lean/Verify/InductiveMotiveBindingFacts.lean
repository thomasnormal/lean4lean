import Lean4Lean.Verify.InductiveMajorContextTranslation
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open TypeChecker (MLCtx)

inductive IndexMLCtxExtension (initial : MLCtx) : List FVarId → MLCtx → Prop where
  | nil : IndexMLCtxExtension initial [] initial
  | push {ids : List FVarId} {model : MLCtx}
      (earlier : IndexMLCtxExtension initial ids model)
      (id : FVarId) (name : Name) (domain : Expr) (semantic : VExpr) (bi : BinderInfo) :
      IndexMLCtxExtension initial (ids ++ [id]) (.vlam id name domain semantic bi model)

theorem IndexMLCtxExtension.trans {initial middle final : MLCtx} {left right : List FVarId}
    (earlier : IndexMLCtxExtension initial left middle)
    (suffix : IndexMLCtxExtension middle right final) :
    IndexMLCtxExtension initial (left ++ right) final := by
  induction suffix with
  | nil => simpa only [List.append_nil] using earlier
  | push _ id name domain semantic bi tailInduction =>
    simpa only [List.append_assoc] using
      IndexMLCtxExtension.push tailInduction id name domain semantic bi

theorem IndexMLCtxExtension.length_eq {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.length = initial.length + ids.length := by
  induction extension with
  | nil => simp only [List.length_nil, Nat.add_zero]
  | push _ _ _ _ _ _ tailInduction =>
    simp only [MLCtx.length, List.length_append, List.length_singleton, tailInduction, Nat.add_assoc]

theorem IndexMLCtxExtension.bound {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) : ids.length ≤ final.length := by
  rw [extension.length_eq]
  omega

theorem IndexMLCtxExtension.selection {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.fvarRevList ids.length extension.bound = ids.reverse := by
  induction extension with
  | nil => rfl
  | push earlier id name domain semantic bi tailInduction =>
    simpa only [List.length_append, List.length_singleton, MLCtx.fvarRevList,
      List.reverse_append, List.reverse_singleton, List.singleton_append] using
      congrArg (List.cons id) tailInduction

theorem IndexMLCtxExtension.drop_eq {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.dropN ids.length extension.bound = initial := by
  induction extension with
  | nil => rfl
  | push earlier id name domain semantic bi tailInduction =>
    simpa only [List.length_append, List.length_singleton, MLCtx.dropN] using tailInduction

theorem IndexMLCtxExtension.weakening {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    VLCtx.FVLift initial.vlctx final.vlctx 0 ids.length 0 := by
  induction extension with
  | nil => exact .refl
  | push earlier id name domain semantic bi tailInduction =>
    simpa only [List.length_append, List.length_singleton, MLCtx.vlctx, VLocalDecl.depth]
      using tailInduction.skip_fvar (id, domain.fvarsList) (.vlam semantic)

theorem IndexMLCtxExtension.receipt {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    ∃ bound : ids.length ≤ final.length,
      final.dropN ids.length bound = initial ∧ final.fvarRevList ids.length bound = ids.reverse ∧
      VLCtx.FVLift initial.vlctx final.vlctx 0 ids.length 0 :=
  ⟨extension.bound, extension.drop_eq, extension.selection, extension.weakening⟩

theorem TranslatedRecursorIndexTrace.mixedContext
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar := by
  induction history generalizing model with
  | stop => exact ⟨model, [], modelWF, native, converted, .nil, by simp only [List.map_nil, List.append_nil]⟩
  | @index name domain body normalized terminal bi index finalIndex indices finalIndices reader finalReader
      virtual finalVirtual semanticDomain bodySemantic peeled normalizedSemantic finalSemantic level
      notParameter normalization tail translated opening normalizedTranslation normalizedEquality
      translatedTail tailInduction =>
    let nextModel := MLCtx.vlam ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) peeled bi model
    have nextWF : nextModel.WF env universes := by
      refine ⟨modelWF, ?_, ?_, ?_⟩
      · rw [native]
        exact reserved.fresh (native ▸ modelWF.tr.1)
      · simpa only [converted] using opening.1
      · exact ⟨level, by simpa only [converted] using opening.2.1.hasType.2⟩
    have nextNative : nextModel.lctx =
        (recursorIndexContext reader name bi (peelTypeAnnotations domain)).lctx := by
      simp only [nextModel, MLCtx.lctx, recursorIndexContext, native]
    have nextConverted : nextModel.vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled := by
      simp only [nextModel, MLCtx.vlctx, peeledIndexVirtualContext, converted]
    obtain ⟨finalModel, ids, finalWF, finalNative, finalConverted, extension, array⟩ :=
      tailInduction nextModel nextWF nextNative nextConverted opening.2.2.2.2.2.reserved
    refine ⟨finalModel, ⟨reader.ngen.curr⟩ :: ids, finalWF, finalNative, finalConverted, ?_, ?_⟩
    · exact (IndexMLCtxExtension.push .nil ⟨reader.ngen.curr⟩ name
        (peelTypeAnnotations domain) peeled bi).trans extension
    · simpa only [Array.toList_push, List.map_cons, List.append_assoc,
        List.singleton_append] using array

def recursorMajorMLCtx (stats : InductiveStats) (parent : Nat) (indices : Array Expr)
    (reader : Context) (model : MLCtx) (peeled : VExpr) : MLCtx :=
  .vlam ⟨reader.ngen.curr⟩ `t (recursorMajorDomain stats parent indices) peeled .default model

theorem RecursorMajorOpening.mixedContext
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (recursorMajorMLCtx stats parent indices reader model peeled).WF env universes ∧
      (recursorMajorMLCtx stats parent indices reader model peeled).lctx =
        (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)).lctx ∧
      (recursorMajorMLCtx stats parent indices reader model peeled).vlctx =
        recursorMajorVirtualContext stats parent indices reader virtual peeled := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨modelWF, ?_, ?_, ?_⟩
    · rw [native]
      exact reserved.fresh (native ▸ modelWF.tr.1)
    · simpa only [converted] using opening.2.2.1
    · exact ⟨level, by simpa only [converted] using opening.2.2.2.2.1⟩
  · simp only [recursorMajorMLCtx, MLCtx.lctx, recursorIndexContext, native]
  · simp only [recursorMajorMLCtx, MLCtx.vlctx, recursorMajorVirtualContext, converted]


theorem mkForall_congr_selected {left right : LocalContext} {body : Expr}
    (ids : List FVarId) (leftScope : left.BindingScope) (rightScope : right.BindingScope)
    (bodyClosed : body.looseBVarRange' = 0) (distinct : ids.Nodup)
    (lookups : ∀ id ∈ ids, left.find? id = right.find? id) :
    left.mkForall (ids.map Expr.fvar).toArray body =
      right.mkForall (ids.map Expr.fvar).toArray body := by
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eq bodyClosed leftScope distinct,
    LocalContext.mkBinding_eq bodyClosed rightScope distinct]
  exact LocalContext.mkBindingList_congr lookups

theorem IndexMLCtxExtension.peelForall {initial model : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids model)
    (name : Name) (domain body : Expr) (bi : BinderInfo) :
    peelTypeAnnotations (model.mkForall ids.length extension.bound (.forallE name domain body bi)) =
      model.mkForall ids.length extension.bound (.forallE name domain body bi) := by
  induction extension generalizing name domain body bi with
  | nil => rfl
  | push earlier id binder binderDomain semantic binderInfo tailInduction =>
    simpa only [List.length_append, List.length_singleton, MLCtx.mkForall] using
      tailInduction binder binderDomain ((Expr.forallE name domain body bi).abstract1 id) binderInfo

theorem IndexMLCtxExtension.nativeMotiveEq
    {env : VEnv} {universes : List Name} {initial model : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids model)
    (modelWF : model.WF env universes)
    (id : FVarId) (name : Name) (domain : Expr) (semantic : VExpr) (bi : BinderInfo)
    (majorWF : (MLCtx.vlam id name domain semantic bi model).WF env universes)
    (level : Level) :
    (MLCtx.vlam id name domain semantic bi model).lctx.mkForall (ids.map Expr.fvar).toArray
      ((MLCtx.vlam id name domain semantic bi model).lctx.mkForall #[.fvar id] (.sort level)) =
    (MLCtx.vlam id name domain semantic bi model).mkForall (ids.length + 1)
      (Nat.add_le_add_right extension.bound 1) (.sort level) := by
  let majorModel := MLCtx.vlam id name domain semantic bi model
  have singleton : majorModel.lctx.mkForall #[.fvar id] (.sort level) =
      Expr.forallE name domain (.sort level) bi := by
    exact majorWF.mkForall_eq 1 (by simp only [MLCtx.length]; omega) rfl rfl
  have domainClosed : domain.looseBVarRange' = 0 :=
    (model.noBV ▸ majorWF.2.2.1.closed).looseBVarRange_zero
  have bodyClosed : (Expr.forallE name domain (.sort level) bi).looseBVarRange' = 0 := by
    simp only [Expr.looseBVarRange', domainClosed, Nat.zero_sub, Nat.max_self]
  have distinct : ids.Nodup := by
    have selected := modelWF.fvarRevList_nodup ids.length extension.bound
    rw [extension.selection] at selected
    exact List.nodup_reverse.mp selected
  have lookups : ∀ selected ∈ ids.reverse, majorModel.lctx.find? selected = model.lctx.find? selected := by
    intro selected member
    have present : selected ∈ model.vlctx.fvars := by
      have suffix := MLCtx.fvarRevList_prefix model (n := ids.length) (hn := extension.bound)
      rw [extension.selection] at suffix
      exact suffix.subset member
    have different : selected ≠ id := by
      intro equality
      subst selected
      exact (modelWF.tr.find?_eq_none.mp majorWF.2.1) present
    have differentBool : (selected == id) = false := by
      simpa only [beq_eq_false_iff_ne] using different
    simp only [majorWF.find?_eq, modelWF.find?_eq, majorModel, MLCtx.decls, List.find?_cons,
      LocalDecl.fvarId, differentBool]
  rw [singleton]
  have binding := mkForall_congr_selected ids majorWF.bindingScope modelWF.bindingScope
    bodyClosed distinct (fun selected member => lookups selected (List.mem_reverse.mpr member))
  rw [binding]
  exact modelWF.mkForall_eq ids.length extension.bound
    (by simp only [List.map_reverse, extension.selection]) bodyClosed

theorem RecursorMajorOpening.motiveBindingEquation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {parent : Nat}
    {indices : Array Expr} {reader : Context} {virtual : VLCtx}
    {rawSemantic peeled : VExpr} {level : VLevel} {initial model : MLCtx} {ids : List FVarId}
    (opening : RecursorMajorOpening env universes stats parent indices reader virtual rawSemantic peeled level)
    (extension : IndexMLCtxExtension initial ids model)
    (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (array : indices.toList = ids.map Expr.fvar) (elimLevel : Level) :
    recursorMotiveDomain elimLevel indices (.fvar ⟨reader.ngen.curr⟩)
      (recursorIndexContext reader `t .default (recursorMajorDomain stats parent indices)) =
    (recursorMajorMLCtx stats parent indices reader model peeled).mkForall (ids.length + 1)
      (Nat.add_le_add_right extension.bound 1) (.sort elimLevel) := by
  obtain ⟨majorWF, majorNative, majorConverted⟩ :=
    opening.mixedContext model modelWF native converted reserved
  have actualArray : indices = (ids.map Expr.fvar).toArray := by
    rw [← array, Array.toArray_toList]
  have nativeBinding := extension.nativeMotiveEq modelWF ⟨reader.ngen.curr⟩ `t
    (recursorMajorDomain stats parent indices) peeled .default majorWF elimLevel
  have binding : (recursorMajorMLCtx stats parent indices reader model peeled).lctx.mkForall indices
      ((recursorMajorMLCtx stats parent indices reader model peeled).lctx.mkForall
        #[.fvar ⟨reader.ngen.curr⟩] (.sort elimLevel)) =
      (recursorMajorMLCtx stats parent indices reader model peeled).mkForall (ids.length + 1)
        (Nat.add_le_add_right extension.bound 1) (.sort elimLevel) := by
    simpa only [← actualArray, recursorMajorMLCtx] using nativeBinding
  unfold recursorMotiveDomain
  rw [← majorNative, binding]
  simpa only [recursorMajorMLCtx, MLCtx.mkForall, Expr.abstract1] using
    extension.peelForall `t (recursorMajorDomain stats parent indices) (.sort elimLevel) .default

end Lean4Lean.AddInductive
