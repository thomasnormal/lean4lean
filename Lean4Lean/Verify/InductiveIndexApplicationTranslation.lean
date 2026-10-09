import Lean4Lean.Verify.InductiveIndexTraceTranslationFacts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem mkAppN_indexPush (head argument : Expr) (indices : Array Expr) :
    mkAppN head (indices.push argument) = .app (mkAppN head indices) argument := by
  simp only [mkAppN, ← Array.foldl_toList, Array.toList_push, List.foldl_append,
    List.foldl_cons, List.foldl_nil, mkApp]

theorem PeeledIndexOpening.application {env : VEnv} {universes : List Name}
    {reader : Context} {virtual : VLCtx} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semanticDomain bodySemantic peeled : VExpr} {level : VLevel}
    (opening : PeeledIndexOpening env universes reader virtual name domain body bi
      semanticDomain bodySemantic level peeled)
    (envWF : env.WF) {value : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual value semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue
      (.forallE semanticDomain bodySemantic)) :
    TrExprS env universes
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
        (.app value (.fvar ⟨reader.ngen.curr⟩)) (.app semanticValue.lift (.bvar 0)) ∧
      env.HasType universes.length
        (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
        (.app semanticValue.lift (.bvar 0)) bodySemantic := by
  have nextWF := opening.2.2.1.wf
  have weakening : VLCtx.FVLift virtual
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled) 0 1 0 :=
    .skip_fvar _ _ .refl
  have valueTranslated : TrExprS env universes
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
      value semanticValue.lift := translated.weakFV envWF.ordered weakening nextWF
  have valueTyped : env.HasType universes.length
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
      semanticValue.lift (.forallE semanticDomain.lift (bodySemantic.liftN 1 1)) := by
    simpa only [peeledIndexVirtualContext, VLCtx.toCtx, VExpr.lift, VExpr.liftN]
      using typed.weak envWF.ordered (B := peeled)
  have argumentTranslated : TrExprS env universes
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled)
      (.fvar ⟨reader.ngen.curr⟩) (.bvar 0) :=
    .fvar (A := peeled.lift) (by
      simp [peeledIndexVirtualContext, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type])
  have argumentTyped : env.HasType universes.length
      (peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled).toCtx
      (.bvar 0) semanticDomain.lift :=
    (opening.2.1.weak envWF.ordered (B := peeled)).symm.defeq (.bvar .zero)
  exact ⟨.app valueTyped argumentTyped valueTranslated argumentTranslated,
    by simpa only [VExpr.instN_bvar0] using valueTyped.app argumentTyped⟩

theorem TranslatedRecursorIndexTrace.application
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) {head : Expr} {semanticValue : VExpr}
    (translated : TrExprS env universes virtual (mkAppN head indices) semanticValue)
    (typed : env.HasType universes.length virtual.toCtx semanticValue semantic) :
    ∃ finalValue,
      TrExprS env universes finalVirtual (mkAppN head finalIndices) finalValue ∧
        env.HasType universes.length finalVirtual.toCtx finalValue finalSemantic := by
  induction history generalizing semanticValue with
  | stop => exact ⟨semanticValue, translated, typed⟩
  | index _ _ _ _ opening _ normalizedEquality _ tailInduction =>
    obtain ⟨applicationTranslated, applicationTyped⟩ :=
      opening.application envWF translated typed
    have normalizedTyped := applicationTyped.defeqU_r envWF
      opening.2.2.1.wf.toCtx normalizedEquality.symm
    exact tailInduction (by simpa only [mkAppN_indexPush] using applicationTranslated)
      normalizedTyped

end Lean4Lean.AddInductive
