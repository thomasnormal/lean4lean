import Lean4Lean.Verify.InductiveAnnotationTyping
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem TypedAnnotationSpine.anonymousBodyTranslation {env : VEnv} {universes : List Name}
    {context : VLCtx} {source body : Expr} {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx source semantic level)
    (envWF : env.WF) (definitions : CanonicalAnnotationDefinitions env)
    (contextWF : context.WF env universes.length)
    (bodyTranslation : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled, TrExprS env universes context (AddInductive.peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam semantic) :: context)
        ((none, .vlam peeled) :: context) ∧
      TrExpr env universes ((none, .vlam peeled) :: context) body bodySemantic := by
  obtain ⟨peeled, peeledTranslation, domainEquality⟩ :=
    spine.peelTypeAnnotations definitions envWF.ordered
  have contextEquality : VLCtx.IsDefEq env universes.length
      ((none, .vlam semantic) :: context) ((none, .vlam peeled) :: context) :=
    .cons (.refl envWF.ordered contextWF) nofun (.vlam domainEquality)
  exact ⟨peeled, peeledTranslation, domainEquality, contextEquality,
    bodyTranslation.defeqDFC' envWF contextEquality⟩

theorem TypedAnnotationSpine.anonymousBodyStrongTranslation {env : VEnv}
    {universes : List Name} {context : VLCtx} {source body : Expr}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx source semantic level)
    (envWF : env.WF) (definitions : CanonicalAnnotationDefinitions env)
    (contextWF : context.WF env universes.length)
    (bodyTranslation : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled converted,
      TrExprS env universes context (AddInductive.peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam semantic) :: context)
        ((none, .vlam peeled) :: context) ∧
      TrExprS env universes ((none, .vlam peeled) :: context) body converted ∧
      env.IsDefEqU universes.length (peeled :: context.toCtx) converted bodySemantic := by
  obtain ⟨peeled, peeledTranslation, domainEquality, contextEquality,
    converted, convertedTranslation, convertedEquality⟩ :=
      spine.anonymousBodyTranslation envWF definitions contextWF bodyTranslation
  exact ⟨peeled, converted, peeledTranslation, domainEquality, contextEquality,
    convertedTranslation, convertedEquality⟩

end Lean4Lean.AddInductive

namespace Lean4Lean
open Lean

theorem TrExpr.openFreshFVar {env : VEnv} {universes : List Name} {context : VLCtx}
    {fvar : FVarId} {dependencies : List FVarId} {declaration : VLocalDecl}
    {body : Expr} {semantic : VExpr}
    (translation : TrExpr env universes ((none, declaration) :: context) body semantic)
    (ordered : env.Ordered)
    (pushedWF : VLCtx.WF env universes.length
      ((some (fvar, dependencies), declaration) :: context)) :
    TrExpr env universes ((some (fvar, dependencies), declaration) :: context)
      (body.instantiate1' (.fvar fvar)) semantic := by
  obtain ⟨translated, bodyTranslation, equality⟩ := translation
  refine ⟨translated, bodyTranslation.inst_fvar ordered pushedWF, ?_⟩
  cases declaration <;> exact equality

end Lean4Lean
