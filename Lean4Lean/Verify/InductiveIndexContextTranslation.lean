import Lean4Lean.Verify.InductiveAnnotationContext
import Lean4Lean.Verify.InductiveAnnotationTranslation
import Lean4Lean.Verify.InductiveIndexPositions
import Lean4Lean.Verify.LocalContext

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def peeledIndexVirtualContext (context : VLCtx) (id : FVarId) (domain : Expr)
    (peeled : VExpr) : VLCtx :=
  (some (id, (AddInductive.peelTypeAnnotations domain).fvarsList), .vlam peeled) :: context

def PeeledIndexOpening (env : VEnv) (universes : List Name) (ctx : Context)
    (context : VLCtx) (name : Name) (domain body : Expr) (bi : BinderInfo)
    (semantic bodySemantic : VExpr) (level : VLevel) (peeled : VExpr) : Prop :=
  TrExprS env universes context (AddInductive.peelTypeAnnotations domain) peeled ∧
  env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
  TrLCtx env universes (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)).lctx
    (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled) ∧
  TrExpr env universes (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled)
    (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) bodySemantic ∧
  BinderPositionedAt (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain))
    (.fvar ⟨ctx.ngen.curr⟩) name (AddInductive.peelTypeAnnotations domain) bi ctx.lctx.decls.size ∧
  ctx.RecursorScopeFrame (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain))

theorem translatedIndexContextPush {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain : Expr}
    {bi : BinderInfo} {peeled : VExpr} {level : VLevel}
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (AddInductive.peelTypeAnnotations domain) peeled)
    (typed : env.HasType universes.length context.toCtx peeled (.sort level)) :
    TrLCtx env universes (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)).lctx
      (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled) :=
  correspondence.mkLocalDecl (reserved.fresh correspondence.1) translated ⟨level, typed⟩

theorem TypedAnnotationSpine.indexContextTranslation {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx domain semantic level)
    (envWF : env.WF) (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (bodyTranslated : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled,
      TrExprS env universes context (AddInductive.peelTypeAnnotations domain) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      TrLCtx env universes (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)).lctx
        (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled) ∧
      TrExpr env universes (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled)
        (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) bodySemantic ∧
      BinderPositionedAt (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain))
        (.fvar ⟨ctx.ngen.curr⟩) name (AddInductive.peelTypeAnnotations domain) bi ctx.lctx.decls.size ∧
      ctx.RecursorScopeFrame (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)) := by
  obtain ⟨peeled, peeledTranslated, domainEquality, _, convertedBody⟩ :=
    spine.anonymousBodyTranslation envWF definitions correspondence.wf bodyTranslated
  have nextCorrespondence := translatedIndexContextPush (name := name) (bi := bi)
    correspondence reserved peeledTranslated domainEquality.hasType.2
  have openedBody : TrExpr env universes
      (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled)
      (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) bodySemantic := by
    rw [Expr.instantiate1_eq]
    exact convertedBody.openFreshFVar envWF.ordered nextCorrespondence.wf
  exact ⟨peeled, peeledTranslated, domainEquality, nextCorrespondence, openedBody,
    newlyAllocatedBinderPositioned ctx name domain bi correspondence.1 reserved,
    Context.RecursorScopeFrame.push ctx correspondence.1 reserved name bi (AddInductive.peelTypeAnnotations domain)⟩

theorem translatedIndexContext_ofDomain {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (uniform : UniformAnnotationUniverse universes domain level)
    (domainTranslated : TrExprS env universes context domain semantic)
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (bodyTranslated : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled,
      TrExprS env universes context (AddInductive.peelTypeAnnotations domain) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      TrLCtx env universes (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)).lctx
        (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled) ∧
      TrExpr env universes (peeledIndexVirtualContext context ⟨ctx.ngen.curr⟩ domain peeled)
        (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) bodySemantic ∧
      BinderPositionedAt (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain))
        (.fvar ⟨ctx.ngen.curr⟩) name (AddInductive.peelTypeAnnotations domain) bi ctx.lctx.decls.size ∧
      ctx.RecursorScopeFrame (recursorIndexContext ctx name bi (AddInductive.peelTypeAnnotations domain)) :=
  (TypedAnnotationSpine.ofTrExprS envWF correspondence.wf.toCtx constants uniform
    domainTranslated domainTyped).indexContextTranslation envWF definitions correspondence
      reserved bodyTranslated

theorem TypedAnnotationSpine.nativeIndexOpening {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx domain semantic level)
    (envWF : env.WF) (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (bodyTranslated : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled, PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled :=
  spine.indexContextTranslation envWF definitions correspondence reserved bodyTranslated

end Lean4Lean.AddInductive
