import Lean4Lean.Verify.InductiveIndexContextTranslation
import Lean4Lean.Verify.InductiveTelescopeTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

theorem translatedForallIndexOpening {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi)
      (.forallE semantic bodySemantic))
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled, PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled := by
  cases translated with
  | forallE _ _ domainTranslated bodyTranslated =>
    exact translatedIndexContext_ofDomain envWF constants definitions correspondence reserved
      uniform domainTranslated domainTyped bodyTranslated

theorem translatedForallIndexOpening_ofIsType {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr}
    {bi : BinderInfo} {semantic : VExpr}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi) semantic) :
    ∃ semanticDomain bodySemantic level,
      semantic = .forallE semanticDomain bodySemantic ∧
      env.HasType universes.length context.toCtx semanticDomain (.sort level) ∧
      (UniformAnnotationUniverse universes domain level → ∃ peeled,
        PeeledIndexOpening env universes ctx context name domain body bi
          semanticDomain bodySemantic level peeled) := by
  obtain ⟨semanticDomain, bodySemantic, level, semanticEq, domainTranslated,
    domainTyped, bodyTranslated⟩ := translatedForallDomain translated
  exact ⟨semanticDomain, bodySemantic, level, semanticEq, domainTyped, fun uniform =>
    translatedIndexContext_ofDomain envWF constants definitions correspondence reserved
      uniform domainTranslated domainTyped bodyTranslated⟩

theorem withLocalDecl.indexOpeningTranslation {ResultType : Type}
    {env : VEnv} {universes : List Name} {context : VLCtx} {ctx : Context}
    {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi)
      (.forallE semantic bodySemantic))
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : ∀ peeled, PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled →
      (next (.fvar ⟨ctx.ngen.curr⟩) (recursorIndexContext ctx name bi (peelTypeAnnotations domain))).WF post) :
    (withLocalDecl name bi (peelTypeAnnotations domain) next ctx).WF post := by
  obtain ⟨peeled, receipt⟩ := translatedForallIndexOpening envWF constants definitions correspondence
    reserved translated domainTyped uniform
  exact nextWF peeled receipt

end Lean4Lean.AddInductive
