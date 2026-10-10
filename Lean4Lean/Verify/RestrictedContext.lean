import Lean4Lean.Verify.StagedLeaves

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

structure RestrictedContext (safety : DefinitionSafety) (env : Environment) (venv : VEnv) where
  checker : CheckerEnv safety env venv
  hasPrimitives : venv.HasPrimitives
  safePrimitives : NativePrimitiveSafety env
  lparams : List Name
  scope : VLCtx
  scope_wf : scope.WF venv lparams.length
  noBV : scope.NoBV

namespace RestrictedContext

def emptyScope {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (checker : CheckerEnv safety env venv) (hasPrimitives : venv.HasPrimitives)
    (safePrimitives : NativePrimitiveSafety env) (lparams : List Name) :
    RestrictedContext safety env venv :=
  { checker, hasPrimitives, safePrimitives, lparams, scope := [], scope_wf := trivial, noBV := rfl }

def toContext {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv) : TypeChecker.Context :=
  { env, safety, lparams := c.lparams }

theorem inferConstant {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (hinfer : inferOnly = true →
      ∃ model, TrExprS venv c.lparams c.scope (.const name levels) model) :
    (TypeChecker.Inner.inferConstant c.toContext name levels inferOnly).WF fun result =>
      ∃ model type, TrTyping venv c.lparams c.scope (.const name levels) result model type :=
  TypeChecker.Inner.inferConstant.checker c.checker c.scope_wf c.noBV hlevels hinfer

theorem inferSort {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hlevel : VLevel.ofLevel c.lparams level = some translated) :
    TrTyping venv c.lparams c.scope (.sort level) (.sort level.succ)
      (.sort translated) (.sort translated.succ) :=
  TypeChecker.Inner.infer_sort.checker hlevel

theorem appExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hfunction : venv.HasType c.lparams.length c.scope.toCtx function'
      (.forallE domain' body'))
    (hargument : venv.HasType c.lparams.length c.scope.toCtx argument' domain')
    (hfunctionTr : TrExprS venv c.lparams c.scope function function')
    (hargumentTr : TrExprS venv c.lparams c.scope argument argument') :
    TrExprS venv c.lparams c.scope (.app function argument) (.app function' argument') :=
  .app hfunction hargument hfunctionTr hargumentTr

theorem forallExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hdomainType : venv.IsType c.lparams.length c.scope.toCtx domain')
    (hbodyType : venv.IsType c.lparams.length (domain' :: c.scope.toCtx) body')
    (hdomainTr : TrExprS venv c.lparams c.scope domain domain')
    (hbodyTr : TrExprS venv c.lparams ((none, .vlam domain') :: c.scope) body body') :
    TrExprS venv c.lparams c.scope
      (.forallE binder domain body binderInfo) (.forallE domain' body') :=
  .forallE hdomainType hbodyType hdomainTr hbodyTr

theorem lamExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (htype : venv.IsType c.lparams.length c.scope.toCtx type')
    (htypeTr : TrExprS venv c.lparams c.scope type type')
    (hbodyTr : TrExprS venv c.lparams ((none, .vlam type') :: c.scope) body body') :
    TrExprS venv c.lparams c.scope
      (.lam binder type body binderInfo) (.lam type' body') :=
  .lam htype htypeTr hbodyTr

theorem letExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hvalueType : venv.HasType c.lparams.length c.scope.toCtx value' type')
    (htypeTr : TrExprS venv c.lparams c.scope type type')
    (hvalueTr : TrExprS venv c.lparams c.scope value value')
    (hbodyTr : TrExprS venv c.lparams ((none, .vlet type' value') :: c.scope) body body') :
    TrExprS venv c.lparams c.scope
      (.letE binder type value body binderInfo) body' :=
  .letE hvalueType htypeTr hvalueTr hbodyTr

theorem litExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (hcontains : venv.ContainsLits literal)
    (hconstructorTr : TrExprS venv c.lparams c.scope literal.toConstructor translated) :
    TrExprS venv c.lparams c.scope (.lit literal) translated :=
  .lit hcontains hconstructorTr

theorem mdataExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (htr : TrExprS venv c.lparams c.scope expression translated) :
    TrExprS venv c.lparams c.scope (.mdata metadata expression) translated :=
  .mdata htr

theorem projExpr {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (c : RestrictedContext safety env venv)
    (htr : TrExprS venv c.lparams c.scope expression expression')
    (hproj : TrProj c.scope.toCtx structName index expression' translated) :
    TrExprS venv c.lparams c.scope (.proj structName index expression) translated :=
  .proj htr hproj

end RestrictedContext

def RestrictedContext.ofOrdinary
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (checker : CheckerEnv safety env venv) (hasPrimitives : venv.HasPrimitives)
    (safePrimitives : NativePrimitiveSafety env) (lparams : List Name) :
    RestrictedContext safety env venv :=
  RestrictedContext.emptyScope checker hasPrimitives safePrimitives lparams

end Lean4Lean
