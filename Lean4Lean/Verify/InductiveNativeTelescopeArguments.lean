import Lean4Lean.Verify.InductiveRecursorApplicationTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

/-- Individual arguments checked against the successively instantiated native
   telescope.  The neutral relation is shared by recursor-call and generated
   rule-body consumers; its operational lemmas remain in the call module. -/
inductive NativeTelescopeArguments (env : VEnv) (universes : List Name) (model : MLCtx) :
    Expr → List Expr → Expr → Prop where
  | nil : NativeTelescopeArguments env universes model source [] source
  | cons {name : Name} {domain body argument : Expr} {binder : BinderInfo}
      {arguments : List Expr} {terminal : Expr} {domainSemantic argumentSemantic : VExpr}
      (domainTranslated : TrExprS env universes model.vlctx domain domainSemantic)
      (argumentTranslated : TrExprS env universes model.vlctx argument argumentSemantic)
      (argumentTyped : env.HasType universes.length model.vlctx.toCtx
        argumentSemantic domainSemantic)
      (remaining : NativeTelescopeArguments env universes model
        (body.instantiate1' argument) arguments terminal) :
      NativeTelescopeArguments env universes model (.forallE name domain body binder)
        (argument :: arguments) terminal

end Lean4Lean.AddInductive
