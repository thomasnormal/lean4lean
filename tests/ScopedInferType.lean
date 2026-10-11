import Lean4Lean.Verify.TypeChecker.ScopedInferType

namespace ScopedInferTypeTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

example {context : VContext} {state : VState} (valid : state.WF context) :
    state.next.WF context :=
  TypeChecker.VState.WF.next valid

example {context : VContext} {mlctx : MLCtx} [context.MLCWF mlctx]
    {state : VState} {name : Name} {domain : Expr} {domain' : VExpr} {binder : BinderInfo}
    {extendedWF : context.MLCWF
      (mlctx.vlam ⟨state.ngen.curr⟩ name domain domain' binder)}
    (valid : state.WF (context.withMLC mlctx))
    (domainTranslation : (context.withMLC mlctx).TrExprS domain domain')
    (domainType : (context.withMLC mlctx).IsType domain') :
    state.next.WF
      (context.withMLC
        (mlctx.vlam ⟨state.ngen.curr⟩ name domain domain' binder) (wf := extendedWF)) :=
  TypeChecker.VState.WF.mkLocalDecl valid domainTranslation domainType

example {context : VContext} {mlctx : MLCtx} [context.MLCWF mlctx]
    {state : VState} {name : Name} {type value : Expr} {type' value' : VExpr}
    {extendedWF : context.MLCWF
      (mlctx.vlet ⟨state.ngen.curr⟩ name type value type' value')}
    (valid : state.WF (context.withMLC mlctx))
    (typeTranslation : (context.withMLC mlctx).TrExprS type type')
    (valueTranslation : (context.withMLC mlctx).TrExprS value value')
    (valueType : (context.withMLC mlctx).HasType value' type') :
    state.next.WF
      (context.withMLC
        (mlctx.vlet ⟨state.ngen.curr⟩ name type value type' value') (wf := extendedWF)) :=
  TypeChecker.VState.WF.mkLetDecl valid typeTranslation valueTranslation valueType

example {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) :
    HeadScopeCacheWF locals { state with ngen := state.ngen.next } :=
  TypeChecker.HeadScopeCacheWF.next stable

example {context : VContext} {state : VState} {continuation : Name → RecM Result}
    {post : Result → VState → Prop}
    (valid : ∀ name, (continuation name).ScopeWF context state.next post) :
    (withFreshId continuation).ScopeWF context state post :=
  TypeChecker.RecM.ScopeWF.withFreshId valid

example {context : VContext} {mlctx : MLCtx} [context.MLCWF mlctx]
    {state : VState} {continuation : Expr → RecM Result}
    {post : Result → VState → Prop} {name : Name} {domain : Expr} {domain' : VExpr}
    {binder : BinderInfo}
    {extendedWF : context.MLCWF
      (mlctx.vlam ⟨state.ngen.curr⟩ name domain domain' binder)}
    (domainTranslation : (context.withMLC mlctx).TrExprS domain domain')
    (domainType : (context.withMLC mlctx).IsType domain')
    (valid : (continuation (.fvar ⟨state.ngen.curr⟩)).ScopeWF
      (context.withMLC
        (mlctx.vlam ⟨state.ngen.curr⟩ name domain domain' binder) (wf := extendedWF))
      state.next post) :
    (withLocalDecl name binder domain continuation).ScopeWF
      (context.withMLC mlctx) state post :=
  TypeChecker.RecM.ScopeWF.withLocalDecl domainTranslation domainType valid

example {context : VContext} {mlctx : MLCtx} [context.MLCWF mlctx]
    {state : VState} {continuation : Expr → RecM Result}
    {post : Result → VState → Prop} {name : Name} {type value : Expr}
    {type' value' : VExpr}
    {extendedWF : context.MLCWF
      (mlctx.vlet ⟨state.ngen.curr⟩ name type value type' value')}
    (typeTranslation : (context.withMLC mlctx).TrExprS type type')
    (valueTranslation : (context.withMLC mlctx).TrExprS value value')
    (valueType : (context.withMLC mlctx).HasType value' type')
    (valid : (continuation (.fvar ⟨state.ngen.curr⟩)).ScopeWF
      (context.withMLC
        (mlctx.vlet ⟨state.ngen.curr⟩ name type value type' value') (wf := extendedWF))
      state.next post) :
    (withLetDecl name type value continuation).ScopeWF
      (context.withMLC mlctx) state post :=
  TypeChecker.RecM.ScopeWF.withLetDecl typeTranslation valueTranslation valueType valid

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (Inner.ensureSortCore expression expression).ScopeWF context state (fun result _ =>
      (∃ level, result = .sort level) ∧ context.TrExpr result semantic ∧
        context.FVarsBelow expression result) :=
  Inner.ensureSortCore.scopeWF translated

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (Inner.ensureForallCore expression expression).ScopeWF context state (fun result _ =>
      context.FVarsBelow expression result ∧ context.TrExpr result semantic ∧
        ∃ name domain body binder, result = .forallE name domain body binder) :=
  Inner.ensureForallCore.scopeWF translated

example {context : VContext} {state : VState} {name : FVarId} :
    RecM.ScopeWF context state
      (readThe Context >>= fun context => liftM (Inner.inferFVar context name))
      (fun type _ => ∃ expression semanticType,
        context.TrTyping (.fvar name) type expression semanticType) :=
  Inner.inferFVar.scopeWF

example {context : VContext} {state : VState} {level : Level}
    (valid : level.hasMVar' = false) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context => liftM (Inner.checkLevel context level))
      (fun _ _ => ∃ level', VLevel.ofLevel context.lparams level = some level') :=
  Inner.checkLevel.scopeWF valid

example {context : VContext} {state : VState} {name : Name} :
    RecM.ScopeWF context state
      ((liftM TypeChecker.getEnv : RecM Kernel.Environment) >>= fun environment =>
        liftM (environment.get name))
      (fun info _ => context.env.find? name = some info) :=
  Inner.envGet.scopeWF

example {context : VContext} {state : VState} {name : Name} {levels : List Level}
    {inferOnly : Bool}
    (validLevels : ∀ level ∈ levels, level.hasMVar' = false)
    (validInference : inferOnly = true → ∃ expression,
      context.TrExprS (.const name levels) expression) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context =>
        liftM (Inner.inferConstant context name levels inferOnly))
      (fun type _ => ∃ expression semanticType,
        context.TrTyping (.const name levels) type expression semanticType) :=
  Inner.inferConstant.scopeWF validLevels validInference

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedInferType
    | throwError "scoped inference module absent"
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "owned scoped inference axiom {name}"
      owned := owned + 1
  logInfo m!"{owned} scoped inference contracts are theorem-backed; no owned axioms"

end ScopedInferTypeTest
