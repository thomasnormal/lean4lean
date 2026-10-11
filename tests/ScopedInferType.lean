import Lean4Lean.Verify.TypeChecker.ScopedInferType

namespace ScopedInferTypeTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

example {context : VContext} {state : VState} (valid : state.WF context) :
    state.next.WF context :=
  TypeChecker.VState.WF.next valid

example {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) :
    HeadScopeCacheWF locals { state with ngen := state.ngen.next } :=
  TypeChecker.HeadScopeCacheWF.next stable

example {context : VContext} {state : VState} {continuation : Name → RecM Result}
    {post : Result → VState → Prop}
    (valid : ∀ name, (continuation name).ScopeWF context state.next post) :
    (withFreshId continuation).ScopeWF context state post :=
  TypeChecker.RecM.ScopeWF.withFreshId valid

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
