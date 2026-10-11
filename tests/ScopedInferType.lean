import Lean4Lean.Verify.TypeChecker.ScopedInferType

namespace ScopedInferTypeTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

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
