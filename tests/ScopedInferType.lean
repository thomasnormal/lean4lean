import Lean4Lean.Verify.TypeChecker.ScopedInferType
import Lean.Util.CollectAxioms

namespace ScopedInferTypeTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

example {context : VContext} {state : VState} {expression : Expr} {inferOnly : Bool}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (Inner.inferType expression inferOnly).ScopeWF context state (fun type _ =>
      ∃ expression' semanticType, context.TrTyping expression type expression' semanticType) :=
  Inner.inferType.scopeWF freeVariables translated

example {context : VContext} {state : VState} {expression : Expr}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (Inner.inferType expression false).ScopeWF context state (fun type _ =>
      ∃ expression' semanticType, context.TrTyping expression type expression' semanticType) :=
  Inner.checkType.scopeWF freeVariables

example {context : VContext} {state : VState} {expression : Expr} {inferOnly : Bool}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (Inner.inferLambda expression inferOnly).ScopeWF context state (fun type _ =>
      ∃ semantic semanticType, context.TrTyping expression type semantic semanticType) :=
  Inner.inferLambda.scopeWF freeVariables translated

example {context : VContext} {state : VState} {outerName innerName : Name}
    {outerDomain innerDomain body : Expr} {outerBinder innerBinder : BinderInfo}
    (freeVariables : (Expr.lam outerName outerDomain
      (.lam innerName innerDomain body innerBinder) outerBinder).FVarsIn (· ∈ context.vlctx.fvars)) :
    (Inner.inferLambda (.lam outerName outerDomain
      (.lam innerName innerDomain body innerBinder) outerBinder) false).ScopeWF context state
      (fun type _ => ∃ semantic semanticType, context.TrTyping
        (.lam outerName outerDomain (.lam innerName innerDomain body innerBinder) outerBinder)
        type semantic semanticType) :=
  Inner.inferLambda.scopeWF freeVariables (by simp)

example {context : VContext} {state : VState} {outerName innerName : Name}
    {outerDomain innerDomain body : Expr} {outerBinder innerBinder : BinderInfo} {semantic : VExpr}
    (translated : context.TrExprS
      (.lam outerName outerDomain (.lam innerName innerDomain body innerBinder) outerBinder) semantic) :
    (Inner.inferLambda (.lam outerName outerDomain
      (.lam innerName innerDomain body innerBinder) outerBinder) true).ScopeWF context state
      (fun type _ => ∃ semantic semanticType, context.TrTyping
        (.lam outerName outerDomain (.lam innerName innerDomain body innerBinder) outerBinder)
        type semantic semanticType) :=
  Inner.inferLambda.scopeWF translated.fvarsIn (fun _ => ⟨_, translated⟩)

example {context : VContext} {state : VState} {expression : Expr} {inferOnly : Bool}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (Inner.inferForall expression inferOnly).ScopeWF context state (fun type _ =>
      ∃ semantic level, context.TrTyping expression type semantic (.sort level)) :=
  Inner.inferForall.scopeWF freeVariables translated

example {context : VContext} {state : VState} {outerName innerName : Name}
    {outerDomain innerDomain body : Expr} {outerBinder innerBinder : BinderInfo}
    (freeVariables : (Expr.forallE outerName outerDomain
      (.forallE innerName innerDomain body innerBinder) outerBinder).FVarsIn (· ∈ context.vlctx.fvars)) :
    (Inner.inferForall (.forallE outerName outerDomain
      (.forallE innerName innerDomain body innerBinder) outerBinder) false).ScopeWF context state
      (fun type _ => ∃ semantic level, context.TrTyping
        (.forallE outerName outerDomain (.forallE innerName innerDomain body innerBinder) outerBinder)
        type semantic (.sort level)) :=
  Inner.inferForall.scopeWF freeVariables (by simp)

example {context : VContext} {state : VState} {outerName innerName : Name}
    {outerDomain innerDomain body : Expr} {outerBinder innerBinder : BinderInfo} {semantic : VExpr}
    (translated : context.TrExprS
      (.forallE outerName outerDomain (.forallE innerName innerDomain body innerBinder) outerBinder) semantic) :
    (Inner.inferForall (.forallE outerName outerDomain
      (.forallE innerName innerDomain body innerBinder) outerBinder) true).ScopeWF context state
      (fun type _ => ∃ semantic level, context.TrTyping
        (.forallE outerName outerDomain (.forallE innerName innerDomain body innerBinder) outerBinder)
        type semantic (.sort level)) :=
  Inner.inferForall.scopeWF translated.fvarsIn (fun _ => ⟨_, translated⟩)

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : context.TrExprS expression semantic) :
    (Inner.inferLet expression true).ScopeWF context state (fun type _ =>
      ∃ semantic' semanticType, context.TrTyping expression type semantic' semanticType) :=
  Inner.inferLet.scopeWF_inferOnly freeVariables translated

example {context : VContext} {state : VState} {expression : Expr}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (Inner.inferLet expression false).ScopeWF context state (fun type _ =>
      ∃ semantic' semanticType, context.TrTyping expression type semantic' semanticType) :=
  Inner.inferLet.scopeWF freeVariables

example {context : VContext} {state : VState} {name : Name}
    {domain value body : Expr} {nondependent : Bool} :
    (hfree : (Expr.letE name domain value body nondependent).FVarsIn
      (· ∈ context.vlctx.fvars)) →
    (Inner.inferLet (.letE name domain value body nondependent) false).ScopeWF context state
      (fun type _ => ∃ semantic' semanticType, context.TrTyping
        (.letE name domain value body nondependent) type semantic' semanticType) :=
  fun hfree => Inner.inferLet.scopeWF hfree

example {context : VContext} {state : VState} {first second : Expr}
    {firstSemantic secondSemantic : VExpr}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqCore first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqCore.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState} {first second : Expr}
    {firstSemantic secondSemantic : VExpr}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEq first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEq.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (Inner.inferApp expression).ScopeWF context state
      (fun type _ => ∃ typeSemantic, context.TrTyping expression type semantic typeSemantic) :=
  Inner.inferApp.scopeWF translated

example {context : VContext} {state : VState} {name : Name}
    {domain value body : Expr} {nondependent : Bool} {semantic : VExpr}
    (translated : context.TrExprS (.letE name domain value body nondependent) semantic) :
    (Inner.inferLet (.letE name domain value body nondependent) true).ScopeWF context state
      (fun type _ => ∃ semantic' semanticType, context.TrTyping
        (.letE name domain value body nondependent) type semantic' semanticType) :=
  Inner.inferLet.scopeWF_inferOnly translated.fvarsIn translated

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

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (Inner.isProp expression).ScopeWF context state
      (fun result _ => result → context.HasType semantic (.sort .zero)) :=
  Inner.isProp.scopeWF translated

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedInferType
    | throwError "scoped inference module absent"
  let inferenceBaseline ← collectAxioms ``Inner.inferLambda.WF
  let forallBaseline ← collectAxioms ``Inner.inferForall.WF
  let normalizerBaseline ← collectAxioms ``Inner.whnf'.WF
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.Expr.instantiateRevRange_eq, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  logInfo m!"existing semantic lambda baseline: {repr inferenceBaseline}"
  logInfo m!"existing semantic forall baseline: {repr forallBaseline}"
  logInfo m!"existing semantic full-normalizer baseline: {repr normalizerBaseline}"
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "owned scoped inference axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless inferenceBaseline.contains dependency || forallBaseline.contains dependency ||
            normalizerBaseline.contains dependency ||
            native.contains dependency do
          throwError "unexpected scoped inference dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned scoped inference declarations audited against existing semantic lambda/forall/WHNF baselines and native scope foundations; inherited admissions remain explicitly visible; no owned axioms"

end ScopedInferTypeTest
