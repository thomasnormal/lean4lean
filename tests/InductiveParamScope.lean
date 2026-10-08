import Lean4Lean.Verify.InductiveParamScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamScopeTest

example : ContextNoLooseBVars {} := ContextNoLooseBVars.empty

example (lctx : LocalContext) (hscope : ContextNoLooseBVars lctx)
    (fvar : FVarId) (name : Name) (domain : Expr) (bi : BinderInfo)
    (hdomain : domain.looseBVarRange' = 0) :
    ContextNoLooseBVars (lctx.mkLocalDecl fvar name domain bi) :=
  hscope.mkLocalDecl fvar name domain bi hdomain

example (body : Expr) (fvar : FVarId) (hbody : body.looseBVarRange' ≤ 1) :
    (body.instantiate1 (.fvar fvar)).looseBVarRange' = 0 :=
  instantiate1_fvar_noLooseBVars body fvar hbody

example (type : Expr) (hscope : type.looseBVarRange' = 0) : type.hasLooseBVars = false :=
  noLooseBVars_flag type hscope

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hscope : ContextNoLooseBVars lctx)
    (index : Nat) (hindex : index < params.size) :
    (lctx.getFVar! params[index]).type.looseBVarRange' = 0 :=
  hvalid.parameterScopeAt hscope index hindex

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment) (state : State)
    (post : α × State → Prop) (htype : type.looseBVarRange' = 0)
    (hnext : ∀ lctx remainder params state', ContextNoLooseBVars lctx →
      remainder.looseBVarRange' = 0 → (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.noLooseBVars type numParams next env state post htype hnext

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ContextNoLooseBVars result.1.1 ∧
        result.1.2.1.looseBVarRange' = 0 :=
  withParams.getScope type numParams env state htype

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamValidity numParams result.1.1 result.1.2.2 ∧
        ContextNoLooseBVars result.1.1 ∧ result.1.2.1.looseBVarRange' = 0 :=
  withParams.getScopedContext type numParams env state htype

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (htype : type.looseBVarRange' = 0) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result =>
        (∀ decl ∈ result.1.1.toList, decl.type.hasLooseBVars = false) ∧
          result.1.2.1.hasLooseBVars = false :=
  withParams.getScopeFlags type numParams env state htype

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Kernel.Environment) (state : State)
    (hscope : ContextNoLooseBVars lctx) :
    (ElimNestedInductive.run.loop numParams lctx params index fuel env state).WF fun result =>
      ContextNoLooseBVars result.1.lctx :=
  ElimNestedInductive.run.loop.contextScope numParams lctx params index fuel env state hscope

example (fuel numParams : Nat) (first : InductiveType) (rest : List InductiveType)
    (env : Kernel.Environment) (state : State) (hfirst : first.type.looseBVarRange' = 0) :
    (ElimNestedInductive.run fuel numParams (first :: rest) env state).WF fun result =>
      ContextNoLooseBVars result.1.lctx :=
  ElimNestedInductive.run.contextScope fuel numParams first rest env state hfirst

example (fuel numParams : Nat) (first : InductiveType) (rest : List InductiveType)
    (env : Kernel.Environment) (state : State) (hfirst : first.type.looseBVarRange' = 0) :
    (StateT.run' (ElimNestedInductive.run fuel numParams (first :: rest) env) state).WF fun result =>
      ContextNoLooseBVars result.lctx :=
  ElimNestedInductive.run.contextScope_run' fuel numParams first rest env state hfirst

example (fuel numParams : Nat) (first : InductiveType) (rest : List InductiveType)
    (env : Kernel.Environment) (state : State) (hfirst : first.type.looseBVarRange' = 0) :
    (ElimNestedInductive.run fuel numParams (first :: rest) env state).WF fun result =>
      ∀ decl ∈ result.1.lctx.toList, decl.type.hasLooseBVars = false :=
  ElimNestedInductive.run.contextScopeFlags fuel numParams first rest env state hfirst

example (type : Expr) (env : Kernel.Environment) (state : State)
    (htype : type.looseBVarRange' = 0) :
    (withParams type 0 (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ContextNoLooseBVars result.1.1 ∧
        result.1.2.1.looseBVarRange' = 0 :=
  withParams.getScope type 0 env state htype

example : (Expr.bvar 0).looseBVarRange' ≠ 0 := by decide

example (mvar : MVarId) : (Expr.mvar mvar).looseBVarRange' = 0 ∧ ¬(Expr.mvar mvar).Closed := by
  exact ⟨rfl, fun hclosed => hclosed⟩

example (env : Kernel.Environment) (state : State) :
    (withParams (.forallE `captured (.sort (.succ .zero)) (.fvar ⟨state.ngen.curr⟩) .default) 1
      (fun lctx remainder params => pure (lctx, remainder, params)) env state).WF fun result =>
        ContextNoLooseBVars result.1.1 ∧ result.1.2.1.looseBVarRange' = 0 :=
  withParams.getScope _ 1 env state rfl

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hscope : ContextNoLooseBVars lctx)
    (index : Nat) (hindex : index < params.size) :
    (lctx.getFVar! params[index]).type.hasLooseBVars = false :=
  noLooseBVars_flag _ (hvalid.parameterScopeAt hscope index hindex)

private def parameterBinders (numParams : Nat) (body : Expr) : Expr :=
  let sortType := Expr.sort (.succ .zero)
  (List.range numParams).foldr (fun index result =>
    let domain := if index = 0 then sortType else .bvar (index - 1)
    let name := if index % 2 = 0 then Name.anonymous else `repeated
    let bi := match index % 4 with
      | 0 => BinderInfo.implicit
      | 1 => .strictImplicit
      | 2 => .instImplicit
      | _ => .default
    Expr.forallE name domain result bi) body

private def parameterApp (numParams offset : Nat) : Expr :=
  mkAppN (.const `ScopeFamily []) ((List.range numParams).map fun index =>
    Expr.bvar (numParams - 1 - index + offset)).toArray

private def sourceTails (numParams : Nat) : List Expr :=
  let sortType := Expr.sort (.succ .zero)
  let dependent := parameterApp numParams 0
  let domain := if numParams = 0 then sortType else .bvar (numParams - 1)
  [sortType, .forallE `extra domain (parameterApp numParams 1) .instImplicit,
    .lam `extra domain (parameterApp numParams 1) .strictImplicit,
    .letE `extra domain dependent (parameterApp numParams 1) true,
    .mdata {} dependent, .proj `ScopePair 0 dependent,
    mkApp (.const `Wrapper []) dependent, .mvar ⟨`Unassigned⟩, .fvar ⟨`OutsideScope⟩]

private def checkContextScope (lctx : LocalContext) (params : Array Expr) : MetaM Unit := do
  let declarations := lctx.decls.toList.filterMap id
  unless declarations.length == params.size do
    throwError "scope fixture declaration count differs from its parameters"
  for decl in declarations do
    unless decl.type.looseBVarRange' == 0 && !decl.type.hasLooseBVars do
      throwError "extracted parameter domain contains a loose bound variable"
  for param in params do
    let some decl := lctx.findFVar? param
      | throwError "scoped parameter missing from concrete lookup"
    let actual := lctx.getFVar! param
    unless decl.type.looseBVarRange' == 0 && !decl.type.hasLooseBVars &&
        actual.type.looseBVarRange' == 0 && !actual.type.hasLooseBVars do
      throwError "parameter lookup/getter lost its domain scope"

private def checkExtraction (env : Kernel.Environment) (state : State)
    (numParams : Nat) (tail : Expr) : MetaM Unit := do
  let type := parameterBinders numParams tail
  unless type.looseBVarRange' == 0 && !type.hasLooseBVars do
    throwError "scope fixture source is not well-scoped"
  match withParams type numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected scoped-parameter extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    unless params.size == numParams && remainder.looseBVarRange' == 0 &&
        !remainder.hasLooseBVars do
      throwError "parameter extraction left a loose variable in the remainder"
    checkContextScope lctx params

private def checkIllScopedExtraction (env : Kernel.Environment) (state : State)
    (numParams : Nat) (looseDomain : Bool) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let type := if looseDomain then
    Expr.forallE `looseDomain (.bvar 0) (parameterBinders (numParams - 1) sortType) .default
    else parameterBinders numParams (.bvar numParams)
  unless type.looseBVarRange' != 0 && type.hasLooseBVars do
    throwError "ill-scoped boundary fixture accidentally satisfies the source premise"
  match withParams type numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "ill-scoped helper boundary unexpectedly rejects extraction"
  | .ok ((lctx, remainder, _), _) =>
    let violatesScope := if looseDomain then
      (lctx.decls.toList.filterMap id).any fun decl =>
        decl.type.looseBVarRange' != 0 && decl.type.hasLooseBVars
      else remainder.looseBVarRange' != 0 && remainder.hasLooseBVars
    unless violatesScope do
      throwError "missing source-scope premise failed to expose a loose domain/remainder"

private def checkCaptureBoundary (env : Kernel.Environment) (state : State) : MetaM Unit := do
  let type := Expr.forallE `captured (.sort (.succ .zero)) (.fvar ⟨state.ngen.curr⟩) .default
  match withParams type 1 (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected scoped source-capture extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    unless type.looseBVarRange' == 0 && remainder.looseBVarRange' == 0 &&
        lctx.mkForall params remainder != type do
      throwError "bound-variable scope unexpectedly guarantees source free-variable freshness"
    checkContextScope lctx params

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``ContextNoLooseBVars.empty, ``ElimNestedInductive.run.loop.contextScope] do
    audit theoremName []
  audit ``ContextNoLooseBVars.mkLocalDecl [``PersistentArray.toList'_push]
  audit ``instantiate1_fvar_noLooseBVars [``Expr.instantiate1_eq]
  audit ``noLooseBVars_flag [``Expr.looseBVarRange_eq]
  let structural := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  audit ``ParamValidity.parameterScopeAt structural
  let scopeInterfaces := [``PersistentArray.toList'_push, ``Expr.instantiate1_eq]
  for theoremName in [``withParams.noLooseBVars, ``withParams.getScope,
      ``ElimNestedInductive.run.contextScope, ``ElimNestedInductive.run.contextScope_run'] do
    audit theoremName scopeInterfaces
  audit ``withParams.getScopedContext (``Expr.instantiate1_eq :: structural)
  for theoremName in [``withParams.getScopeFlags, ``ElimNestedInductive.run.contextScopeFlags] do
    audit theoremName (``Expr.looseBVarRange_eq :: scopeInterfaces)
  let env := (← Lean.getEnv).toKernelEnv
  let states : List State := [
    { lvls := [], newTypes := #[] },
    { ngen := { namePrefix := `ScopeSeed, idx := 17 }, lvls := [.param `u], nextIdx := 7,
      nestedAux := #[(.const ``Nat [], `StoredAux)],
      newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] }]
  for state in states do
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      for tail in sourceTails numParams do
        checkExtraction env state numParams tail
    for numParams in [1, 2, 33] do
      checkIllScopedExtraction env state numParams false
      checkIllScopedExtraction env state numParams true
    checkCaptureBoundary env state

end InductiveParamScopeTest
