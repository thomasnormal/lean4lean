import Lean4Lean.Verify.InductiveParamValidity
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamValidityTest

example (ngen : NameGenerator) : ContextReserved {} ngen := ContextReserved.empty ngen

example (lctx : LocalContext) (ngen : NameGenerator)
    (hreserved : ContextReserved lctx ngen) (hwf : lctx.WF) :
    lctx.find? ⟨ngen.curr⟩ = none :=
  hreserved.fresh hwf

example (lctx : LocalContext) (ngen : NameGenerator)
    (hreserved : ContextReserved lctx ngen) (name : Name) (domain : Expr) (bi : BinderInfo) :
    ContextReserved (lctx.mkLocalDecl ⟨ngen.curr⟩ name domain bi) ngen.next :=
  hreserved.push_current name domain bi

example : ParamValidity 0 {} #[] := ParamValidity.empty

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr) (ngen : NameGenerator)
    (hvalid : ParamValidity numParams lctx params) (hreserved : ContextReserved lctx ngen)
    (name : Name) (domain : Expr) (bi : BinderInfo) :
    ParamValidity (numParams + 1) (lctx.mkLocalDecl ⟨ngen.curr⟩ name domain bi)
      (params.push (.fvar ⟨ngen.curr⟩)) :=
  hvalid.push_current hreserved name domain bi

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) : params.toList.Nodup :=
  hvalid.nodup

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (decl : LocalDecl) (hdecl : decl ∈ lctx.toList) :
    lctx.find? decl.fvarId = some decl :=
  hvalid.find?_eq hdecl

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (fvar : FVarId)
    (hparam : Expr.fvar fvar ∈ params) :
    ∃ decl, lctx.find? fvar = some decl ∧ decl.toExpr = .fvar fvar ∧
      decl.value? (allowNondep := true) = none ∧ decl.kind = .default :=
  hvalid.parameterLookup hparam

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M α) (env : Kernel.Environment)
    (state : State) (post : α × State → Prop)
    (hnext : ∀ lctx remainder params state', ParamValidity numParams lctx params →
      ContextReserved lctx state'.ngen → (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.validContext type numParams next env state post hnext

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamValidity numParams result.1.1 result.1.2.2 ∧
        ContextReserved result.1.1 result.2.ngen :=
  withParams.getValidContext type numParams env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.ParamValidity numParams :=
  ElimNestedInductive.run.paramValidity fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result => result.1.lctx.WF :=
  ElimNestedInductive.run.contextWF fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      ∀ decl ∈ result.1.lctx.toList, result.1.lctx.find? decl.fvarId = some decl :=
  ElimNestedInductive.run.contextLookup fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.ParamValidity numParams :=
  ElimNestedInductive.run.paramValidity_run' fuel numParams types env state

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.2.2.toList.Nodup :=
  (withParams.getValidContext type numParams env state).mono fun _ hvalid => hvalid.1.nodup

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.find? ⟨result.2.ngen.curr⟩ = none :=
  (withParams.getValidContext type numParams env state).mono fun _ hvalid =>
    hvalid.2.fresh hvalid.1.wf

example (lctx : LocalContext) (fvar : FVarId) :
    ¬ParamValidity 2 lctx #[Expr.fvar fvar, Expr.fvar fvar] := by
  intro hvalid
  have hnodup := hvalid.nodup
  simp at hnodup

private def sourceType (numParams : Nat) : Expr :=
  let sortType := Expr.sort (.succ .zero)
  (List.range numParams).foldr (fun index body =>
    let domain := if index = 0 then sortType else .bvar (index - 1)
    Expr.forallE `repeated domain body .implicit) sortType

private def checkFreshParameters (initial final : State) (lctx : LocalContext)
    (params : Array Expr) : MetaM Unit := do
  unless params.toList.eraseDups.length == params.size &&
      final.ngen.namePrefix == initial.ngen.namePrefix &&
      final.ngen.idx == initial.ngen.idx + params.size &&
      (lctx.find? ⟨final.ngen.curr⟩).isNone do
    throwError "incorrect parameter distinctness, generator progress, or next-name freshness"
  for index in [:params.size] do
    let .fvar fvar := params[index]! | throwError "extracted parameter is not a free variable"
    unless fvar.name == .num initial.ngen.namePrefix (initial.ngen.idx + index) do
      throwError "unexpected fresh parameter identifier"
    let some decl := lctx.find? fvar | throwError "fresh parameter missing from concrete lookup"
    unless decl.index == index && decl.fvarId == fvar && decl.toExpr == params[index]! &&
        (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "incorrect fresh parameter lookup record"

private def checkExtraction (env : Kernel.Environment) (state : State)
    (numParams : Nat) (accepted : Bool) : MetaM Unit := do
  let requested := if accepted then numParams else numParams + 1
  match withParams (sourceType numParams) requested
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .ok ((lctx, _, params), final) =>
    unless accepted && params.size == requested && lctx.numIndices == requested do
      throwError "unexpected valid-context extraction success"
    checkFreshParameters state final lctx params
  | .error (.other message) =>
    unless !accepted && message ==
        "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected valid-context extraction rejection: {message}"
  | .error _ => throwError "unexpected valid-context extraction exception"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``ContextReserved.empty, ``ParamValidity.empty] do
    audit theoremName
  audit ``ContextReserved.push_current [``PersistentArray.toList'_push]
  for theoremName in [``ContextReserved.fresh, ``ParamValidity.push_current, ``ParamValidity.nodup,
      ``ParamValidity.find?_eq, ``ParamValidity.parameterLookup, ``withParams.validContext,
      ``withParams.getValidContext, ``ElimNestedInductive.run.paramValidity,
      ``ElimNestedInductive.run.contextWF, ``ElimNestedInductive.run.contextLookup,
      ``ElimNestedInductive.run.paramValidity_run'] do
    audit theoremName [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
      ``PersistentHashMap.WF.toList'_insert]
  let env := (← Lean.getEnv).toKernelEnv
  let generators : List NameGenerator := [
    {}, { namePrefix := `FreshnessSeed, idx := 17 },
    { namePrefix := Name.anonymous, idx := 19 },
    { namePrefix := `Nested.Scope.Parameters, idx := 1000003 }]
  for ngen in generators do
    let state : State := {
      ngen, lvls := [.param `u], nestedAux := #[(.const ``Nat [], `StoredAux)], nextIdx := 7,
      newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] }
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      checkExtraction env state numParams true
      checkExtraction env state numParams false

end InductiveParamValidityTest
