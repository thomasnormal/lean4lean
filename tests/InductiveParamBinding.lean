import Lean4Lean.Verify.InductiveParamBinding
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamBindingTest

example (type : Expr) (fvar : FVarId) (index depth : Nat) :
    AddInductive.declareConstructors.arity index (type.abstract1 fvar depth) =
      AddInductive.declareConstructors.arity index type :=
  arity_abstract1 type fvar index depth

example (decls : List LocalDecl) (params : Array Expr) (body : Expr) :
    AddInductive.declareConstructors.arity 0 (paramForall decls params body) =
      decls.length + AddInductive.declareConstructors.arity 0 (body.abstract params) :=
  paramForall.arity decls params body

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    lctx.mkForall params body = paramForall lctx.toList.reverse params body :=
  hvalid.mkForall_eq body

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    AddInductive.declareConstructors.arity 0 (lctx.mkForall params body) =
      numParams + AddInductive.declareConstructors.arity 0 body :=
  hvalid.mkForall_arity body

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    numParams ≤ AddInductive.declareConstructors.arity 0 (lctx.mkForall params body) :=
  hvalid.mkForall_arity_ge body

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) : ParamBinding numParams lctx params :=
  hvalid.binding

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamBinding numParams result.1.1 result.1.2.2 :=
  withParams.getBinding type numParams env state

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result =>
        AddInductive.declareConstructors.arity 0
          (result.1.1.mkForall result.1.2.2 result.1.2.1) =
            AddInductive.declareConstructors.arity 0 type :=
  withParams.getReabstractArity type numParams env state

example (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M Expr) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => do
      return lctx.mkForall params (← next lctx remainder params)) env state).WF fun result =>
        numParams ≤ AddInductive.declareConstructors.arity 0 result.1 :=
  withParams.mkForall_arity type numParams next env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.ParamBinding numParams :=
  ElimNestedInductive.run.paramBinding fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.ParamBinding numParams :=
  ElimNestedInductive.run.paramBinding_run' fuel numParams types env state

example : ParamBinding 0 {} #[] := ParamValidity.empty.binding

example (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity 0 lctx params) (body : Expr) : lctx.mkForall params body = body := by
  have hnil : lctx.toList = [] := List.eq_nil_of_length_eq_zero hvalid.context.length
  rw [hvalid.mkForall_eq, hnil]
  have hparams : params = #[] := Array.eq_empty_of_size_eq_zero hvalid.context.size
  simp only [List.reverse_nil, paramForall, List.foldr_nil, hparams]
  exact (Expr.abstract_eq body []).trans (Expr.abstractFVars_nil body 0)

example (ngen : NameGenerator) (name : Name) (domain body : Expr) (bi : BinderInfo) :
    (({} : LocalContext).mkLocalDecl ⟨ngen.curr⟩ name domain bi).mkForall
      #[.fvar ⟨ngen.curr⟩] body = .forallE name
        (domain.abstractRange 0 #[.fvar ⟨ngen.curr⟩]) (body.abstract #[.fvar ⟨ngen.curr⟩]) bi := by
  have hvalid := ParamValidity.empty.push_current (ContextReserved.empty ngen) name domain bi
  simpa [paramForall, LocalContext.mkLocalDecl_toList] using hvalid.mkForall_eq body

example (type : Expr) (numParams : Nat) (params : Array Expr)
    (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder args => do
      assert! args.size == numParams
      return lctx.mkForall args (← replaceAllNested lctx params args remainder)) env state).WF
        fun result => numParams ≤ AddInductive.declareConstructors.arity 0 result.1 := by
  simpa only [withParams.assert_size] using withParams.mkForall_arity type numParams
    (fun lctx remainder args => replaceAllNested lctx params args remainder) env state

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (name : Name) (domain body : Expr)
    (bi : BinderInfo) :
    AddInductive.declareConstructors.arity 0
      (lctx.mkForall params (.mdata {} (.forallE name domain body bi))) = numParams := by
  simpa [AddInductive.declareConstructors.arity] using
    hvalid.mkForall_arity (.mdata {} (.forallE name domain body bi))

private def sourceType (numParams numExtra : Nat) : Expr :=
  let sortType := Expr.sort (.succ .zero)
  (List.range (numParams + numExtra)).foldr (fun index body =>
    let domain := if index = 0 then sortType else .bvar (index - 1)
    let name := if index % 2 = 0 then Name.anonymous else `repeated
    let bi := match index % 4 with
      | 0 => BinderInfo.implicit
      | 1 => .strictImplicit
      | 2 => .instImplicit
      | _ => .default
    Expr.forallE name domain body bi) sortType

private def replacementBodies (params : Array Expr) : List Expr :=
  let sortType := Expr.sort (.succ .zero)
  let dependent := mkAppN (.const `BodyFamily []) params
  [.bvar 0, .fvar ⟨`OutsideParameter⟩, .mvar ⟨`Unassigned⟩, .sort .zero,
    .const ``Nat [], .lit (.natVal 5), dependent,
    .lam `inner sortType dependent .implicit,
    .forallE `inner sortType (.forallE `inner dependent dependent .default) .strictImplicit,
    .letE `inner sortType (.lit (.natVal 0)) dependent false,
    .mdata {} (.forallE `annotated sortType dependent .default), .proj `Pair 0 dependent]

private def checkBinding (lctx : LocalContext) (params : Array Expr) (body : Expr) : MetaM Unit := do
  let declarations := lctx.decls.toList.filterMap id
  let actual := lctx.mkForall params body
  let expected := paramForall declarations params body
  unless actual == expected && AddInductive.declareConstructors.arity 0 actual ==
      params.size + AddInductive.declareConstructors.arity 0 body do
    throwError "parameter re-abstraction mismatch: count={params.size}, body={repr body}, actual={repr actual}, expected={repr expected}"

private def checkExtraction (env : Kernel.Environment) (state : State)
    (numParams numExtra : Nat) : MetaM Unit := do
  let type := sourceType numParams numExtra
  match withParams type numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected parameter binding extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    unless params.size == numParams && lctx.mkForall params remainder == type do
      throwError "parameter binding failed its closed-source round trip"
    checkBinding lctx params remainder
    for body in replacementBodies params do
      checkBinding lctx params body

private def checkCaptureBoundary (env : Kernel.Environment) (state : State) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let type := Expr.forallE `captured sortType (.fvar ⟨state.ngen.curr⟩) .default
  match withParams type 1 (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected source-freshness boundary extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    let rebound := lctx.mkForall params remainder
    unless rebound != type && rebound == .forallE `captured sortType (.bvar 0) .default do
      throwError "source-freshness boundary failed to expose existing-free-variable capture"
    checkBinding lctx params remainder

private def checkUnscopedSource (env : Kernel.Environment) (state : State) : MetaM Unit := do
  let type := Expr.forallE `looseDomain (.bvar 0)
    (.forallE `later (.bvar 2) (.bvar 3) .instImplicit) .implicit
  match withParams type 2 (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected unscoped-source extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    checkBinding lctx params remainder
    for body in replacementBodies params do
      checkBinding lctx params body

private def checkLetBoundary (nondep : Bool) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let fvar : FVarId := ⟨`LetParameter⟩
  let lctx := ({} : LocalContext).mkLetDecl fvar `letParam sortType (.lit (.natVal 0)) nondep
  let rebound := lctx.mkForall #[.fvar fvar] sortType
  unless rebound == sortType && AddInductive.declareConstructors.arity 0 rebound == 0 do
    throwError "unused let boundary unexpectedly introduced a parameter forall"

private def checkAbstractionBoundary : MetaM Unit := do
  let fvar : FVarId := ⟨`AbstractionBoundary⟩
  let body := Expr.bvar 0
  let actual := body.abstract #[.fvar fvar]
  let modeled := body.abstractList [fvar]
  unless actual == .bvar 0 && modeled == .bvar 1 do
    throwError "loose-variable abstraction interface boundary changed"
  logInfo "loose-variable abstraction boundary: executable bvar 0, modeled bvar 1"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``arity_abstract1, ``paramForall.arity] do
    audit theoremName []
  let structural := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  audit ``ParamValidity.mkForall_eq structural
  let interfaces := ``Expr.abstract_eq :: structural
  for theoremName in [``ParamValidity.mkForall_arity,
      ``ParamValidity.mkForall_arity_ge, ``ParamValidity.binding, ``withParams.getBinding,
      ``withParams.mkForall_arity, ``ElimNestedInductive.run.paramBinding,
      ``ElimNestedInductive.run.paramBinding_run'] do
    audit theoremName interfaces
  audit ``withParams.getReabstractArity (``Expr.instantiate1_eq :: interfaces)
  let env := (← Lean.getEnv).toKernelEnv
  let states : List State := [
    { lvls := [], newTypes := #[] },
    { ngen := { namePrefix := `BindingSeed, idx := 17 }, lvls := [.param `u], nextIdx := 7,
      nestedAux := #[(.const ``Nat [], `StoredAux)],
      newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] }]
  for state in states do
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      for numExtra in [0, 1, 2] do
        checkExtraction env state numParams numExtra
    checkCaptureBoundary env state
    checkUnscopedSource env state
  checkLetBoundary false
  checkLetBoundary true
  checkAbstractionBoundary

end InductiveParamBindingTest
