import Lean4Lean.Verify.InductiveParamValidity
import Lean.Util.CollectAxioms

open Lean Lean4Lean
open Lean4Lean.ElimNestedInductive

namespace InductiveParamIndicesTest

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) :
    lctx.toList.reverse.map LocalDecl.index = List.range numParams :=
  hvalid.indices

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (index : Nat) (hindex : index < params.size) :
    ∃ decl, lctx.toList.reverse[index]? = some decl ∧ decl.index = index ∧
      decl.toExpr = params[index] ∧ decl.value? (allowNondep := true) = none ∧
      decl.kind = .default :=
  hvalid.declarationAt index hindex

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (index : Nat) (hindex : index < params.size) :
    ∃ decl, lctx.findFVar? params[index] = some decl ∧ decl.index = index ∧
      decl.toExpr = params[index] ∧ decl.value? (allowNondep := true) = none ∧
      decl.kind = .default :=
  hvalid.parameterLookupAt index hindex

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (index : Nat) (hindex : index < params.size) :
    (lctx.getFVar! params[index]).index = index :=
  hvalid.getFVar!_index index hindex

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) : IndexedParamLookup numParams lctx params :=
  hvalid.indexedLookup

example (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => IndexedParamLookup numParams result.1.1 result.1.2.2 :=
  withParams.getIndexedLookup type numParams env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (ElimNestedInductive.run fuel numParams types env state).WF fun result =>
      result.1.IndexedParamLookup numParams :=
  ElimNestedInductive.run.indexedLookup fuel numParams types env state

example (fuel numParams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : State) :
    (StateT.run' (ElimNestedInductive.run fuel numParams types env) state).WF fun result =>
      result.IndexedParamLookup numParams :=
  ElimNestedInductive.run.indexedLookup_run' fuel numParams types env state

example : IndexedParamLookup 0 {} #[] := ParamValidity.empty.indexedLookup

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hnonempty : 0 < params.size) :
    (lctx.getFVar! params[0]).index = 0 :=
  hvalid.getFVar!_index 0 hnonempty

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hpositive : 0 < numParams) :
    (lctx.getFVar! (params[numParams - 1]'(by have hsize := hvalid.context.size; omega))).index =
      numParams - 1 :=
  hvalid.getFVar!_index (numParams - 1) (by have hsize := hvalid.context.size; omega)

example (lctx : LocalContext) (fvar : FVarId) :
    ¬IndexedParamLookup 2 lctx #[Expr.fvar fvar, Expr.fvar fvar] := by
  intro hindexed
  rcases hindexed.2 0 (by simp) with ⟨first, hfirst, hfirstindex, _⟩
  rcases hindexed.2 1 (by simp) with ⟨second, hsecond, hsecondindex, _⟩
  have heq : first = second := Option.some.inj (hfirst.symm.trans hsecond)
  subst second
  omega

private def sourceType (numParams : Nat) : Expr :=
  let sortType := Expr.sort (.succ .zero)
  (List.range numParams).foldr (fun index body =>
    let domain := if index = 0 then sortType else .bvar (index - 1)
    let name := if index % 2 = 0 then Name.anonymous else `repeated
    let bi := match index % 4 with
      | 0 => BinderInfo.implicit
      | 1 => .strictImplicit
      | 2 => .instImplicit
      | _ => .default
    Expr.forallE name domain body bi) sortType

private def indexedAtRuntime (lctx : LocalContext) (params : Array Expr) : Bool :=
  params.toList.zipIdx.all fun (param, index) =>
    match lctx.findFVar? param with
    | some decl => decl.index == index && decl.toExpr == param && decl.kind == .default &&
        (decl.value? (allowNondep := true)).isNone && (lctx.getFVar! param).index == index
    | none => false

private def checkExtraction (env : Kernel.Environment) (state : State)
    (numParams : Nat) : MetaM Unit := do
  match withParams (sourceType numParams) numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected indexed-parameter extraction failure"
  | .ok ((lctx, _, params), _) =>
    let declarations := lctx.decls.toList.filterMap id
    unless params.size == numParams && declarations.length == numParams &&
        declarations.map LocalDecl.index == List.range numParams && indexedAtRuntime lctx params do
      throwError "incorrect chronological declaration or indexed parameter lookup"
    for (decl, index) in declarations.zipIdx do
      unless decl.toExpr == params[index]! && (lctx.getFVar! params[index]!).index == index do
        throwError "parameter getter index differs from its declaration position"
    if 2 ≤ numParams then
      unless !(indexedAtRuntime lctx params.reverse) do
        throwError "indexed lookup accepted a reversed parameter array"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``ParamValidity.indices, ``ParamValidity.declarationAt] do
    audit theoremName [``PersistentArray.toList'_push]
  for theoremName in [``ParamValidity.parameterLookupAt, ``ParamValidity.getFVar!_index,
      ``ParamValidity.indexedLookup, ``withParams.getIndexedLookup,
      ``ElimNestedInductive.run.indexedLookup, ``ElimNestedInductive.run.indexedLookup_run'] do
    audit theoremName [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
      ``PersistentHashMap.WF.toList'_insert]
  let env := (← Lean.getEnv).toKernelEnv
  let states : List State := [
    { lvls := [], newTypes := #[] },
    { ngen := { namePrefix := `IndexSeed, idx := 17 }, lvls := [.param `u], nextIdx := 7,
      nestedAux := #[(.const ``Nat [], `StoredAux)],
      newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] }]
  for state in states do
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      checkExtraction env state numParams

end InductiveParamIndicesTest
