import Lean4Lean.Verify.ConstructorParams
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace ConstructorParamsTest

example (ctx : Context) (nparams : Nat) (types : Array InductiveType) (isUnsafe : Bool)
    (parent : Nat) (ctor : Name) (type : Expr) :
    (checkInductiveTypes nparams types (fun stats current =>
      (current.env.checkNoMVarNoFVar ctor type >>= fun _ =>
        checkConstructors.loop stats isUnsafe parent ctor type 0
          current.fuel.inductiveFuel current) >>= fun _ => pure stats) ctx).WF fun stats =>
            stats.params.size ≤ declareConstructors.arity 0 type :=
  checkInductiveTypes.checkedConstructorArity nparams types isUnsafe parent ctor type ctx

example (stats : InductiveStats) (type : Expr) (parent : Nat)
    (hvalid : isValidIndAppIdx stats type parent = true) :
    stats.params.size ≤ type.getAppArgs.size :=
  (isValidIndAppIdx.parameterMatches stats type parent hvalid).1

example (stats : InductiveStats) (type : Expr) (parent index : Nat)
    (hvalid : isValidIndAppIdx stats type parent = true) (hindex : index < stats.params.size) :
    (stats.params[index]! == type.getAppArgs[index]!) = true :=
  (isValidIndAppIdx.parameterMatches stats type parent hvalid).2 index hindex

example (stats : InductiveStats) (type : Expr) (parent : Nat)
    (hvalid : isValidIndAppIdx stats type parent = true) :
    ∀ index, stats.params.size ≤ index → index < type.getAppArgs.size →
      hasIndOcc stats.indConsts type.getAppArgs[index]! = false :=
  isValidIndAppIdx.indexNoIndOcc stats type parent hvalid

example (stats : InductiveStats) (isUnsafe : Bool) (parent : Nat) (ctor : Name)
    (type : Expr) (index fuel : Nat) (ctx : Context) :
    (checkConstructors.loop stats isUnsafe parent ctor type index fuel ctx).WF fun _ =>
      ∃ terminal, ConstructorSpine type terminal ∧
        isValidIndAppIdx stats terminal parent = true :=
  checkConstructors.loop_spine stats isUnsafe parent ctor type index fuel ctx

example (stats : InductiveStats) (type : Expr) (index parent : Nat)
    (hfvars : stats.ParamsAreFVars) (habsent : stats.RemainingParamsAbsent index type)
    (hvalid : isValidIndAppIdx stats type parent = true) : stats.params.size ≤ index :=
  habsent.validIndAppIdx hfvars hvalid

example (stats : InductiveStats) (isUnsafe : Bool) (parent : Nat) (ctor : Name)
    (type : Expr) (fuel : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (hclosed : FVarsIn (fun _ => False) type)
    (hcheck : checkConstructors.loop stats isUnsafe parent ctor type 0 fuel ctx = .ok ()) :
    stats.params.size ≤ declareConstructors.arity 0 type :=
  checkConstructors.loop_arity_of_noFVars stats isUnsafe parent ctor type fuel ctx
    hfvars hnodup hclosed _ hcheck

example (stats : InductiveStats) (isUnsafe : Bool) (parent : Nat) (ctor : Name)
    (type : Expr) (fuel : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup) :
    (ctx.env.checkNoMVarNoFVar ctor type >>= fun _ =>
      checkConstructors.loop stats isUnsafe parent ctor type 0 fuel ctx).WF fun _ =>
        stats.params.size ≤ declareConstructors.arity 0 type :=
  checkConstructors.checked_loop_arity stats isUnsafe parent ctor type fuel ctx hfvars hnodup

example (ctx : Context) (stats : InductiveStats) (type : Expr)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (hclosed : FVarsIn (fun _ => False) type) :
    (checkConstructors.loop stats false 0 `NoFuel type 0 0 ctx).WF fun _ =>
      stats.params.size ≤ declareConstructors.arity 0 type :=
  checkConstructors.loop_arity_of_noFVars stats false 0 `NoFuel type 0 ctx hfvars hnodup hclosed

private def sortType : Expr := .sort (.succ .zero)

private def param (name : Name) : Expr := .fvar ⟨name⟩

private def listConst : Expr := .const ``List [.succ .zero]

private def prodConst : Expr := .const ``Prod [.succ .zero, .succ .zero]

private def stats (head : Expr) (params : Array Expr) (indices : Nat := 0) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, indConsts := #[head], params,
  nindices := #[indices], isNotZero := true }

private def checkReturn (stats : InductiveStats) (type : Expr) (expected : Bool) : MetaM Unit := do
  unless isValidIndAppIdx stats type 0 == expected do
    throwError "incorrect inductive return-parameter check"

private def checkLoop (ctx : Context) (stats : InductiveStats) (type : Expr)
    (isUnsafe : Bool) (expected : Bool) (fuel : Nat := 16) : MetaM Unit := do
  unless (checkConstructors.loop stats isUnsafe 0 `Fixture type 0 fuel ctx).isOk == expected do
    throwError "incorrect constructor parameter-consumption outcome"
  if expected && !type.hasFVar && !type.hasMVar &&
      stats.params.toList.eraseDups.length == stats.params.size then
    unless declareConstructors.arity 0 type ≥ stats.params.size do
      throwError "successful distinct-parameter loop has too few raw binders"

private def checkCheckedArity (ctx : Context) (nparams : Nat) (type : Expr)
    (isUnsafe expected : Bool) : MetaM Unit := do
  let headerType := nparams.fold
    (fun _ _ body => Expr.forallE `parameter sortType body .default) sortType
  let headers : Array InductiveType := #[{ name := `CheckedType, type := headerType, ctors := [] }]
  let result := checkInductiveTypes nparams headers (fun stats current =>
    (current.env.checkNoMVarNoFVar `CheckedCtor type >>= fun _ =>
      checkConstructors.loop stats isUnsafe 0 `CheckedCtor type 0
        current.fuel.inductiveFuel current) >>= fun _ => pure stats) ctx
  unless result.isOk == expected do
    throwError "incorrect checked-parameter constructor-arity outcome"
  if let .ok stats := result then
    unless stats.params.size == nparams &&
        stats.params.toList.eraseDups.length == stats.params.size &&
        stats.params.size ≤ declareConstructors.arity 0 type do
      throwError "checked parameters failed distinctness or constructor arity"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        interfaces.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``isValidIndAppIdx.parameterMatches
  audit ``isValidIndAppIdx.indexNoIndOcc
  audit ``isValidIndAppIdx.parameterFVar [``Expr.eqv_eq]
  audit ``isValidIndAppIdx.parameterFVarsIn [``Expr.eqv_eq]
  audit ``InductiveStats.RemainingParamsAbsent.of_noFVars
  audit ``InductiveStats.RemainingParamsAbsent.mono
  audit ``InductiveStats.RemainingParamsAbsent.instantiate1 [``Expr.instantiate1_eq]
  audit ``InductiveStats.RemainingParamsAbsent.forallBody
  audit ``InductiveStats.RemainingParamsAbsent.consume_param [``Expr.instantiate1_eq]
  audit ``InductiveStats.RemainingParamsAbsent.validIndAppIdx [``Expr.eqv_eq]
  audit ``checkConstructors.loop_arity [``Expr.eqv_eq, ``Expr.instantiate1_eq]
  audit ``checkConstructors.loop_spine [``Expr.eqv_eq, ``Expr.instantiate1_eq]
  audit ``checkConstructors.loop_arity_of_noFVars [``Expr.eqv_eq, ``Expr.instantiate1_eq]
  audit ``checkConstructors.checked_loop_arity
    [``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq,
      ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``checkInductiveTypes.checkedConstructorArity
    [``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq,
      ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  let imported := (← Lean.getEnv).toKernelEnv
  let first := param `FirstParameter
  let second := param `SecondParameter
  let lctx := ({} : LocalContext).mkLocalDecl ⟨`FirstParameter⟩ `A sortType
    |>.mkLocalDecl ⟨`SecondParameter⟩ `B sortType
  let ctx : Context := {
    env := imported, lctx, lparams := [], safety := .safe, allowPrimitive := false }
  let natStats := stats (.const ``Nat []) #[]
  let listStats := stats listConst #[first]
  let prodStats := stats prodConst #[first, second]
  let indexed := stats prodConst #[first] 1
  checkReturn natStats (.const ``Nat []) true
  checkReturn listStats (.app listConst first) true
  checkReturn listStats listConst false
  checkReturn listStats (.app listConst second) false
  checkReturn listStats (.app listConst (.bvar 0)) false
  checkReturn prodStats (.mkAppList prodConst [first, second]) true
  checkReturn prodStats (.mkAppList prodConst [second, first]) false
  checkReturn prodStats (.mkAppList prodConst [first, first]) false
  checkReturn prodStats (.app prodConst first) false
  checkReturn indexed (.mkAppList prodConst [first, second]) true
  checkReturn indexed (.mkAppList prodConst [second, first]) false
  let listType := Expr.forallE `A sortType (.app listConst (.bvar 0)) .default
  let prodType := Expr.forallE `A sortType (.forallE `B sortType
    (.mkAppList prodConst [.bvar 1, .bvar 0]) .implicit) .default
  let fieldsType := Expr.forallE `A sortType (.forallE `B sortType
    (.forallE `value (.bvar 1) (.mkAppList prodConst [.bvar 2, .bvar 1]) .default)
      .strictImplicit) .default
  let missingSecond := Expr.forallE `A sortType
    (.mkAppList prodConst [.bvar 0, .bvar 0]) .default
  for isUnsafe in [false, true] do
    let ctx := { ctx with safety := if isUnsafe then .unsafe else .safe }
    checkLoop ctx natStats (.const ``Nat []) isUnsafe true
    checkLoop ctx natStats (.forallE `value (.const ``Nat []) (.const ``Nat []) .default)
      isUnsafe true
    checkLoop ctx listStats listType isUnsafe true
    checkLoop ctx prodStats prodType isUnsafe true
    checkLoop ctx prodStats fieldsType isUnsafe true
    checkLoop ctx prodStats missingSecond isUnsafe false
    checkLoop ctx listStats (.app listConst first) isUnsafe true
    checkLoop ctx listStats listType isUnsafe false 1
    checkLoop ctx prodStats prodType isUnsafe false 2
    checkLoop ctx prodStats fieldsType isUnsafe false 3
    checkLoop ctx natStats (.const ``Nat []) isUnsafe false 0
    let duplicateStats := stats prodConst #[first, first]
    checkLoop ctx duplicateStats missingSecond isUnsafe true
    unless declareConstructors.arity 0 missingSecond < duplicateStats.params.size do
      throwError "duplicate parameters must demonstrate the distinctness premise"
  unless (ctx.env.checkNoMVarNoFVar `Open (.app listConst first)).isOk == false do
    throwError "open source return must be rejected before constructor traversal"
  let checkedHead := Expr.const `CheckedType []
  let checkedOne := Expr.forallE `A sortType (.app checkedHead (.bvar 0)) .default
  let checkedTwo := Expr.forallE `A sortType (.forallE `B sortType
    (.mkAppList checkedHead [.bvar 1, .bvar 0]) .default) .default
  let checkedField := Expr.forallE `A sortType (.forallE `B sortType
    (.forallE `value (.bvar 1) (.mkAppList checkedHead [.bvar 2, .bvar 1]) .default)
      .default) .default
  let checkedMissing := Expr.forallE `A sortType
    (.mkAppList checkedHead [.bvar 0, .bvar 0]) .default
  let checkedSwapped := Expr.forallE `A sortType (.forallE `B sortType
    (.mkAppList checkedHead [.bvar 0, .bvar 1]) .default) .default
  for isUnsafe in [false, true] do
    let ctx := { ctx with safety := if isUnsafe then .unsafe else .safe }
    checkCheckedArity ctx 0 checkedHead isUnsafe true
    checkCheckedArity ctx 1 checkedOne isUnsafe true
    checkCheckedArity ctx 2 checkedTwo isUnsafe true
    checkCheckedArity ctx 2 checkedField isUnsafe true
    checkCheckedArity ctx 2 checkedMissing isUnsafe false
    checkCheckedArity ctx 2 checkedSwapped isUnsafe false
    checkCheckedArity ctx 1 (.app checkedHead first) isUnsafe false
    checkCheckedArity { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
      2 checkedField isUnsafe false

end ConstructorParamsTest
