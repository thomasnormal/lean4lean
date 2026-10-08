import Lean4Lean.Verify.ConstructorParams
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace ConstructorBatchArityTest

example (ctx : Context) (types : Array InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup) :
    (checkConstructors types stats isUnsafe ctx).WF fun _ =>
      ∀ type ∈ types, ∀ ctor ∈ type.ctors,
        stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
  checkConstructors.arity types stats isUnsafe ctx hfvars hnodup

example (ctx : Context) (types : Array InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (hcheck : checkConstructors types stats isUnsafe ctx = .ok ())
    (type : InductiveType) (htype : type ∈ types) (ctor : Constructor)
    (hctor : ctor ∈ type.ctors) : stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
  checkConstructors.arity types stats isUnsafe ctx hfvars hnodup _ hcheck type htype ctor hctor

example (ctx : Context) (types : Array InductiveType) (nparams : Nat) (isUnsafe : Bool) :
    (checkInductiveTypes nparams types (fun stats =>
      checkConstructors types stats isUnsafe >>= fun _ => pure stats) ctx).WF fun stats =>
        ∀ type ∈ types, ∀ ctor ∈ type.ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
  checkInductiveTypes.checkedConstructorsArity nparams types isUnsafe ctx

example (ctx : Context) (env : Kernel.Environment) (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (hfvars : stats.ParamsAreFVars)
    (hnodup : stats.params.toList.Nodup) :
    (withEnv env (checkConstructors types stats isUnsafe) ctx).WF fun _ =>
      ∀ type ∈ types, ∀ ctor ∈ type.ctors,
        stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
  checkConstructors.arity types stats isUnsafe { ctx with env } hfvars hnodup

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def checkBatch (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe expected : Bool) (fuel : Nat := 16) : MetaM Unit := do
  let result := checkInductiveTypes nparams types (fun stats current => do
    let env ← declareInductiveTypes stats nparams types 0 isUnsafe current
    checkConstructors types stats isUnsafe
      { current with env, fuel := { current.fuel with inductiveFuel := fuel } }
    pure stats) ctx
  unless result.isOk == expected do
    throwError "incorrect full constructor-batch outcome for {types.map (·.name)}"
  if let .ok stats := result then
    unless stats.params.size == nparams do
      throwError "incorrect checked parameter count"
    for type in types do
      for ctor in type.ctors do
        unless stats.params.size ≤ declareConstructors.arity 0 ctor.type do
          throwError "successful constructor batch has too few raw binders"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound, ``Expr.eqv_eq,
    ``Expr.instantiate1_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

private def checkImportedBatch (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe expected : Bool) : MetaM Unit := do
  let result := checkInductiveTypes nparams types (fun stats =>
    checkConstructors types stats isUnsafe >>= fun _ => pure stats) ctx
  unless result.isOk == expected do
    throwError "incorrect checked-type/full-batch composition outcome"
  if let .ok stats := result then
    unless stats.params.size == nparams do
      throwError "incorrect imported batch parameter count"
    for type in types do
      for ctor in type.ctors do
        unless stats.params.size ≤ declareConstructors.arity 0 ctor.type do
          throwError "checked-type/full-batch composition has too few raw binders"

run_meta
  audit ``checkConstructors.arity
  audit ``checkInductiveTypes.checkedConstructorsArity
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let zero := Expr.const `BatchZero []
  let one := Expr.const `BatchOne []
  let other := Expr.const `BatchOther []
  let two := Expr.const `BatchTwo []
  let indexed := Expr.const `BatchIndexed []
  let natType := Expr.const ``Nat []
  let zeroCtor : Constructor := { name := `BatchCtor, type := zero }
  let oneCtor : Constructor := {
    name := `BatchCtor, type := closeParams 1 (.app one (.bvar 0)) }
  let fieldCtor : Constructor := {
    name := `BatchField, type := closeParams 1
      (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `BatchMutual, type := closeParams 1
      (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherCtor : Constructor := {
    name := `BatchCtor, type := closeParams 1 (.app other (.bvar 0)) }
  let twoCtor : Constructor := {
    name := `BatchCtor, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let twoFields : Constructor := {
    name := `BatchFields, type := closeParams 2
      (.forallE `value (.bvar 1) (.mkAppList two [.bvar 2, .bvar 1]) .default) }
  let missing : Constructor := {
    name := `BatchMissing, type := closeParams 1 (.mkAppList two [.bvar 0, natType]) }
  let swapped : Constructor := {
    name := `BatchSwapped, type := closeParams 2 (.mkAppList two [.bvar 0, .bvar 1]) }
  let malformed : Constructor := { name := `BatchMalformed, type := .app natType natType }
  let openCtor : Constructor := { name := `BatchOpen, type := .app one (.fvar ⟨`Open⟩) }
  let metaCtor : Constructor := { name := `BatchMeta, type := .mvar ⟨`Meta⟩ }
  let wrongDomain : Constructor := {
    name := `BatchWrongDomain, type := .forallE `parameter (.sort (.succ (.succ .zero)))
      (.app one natType) .default }
  let indexedCtor : Constructor := {
    name := `BatchCtor, type := closeParams 1
      (.mkAppList indexed [.bvar 0, .const ``Nat.zero []]) }
  let indexedField : Constructor := {
    name := `BatchIndexField, type := closeParams 1
      (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }
  let missingIndex : Constructor := {
    name := `BatchMissingIndex, type := closeParams 1 (.app indexed (.bvar 0)) }
  let indexedHeader (ctors : List Constructor) : InductiveType := {
    name := `BatchIndexed, type := closeParams 1 (.forallE `index natType sortType .default),
    ctors }
  let importedNat : InductiveType := header ``Nat 0 [
    { name := `ImportedZero, type := natType },
    { name := `ImportedSucc, type := .forallE `value natType natType .default }]
  let importedBool : InductiveType := header ``Bool 0 [
    { name := `ImportedFalse, type := .const ``Bool [] },
    { name := `ImportedTrue, type := .const ``Bool [] }]
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyList := Expr.app (.const ``List [polyLevel]) (.bvar 0)
  let importedList : InductiveType := {
    name := ``List, type := .forallE `parameter polySort polySort .default,
    ctors := [{ name := `ImportedList, type := .forallE `parameter polySort polyList .default }] }
  for isUnsafe in [false, true] do
    let ctx := { ctx with safety := if isUnsafe then .unsafe else .safe }
    checkBatch ctx 0 #[] isUnsafe true
    checkBatch ctx 0 #[header `BatchZero 0 []] isUnsafe true
    checkBatch ctx 0 #[header `BatchZero 0 [zeroCtor]] isUnsafe true
    checkBatch ctx 1 #[header `BatchOne 1 []] isUnsafe true 0
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, fieldCtor]] isUnsafe true
    checkBatch ctx 2 #[header `BatchTwo 2 [twoCtor, twoFields]] isUnsafe true
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, fieldCtor, mutualCtor],
      header `BatchEmpty 1 [], header `BatchOther 1 [otherCtor]] isUnsafe true
    checkBatch ctx 1 #[indexedHeader [indexedCtor, indexedField]] isUnsafe true
    checkBatch ctx 1 #[indexedHeader [indexedCtor, missingIndex]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, oneCtor]] isUnsafe false
    checkBatch ctx 2 #[header `BatchTwo 2 [twoCtor, missing]] isUnsafe false
    checkBatch ctx 2 #[header `BatchTwo 2 [twoCtor, swapped]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, malformed]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, openCtor]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, metaCtor]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor, wrongDomain]] isUnsafe false
    checkBatch ctx 1 #[header `BatchOne 1 [oneCtor], header `BatchEmpty 1 [],
      header `BatchOther 1 [otherCtor, { oneCtor with name := `BatchWrongParent }]]
      isUnsafe false
    checkBatch ctx 0 #[header `BatchZero 0 [zeroCtor]] isUnsafe false 0
    checkBatch ctx 2 #[header `BatchTwo 2 [twoCtor, twoFields]] isUnsafe false 3
    checkImportedBatch ctx 0 #[importedNat] isUnsafe true
    checkImportedBatch ctx 0 #[importedNat, importedBool] isUnsafe true
    checkImportedBatch ctx 0 #[{ importedNat with ctors := importedNat.ctors ++ importedNat.ctors }]
      isUnsafe false
    checkImportedBatch { ctx with lparams := [`u] } 1 #[importedList] isUnsafe true

end ConstructorBatchArityTest
