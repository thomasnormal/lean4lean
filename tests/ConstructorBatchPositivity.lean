import Lean4Lean.Verify.InductivePositivity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace ConstructorBatchPositivityTest

example (types : Array InductiveType) (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkConstructors types stats false ctx).WF fun _ =>
      stats.SafeConstructorTraces types normalizes ctx :=
  checkConstructors.safeTraces_of_whnf types stats normalizes ctx hwhnf

example (types : Array InductiveType) (stats : InductiveStats) (ctx : Context) :
    (checkConstructors types stats false ctx).WF fun _ =>
      stats.SafeConstructorTraces types PositivityWHNF ctx :=
  checkConstructors.safeTraces types stats ctx

example (types : Array InductiveType) (stats : InductiveStats) (ctx : Context)
    (hchecked : checkConstructors types stats false ctx = .ok ())
    (parent : Nat) (hparent : parent < types.size) (ctor : Constructor)
    (hctor : ctor ∈ types[parent].ctors) :
    ∃ terminal, SafeConstructorTrace stats PositivityWHNF parent ctx 0 ctor.type terminal :=
  checkConstructors.safeTraces types stats ctx _ hchecked parent hparent ctor hctor

example (types : Array InductiveType) (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (ctx : Context)
    (htraces : stats.SafeConstructorTraces types normalizes ctx) :
    ∀ parent, ∀ hparent : parent < types.size, ∀ ctor ∈ types[parent].ctors,
      ∃ terminal, ConstructorSpine ctor.type terminal ∧
        isValidIndAppIdx stats terminal parent = true :=
  htraces.spine

example (types : Array InductiveType) (stats : InductiveStats) (ctx : Context)
    (env : Kernel.Environment)
    (hchecked : withEnv env (checkConstructors types stats false) ctx = .ok ()) :
    stats.SafeConstructorTraces types PositivityWHNF { ctx with env } :=
  checkConstructors.safeTraces types stats { ctx with env } _ hchecked

example (stats : InductiveStats) (normalizes : Context → Expr → Expr → Prop)
    (ctx : Context) : stats.SafeConstructorTraces #[] normalizes ctx := by
  intro parent hparent
  simp at hparent

private def stats (heads : Array Expr) (params : Array Expr := #[])
    (indices : Array Nat := #[0]) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, indConsts := heads, params,
  nindices := indices, isNotZero := true }

private def header (name : Name) (ctors : List Constructor) : InductiveType := {
  name, type := .sort (.succ .zero), ctors }

private def checkBatch (ctx : Context) (stats : InductiveStats)
    (types : Array InductiveType) (expected : Bool) (fuel : Nat := 16)
    (isUnsafe : Bool := false) : MetaM Unit := do
  let ctx := { ctx with fuel := { ctx.fuel with inductiveFuel := fuel } }
  let result := checkConstructors types stats isUnsafe ctx
  unless result.isOk == expected do
    match result with
    | .error error =>
      throwError "incorrect constructor-batch outcome for {types.map (·.name)}: \
        {error.toMessageData (← getOptions)}"
    | .ok _ => throwError "unexpected constructor-batch success for {types.map (·.name)}"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``InductiveStats.SafeConstructorTraces.spine
  audit ``checkConstructors.safeTraces_of_whnf
  audit ``checkConstructors.safeTraces
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let natStats := stats #[natType]
  let mutualStats := stats #[natType, boolType] #[] #[0, 0]
  let base : Constructor := { name := `SharedName, type := natType }
  let recursive : Constructor := {
    name := `Recursive, type := .forallE `value natType natType .default }
  let positive : Constructor := {
    name := `Positive, type := .forallE `function
      (.forallE `value boolType natType .default) natType .implicit }
  let negative : Constructor := {
    name := `Negative, type := .forallE `function
      (.forallE `value natType boolType .default) natType .default }
  let twoFields : Constructor := {
    name := `TwoFields, type := .forallE `first boolType recursive.type .strictImplicit }
  let other : Constructor := { name := `SharedName, type := boolType }
  let mutualCtor : Constructor := {
    name := `Mutual, type := .forallE `value natType boolType .default }
  checkBatch ctx natStats #[] true
  checkBatch ctx natStats #[header ``Nat []] true 0
  checkBatch ctx natStats #[header ``Nat [base, recursive, positive, twoFields]] true
  checkBatch ctx mutualStats #[header ``Nat [base, recursive], header ``Bool [other, mutualCtor]] true
  checkBatch ctx mutualStats #[header ``Nat [], header ``Bool [other, mutualCtor]] true
  checkBatch ctx mutualStats #[header ``Nat [base], header ``Bool []] true
  checkBatch ctx natStats #[header ``Nat [base, recursive, negative]] false
  checkBatch ctx mutualStats #[header ``Nat [base], header ``Bool [other,
    { negative with name := `LaterNegative, type := (.forallE `function
      (.forallE `value boolType natType .default) boolType .default) }]] false
  checkBatch ctx natStats #[header ``Nat [base, base]] false
  checkBatch ctx mutualStats #[header ``Nat [base], header ``Bool [other, other]] false
  checkBatch ctx mutualStats #[header ``Nat [base], header ``Bool [other, base]] false
  checkBatch ctx natStats #[header ``Nat [base, { name := `Open, type := .fvar ⟨`Open⟩ }]] false
  checkBatch ctx natStats #[header ``Nat [base, { name := `Meta, type := .mvar ⟨`Meta⟩ }]] false
  checkBatch ctx natStats #[header ``Nat [base,
    { name := `IllTyped, type := .app natType natType }]] false
  checkBatch ctx natStats #[header ``Nat [base]] false 0
  checkBatch ctx natStats #[header ``Nat [recursive]] false 1
  checkBatch ctx natStats #[header ``Nat [recursive, { recursive with name := `Another }]] true 2
  checkBatch ctx natStats #[header ``Nat [base, twoFields]] false 2
  checkBatch ctx natStats #[header ``Nat [base, twoFields]] true 3
  checkBatch { ctx with ngen := { namePrefix := `BatchSeed, idx := 12 } }
    natStats #[header ``Nat [recursive, twoFields]] true
  checkBatch ctx natStats #[header ``Nat [negative]] true 16 true
  let finType := Expr.const ``Fin []
  let finStats := stats #[natType, finType] #[] #[0, 1]
  let indexed : Constructor := {
    name := `Indexed, type := .forallE `index natType (.app finType (.bvar 0)) .default }
  checkBatch ctx finStats #[header ``Nat [base], header ``Fin [indexed]] true
  checkBatch ctx finStats #[header ``Nat [base], header ``Fin [
    { indexed with type := (.forallE `index natType
      (.app finType (.app finType (.bvar 0))) .default) }]] false
  checkBatch ctx finStats #[header ``Nat [base], header ``Fin [
    { indexed with type := .forallE `index natType natType .default }]] false
  let parameter := Expr.fvar ⟨`Parameter⟩
  let sortType := Expr.sort (.succ .zero)
  let listType := Expr.const ``List [.zero]
  let listStats := stats #[listType] #[parameter]
  let ctx := { ctx with lctx := ctx.lctx.mkLocalDecl ⟨`Parameter⟩ `A sortType }
  let parameterOnly : Constructor := {
    name := `ParameterOnly, type := .forallE `A sortType (.app listType (.bvar 0)) .default }
  let parameterRecursive : Constructor := {
    name := `ParameterRecursive, type := .forallE `A sortType
      (.forallE `tail (.app listType (.bvar 0)) (.app listType (.bvar 1)) .default) .default }
  let parameterNegative : Constructor := {
    name := `ParameterNegative, type := .forallE `A sortType
      (.forallE `function (.forallE `tail (.app listType (.bvar 0)) (.bvar 1) .default)
        (.app listType (.bvar 1)) .default) .default }
  checkBatch ctx listStats #[header ``List [parameterOnly, parameterRecursive]] true
  checkBatch ctx listStats #[header ``List [parameterOnly, parameterNegative]] false
  checkBatch ctx listStats #[header ``List [parameterOnly, parameterRecursive]] false 2
  checkBatch ctx listStats #[header ``List [parameterOnly, parameterRecursive]] true 3
  checkBatch ctx listStats #[header ``List [
    { name := `OpenReturn, type := .app listType parameter }]] false
  checkBatch ctx listStats #[header ``List [parameterOnly,
    { name := `WrongParameter, type := .forallE `A natType (.app listType natType) .default }]] false
  logInfo "30 constructor-batch outcomes, including unsafe control, passed"

end ConstructorBatchPositivityTest
