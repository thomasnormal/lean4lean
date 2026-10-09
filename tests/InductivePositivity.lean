import Lean4Lean.Verify.InductivePositivity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductivePositivityTest

example (stats : InductiveStats) (type : Expr) (parent : Nat)
    (hvalid : isValidIndApp? stats type = some parent) :
    parent < stats.indConsts.size ∧ isValidIndAppIdx stats type parent = true :=
  isValidIndApp?.valid stats type parent hvalid

example (stats : InductiveStats) (type : Expr) (parent : Nat)
    (hvalid : isValidIndApp? stats type = some parent) :
    ∀ index, stats.params.size ≤ index → index < type.getAppArgs.size →
      hasIndOcc stats.indConsts type.getAppArgs[index]! = false :=
  isValidIndAppIdx.indexNoIndOcc stats type parent
    (isValidIndApp?.valid stats type parent hvalid).2

example (stats : InductiveStats) (normalizes : Context → Expr → Expr → Prop)
    (type : Expr) (ctor : Name) (index : Nat) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkPositivity stats type ctor index ctx).WF
      fun _ => PositivityTrace stats normalizes ctx type :=
  checkPositivity.trace_of_whnf stats normalizes type ctor index ctx hwhnf

example (stats : InductiveStats) (type : Expr) (ctor : Name) (index : Nat)
    (ctx : Context) (hchecked : checkPositivity stats type ctor index ctx = .ok ()) :
    PositivityTrace stats PositivityWHNF ctx type :=
  checkPositivity.trace stats type ctor index ctx _ hchecked

example (stats : InductiveStats) (normalizes : Context → Expr → Expr → Prop)
    (ctor : Name) (index : Nat) (type : Expr) (ctx : Context) :
    (checkPositivity.loop stats ctor index type 0 ctx).WF
      fun _ => PositivityTrace stats normalizes ctx type :=
  Except.WF.throw

example (stats : InductiveStats) (ctx : Context) (type normal : Expr) (parent : Nat)
    (hwhnf : PositivityWHNF ctx type normal)
    (hocc : hasIndOcc stats.indConsts normal = true)
    (hnotForall : normal.isForall = false)
    (hvalid : isValidIndApp? stats normal = some parent) :
    PositivityTrace stats PositivityWHNF ctx type :=
  .inductiveApp hwhnf hocc hnotForall
    (isValidIndApp?.valid stats normal parent hvalid).1
    (isValidIndApp?.valid stats normal parent hvalid).2

example (stats : InductiveStats) (ctx : Context) (type : Expr) (name : Name)
    (domain body : Expr) (bi : BinderInfo)
    (hwhnf : PositivityWHNF ctx type (.forallE name domain body bi))
    (hocc : hasIndOcc stats.indConsts (.forallE name domain body bi) = true)
    (hdom : hasIndOcc stats.indConsts domain = false)
    (hbody : PositivityTrace stats PositivityWHNF (ctx.withPositivityArg name domain bi)
      (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩))) :
    PositivityTrace stats PositivityWHNF ctx type :=
  .forallE hwhnf hocc hdom hbody

private def stats (heads : Array Expr) (params : Array Expr := #[])
    (indices : Array Nat := #[0]) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, indConsts := heads, params,
  nindices := indices, isNotZero := true }

private def checkClassifier (stats : InductiveStats) (type : Expr)
    (expected : Option Nat) : MetaM Unit := do
  unless isValidIndApp? stats type == expected do
    throwError "incorrect recursive inductive-application classifier"

private def checkPositive (ctx : Context) (stats : InductiveStats) (type : Expr)
    (expected : Bool) (fuel : Nat := 16) : MetaM Unit := do
  let ctx := { ctx with fuel := { ctx.fuel with inductiveFuel := fuel } }
  unless (checkPositivity stats type `PositiveFixture 0 ctx).isOk == expected do
    throwError "incorrect positivity outcome for {type} with fuel {fuel}"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``isValidIndApp?.valid
  audit ``checkPositivity.loop.trace_of_whnf
  audit ``checkPositivity.trace_of_whnf
  audit ``checkPositivity.trace
  let imported := (← Lean.getEnv).toKernelEnv
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let sortType := Expr.sort (.succ .zero)
  let natStats := stats #[natType]
  let mutualStats := stats #[boolType, natType] #[] #[0, 0]
  let ctx : Context := {
    env := imported, lparams := [], safety := .safe, allowPrimitive := false }
  checkClassifier natStats natType (some 0)
  checkClassifier natStats boolType none
  checkClassifier mutualStats boolType (some 0)
  checkClassifier mutualStats natType (some 1)
  checkClassifier mutualStats (.const ``String []) none
  checkClassifier (stats #[] #[] #[]) natType none
  checkClassifier (stats #[natType, natType] #[] #[0, 0]) natType (some 0)
  let reflexive := Expr.forallE `value boolType natType .default
  let twiceReflexive := Expr.forallE `first boolType reflexive .implicit
  let negative := Expr.forallE `value natType boolType .default
  let higherNegative := Expr.forallE `function negative natType .default
  let erasedOccurrence := Expr.app (.lam `unused sortType boolType .default) natType
  checkPositive ctx natStats boolType true
  checkPositive ctx natStats natType true
  checkPositive ctx mutualStats natType true
  checkPositive ctx mutualStats boolType true
  checkPositive ctx natStats reflexive true
  checkPositive ctx natStats twiceReflexive true
  checkPositive ctx natStats negative false
  checkPositive ctx natStats higherNegative false
  checkPositive ctx natStats (.forallE `recursive natType natType .default) false
  checkPositive ctx natStats (.mdata {} reflexive) true
  checkPositive ctx natStats (.letE `type sortType natType (.bvar 0) false) true
  checkPositive ctx natStats erasedOccurrence true
  unless hasIndOcc natStats.indConsts erasedOccurrence do
    throwError "normalization fixture must contain a raw inductive occurrence"
  let .ok erasedNormal := (monadLift (TypeChecker.whnf erasedOccurrence) : M Expr) ctx
    | throwError "normalization fixture failed"
  unless hasIndOcc natStats.indConsts erasedNormal == false do
    throwError "normalization fixture must erase its raw occurrence"
  checkPositive ctx natStats natType false 0
  checkPositive ctx natStats boolType true 1
  checkPositive ctx natStats reflexive false 1
  checkPositive ctx natStats reflexive true 2
  checkPositive ctx natStats twiceReflexive false 2
  checkPositive ctx natStats twiceReflexive true 3
  checkPositive { ctx with fuel := { ctx.fuel with recDepth := 0 } }
    natStats boolType false
  checkPositive { ctx with ngen := { namePrefix := `Seeded, idx := 12 } }
    natStats twiceReflexive true
  let first := Expr.fvar ⟨`FirstParameter⟩
  let second := Expr.fvar ⟨`SecondParameter⟩
  let listType := Expr.const ``List [.succ .zero]
  let listStats := stats #[listType] #[first]
  let lctx := ctx.lctx.mkLocalDecl ⟨`FirstParameter⟩ `A sortType
    |>.mkLocalDecl ⟨`SecondParameter⟩ `B sortType
  let ctx := { ctx with lctx }
  checkClassifier listStats (.app listType first) (some 0)
  checkClassifier listStats (.app listType second) none
  checkClassifier listStats listType none
  checkPositive ctx listStats (.app listType first) true
  checkPositive ctx listStats (.app listType second) false
  checkPositive ctx listStats listType false
  checkPositive ctx listStats (.forallE `value first (.app listType first) .strictImplicit) true
  let finType := Expr.const ``Fin []
  let finStats := stats #[finType] #[] #[1]
  let finApplication := Expr.app finType (.lit (.natVal 3))
  let recursiveIndex := Expr.app finType finType
  checkClassifier finStats finApplication (some 0)
  checkClassifier finStats recursiveIndex none
  checkPositive ctx finStats finApplication true
  checkPositive ctx finStats recursiveIndex false
  checkPositive ctx finStats (.forallE `index natType (.app finType (.bvar 0)) .default) true
  checkPositive ctx finStats (.forallE `index natType
    (.app finType (.app finType (.bvar 0))) .default) false
  logInfo "12 classifier fixtures, 28 positivity outcomes, and normalized-erasure boundary passed"

end InductivePositivityTest
