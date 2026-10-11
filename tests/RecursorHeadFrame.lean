import Lean4Lean.Verify.TypeChecker.RecursorHeadFrame
import Lean.Util.CollectAxioms

namespace RecursorHeadFrameTest
open Lean hiding Environment Exception
open Lean4Lean

private def naturalControl : Nat := Nat.rec 7 (fun _ result => result + 1) 2

private def equalityControl : Nat := @Eq.rec Nat 4 (fun _ _ => Nat) 7 4 rfl

private noncomputable def structureControl (pair : Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun first _ => first) pair

private def conjunctionControl (proof : True ∧ True) : True :=
  And.rec (motive := fun _ => True) (fun first _ => first) proof

private def quotientControl : Nat :=
  Quot.lift (fun value : Nat => value) (by intro first second relation; exact relation) (Quot.mk Eq 5)

private def quotientIndControl : True :=
  Quot.ind (β := fun _ => True) (fun _ : Nat => True.intro) (Quot.mk Eq 5)

private noncomputable def stringControl : Nat := String.rec (motive := fun _ => Nat) (fun _ _ => 7) ""

example (expression : Expr) (cheapRec cheapProj : Bool) (methods : TypeChecker.Methods)
    (valid : methods.HeadWF) :
    (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods).HeadWF (fun _ => True) :=
  TypeChecker.Inner.reduceRecursor.headWF expression cheapRec cheapProj methods valid

example (expression : Expr) (cheapRec cheapProj : Bool) (methods : TypeChecker.Methods)
    (valid : methods.HeadWF) :
    (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods).HeadWF NativeHeadClean :=
  TypeChecker.Inner.whnfCore'.headWFOfMethods expression cheapRec cheapProj methods valid

example (expression : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (TypeChecker.Inner.whnf' expression methods).HeadWF NativeHeadClean :=
  TypeChecker.Inner.whnf'.headWFOfMethods expression methods valid

example (expression : Expr) (cheapRec cheapProj : Bool) :
    ((TypeChecker.Methods.withFuel 1).whnfCore expression cheapRec cheapProj).HeadWF NativeHeadClean :=
  TypeChecker.Methods.withFuel.whnfCore_succ_headWF 0 TypeChecker.Methods.withFuel.zero_headWF
    expression cheapRec cheapProj

example (expression : Expr) :
    ((TypeChecker.Methods.withFuel 1).whnf expression).HeadWF NativeHeadClean :=
  TypeChecker.Methods.withFuel.whnf_succ_headWF 0 TypeChecker.Methods.withFuel.zero_headWF expression

private def cleanHead (expression : Expr) : Bool := !expression.isMData && !expression.isLet

private def cleanCaches (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => cleanHead entry.2) &&
    state.whnfCache.toList.all (fun entry => cleanHead entry.2)

private def declarationValue (name : Name) : MetaM Expr := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "native recursor fixture definition absent: {name}"
  return info.value

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural ← declarationValue ``naturalControl
  let equality ← declarationValue ``equalityControl
  let structureValue ← declarationValue ``structureControl
  let conjunction ← declarationValue ``conjunctionControl
  let quotient ← declarationValue ``quotientControl
  let quotientInd ← declarationValue ``quotientIndControl
  let string ← declarationValue ``stringControl
  let .lam _ pairType pairBody _ := structureValue | throwError "native structure fixture lost its binder"
  let .lam _ proofType proofBody _ := conjunction | throwError "native conjunction fixture lost its binder"
  let locals := ({} : LocalContext).mkLocalDecl ⟨`pair⟩ `pair pairType .default
    |>.mkLocalDecl ⟨`proof⟩ `proof proofType .default
  let expressions := #[natural, equality, pairBody.instantiate1 (.fvar ⟨`pair⟩),
    proofBody.instantiate1 (.fvar ⟨`proof⟩), quotient, quotientInd, string]
  let expected : Array (Option Expr) := #[some (.lit (.natVal 9)), some (.lit (.natVal 7)),
    some (.proj ``Prod 0 (.fvar ⟨`pair⟩)), none, some (.lit (.natVal 5)),
    some (.const ``True.intro []), some (.lit (.natVal 7))]
  let methods := TypeChecker.Methods.withFuel 128
  let mut reductions := 0
  let mut stops := 0
  let mut coreCount := 0
  let mut fullCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      let context : TypeChecker.Context := { env := environment, lctx := locals, safety, eagerReduce := eager }
      for source in [:expressions.size] do
        let expression := expressions[source]!
        unless (TypeChecker.checkType expression context {}).isOk do
          throwError "genuinely typed native recursor fixture rejected"
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            let mut state : TypeChecker.State := {}
            for _ in [:2] do
              let .ok (reduced, reductionState) := TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods context state
                | throwError "native recursor cache-frame fixture rejected"
              unless cleanCaches reductionState do throwError "native recursor corrupted WHNF caches"
              if reduced.isSome then reductions := reductions + 1 else stops := stops + 1
              let .ok (normalized, finalState) := TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods context reductionState
                | throwError "native recursor core head-shape fixture rejected"
              unless cleanHead normalized && cleanCaches finalState do throwError "native core recursor lost clean head/caches"
              state := finalState
              coreCount := coreCount + 1
        let mut state : TypeChecker.State := {}
        for _ in [:2] do
          let .ok (normalized, finalState) := TypeChecker.Inner.whnf' expression methods context state
            | throwError "native recursor full head-shape fixture rejected"
          unless cleanHead normalized && cleanCaches finalState do throwError "native full recursor lost clean head/caches"
          if let some expectedResult := expected[source]! then
            unless normalized == expectedResult do throwError "typed native recursor lost its expected full reduction endpoint"
          state := finalState
          fullCount := fullCount + 1
      let malformed := mkAppN (.const ``Nat.rec []) #[.sort .zero, .lit (.natVal 1)]
      let .ok (reduced, finalState) := TypeChecker.Inner.reduceRecursor malformed false false methods context {}
        | throwError "underapplied recursor negative control failed"
      unless reduced.isNone && cleanCaches finalState do throwError "underapplied recursor unexpectedly reduced"
  logInfo m!"{reductions} actual recursor reductions and {stops} irreducible stops preserve caches; {coreCount} core and {fullCount} full typed recursor cold/warm head controls pass with expected nat/K/structure/string/quotient full endpoints; actual Prop stops, both safeties/eager modes and all cheap flags covered; underapplications stop; no full-fuel Methods.HeadWF or semantic checker is fabricated"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.RecursorHeadFrame
    | throwError "native recursor head-frame module absent"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned recursor head-frame axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected recursor head-frame dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned native recursor head-frame declarations audited against unchanged logical/native representation foundations; no checker/metatheory admissions"
  nativeControls

end RecursorHeadFrameTest
