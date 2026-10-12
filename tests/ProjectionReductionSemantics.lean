import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace ProjectionReductionSemanticsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapRec cheapProj).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS (.proj name index source) semantic) :
    (Inner.reduceProj index source cheapRec cheapProj).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow (.proj name index source) reduced ∧ context.TrExpr reduced semantic) :=
  Inner.reduceProj.WF translated

example {context : VContext} {state : VState} {methods : Methods}
    (valid : methods.WF) (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapRec cheapProj methods).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated methods valid

example {context : VContext} {state : VState} (depth : Nat)
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapRec cheapProj (Methods.withFuel depth)).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated _ Methods.withFuel.WF

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment)
    (translated : (VContext.mk' wellFormed safety levels fuel).TrExprS source semantic) :
    (M.run environment safety {} levels fuel
      (RecM.run (Inner.reduceProj index source cheapRec cheapProj))).WF (fun outcome => outcome = none) :=
  M.WF.run wellFormed (Inner.reduceProj.none_of_translation translated).run

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let literal := Expr.lit (.natVal 7)
  let localId : FVarId := ⟨`projectionReductionLocal⟩
  let letId : FVarId := ⟨`projectionReductionLet⟩
  let localHead := Expr.fvar localId
  let locals := ({} : LocalContext).mkLocalDecl localId `value natural .default
    |>.mkLetDecl letId `alias natural (.mdata {} literal)
  let identity := Expr.lam `argument natural (.bvar 0) .default
  let negatives : List Expr := [
    natural, literal, localHead, .fvar letId, .sort .zero, .mdata {} literal,
    .app identity literal, .letE `value natural literal (.bvar 0) false]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, localHead]
  let mut noneCount := 0
  let mut constructorCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for depth in [32, 128] do
        let methods := Methods.withFuel depth
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager,
          fuel := { recDepth := depth, whnf := depth, whnfEager := depth } }
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            let mut negativeState : State := {}
            for _ in [:2] do
              for source in negatives do
                for index in [0, 11, 9999] do
                  let result := Inner.reduceProj index source cheapRec cheapProj methods context negativeState
                  let .ok (outcome, finalState) := result
                    | throwError "projection rejection worker failed: {repr source}"
                  unless outcome.isNone do
                    throwError "projection rejection worker returned a value: {repr source}"
                  negativeState := finalState
                  noneCount := noneCount + 1
            let mut positiveState : State := {}
            for _ in [:2] do
              for (index, expected) in [(0, literal), (1, localHead)] do
                let .ok (outcome, finalState) :=
                    Inner.reduceProj index pair cheapRec cheapProj methods context positiveState
                  | throwError "native constructor projection control rejected"
                unless outcome == some expected do
                  throwError "native constructor projection control lost its expected field"
                positiveState := finalState
                constructorCount := constructorCount + 1
            let .ok (underApplied, _) := Inner.reduceProj 0
                (.const ``Prod.mk [.zero, .zero]) cheapRec cheapProj methods context {}
              | throwError "under-applied native constructor projection rejected"
            unless underApplied.isNone do
              throwError "under-applied native constructor projection returned a field"
  let context : Context := { env := environment, lctx := locals }
  let zero := Methods.withFuel 0
  for cheapRec in [false, true] do
    for cheapProj in [false, true] do
      unless !(Inner.reduceProj 0 literal cheapRec cheapProj zero context {}).isOk do
        throwError "zero-depth projection callback unexpectedly accepted"
  let poisonedSource := Expr.app identity literal
  let poisoned : State := {
    whnfCoreCache := ({} : ExprMap Expr).insert poisonedSource pair,
    whnfCache := ({} : ExprMap Expr).insert poisonedSource pair }
  for cheapProj in [false, true] do
    let .ok (outcome, _) := Inner.reduceProj 0 poisonedSource false cheapProj
        (Methods.withFuel 128) context poisoned
      | throwError "poisoned projection-cache premise control rejected"
    unless outcome == some literal do
      throwError "poisoned projection-cache premise control disappeared"
  let stringMethods := Methods.withFuel 1024
  let stringContext : Context := {
    context with fuel := { recDepth := 1024, whnf := 1024, whnfEager := 1024 } }
  let characterList := mkAppN (.const ``List.cons [.zero]) #[
    .const ``Char [], .app (.const ``Char.ofNat []) (.lit (.natVal 65)),
    .app (.const ``List.nil [.zero]) (.const ``Char [])]
  let expectedEncoding := Expr.app (.const ``List.utf8Encode []) characterList
  let .ok (some characters, stringState) := Inner.reduceProj 0 (.lit (.strVal "A"))
      false false stringMethods stringContext {}
    | throwError "native string projection expansion control rejected"
  unless characters == expectedEncoding do
    throwError "native string projection helper lost its encoded field: {repr characters}"
  let .ok (normalizedCharacters, _) := Inner.whnf characters stringMethods stringContext stringState
    | throwError "native string projection field normalization rejected"
  unless normalizedCharacters.getAppFn == .const ``ByteArray.mk [] do
    throwError "native string projection field normalization lost its byte-array head"
  logInfo m!"{noneCount} actual cold/warm projection rejection controls and {constructorCount} native constructor-field successes pass; both safeties/eager modes, callback depths 32/128, all cheap flags, varied indices, metadata/beta/local-let heads, under-application and zero-depth guards covered; native constructor/string successes are outside the current TrEnv fragment, and poisoned caches are excluded by the original state premise"

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  for theoremName in #[``Inner.reduceProj.none_of_translation, ``Inner.reduceProj.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "projection theorem is an axiom: {theoremName}"
    let some proof := information.value? | throwError "projection proof missing: {theoremName}"
    if proof.hasSorry then throwError "projection theorem has an admission: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected projection theorem dependency: {dependency} in {theoremName}"
  logInfo m!"projection no-result contract and original soundness theorem have no direct admission or axiom; inherited semantic/native baseline remains explicit: {repr baseline}"
  nativeControls

end ProjectionReductionSemanticsTest
