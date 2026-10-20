import Lean4Lean.Verify.TypeChecker.ScopedComparison
import Lean.Util.CollectAxioms

namespace ComparisonFragmentRejectionTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private def ignoredConstructor : ConstructorVal := {
  name := `IgnoredComparisonConstructor
  levelParams := []
  type := .sort (.succ .zero)
  induct := `IgnoredComparisonHeader
  cidx := 0
  numParams := 0
  numFields := 0
  isUnsafe := true }

private theorem ignoredConstructorSupported :
    TrEnv' .safe (({} : ConstMap).insert ignoredConstructor.name (.ctorInfo ignoredConstructor))
      false VEnv.empty :=
  .ignoreConst (C := {}) (ci := .ctorInfo ignoredConstructor)
    (by simp [SMap.find?]) (by decide) .empty

example : ({} : VEnv).constants ignoredConstructor.name = none := rfl

example (valid : TrEnv safety native environment)
    (found : native.find? name = some (.ctorInfo header)) : ¬environment.contains name :=
  valid.constructorNotInModel found

example {context : VContext} (translated : context.TrExprS expression semantic)
    (headEq : expression.getAppFn = .const name levels) : context.venv.contains name :=
  context.constAppHeadInModel translated headEq

example {context : VContext} {state : VState} (translated : context.TrExprS second semantic) :
    (Inner.tryEtaStructCore first second).WF context state (fun equal _ => equal = false) :=
  Inner.tryEtaStructCore.false_of_translation translated

example {context : VContext} {state : VState} (translated : context.TrExprS first semantic) :
    (Inner.isDefEqUnitLike first second).WF context state (fun equal _ => equal = false) :=
  Inner.isDefEqUnitLike.false_of_translation translated

example {context : VContext} {state : VState} (translated : context.TrExprS second semantic) :
    (Inner.tryEtaStructCore (.mvar identifier) second).ScopeWF context state (fun equal _ => equal = false) :=
  Inner.tryEtaStructCore.scopeFalse translated

example {context : VContext} {state : VState} (translated : context.TrExprS first semantic) :
    (Inner.isDefEqUnitLike first (.mvar identifier)).ScopeWF context state (fun equal _ => equal = false) :=
  Inner.isDefEqUnitLike.scopeFalse translated

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryEtaStructCore first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryEtaStructCore.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryEtaStruct first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryEtaStruct.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqUnitLike first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqUnitLike.scopeWF firstTranslation secondTranslation

private def stableHead (locals : LocalContext) (expression : Expr) : Bool :=
  !expression.isMData && !expression.isLet && match expression with
    | .fvar identifier => !Inner.isLetFVar locals identifier
    | _ => true

private def stableCaches (locals : LocalContext) (state : State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => stableHead locals entry.2) &&
    state.whnfCache.toList.all (fun entry => stableHead locals entry.2)

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let pair := Expr.fvar ⟨`comparisonBoundaryPair⟩
  let firstUnit := Expr.fvar ⟨`comparisonBoundaryFirstUnit⟩
  let secondUnit := Expr.fvar ⟨`comparisonBoundarySecondUnit⟩
  let aliasIdentifier : FVarId := ⟨`comparisonBoundaryAlias⟩
  let pairType := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let locals := ({} : LocalContext).mkLocalDecl ⟨`comparisonBoundaryPair⟩ `pair pairType .default
    |>.mkLocalDecl ⟨`comparisonBoundaryFirstUnit⟩ `firstUnit (.const ``Unit []) .default
    |>.mkLocalDecl ⟨`comparisonBoundarySecondUnit⟩ `secondUnit (.const ``Unit []) .default
    |>.mkLetDecl aliasIdentifier `alias (.sort (.succ .zero)) natural
  let etaPair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural,
    .proj ``Prod 0 pair, .proj ``Prod 1 pair]
  let unknown := Expr.mvar ⟨`comparisonBoundaryUnread⟩
  let guards : List (RecM Bool) := [
    Inner.tryEtaStructCore unknown natural,
    Inner.tryEtaStructCore unknown (.mdata {} natural),
    Inner.tryEtaStruct natural natural,
    Inner.isDefEqUnitLike (.sort .zero) unknown]
  let positives : List (RecM Bool) := [
    Inner.tryEtaStructCore pair etaPair,
    Inner.tryEtaStruct pair etaPair,
    Inner.tryEtaStruct etaPair pair,
    Inner.isDefEqUnitLike firstUnit secondUnit]
  let mut guardCount := 0
  let mut positiveCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager, fuel := { recDepth := fuel } }
        let methods := Methods.withFuel fuel
        for (actions, expected) in [(guards, false), (positives, true)] do
          for action in actions do
            let mut state : State := {}
            for _ in [:2] do
              let .ok (equal, finalState) := action methods context state
                | throwError "comparison fragment native boundary control rejected"
              unless equal == expected && stableCaches locals finalState do
                throwError "comparison fragment native boundary control loses result or scoped caches"
              state := finalState
              if expected then positiveCount := positiveCount + 1 else guardCount := guardCount + 1
  let context : Context := { env := environment, lctx := locals }
  let .ok (equal, finalState) := Inner.tryEtaStructCore unknown natural (Methods.withFuel 0) context {}
    | throwError "pure zero-fuel structure rejection failed"
  unless !equal && stableCaches locals finalState do throwError "pure structure guard lost frame"
  let poisoned : State := { whnfCache := ({} : ExprMap Expr).insert natural (.fvar aliasIdentifier) }
  let .ok (_, poisonedFinal) := Inner.tryEtaStructCore unknown natural (Methods.withFuel 0) context poisoned
    | throwError "structure cache-premise control rejected"
  unless !stableCaches locals poisonedFinal do throwError "structure cache premise disappeared"
  logInfo m!"{guardCount} cold/warm actual structure/unit-like guards return false and preserve scoped caches; {positiveCount} cold/warm native host structure-eta/unit-like positives preserve scoped caches outside the current TrEnv fragment; both safeties/eager modes and fuels 32/128; unread metavariables, symmetric eta, pure zero-fuel guard and poisoned-cache premise covered; no scoped method instance or inductive semantic model is fabricated"

run_meta
  let environment ← getEnv
  let baseline ← collectAxioms ``Inner.isDefEqCore'.WF
  let native := #[``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  for theoremName in #[``TrEnv'.constructorLookupRejected, ``TrEnv.constructorLookupRejected,
      ``TrEnv.constructorNotInModel, ``VContext.constAppHeadInModel,
      ``Inner.tryEtaStructCore.false_of_translation, ``Inner.tryEtaStructCore.WF,
      ``Inner.isDefEqUnitLike.false_of_translation, ``Inner.isDefEqUnitLike.WF,
      ``Inner.tryEtaStructCore.scopeFalse, ``Inner.tryEtaStructCore.scopeWF,
      ``Inner.tryEtaStruct.scopeWF, ``Inner.isDefEqUnitLike.scopeFalse,
      ``Inner.isDefEqUnitLike.scopeWF, ``ignoredConstructorSupported] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then throwError "comparison boundary axiom {theoremName}"
    let some proof := information.value? (allowOpaque := true) | throwError "comparison boundary proof absent {theoremName}"
    if proof.hasSorry then throwError "comparison boundary admission {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency || native.contains dependency do
        throwError "unexpected comparison boundary dependency {dependency} in {theoremName}"
  let mut owned := 0
  for moduleName in #[`Lean4Lean.Verify.Environment.Lemmas, `Lean4Lean.Verify.TypeChecker.IsDefEq] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "comparison boundary module absent"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned comparison boundary axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "owned comparison boundary admission {name}"
        owned := owned + 1
  logInfo m!"{owned} exhaustive owned environment/comparison declarations have no direct proof admissions or axioms; structure eta and unit-like inference cannot return true in the current TrEnv fragment; inherited semantic/native baseline remains explicit: {repr baseline}"
  nativeControls

end ComparisonFragmentRejectionTest
