import Lean4Lean.Verify.TypeChecker.ScopedComparison
import Lean.Util.CollectAxioms

namespace ScopedAuxComparisonTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private def successorAlias := Nat.succ

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.inferType expression true).ScopeWF context state fun type _ =>
      ∃ semanticType, context.TrTyping expression type semantic semanticType :=
  Inner.inferType.scopeWF_of_translation translated

example {context : VContext} {state : VState}
    (heads : ∃ firstHead, context.TrExprS first.getAppFn firstHead ∧
      ∃ secondHead, context.TrExprS second.getAppFn secondHead ∧ context.IsDefEqU firstHead secondHead)
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqArgs first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqArgs.scopeWF heads firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryEtaExpansionCore first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryEtaExpansionCore.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryEtaExpansion first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryEtaExpansion.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqApp first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqApp.scopeWF firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqProofIrrel first second).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqProofIrrel.scopeWF firstTranslation secondTranslation

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
  let seven := Expr.lit (.natVal 7)
  let eight := Expr.lit (.natVal 8)
  let successor := Expr.const ``Nat.succ []
  let predecessor := Expr.const ``Nat.pred []
  let addition := Expr.const ``Nat.add []
  let functionIdentifier : FVarId := ⟨`scopedAuxFunction⟩
  let otherIdentifier : FVarId := ⟨`scopedAuxOther⟩
  let dependentIdentifier : FVarId := ⟨`scopedAuxDependent⟩
  let firstProofIdentifier : FVarId := ⟨`scopedAuxFirstProof⟩
  let secondProofIdentifier : FVarId := ⟨`scopedAuxSecondProof⟩
  let falseProofIdentifier : FVarId := ⟨`scopedAuxFalseProof⟩
  let aliasIdentifier : FVarId := ⟨`scopedAuxAlias⟩
  let propositionAliasIdentifier : FVarId := ⟨`scopedAuxPropositionAlias⟩
  let functionType := Expr.forallE `argument natural natural .default
  let dependentType := Expr.forallE `domain (.sort (.succ .zero))
    (.forallE `argument (.bvar 0) (.bvar 1) .default) .default
  let locals := ({} : LocalContext).mkLocalDecl functionIdentifier `function functionType .default
    |>.mkLocalDecl otherIdentifier `other functionType .default
    |>.mkLocalDecl dependentIdentifier `dependent dependentType .default
    |>.mkLetDecl propositionAliasIdentifier `propositionAlias (.sort .zero) (.const ``True [])
    |>.mkLocalDecl firstProofIdentifier `firstProof (.const ``True []) .default
    |>.mkLocalDecl secondProofIdentifier `secondProof (.fvar propositionAliasIdentifier) .default
    |>.mkLocalDecl falseProofIdentifier `falseProof (.const ``False []) .default
    |>.mkLetDecl aliasIdentifier `alias functionType (.fvar functionIdentifier)
  let function := Expr.fvar functionIdentifier
  let other := Expr.fvar otherIdentifier
  let dependent := Expr.fvar dependentIdentifier
  let firstProof := Expr.fvar firstProofIdentifier
  let secondProof := Expr.fvar secondProofIdentifier
  let falseProof := Expr.fvar falseProofIdentifier
  let expanded := Expr.lam `argument natural (.app function (.bvar 0)) .default
  let otherExpanded := Expr.lam `argument natural (.app other (.bvar 0)) .default
  let dependentExpanded := Expr.lam `domain (.sort (.succ .zero)) (.app dependent (.bvar 0)) .default
  let identity := Expr.lam `argument natural (.bvar 0) .default
  let booleanActions : List (RecM Bool × Bool) := [
    (Inner.isDefEqArgs (.app successor seven) (.app successor seven), true),
    (Inner.isDefEqArgs (.app successor seven) (.app successor eight), false),
    (Inner.isDefEqArgs (.app successor seven) (.app predecessor seven), true),
    (Inner.isDefEqArgs natural (.const ``Bool []), true),
    (Inner.isDefEqArgs (mkAppN addition #[seven, eight]) (mkAppN addition #[seven, eight]), true),
    (Inner.isDefEqArgs (mkAppN addition #[seven, eight]) (mkAppN addition #[eight, seven]), false),
    (Inner.isDefEqArgs (.app addition seven) (mkAppN addition #[seven, eight]), false),
    (Inner.isDefEqArgs natural (.app successor seven), false),
    (Inner.isDefEqApp (.app successor seven) (.app successor seven), true),
    (Inner.isDefEqApp (.app successor seven) (.app successor eight), false),
    (Inner.isDefEqApp (.app successor seven) (.app predecessor seven), false),
    (Inner.isDefEqApp (.app successor seven) (.app (.const ``successorAlias []) seven), true),
    (Inner.isDefEqApp (mkAppN addition #[seven, eight]) (mkAppN addition #[seven, eight]), true),
    (Inner.isDefEqApp (mkAppN addition #[seven, eight]) (mkAppN addition #[eight, seven]), false),
    (Inner.isDefEqApp (.app addition seven) (mkAppN addition #[seven, eight]), false),
    (Inner.isDefEqApp natural natural, false),
    (Inner.isDefEqApp (.app dependent natural) (.app dependent natural), true),
    (Inner.tryEtaExpansionCore expanded function, true),
    (Inner.tryEtaExpansionCore otherExpanded function, false),
    (Inner.tryEtaExpansionCore dependentExpanded dependent, true),
    (Inner.tryEtaExpansionCore expanded (.fvar aliasIdentifier), true),
    (Inner.tryEtaExpansionCore function expanded, false),
    (Inner.tryEtaExpansionCore identity natural, false),
    (Inner.tryEtaExpansionCore function other, false),
    (Inner.tryEtaExpansion expanded function, true),
    (Inner.tryEtaExpansion function expanded, true),
    (Inner.tryEtaExpansion dependentExpanded dependent, true),
    (Inner.tryEtaExpansion dependent dependentExpanded, true),
    (Inner.tryEtaExpansion otherExpanded function, false),
    (Inner.tryEtaExpansion function otherExpanded, false),
    (Inner.tryEtaExpansion identity identity, false),
    (Inner.tryEtaExpansion seven eight, false)]
  let proofActions : List (RecM LBool × LBool) := [
    (Inner.isDefEqProofIrrel firstProof secondProof, .true),
    (Inner.isDefEqProofIrrel secondProof firstProof, .true),
    (Inner.isDefEqProofIrrel firstProof falseProof, .false),
    (Inner.isDefEqProofIrrel falseProof firstProof, .false),
    (Inner.isDefEqProofIrrel seven eight, .undef),
    (Inner.isDefEqProofIrrel function other, .undef)]
  let mut booleanCount := 0
  let mut proofCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager, fuel := { recDepth := fuel } }
        let methods := Methods.withFuel fuel
        for (action, expected) in booleanActions do
          let mut state : State := {}
          for _ in [:2] do
            let .ok (equal, finalState) := action methods context state
              | throwError "scoped auxiliary Boolean comparison rejected"
            unless equal == expected && stableCaches locals finalState do
              throwError "scoped auxiliary Boolean comparison loses result or scoped caches"
            state := finalState
            booleanCount := booleanCount + 1
        for (action, expected) in proofActions do
          let mut state : State := {}
          for _ in [:2] do
            let .ok (equal, finalState) := action methods context state
              | throwError "scoped proof comparison rejected"
            unless equal == expected && stableCaches locals finalState do
              throwError "scoped proof comparison loses three-valued result or scoped caches"
            state := finalState
            proofCount := proofCount + 1
  let context : Context := { env := environment, lctx := locals }
  for (action, expected) in [(Inner.isDefEqArgs natural natural, true),
      (Inner.isDefEqApp natural natural, false), (Inner.tryEtaExpansionCore function other, false)] do
    let .ok (equal, finalState) := action (Methods.withFuel 0) context {}
      | throwError "pure zero-fuel auxiliary guard rejected"
    unless equal == expected && stableCaches locals finalState do
      throwError "pure zero-fuel auxiliary guard lost result or frame"
  unless !(Inner.isDefEqArgs (.app successor seven) (.app successor seven)
      (Methods.withFuel 0) context {}).isOk do
    throwError "zero-fuel argument callback unexpectedly succeeded"
  unless !(Inner.isDefEqProofIrrel firstProof secondProof (Methods.withFuel 0) context {}).isOk do
    throwError "zero-fuel proof inference unexpectedly succeeded"
  unless !(Inner.tryEtaExpansionCore expanded function (Methods.withFuel 0) context {}).isOk do
    throwError "zero-fuel eta inference unexpectedly succeeded"
  unless !(Inner.isDefEqApp (.app successor seven) (.app successor seven)
      (Methods.withFuel 0) context {}).isOk do
    throwError "zero-fuel application head callback unexpectedly succeeded"
  let poisoned : State := { whnfCache := ({} : ExprMap Expr).insert natural (.fvar aliasIdentifier) }
  let .ok (_, poisonedFinal) := Inner.tryEtaExpansionCore function other (Methods.withFuel 0) context poisoned
    | throwError "auxiliary cache-premise guard rejected"
  unless !stableCaches locals poisonedFinal do throwError "auxiliary cache premise disappeared"
  logInfo m!"{booleanCount} cold/warm actual argument/application/function-eta controls and {proofCount} three-valued proof controls preserve results and scoped caches; both safeties/eager modes, fuels 32/128, dependent functions, head aliases/mismatches, arity/argument mismatches, symmetric eta, normalized proposition aliases, false/undefined proof branches, zero-fuel guards/callbacks and poisoned-cache premise covered; raw argument controls deliberately retain true for mismatched heads to guard the theorem's explicit head-equality premise; no arbitrary-fuel scoped method instance is fabricated"

run_meta
  let environment ← getEnv
  let mut baseline := #[]
  for theoremName in #[``Inner.isDefEqArgs.WF, ``Inner.isDefEqApp.WF,
      ``Inner.tryEtaExpansionCore.WF, ``Inner.tryEtaExpansion.WF, ``Inner.isDefEqProofIrrel.WF,
      ``Inner.isDefEqLambda.WF, ``Inner.isDefEqForall.WF, ``Inner.quickIsDefEq.WF,
      ``Inner.inferType'.WF, ``Inner.whnf'.WF] do
    let dependencies ← collectAxioms theoremName
    logInfo m!"existing semantic baseline {theoremName}: {repr dependencies}"
    baseline := baseline ++ dependencies
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  let mut owned := 0
  for moduleName in #[`Lean4Lean.Verify.TypeChecker.ScopedInferType,
      `Lean4Lean.Verify.TypeChecker.ScopedComparison] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "scoped auxiliary module absent"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned scoped auxiliary axiom {name}"
        if let some proof := information.value? then
          if proof.hasSorry then throwError "owned scoped auxiliary admission {name}"
        let dependencies ← collectAxioms name
        for dependency in dependencies do
          unless baseline.contains dependency || native.contains dependency do
            throwError "unexpected scoped auxiliary dependency {dependency} in {name}"
        owned := owned + 1
  logInfo m!"{owned} exhaustive owned scoped inference/comparison declarations audited against original semantic worker and native scope baselines; inherited admissions remain explicit; no owned axioms or proof admissions"
  nativeControls

end ScopedAuxComparisonTest
