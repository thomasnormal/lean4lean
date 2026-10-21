import Lean4Lean.Verify.TypeChecker.ScopedMethods
import Lean.Util.CollectAxioms

namespace ScopedMethodsTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.TypeChecker

private def seven : Nat := 7

example (depth : Nat) : (Methods.withFuel depth).ScopeWF := Methods.withFuel.scopeWF

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    ((Methods.withFuel depth).whnfCore expression cheapProj).ScopeWF context state
      (fun normalized _ => context.FVarsBelow expression normalized ∧
        context.TrExpr normalized semantic ∧ NativeHeadScoped context.lctx' normalized) :=
  Methods.withFuel.scopeWF.whnfCore translated

example {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    ((Methods.withFuel depth).inferType expression inferOnly).ScopeWF context state
      (fun type _ => ∃ semantic semanticType, context.TrTyping expression type semantic semanticType) :=
  Methods.withFuel.scopeWF.inferType freeVariables translated

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    ((Methods.withFuel depth).isDefEqCore first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Methods.withFuel.scopeWF.isDefEqCore firstTranslation secondTranslation

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqCore' first second (Methods.withFuel depth)).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqCore'.scopeWF firstTranslation secondTranslation _ Methods.withFuel.scopeWF

example {context : VContext} {state : VState} {action : RecM Result} {post}
    (valid : action.ScopeWF context state post) : (RecM.run action).ScopeWF context state post := valid.run

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.whnfCore expression).ScopeWF context state
      (fun normalized _ => context.FVarsBelow expression normalized ∧
        context.TrExpr normalized semantic ∧ NativeHeadScoped context.lctx' normalized) :=
  TypeChecker.whnfCore.scopeWF translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.whnf expression).ScopeWF context state
      (fun normalized _ => context.FVarsBelow expression normalized ∧
        context.TrExpr normalized semantic ∧ NativeHeadScoped context.lctx' normalized) :=
  TypeChecker.whnf.scopeWF translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.inferType expression).ScopeWF context state
      (fun type _ => ∃ semanticType, context.TrTyping expression type semantic semanticType) :=
  TypeChecker.inferType.scopeWF translated

example {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (TypeChecker.checkType expression).ScopeWF context state
      (fun type _ => ∃ semantic semanticType, context.TrTyping expression type semantic semanticType) :=
  TypeChecker.checkType.scopeWF freeVariables

example {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (TypeChecker.isDefEq first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  TypeChecker.isDefEq.scopeWF firstTranslation secondTranslation

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment) {action : M Result} {post : Result → Prop}
    (valid : action.ScopeWF (VContext.mk' wellFormed safety levels fuel) {}
      (fun result _ => post result)) :
    (M.run environment safety {} levels fuel action).WF post := M.ScopeWF.run wellFormed valid

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment)
    (translated : (VContext.mk' wellFormed safety levels fuel).TrExprS expression semantic) :
    (M.run environment safety {} levels fuel (TypeChecker.whnf expression)).WF
      (fun normalized => (VContext.mk' wellFormed safety levels fuel).FVarsBelow expression normalized ∧
        (VContext.mk' wellFormed safety levels fuel).TrExpr normalized semantic ∧
        NativeHeadScoped {} normalized) :=
  M.ScopeWF.run wellFormed (TypeChecker.whnf.scopeWF translated)

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
  let literal := Expr.lit (.natVal 7)
  let different := Expr.lit (.natVal 8)
  let identity := Expr.lam `argument natural (.bvar 0) .default
  let renamed := Expr.lam `renamed natural (.bvar 0) .default
  let functionIdentifier : FVarId := ⟨`scopedMethodsFunction⟩
  let firstUnitIdentifier : FVarId := ⟨`scopedMethodsFirstUnit⟩
  let secondUnitIdentifier : FVarId := ⟨`scopedMethodsSecondUnit⟩
  let firstProofIdentifier : FVarId := ⟨`scopedMethodsFirstProof⟩
  let secondProofIdentifier : FVarId := ⟨`scopedMethodsSecondProof⟩
  let aliasIdentifier : FVarId := ⟨`scopedMethodsAlias⟩
  let boolAliasIdentifier : FVarId := ⟨`scopedMethodsBoolAlias⟩
  let functionType := Expr.forallE `argument natural natural .default
  let locals := ({} : LocalContext).mkLocalDecl functionIdentifier `function functionType .default
    |>.mkLocalDecl firstUnitIdentifier `firstUnit (.const ``Unit []) .default
    |>.mkLocalDecl secondUnitIdentifier `secondUnit (.const ``Unit []) .default
    |>.mkLocalDecl firstProofIdentifier `firstProof (.const ``True []) .default
    |>.mkLocalDecl secondProofIdentifier `secondProof (.const ``True []) .default
    |>.mkLetDecl aliasIdentifier `alias natural literal
    |>.mkLetDecl boolAliasIdentifier `boolAlias (.const ``Bool []) (.const ``Bool.true [])
  let function := Expr.fvar functionIdentifier
  let expanded := Expr.lam `argument natural (.app function (.bvar 0)) .default
  let addition := mkAppN (.const ``Nat.add []) #[.lit (.natVal 3), .lit (.natVal 4)]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, different]
  let projection := Expr.proj ``Prod 0 pair
  let boolTrue := Expr.const ``Bool.true []
  let boolExpression := mkAppN (.const ``Bool.and []) #[boolTrue, boolTrue]
  let controls : Array (Expr × Expr × Bool) := #[
    (literal, literal, true), (literal, different, false),
    (identity, renamed, true), (expanded, function, true),
    (.forallE `argument natural natural .default, .forallE `renamed natural natural .default, true),
    (.const ``seven [], literal, true), (addition, literal, true),
    (.app (.const ``Nat.succ []) (.lit (.natVal 6)), literal, true),
    (.lit (.strVal "ab"), .strLitToConstructor "ab", true),
    (.mdata {} literal, literal, true), (.letE `value natural literal (.bvar 0) false, literal, true),
    (projection, literal, true), (projection, .proj ``Prod 1 pair, false),
    (.fvar firstUnitIdentifier, .fvar secondUnitIdentifier, true),
    (.fvar firstProofIdentifier, .fvar secondProofIdentifier, true),
    (natural, .const ``Bool [], false),
    (boolExpression, boolTrue, true), (.fvar boolAliasIdentifier, boolTrue, true)]
  let entries : Array Expr := #[literal, .const ``seven [], addition, projection,
    .mdata {} literal, .letE `value natural literal (.bvar 0) false,
    .app identity literal, .fvar aliasIdentifier]
  let mut comparisonCount : Nat := 0
  let mut initializedComparisonCount : Nat := 0
  let mut entryCount : Nat := 0
  let mut initializedHeadCount : Nat := 0
  let mut universeCount : Nat := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager, fuel := { recDepth := fuel } }
        let methods := Methods.withFuel fuel
        for control in [:controls.size] do
          let (first, second, expected) := controls[control]!
          unless (TypeChecker.checkType first context {}).isOk && (TypeChecker.checkType second context {}).isOk do
            throwError "typed scoped-method comparison rejected at {control}"
          for reversed in [false, true] do
            let (left, right) := if reversed then (second, first) else (first, second)
            for action in [Inner.isDefEqCore' left right methods, methods.isDefEqCore left right,
                TypeChecker.isDefEq left right] do
              let mut state : State := {}
              for _ in [:2] do
                let .ok (equal, finalState) := action context state
                  | throwError "actual scoped dispatcher/method/public comparison rejected at {control}"
                unless equal == expected && stableCaches locals finalState do
                  throwError "actual scoped dispatcher/method/public comparison loses result/frame at {control}"
                state := finalState
                comparisonCount := comparisonCount + 1
            unless left.hasFVar || right.hasFVar do
              let .ok equal := M.run environment safety {} [] { recDepth := fuel }
                  (TypeChecker.isDefEq left right) | throwError "cold initialized comparison rejected"
              unless equal == expected do throwError "cold initialized comparison loses result"
              initializedComparisonCount := initializedComparisonCount + 1
        for source in [:entries.size] do
          let expression := entries[source]!
          for action in [methods.inferType expression true, methods.inferType expression false,
              TypeChecker.inferType expression, TypeChecker.checkType expression] do
            let mut state : State := {}
            for _ in [:2] do
              let .ok (type, finalState) := action context state | throwError "scoped inference entry rejected"
              let .ok (equal, checkedState) := methods.isDefEqCore type natural context finalState
                | throwError "scoped inferred-type comparison rejected"
              unless equal && stableCaches locals checkedState do throwError "scoped inference entry loses type/frame"
              state := checkedState
              entryCount := entryCount + 1
          for action in [methods.whnf expression, TypeChecker.whnf expression] do
            let mut state : State := {}
            for _ in [:2] do
              let .ok (normalized, finalState) := action context state | throwError "scoped full normalization rejected"
              unless normalized == literal && stableHead locals normalized && stableCaches locals finalState do
                throwError "scoped full normalization loses expected head/frame"
              state := finalState
              entryCount := entryCount + 1
          let coreActions := [TypeChecker.whnfCore expression] ++
            ([false, true].map fun cheapProj => methods.whnfCore expression cheapProj)
          for action in coreActions do
            let mut state : State := {}
            for _ in [:2] do
              let .ok (normalized, finalState) := action context state | throwError "scoped core normalization rejected"
              unless stableHead locals normalized && stableCaches locals finalState do
                throwError "scoped core normalization loses scoped head/frame"
              state := finalState
              entryCount := entryCount + 1
          unless expression.hasFVar do
            let .ok normalized := M.run environment safety {} [] { recDepth := fuel } (TypeChecker.whnf expression)
              | throwError "cold initialized scoped normalization rejected"
            unless normalized == literal && stableHead {} normalized do
              throwError "cold initialized scoped normalization loses expected head"
            initializedHeadCount := initializedHeadCount + 1
        let universeName := `scopedMethodsUniverse
        let levelContext : Context := { context with lparams := [universeName] }
        let firstPolymorphic := Expr.const ``id [.param universeName]
        let secondPolymorphic := Expr.const ``id [.max (.param universeName) .zero]
        unless (TypeChecker.checkType firstPolymorphic levelContext {}).isOk &&
            (TypeChecker.checkType secondPolymorphic levelContext {}).isOk do
          throwError "polymorphic scoped inputs rejected"
        for action in [Inner.isDefEqCore' firstPolymorphic secondPolymorphic methods,
            methods.isDefEqCore firstPolymorphic secondPolymorphic,
            TypeChecker.isDefEq firstPolymorphic secondPolymorphic] do
          let mut state : State := {}
          for _ in [:2] do
            let .ok (equal, finalState) := action levelContext state
              | throwError "polymorphic scoped comparison rejected"
            unless equal && stableCaches locals finalState do
              throwError "polymorphic scoped comparison loses result/frame"
            state := finalState
            universeCount := universeCount + 1
        let .ok equal := M.run environment safety {} [universeName] { recDepth := fuel }
            (TypeChecker.isDefEq firstPolymorphic secondPolymorphic)
          | throwError "polymorphic cold initialized comparison rejected"
        unless equal do throwError "polymorphic cold initialized comparison loses result"
        initializedComparisonCount := initializedComparisonCount + 1
  let context : Context := { env := environment, lctx := locals }
  let zero := Methods.withFuel 0
  unless !(zero.isDefEqCore literal literal context {}).isOk &&
      !(zero.whnf literal context {}).isOk && !(zero.whnfCore literal false context {}).isOk &&
      !(zero.inferType literal true context {}).isOk do throwError "zero method fields unexpectedly succeed"
  let zeroContext : Context := { context with fuel := { recDepth := 0 } }
  unless !(TypeChecker.isDefEq literal literal zeroContext {}).isOk &&
      !(TypeChecker.whnf literal zeroContext {}).isOk && !(TypeChecker.whnfCore literal zeroContext {}).isOk &&
      !(TypeChecker.inferType literal true zeroContext {}).isOk && !(TypeChecker.checkType literal zeroContext {}).isOk do
    throwError "configured zero-depth public entries unexpectedly succeed"
  unless !(M.run environment .safe {} [] { recDepth := 0 } (TypeChecker.whnf literal)).isOk do
    throwError "cold initialized zero-depth normalization unexpectedly succeeds"
  let .ok (equal, finalState) := (Methods.withFuel 1).isDefEqCore literal literal context {}
    | throwError "one-depth pure comparison rejected"
  unless equal && stableCaches locals finalState do throwError "one-depth comparison loses result/frame"
  let poisoned : State := { whnfCache := ({} : ExprMap Expr).insert natural (.fvar aliasIdentifier) }
  let .ok (_, poisonedFinal) := (Methods.withFuel 1).isDefEqCore literal literal context poisoned
    | throwError "scoped method cache-premise control rejected"
  unless !stableCaches locals poisonedFinal do throwError "scoped method cache premise disappeared"
  logInfo m!"{comparisonCount} actual typed cold/warm bidirectional dispatcher/method/public comparisons, {entryCount} method/public inference/checking/core/full entries, {initializedComparisonCount} cold-initialized comparisons, {initializedHeadCount} cold-initialized full heads and {universeCount} polymorphic cold/warm comparisons preserve expected results and scoped caches; both safeties/eager modes, fuels 32/128 and both cheap-projection flags; Boolean shortcut reader policy, universe-equivalent constant levels, proof/eta/unit helpers, primitives, aliases, metadata, lets, beta and projections covered; all zero method fields, configured public entries and cold normalization reject, actual depth-one pure comparison succeeds, poisoned-cache premise retained; arbitrary-fuel Methods.ScopeWF is now formally derived from the actual recursive workers, not fabricated; inherited semantic/native foundations remain explicit"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.ScopedMethods
    | throwError "scoped methods module absent"
  let baseline ← collectAxioms ``Methods.withFuel.WF
  let native := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  logInfo m!"existing semantic arbitrary-fuel method baseline: {repr baseline}"
  let mut owned : Nat := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned scoped methods axiom {name}"
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then throwError "owned scoped methods admission {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency || native.contains dependency do
          throwError "unexpected scoped methods dependency {dependency} in {name}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned dispatcher/arbitrary-fuel/run/public scoped declarations audited against original semantic methods and native scope foundations; inherited admissions remain explicit; no owned axioms or proof admissions"
  nativeControls

end ScopedMethodsTest
