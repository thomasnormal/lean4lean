import Lean4Lean.Verify.TypeChecker.HeadShape
import Lean.Util.CollectAxioms

namespace WHNFHeadShapeTest
open Lean hiding Environment Exception
open Lean4Lean

private def aliasedType : Type := Nat

private def universeType.{universeLevel} : Type (universeLevel + 1) := Type universeLevel

example : TypeChecker.HeadCacheWF {} := TypeChecker.HeadCacheWF.empty

example (expression : Expr) (cheapRec cheapProj : Bool) (methods : TypeChecker.Methods)
    (valid : methods.HeadWF)
    (recursorFrame : ∀ expression cheapRec cheapProj,
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods).HeadWF (fun _ => True))
    (context : TypeChecker.Context) (state : TypeChecker.State) (caches : TypeChecker.HeadCacheWF state)
    (normalized : Expr) (finalState : TypeChecker.State)
    (accepted : TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods context state =
      .ok (normalized, finalState)) :
    TypeChecker.HeadCacheWF finalState ∧ NativeHeadClean normalized :=
  TypeChecker.Inner.whnfCore'.headWF expression cheapRec cheapProj methods valid recursorFrame
    context state caches normalized finalState accepted

example (expression : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (recursorFrame : ∀ expression cheapRec cheapProj,
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods).HeadWF (fun _ => True))
    (context : TypeChecker.Context) (state : TypeChecker.State) (caches : TypeChecker.HeadCacheWF state)
    (normalized : Expr) (finalState : TypeChecker.State)
    (accepted : TypeChecker.Inner.whnf' expression methods context state = .ok (normalized, finalState)) :
    TypeChecker.HeadCacheWF finalState ∧ NativeHeadClean normalized :=
  TypeChecker.Inner.whnf'.headWF expression methods valid recursorFrame
    context state caches normalized finalState accepted

example (key : Expr) :
    ¬TypeChecker.HeadCacheWF { whnfCoreCache := ({} : ExprMap Expr).insert key (.mdata {} (.sort .zero)) } := by
  intro caches
  have clean := caches.1 key (.mdata {} (.sort .zero)) (by simp)
  cases clean.1

example (key : Expr) :
    ¬TypeChecker.HeadCacheWF {
      whnfCache := ({} : ExprMap Expr).insert key
        (.letE `value (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false) } := by
  intro caches
  have clean := caches.2 key
    (.letE `value (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false) (by simp)
  cases clean.2

private def cleanHead (expression : Expr) : Bool := !expression.isMData && !expression.isLet

private def cleanCaches (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => cleanHead entry.2) &&
    state.whnfCache.toList.all (fun entry => cleanHead entry.2)

private def inputs : Array Expr := Id.run do
  let sort := Expr.sort (.succ .zero)
  let quantified := Expr.forallE `index sort (.mdata {} sort) .default
  let identity := Expr.lam `value sort (.bvar 0) .default
  let hidden := Expr.letE `value sort sort (.mdata {} (.bvar 0)) false
  let mut expressions := #[sort, quantified, .mdata {} quantified, hidden,
    .app identity quantified, .mdata {} (.app identity hidden),
    mkApp2 (.lam `first sort (.lam `second sort (.bvar 1) .default) .default) quantified sort,
    .proj ``Prod 0 (mkApp4 (.const ``Prod.mk [.zero, .zero]) sort sort sort sort),
    .proj ``Prod 0 (.fvar ⟨`plain⟩),
    .fvar ⟨`plain⟩, .fvar ⟨`localLet⟩, .lit (.strVal "head"),
    .const ``aliasedType [], .const ``universeType [.zero],
    .app (.const ``Nat.succ []) (.lit (.natVal 4))]
  for operation in [``Nat.add, ``Nat.mul, ``Nat.pow, ``Nat.sub, ``Nat.beq, ``Nat.ble,
      ``Nat.shiftLeft, ``Nat.div, ``Nat.shiftRight, ``Nat.mod] do
    expressions := expressions.push (mkApp2 (.const operation []) (.lit (.natVal 4)) (.lit (.natVal 2)))
  return expressions

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let sort := Expr.sort (.succ .zero)
  let locals := ({} : LocalContext).mkLetDecl ⟨`localLet⟩ `value sort (.mdata {} sort)
  let methods := TypeChecker.Methods.withFuel 32
  let mut coreCount := 0
  let mut fullCount := 0
  let mut dirtyCount := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      let context : TypeChecker.Context := { env := environment, lctx := locals, safety, eagerReduce := eager }
      for expression in inputs do
        for cheapRec in [false, true] do
          for cheapProj in [false, true] do
            let mut state : TypeChecker.State := {}
            for _ in [:2] do
              let .ok (normalized, finalState) := TypeChecker.Inner.whnfCore' expression cheapRec cheapProj methods context state
                | throwError "native core head-shape control failed"
              unless cleanHead normalized && cleanCaches finalState do
                throwError "native core returned a dirty head or cache"
              state := finalState
              coreCount := coreCount + 1
        let mut state : TypeChecker.State := {}
        for _ in [:2] do
          let .ok (normalized, finalState) := TypeChecker.Inner.whnf' expression methods context state
            | throwError "native full head-shape control failed"
          unless cleanHead normalized && cleanCaches finalState do
            throwError "native full returned a dirty head or cache"
          state := finalState
          fullCount := fullCount + 1
      let key := Expr.letE `value sort sort (.bvar 0) false
      let dirty := Expr.mdata {} sort
      let poisoned : TypeChecker.State := {
        whnfCoreCache := ({} : ExprMap Expr).insert key dirty
        whnfCache := ({} : ExprMap Expr).insert key dirty }
      for cheapRec in [false, true] do
        for cheapProj in [false, true] do
          let .ok (_, cleanState) := TypeChecker.Inner.whnfCore' key cheapRec cheapProj methods context {}
            | throwError "native core cache policy control failed"
          unless cleanState.whnfCoreCache[key]?.isSome == (!cheapRec && !cheapProj) do
            throwError "native core cheap-flag insertion policy changed"
          if (TypeChecker.Inner.whnfCore' key cheapRec cheapProj (TypeChecker.Methods.withFuel 0) context {}).isOk then
            throwError "cold core worker escaped exhausted callback fuel"
          let .ok (normalized, _) := TypeChecker.Inner.whnfCore' key cheapRec cheapProj methods context poisoned
            | throwError "poisoned core cache control unexpectedly rejected"
          unless normalized == dirty && !cleanHead normalized do
            throwError "core cache invariant negative control lost its dirty cache hit"
          dirtyCount := dirtyCount + 1
      let .ok (normalized, _) := TypeChecker.Inner.whnf' key methods context poisoned
        | throwError "poisoned full cache control unexpectedly rejected"
      unless normalized == dirty && !cleanHead normalized do
        throwError "full cache invariant negative control lost its dirty cache hit"
      dirtyCount := dirtyCount + 1
      if (TypeChecker.Inner.whnf'.loop key 0 methods context {}).isOk then
        throwError "zero-fuel full worker unexpectedly accepted"
  logInfo m!"{coreCount} native core and {fullCount} full cold/warm head/cache controls pass; {dirtyCount} poisoned-cache negative controls demonstrate the initial invariant is necessary; both safeties/eager modes, all cheap flags, metadata/let/beta/fvar/projection/nat/string and monomorphic/polymorphic delta paths covered; no strong semantic checker is fabricated"

run_meta
  let environment ← getEnv
  let moduleName := `Lean4Lean.Verify.TypeChecker.HeadShape
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "head-shape module absent"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned head-shape axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected head-shape dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned native head-shape declarations audited against three logical foundations and three existing native representation axioms, without checker/metatheory admissions"
  nativeControls

end WHNFHeadShapeTest
