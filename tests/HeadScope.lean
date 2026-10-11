import Lean4Lean.Verify.TypeChecker.HeadScope
import Lean.Util.CollectAxioms

namespace HeadScopeTest
open Lean hiding Environment Exception
open Lean4Lean
open Kernel
open TypeChecker.Inner

example (name : Name) (binder : BinderInfo) (domain : Expr) (methods : TypeChecker.Methods) :
    (withLocalDecl name binder domain (fun _ => (pure () : TypeChecker.RecM Unit)) methods).HeadScopeWF :=
  withLocalDecl.headScopeWF name binder domain (fun _ => pure ()) methods
    (fun _ => TypeChecker.M.HeadScopeWF.pure ())

example (name : Name) (type value : Expr) (methods : TypeChecker.Methods) :
    (withLetDecl name type value (fun _ => (pure () : TypeChecker.RecM Unit)) methods).HeadScopeWF :=
  withLetDecl.headScopeWF name type value (fun _ => pure ()) methods
    (fun _ => TypeChecker.M.HeadScopeWF.pure ())

example (first second : TypeChecker.M Unit) (initial : first.HeadScopeWF) (next : second.HeadScopeWF) :
    (first >>= fun _ => second).HeadScopeWF := initial.bind (fun _ => next)

private def cleanHead (expression : Expr) : Bool := !expression.isMData && !expression.isLet

private def stableHead (locals : LocalContext) (expression : Expr) : Bool :=
  cleanHead expression && match expression with
    | .fvar identifier => !TypeChecker.Inner.isLetFVar locals identifier
    | _ => true

private def stableCaches (locals : LocalContext) (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => stableHead locals entry.2) &&
    state.whnfCache.toList.all (fun entry => stableHead locals entry.2)

private def reservedNames (generator : NameGenerator) : Expr → Bool
  | .fvar identifier => match identifier.name with
    | .num namePrefix index => namePrefix != generator.namePrefix || index < generator.idx
    | _ => true
  | .app function argument => reservedNames generator function && reservedNames generator argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
    reservedNames generator domain && reservedNames generator body
  | .letE _ type value body _ =>
    reservedNames generator type && reservedNames generator value && reservedNames generator body
  | .mdata _ body | .proj _ _ body => reservedNames generator body
  | _ => true

private def reservedCaches (state : TypeChecker.State) : Bool :=
  state.whnfCoreCache.toList.all (fun entry => reservedNames state.ngen entry.2) &&
    state.whnfCache.toList.all (fun entry => reservedNames state.ngen entry.2)

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := .const ``Nat []
  let literal := .lit (.natVal 7)
  let generator : NameGenerator := { namePrefix := `headScopeFresh, idx := 1 }
  let old : FVarId := ⟨.num generator.namePrefix 0⟩
  let locals := ({} : LocalContext).mkLocalDecl old `old natural .default
  let localAction : TypeChecker.RecM (Expr × Expr × LocalContext × LocalContext) := do
    let (core, full, inside) ← withLocalDecl `fresh .default natural fun boundExpression => do
      let core ← whnfCore (.mdata {} boundExpression)
      let full ← whnf (.mdata {} boundExpression)
      return (core, full, ← getLCtx)
    return (core, full, inside, ← getLCtx)
  let letAction : TypeChecker.RecM (Expr × Expr × LocalContext × LocalContext) := do
    let (core, full, inside) ← withLetDecl `fresh natural literal fun boundExpression => do
      let core ← whnfCore (.mdata {} boundExpression)
      let full ← whnf (.mdata {} boundExpression)
      return (core, full, ← getLCtx)
    return (core, full, inside, ← getLCtx)
  let mut normalizations := 0
  let mut scopes := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for fuel in [32, 128] do
        let methods := TypeChecker.Methods.withFuel fuel
        let context : TypeChecker.Context := {
          env := environment, safety, lctx := locals, eagerReduce := eager, fuel := { recDepth := fuel } }
        for warm in [false, true] do
          let mut state : TypeChecker.State := { ngen := generator }
          if warm then
            let .ok (head, initial) := TypeChecker.whnf (.mdata {} (.fvar old)) context state
              | throwError "actual initial warm normalization rejected"
            unless head == .fvar old && stableCaches locals initial && reservedCaches initial do
              throwError "actual initial warm normalization lost scoped caches"
            state := initial
          for _ in [0:4] do
            let localId : FVarId := ⟨state.ngen.curr⟩
            let .ok ((core, full, inside, outside), localState) := localAction methods context state
              | throwError "actual fresh local scope normalization rejected"
            unless core == .fvar localId && full == core &&
                (inside.find? localId).isSome && (outside.find? localId).isNone &&
                (outside.find? old).isSome && !TypeChecker.Inner.isLetFVar inside localId &&
                localState.ngen.idx == state.ngen.idx + 1 &&
                stableCaches inside localState && stableCaches outside localState && reservedCaches localState do
              throwError "actual fresh local entry/exit or scoped caches differ"
            let letId : FVarId := ⟨localState.ngen.curr⟩
            let .ok ((core, full, inside, outside), letState) := letAction methods context localState
              | throwError "actual fresh let scope normalization rejected"
            unless core == literal && full == literal && TypeChecker.Inner.isLetFVar inside letId &&
                (outside.find? letId).isNone && (outside.find? old).isSome &&
                letState.ngen.idx == localState.ngen.idx + 1 &&
                stableCaches inside letState && stableCaches outside letState && reservedCaches letState do
              throwError "actual fresh let entry/exit or scoped caches differ"
            state := letState
            normalizations := normalizations + 4
            scopes := scopes + 2
  let identifier : FVarId := ⟨generator.curr⟩
  let future := Expr.fvar identifier
  let empty : LocalContext := {}
  let futureLet := empty.mkLetDecl identifier `future natural literal
  unless cleanHead future && stableHead empty future && !stableHead futureLet future do
    throwError "unreserved future cached head precondition control disappeared"
  let invalid : TypeChecker.State := {
    ngen := generator, whnfCoreCache := ({} : ExprMap Expr).insert future future,
    whnfCache := ({} : ExprMap Expr).insert future future }
  unless stableCaches empty invalid && !reservedCaches invalid && !stableCaches futureLet invalid do
    throwError "unreserved cache reuse control disappeared"
  let shadow := futureLet.mkLocalDecl identifier `shadow natural .default
  unless stableHead shadow future && !stableHead futureLet future do
    throwError "nonfresh shadowing scope-exit precondition control disappeared"
  let zero := TypeChecker.Methods.withFuel 0
  let zeroContext : TypeChecker.Context := { env := environment, fuel := { recDepth := 0 } }
  unless !(letAction zero zeroContext {}).isOk do
    throwError "zero-fuel scoped normalization unexpectedly accepted"
  logInfo m!"{normalizations} actual core/full normalizations across {scopes} fresh local/let scopes retain expected heads, restored readers, advanced generators, scoped caches and reserved cached names; both safeties/eager modes, fuels 32/128, cold/warm states; local-let, unreserved-cache, nonfresh-shadowing and zero-fuel precondition controls pass; stronger worker/fuel and semantic WHNF closure remain open"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.HeadScope
    | throwError "native head-scope module absent"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push]
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned native head-scope axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected head-scope dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned native scope/cache/allocation/frame declarations audited against logical/native representation foundations and three existing local-context container interfaces; no checker/metatheory admissions"
  nativeControls

end HeadScopeTest
