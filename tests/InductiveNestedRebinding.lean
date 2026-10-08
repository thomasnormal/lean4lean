import Lean4Lean.Verify.InductiveNestedRebinding
import Lean4Lean.Verify.InductiveNestedRewrite
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive

namespace InductiveNestedRebindingTest

example (type : Expr) (ids : List FVarId) (depth : Nat) :
    (type.abstractFVars ids depth).looseBVarRange' ≤
      max type.looseBVarRange' (depth + ids.length) :=
  Expr.abstractFVars_looseBVarRange type ids depth

example (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hcontext : ParamContext numParams lctx params) (type : Expr)
    (htype : type.looseBVarRange' = 0) :
    (type.abstract params).looseBVarRange' ≤ numParams :=
  hcontext.abstract_scopedRange type htype

example (type : Expr) (params : List Name) (levels : List Level) :
    (type.instantiateLevelParams params levels).looseBVarRange' = type.looseBVarRange' :=
  Lean.Expr.instantiateLevelParams_looseBVarRange type params levels

example (env : Kernel.Environment) (hclosure : Lean4Lean.Environment.InductiveDeclRange env)
    (name : Name) (info : InductiveVal)
    (hget : env.get name = .ok (.inductInfo info)) (levels : List Level) :
    (info.type.instantiateLevelParams info.levelParams levels).looseBVarRange' = 0 :=
  Lean4Lean.Environment.InductiveDeclRange.inductiveType hclosure hget

example (env : Kernel.Environment) (hclosure : Lean4Lean.Environment.InductiveDeclRange env)
    (name : Name) (info : InductiveVal)
    (hget : env.get name = .ok (.inductInfo info))
    (ctorName : Name) (hctor : ctorName ∈ info.ctors) (ctorInfo : ConstructorVal)
    (hctorGet : env.get ctorName = .ok (.ctorInfo ctorInfo)) (levels : List Level) :
    (ctorInfo.type.instantiateLevelParams ctorInfo.levelParams levels).looseBVarRange' = 0 :=
  Lean4Lean.Environment.InductiveDeclRange.constructorType hclosure hget ctorName hctor ctorInfo hctorGet

example (numParams : Nat) (source target : LocalContext) (sourceParams params : Array Expr)
    (type : Expr) (env : Kernel.Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamContext numParams target params) (htype : type.looseBVarRange' = 0) :
    (replaceParams params type sourceParams env state).WF fun result =>
      result.1.looseBVarRange' = 0 ∧ result.2 = state :=
  replaceParams.noLooseBVars numParams source target sourceParams params type env state
    hsource htarget htype

example (result : Result) (numParams : Nat) (source : LocalContext)
    (sourceParams : Array Expr) (type : Expr) (env : Kernel.Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamValidity numParams result.lctx result.params)
    (htype : type.looseBVarRange' = 0) :
    (replaceParams result.params type sourceParams env state).WF fun returned =>
      (result.openAux (returned.1.abstract result.params)).hasLooseBVars = false :=
  replaceParams.finalAux_scope result numParams source sourceParams type env state
    hsource htarget htype

example (numParams : Nat) (source target : LocalContext) (sourceParams params : Array Expr)
    (type : Expr) (name : Name) (env : Kernel.Environment) (state : State)
    (hsource : ParamContext numParams source sourceParams)
    (htarget : ParamContext numParams target params)
    (hstate : state.NestedAuxScoped) (htype : type.looseBVarRange' = 0) :
    (do
      let entry ← replaceParams params type sourceParams
      modify fun state => { state with nestedAux := state.nestedAux.push (entry, name) }
      return entry : M Expr) env state |>.WF fun returned => returned.2.NestedAuxScoped :=
  replaceParams.pushNestedAuxScoped numParams source target sourceParams params type name env state
    hsource htarget hstate htype

example (numParams : Nat) (source lctx : LocalContext) (sourceParams As : Array Expr)
    (type : Expr) (env : Kernel.Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceIfNested lctx sourceParams As type env state).WF fun returned =>
      returned.2.NestedAuxScoped :=
  replaceIfNested.scope numParams source lctx sourceParams As type env state hsource htarget hstate

example (numParams : Nat) (source lctx : LocalContext) (sourceParams As : Array Expr)
    (type : Expr) (env : Kernel.Environment) (state : State)
    (hsource : ParamContext numParams lctx As)
    (htarget : ParamContext numParams source sourceParams)
    (hstate : state.NestedAuxScoped) :
    (replaceAllNested lctx sourceParams As type env state).WF fun returned =>
      returned.2.NestedAuxScoped :=
  replaceAllNested.scope numParams source lctx sourceParams As type env state hsource htarget hstate

private def parameterType (numParams : Nat) (dependent : Bool) : Expr :=
  if dependent then
    .forallE `A (.sort (.succ (.param `u)))
      (.forallE `value (.bvar 0) (.sort (.succ (.param `u))) .implicit) .implicit
  else
    (List.range numParams).foldr (fun index result =>
      .forallE (Name.mkNum `parameter index) (.sort (.succ (.param `u))) result .implicit)
      (.sort (.succ (.param `u)))

private def sourceCases (params : Array Expr) : List Expr :=
  let first := params[0]?.getD (.fvar ⟨`UnrelatedFreeVariable⟩)
  let last := params[params.size - 1]?.getD (.fvar ⟨`UnrelatedFreeVariable⟩)
  let sortType := Expr.sort (.succ (.param `u))
  let application := Expr.app first last
  [sortType, .const ``List [.param `u], first, .mvar ⟨`UncheckedMetavariable⟩,
    .lit (.natVal 3), application,
    .lam `bound sortType (.app first (.bvar 0)) .default,
    .forallE `bound first (.app last (.bvar 0)) .implicit,
    .letE `bound sortType first (.app last (.bvar 0)) false,
    .mdata {} application, .proj `ProjectionFixture 1 application,
    .lam `outer sortType
      (.forallE `inner (.bvar 0) (.app application (.bvar 1)) .default) .implicit]

private def sameState (expected actual : State) : Bool :=
  expected.ngen.namePrefix == actual.ngen.namePrefix && expected.ngen.idx == actual.ngen.idx &&
    expected.lvls == actual.lvls && expected.nextIdx == actual.nextIdx &&
    expected.nestedAux == actual.nestedAux &&
    expected.newTypes.map (·.name) == actual.newTypes.map (·.name)

private def checkRebinding (env : Kernel.Environment) (state : State) (target : Result)
    (sourceParams : Array Expr) (type expected : Expr) : MetaM Unit := do
  unless type.looseBVarRange' == 0 do
    throwError "positive rebinding fixture violates its source scope premise"
  let .ok (rebound, finalState) := replaceParams target.params type sourceParams env state
    | throwError "scoped parameter rebinding failed"
  unless rebound == expected && rebound.looseBVarRange' == 0 && !rebound.hasLooseBVars do
    throwError "parameter rebinding changed syntax or introduced loose variables"
  unless sameState state finalState do
    throwError "parameter rebinding modified its preprocessing state"
  let auxiliary := rebound.abstract target.params
  unless auxiliary.looseBVarRange' ≤ target.nparams do
    throwError "final auxiliary abstraction exceeds its parameter range"
  unless !(target.openAux auxiliary).hasLooseBVars do
    throwError "opening the rebound/abstracted auxiliary left loose variables"
  unless target.openAux auxiliary == rebound do
    throwError "opening the auxiliary failed its independent syntax comparison"

private def checkContexts (env : Kernel.Environment) (numParams : Nat)
    (generator : NameGenerator) (dependent : Bool) : MetaM Unit := do
  let header := parameterType numParams dependent
  let state : State := {
    ngen := generator, lvls := [.param `u], nextIdx := 7,
    nestedAux := #[(.const ``Nat [], `StoredAux)],
    newTypes := #[{ name := `StoredType, type := .sort (.succ .zero), ctors := [] }] }
  let .ok ((_, _, sourceParams), _) := withParams header numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state
    | throwError "source parameter extraction failed"
  let indType : InductiveType := { name := `RebindingTarget, type := header, ctors := [] }
  let .ok target := StateT.run' (ElimNestedInductive.run ({} : FuelConfig).inductiveFuel
      numParams [indType] env) {
        ngen := { namePrefix := `TargetSeed, idx := generator.idx + 100 },
        lvls := [.param `u], newTypes := #[indType] }
    | throwError "target preprocessing failed"
  unless sourceParams.size == numParams && target.params.size == numParams &&
      target.params == target.lctx.getFVars do
    throwError "fixture parameter extraction changed count or chronological order"
  for (type, expected) in (sourceCases sourceParams).zip (sourceCases target.params) do
    checkRebinding env state target sourceParams type expected

private def wrapDepth (depth : Nat) (body : Expr) : Expr :=
  (List.range depth).foldr (fun index result =>
    .lam (Name.mkNum `bound index) (.sort (.succ .zero)) result .default) body

private def checkRawAbstraction (ids : List FVarId) (depth : Nat) (type : Expr) : MetaM Unit := do
  let params := (ids.map Expr.fvar).toArray
  let structural := type.abstractFVars ids depth
  let native := (List.range depth).foldl (fun result _ => result.bindingBody!)
    ((wrapDepth depth type).abstract params)
  unless structural == native do
    throwError "raw abstraction disagrees with native under binder depth {depth}"
  unless structural.looseBVarRange' ≤ max type.looseBVarRange' (depth + ids.length) do
    throwError "raw abstraction violated its structural range bound"
  unless structural.looseBVarRange' == native.looseBVarRange do
    throwError "structural abstraction range disagrees with native metadata"

private def checkPremiseBoundaries (env : Kernel.Environment) : MetaM Unit := do
  let sourceParams := #[Expr.fvar ⟨`SourceParameter⟩]
  let targetParams := #[Expr.fvar ⟨`TargetParameter⟩]
  let state : State := { lvls := [], newTypes := #[] }
  let loose := Expr.bvar 0
  unless loose.abstract sourceParams == loose && loose.hasLooseBVars do
    throwError "native abstraction no longer preserves this loose source variable"
  let .ok (captured, _) := replaceParams targetParams loose sourceParams env state
    | throwError "helper source-scope boundary unexpectedly rejects"
  unless captured == targetParams[0]! && !captured.hasLooseBVars do
    throwError "source-scope boundary no longer demonstrates parameter capture"
  let .ok (unscoped, _) := replaceParams #[.bvar 0] sourceParams[0]! sourceParams env state
    | throwError "helper target-context boundary unexpectedly rejects"
  unless unscoped == loose && unscoped.hasLooseBVars do
    throwError "target-context boundary no longer demonstrates scope failure"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta do
  for theoremName in [``Expr.abstractFVars_looseBVarRange, ``ParamContext.params_eq_fvars,
      ``replaceParams.eq_ok] do
    audit theoremName []
  for theoremName in [``ParamContext.abstract_range, ``ParamContext.abstract_scopedRange] do
    audit theoremName [``Expr.abstract_eq]
  let interfaces := [``Expr.abstract_eq, ``Expr.instantiate_eq, ``Expr.instantiateRev_eq]
  for theoremName in [``replaceParams.noLooseBVars, ``replaceParams.auxRange] do
    audit theoremName interfaces
  audit ``replaceParams.finalAux_scope (``Expr.looseBVarRange_eq :: interfaces)
  for theoremName in [``State.NestedAuxScoped.empty, ``State.NestedAuxScoped.push,
      ``mkUniqueName.frame] do
    audit theoremName []
  audit ``NestedAppScope.constPrefixRange [``Expr.looseBVarRange_eq,
    `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``replaceParams.pushNestedAuxScoped interfaces
  audit ``replaceIfNested.scope [``Expr.looseBVarRange_eq, ``Expr.abstract_eq, ``Expr.instantiate_eq,
    ``Expr.instantiateRev_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``replaceIfNested.range [``Expr.looseBVarRange_eq, ``Expr.abstract_eq, ``Expr.instantiate_eq,
    ``Expr.instantiateRev_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``replaceAllNested.scope [``Expr.looseBVarRange_eq, ``Expr.abstract_eq, ``Expr.instantiate_eq,
    ``Expr.instantiateRev_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``replaceAllNested.range [``Expr.looseBVarRange_eq, ``Expr.abstract_eq, ``Expr.instantiate_eq,
    ``Expr.instantiateRev_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``replaceAllNested.rangeWithNewTypes [``Expr.looseBVarRange_eq, ``Expr.abstract_eq,
    ``Expr.instantiate_eq, ``Expr.instantiateRev_eq, `Lean.Expr.mkAppRangeAux.eq_def]
  audit ``Lean.Expr.instantiateLevelParams_looseBVarRange [``Lean.Expr.replace_eq,
    ``Lean.Level.hasParam_eq, ``Lean.Expr.hasLevelParam_eq]
  for theoremName in [``Lean4Lean.Environment.InductiveDeclRange.inductiveType,
      ``Lean4Lean.Environment.InductiveDeclRange.constructorType] do
    audit theoremName [``Lean.Expr.replace_eq, ``Lean.Level.hasParam_eq,
      ``Lean.Expr.hasLevelParam_eq]
  audit ``Expr.instantiateRevRange_looseBVarRange [``Expr.instantiateRevRange_eq,
    ``Expr.instantiateRev_eq, ``Expr.instantiate_eq]
  audit ``instantiateForallParams.range [``Expr.instantiateRevRange_eq,
    ``Expr.instantiateRev_eq, ``Expr.instantiate_eq]
  audit ``mkAppN_range []
  audit ``mkAppRange_tail_range [``Lean.Expr.mkAppRangeAux.eq_def]
  audit ``withParams.contextScope [``Lean.PersistentArray.toList'_push]
  audit ``withParams.contextRange [``Lean.PersistentArray.toList'_push,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Expr.instantiate1_eq]
  for theoremName in [``run.loop.nestedAuxScoped, ``run.loop.newTypesRange, ``run.nestedAuxScoped] do
    audit theoremName [``Lean.PersistentArray.toList'_push, ``Expr.looseBVarRange_eq,
      ``Expr.abstract_eq, ``Expr.instantiate_eq, ``Expr.instantiateRev_eq,
      ``Expr.abstractRange_eq, ``Lean.PersistentHashMap.WF.find?_eq,
      ``Lean.PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq,
      `Lean.Expr.mkAppRangeAux.eq_def]
  let env := (← Lean.getEnv).toKernelEnv
  for generator in [NameGenerator.mk `_nested_fresh 0, { namePrefix := `SourceSeed, idx := 17 }] do
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      checkContexts env numParams generator false
    checkContexts env 2 generator true
  let first : FVarId := ⟨`FirstParameter⟩
  let second : FVarId := ⟨`SecondParameter⟩
  for ids in [[], [first], [first, first], [first, second], [second, first]] do
    let cases := sourceCases (ids.map Expr.fvar).toArray ++
      [.bvar 0, .bvar 8, .lam `loose (.bvar 4) (.bvar 3) .default]
    for depth in [0, 1, 2, 5] do
      for type in cases do
        checkRawAbstraction ids depth type
  checkPremiseBoundaries env
  logInfo "checked thirty-one proof audits, 216 scoped rebinding/auxiliary comparisons, 300 raw abstraction comparisons, and two necessary-premise boundaries"

end InductiveNestedRebindingTest
