import Lean4Lean.Verify.InductiveHeaderCheckerTransport

namespace InductiveHeaderCheckerTransportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive

example {root : TypeChecker.VContext} {reader current : Context} {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual : Kernel.Environment}
    (stage : HeaderAxiomContinuation root reader nparams types stats current actual) :
    HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual stage.shadow :=
  stage.lookups

example {root : TypeChecker.VContext} {reader current : Context} {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual : Kernel.Environment}
    (stage : HeaderAxiomContinuation root reader nparams types stats current actual)
    (fresh : ConstructorsFresh actual types) (name : Name) (header : InductiveVal)
    (lookup : actual.find? name = some (.inductInfo header))
    (different : actual.find? name ≠ stage.shadow.find? name) :
    ∀ constructor ∈ header.ctors, actual.find? constructor = none :=
  HeaderAxiomLookupAgreement.missingChangedHeader stage.lookups stage.constructorHeaders
    fresh name header lookup different

example {changed : Name → Prop} {actual shadow : Kernel.Environment}
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (name : Name) (untouched : ¬changed name) :
    actual.find? name = shadow.find? name :=
  agreement.unchanged name untouched

example {changed : Name → Prop} {actual shadow : Kernel.Environment}
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (expression : Expr) :
    TypeChecker.Inner.isDelta actual expression = TypeChecker.Inner.isDelta shadow expression :=
  agreement.delta expression

example {changed : Name → Prop} (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) :
    (TypeChecker.checkType (.const name levels) context state).WF fun result =>
      TypeChecker.checkType (.const name levels) { context with env := shadow } state = .ok result :=
  TypeChecker.checkType.headerConstantTransport context shadow agreement state name levels

example {changed : Name → Prop} (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (name : Name) (levels : List Level) :
    (TypeChecker.inferType (.const name levels) context state).WF fun result =>
      TypeChecker.inferType (.const name levels) { context with env := shadow } state = .ok result :=
  TypeChecker.inferType.headerConstantTransport context shadow agreement state name levels

example {changed : Name → Prop} (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (shadow : Kernel.Environment) (agreement : HeaderAxiomLookupAgreement changed context.env shadow)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.Inner.unfoldDefinition expression methods context state =
      TypeChecker.Inner.unfoldDefinition expression methods { context with env := shadow } state :=
  TypeChecker.Inner.unfoldDefinition.headerAxiomTransport methods context shadow agreement state expression

private def sortType : Expr := .sort (.succ .zero)

private def family (name : Name) (parameters indices : Nat) : InductiveType :=
  let result := mkAppN (.const name [])
    (((List.range parameters).toArray.map fun index => .bvar (parameters - index - 1)) ++
      (List.replicate indices (.const ``Nat.zero [])).toArray)
  let close := fun body => (List.range parameters).foldr (fun _ body =>
    .forallE `parameter sortType body .implicit) body
  let header := (List.range indices).foldr (fun _ body =>
    .forallE `index (.const ``Nat []) body .default) sortType
  { name, type := close header, ctors := [⟨name ++ `mk, close result⟩] }

private def sameConstant : Option ConstantInfo → Option ConstantInfo → Bool
  | none, none => true
  | some (.axiomInfo first), some (.axiomInfo second) => first == second
  | some (.defnInfo first), some (.defnInfo second) => first == second
  | some (.thmInfo first), some (.thmInfo second) => first == second
  | some (.opaqueInfo first), some (.opaqueInfo second) => first == second
  | some (.quotInfo first), some (.quotInfo second) =>
    first.toConstantVal == second.toConstantVal && match first.kind, second.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | some (.inductInfo first), some (.inductInfo second) =>
    first.toConstantVal == second.toConstantVal && first.numParams == second.numParams &&
      first.numIndices == second.numIndices && first.all == second.all && first.ctors == second.ctors &&
      first.numNested == second.numNested && first.isRec == second.isRec &&
      first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive
  | some (.ctorInfo first), some (.ctorInfo second) => first == second
  | some (.recInfo first), some (.recInfo second) => first == second
  | _, _ => false

private def sameState (first second : TypeChecker.State) : Bool :=
  first.ngen.namePrefix == second.ngen.namePrefix && first.ngen.idx == second.ngen.idx &&
    first.inferTypeI.toList == second.inferTypeI.toList && first.inferTypeC.toList == second.inferTypeC.toList &&
    first.whnfCoreCache.toList == second.whnfCoreCache.toList && first.whnfCache.toList == second.whnfCache.toList &&
    first.eqvManager.toNodeMap.toList == second.eqvManager.toNodeMap.toList &&
    (first.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) ==
      (second.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) &&
    first.failure.toList == second.failure.toList && first.unfold.toList == second.unfold.toList

private def checkExpressionResult (actual shadow : Except Kernel.Exception (Expr × TypeChecker.State)) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "constant checker transport changed its expression or full state"
  | .error _, .error _ => pure ()
  | _, _ => throwError "constant checker transport changed success/failure"

private def checkUnfoldResult
    (actual shadow : Except Kernel.Exception (Option Expr × TypeChecker.State)) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "delta transport changed its optional expression or full state"
  | _, _ => throwError "delta transport unexpectedly failed"

private def seededState : TypeChecker.State :=
  let (_, manager) := EquivManager.toNode (.const ``Nat []) {}
  { ngen := { namePrefix := `_header_transport_checker, idx := 17 }
    inferTypeI := ({} : InferCache).insert (.const ``Nat []) sortType
    inferTypeC := ({} : InferCache).insert (.const ``Nat []) sortType
    whnfCoreCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    whnfCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (.const ``Nat [], sortType)
    unfold := ({} : InferCache).insert (.const `TransportUniverseAlias [.zero]) (.sort .zero) }

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment) (nparams : Nat)
    (types : Array InductiveType) (universes : List Name := []) : MetaM Unit := do
  unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes nparams types.toList false) none).isOk do
    throwError "native kernel rejected checker transport fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env, lparams := universes, safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes nparams types (fun stats => do
          let actual ← declareInductiveTypes stats nparams types 0 isUnsafe
          return (stats, ← read, actual)) reader
        | throwError "checker transport header checkpoint failed"
      let infos := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo info) => info
        | _ => default
      let shadow := headerAxiomView env infos
      let changed := types.toList.map InductiveType.name
      for (name, information) in actual.constants.toList do
        if changed.contains name then
          let some (.inductInfo header) := actual.find? name
            | throwError "checker transport changed name is not a native header"
          unless sameConstant (shadow.find? name) (some (headerAxiomInfo header)) do
            throwError "checker transport changed header is not its exact axiom view"
        else
          unless sameConstant (shadow.find? name) (some information) do
            throwError "checker transport changed an exact non-header record"
      for (name, _) in shadow.constants.toList do
        unless (actual.find? name).isSome do
          throwError "checker transport invented an extra shadow name"
      for type in types do
        for constructor in type.ctors do
          if (actual.find? constructor.name).isSome || (shadow.find? constructor.name).isSome then
            throwError "checker transport freshness fixture contains a future constructor"
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
        throwError "checker transport fixture did not accept actual constructor checking"
      let .ok _ := declareConstructors stats types isUnsafe { current with env := actual }
        | throwError "checker transport fixture did not reach successful constructor registration"
      let checker : TypeChecker.Context := {
        env := actual, lctx := current.lctx, lparams := current.lparams, safety := current.safety, fuel := current.fuel }
      let shadowChecker := { checker with env := shadow }
      for state in [({} : TypeChecker.State), seededState] do
        let queries := (types.toList.map fun type => (type.name, universes.map Level.param)) ++
          [(``Nat, []), (``Nat.zero, []), (``List, [.zero]), (`TransportSortAlias, []),
            (`TransportUniverseAlias, [.zero]), (`TransportUniverseAlias, [.succ .zero]),
            (`TransportPartialAlias, []), (`TransportUnsafeAlias, []),
            (`TransportMissing, []), (`TransportUniverseAlias, [])]
        for (name, levels) in queries do
          let expression := Expr.const name levels
          checkExpressionResult (TypeChecker.checkType expression checker state)
            (TypeChecker.checkType expression shadowChecker state)
          checkExpressionResult (TypeChecker.inferType expression checker state)
            (TypeChecker.inferType expression shadowChecker state)
          for inferOnly in [false, true] do
            let first := TypeChecker.Inner.inferConstant checker name levels inferOnly
            let second := TypeChecker.Inner.inferConstant shadowChecker name levels inferOnly
            match first, second with
            | .ok first, .ok second => unless first == second do throwError "raw constant lookup changed its type"
            | .error _, .error _ => pure ()
            | _, _ => throwError "raw constant lookup changed success/failure"
          for action in [TypeChecker.Inner.unfoldDefinitionCore expression, TypeChecker.Inner.unfoldDefinition expression] do
            checkUnfoldResult (action.run checker state) (action.run shadowChecker state)
        let application : Expr := .app (.const `TransportUniverseAlias [.succ .zero]) (.const ``Nat.zero [])
        checkUnfoldResult ((TypeChecker.Inner.unfoldDefinition application).run checker state)
          ((TypeChecker.Inner.unfoldDefinition application).run shadowChecker state)
        for expression in ([.const ``Nat.zero [], .app (.const ``Nat.succ []) (.const ``Nat.zero []),
            .const `TransportMissing [], .sort .zero] : List Expr) do
          unless expression.isConstructorApp?' actual == expression.isConstructorApp?' shadow do
            throwError "constructor-app observation changed across header staging"
        for type in types do
          unless (TypeChecker.checkType (.const type.name (universes.map Level.param)) checker state).isOk do
            throwError "checker transport did not accept a new bare header constant"
        let zeroFuel := { checker with fuel := { checker.fuel with recDepth := 0 } }
        if (TypeChecker.checkType (.const ``Nat []) zeroFuel state).isOk ||
            (TypeChecker.checkType (.const ``Nat []) { zeroFuel with env := shadow } state).isOk then
          throwError "checker transport bypassed exhausted recursion fuel"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderCheckerTransport
    | throwError "checker transport production module absent"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound, ``Expr.looseBVarRange_eq]
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "checker transport module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "checker transport unexpected dependency {dependency} in {name}"
        if dependency == ``sorryAx then throwError "checker transport inherits sorryAx: {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"checker transport: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let imported ← getEnv
  let mut host := imported
  let mut env := imported.toKernelEnv
  let definitions : List DefinitionVal := [
    { name := `TransportSortAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
      value := sortType, hints := .abbrev, safety := .safe },
    { name := `TransportUniverseAlias, levelParams := [`u], type := .sort (.succ (.param `u)),
      value := .sort (.param `u), hints := .abbrev, safety := .safe },
    { name := `TransportPartialAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
      value := sortType, hints := .abbrev, safety := .partial },
    { name := `TransportUnsafeAlias, levelParams := [], type := .sort (.succ (.succ .zero)),
      value := sortType, hints := .abbrev, safety := .unsafe }]
  for definition in definitions do
    let .ok nextHost := host.addDeclCore 0 (.defnDecl definition) none
      | throwError "native checker transport seed failed"
    let .ok nextEnv := Lean4Lean.addDecl env (.defnDecl definition) true
      | throwError "checker transport seed failed"
    host := nextHost
    env := nextEnv
  checkBatch host env 0 #[family `TransportSingle 0 0]
  checkBatch host env 1 #[family `TransportMutualFirst 1 0, family `TransportMutualSecond 1 0]
  checkBatch host env 2 #[family `TransportParameters 2 0]
  checkBatch host env 0 #[family `TransportIndexed 0 2]
  let universeType : InductiveType := {
    name := `TransportUniverse, type := .sort (.param `u),
    ctors := [⟨`TransportUniverse.mk, .const `TransportUniverse [.param `u]⟩] }
  checkBatch host env 0 #[universeType] [`u]
  checkBatch host env 0 #[]
  logInfo "5 native-accepted checker transport fixtures and the empty checkpoint passed both safeties/primitive flags, exact old and changed-header lookups, future-constructor absence, bare constant inference/checking, full cache/state receipts, universe instantiation, delta/application unfolding, partial/unsafe/missing/level-mismatch and zero-fuel controls"

end InductiveHeaderCheckerTransportTest
