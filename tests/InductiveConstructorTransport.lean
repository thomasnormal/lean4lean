import Lean4Lean.Verify.InductiveConstructorContinuation

namespace InductiveConstructorTransportTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment

example (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow)
    (types : Array InductiveType) (stats : InductiveStats) (isUnsafe : Bool)
    (accepted : checkConstructors types stats isUnsafe reader = .ok ()) :
    checkConstructors types stats isUnsafe { reader with env := shadow } = .ok () :=
  checkConstructors.headerAxiomTransport types stats isUnsafe reader shadow metadata () accepted

example (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow)
    (stats : InductiveStats) (isUnsafe : Bool) (parent : Nat) (constructor : Name)
    (type : Expr) (index fuel : Nat)
    (accepted : checkConstructors.loop stats isUnsafe parent constructor type index fuel reader = .ok ()) :
    checkConstructors.loop stats isUnsafe parent constructor type index fuel { reader with env := shadow } = .ok () :=
  checkConstructors.loop.headerAxiomTransport stats isUnsafe parent constructor type index fuel reader shadow metadata () accepted

example (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow)
    (stats : InductiveStats) (constructor : Name) (type : Expr) (index fuel : Nat)
    (accepted : checkPositivity.loop stats constructor index type fuel reader = .ok ()) :
    checkPositivity.loop stats constructor index type fuel { reader with env := shadow } = .ok () :=
  checkPositivity.loop.headerAxiomTransport stats constructor index type fuel reader shadow metadata () accepted

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (fresh : ConstructorsFresh actual types) (constructors : NativeConstructorParentClosure actual)
    (recursors : ∀ name information, actual.find? name = some (.recInfo information) →
      ∃ header, stage.shadow.find? information.getMajorInduct = some (.inductInfo header))
    (quotInit : actual.quotInit = stage.shadow.quotInit) (isUnsafe : Bool)
    (accepted : checkConstructors types stats isUnsafe { reader with env := actual } = .ok ()) :
    checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok () ∧
      stats.AcceptedConstructorTraces types isUnsafe { reader with env := stage.shadow } :=
  stage.acceptedConstructors isUnsafe fresh constructors recursors quotInit () accepted

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []
private def zero : Expr := .const ``Nat.zero []

private def closeParameters (parameters : Nat) (body : Expr) : Expr :=
  (List.range parameters).foldr (fun _ body => .forallE `parameter sortType body .implicit) body

private def parentAt (name : Name) (parameters fields : Nat) : Expr :=
  mkAppN (.const name []) ((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1))

private def family (name : Name) (parameters : Nat := 0) : InductiveType :=
  { name, type := closeParameters parameters sortType
    ctors := [
      ⟨name ++ `base, closeParameters parameters (parentAt name parameters 0)⟩,
      ⟨name ++ `natural, closeParameters parameters (.forallE `value natural (parentAt name parameters 1) .default)⟩,
      ⟨name ++ `recursive, closeParameters parameters
        (.forallE `child (parentAt name parameters 0) (parentAt name parameters 1) .default)⟩,
      ⟨name ++ `higher, closeParameters parameters
        (.forallE `children (.forallE `index natural (parentAt name parameters 1) .default)
          (parentAt name parameters 1) .default)⟩] }

private def indexedFamily (name : Name) : InductiveType :=
  { name, type := .forallE `index natural sortType .default
    ctors := [⟨name ++ `base, mkApp (.const name []) zero⟩,
      ⟨name ++ `indexed, .forallE `index natural
        (.forallE `child (mkApp (.const name []) (.bvar 0)) (mkApp (.const name []) (.bvar 1)) .default) .default⟩] }

private def dependentFamily (name : Name) : InductiveType :=
  let close := fun body => .forallE `type sortType (.forallE `value (.bvar 0) body .default) .implicit
  let result := fun fields => mkAppN (.const name []) #[.bvar (fields + 1), .bvar fields]
  { name, type := close sortType
    ctors := [⟨name ++ `base, close (result 0)⟩,
      ⟨name ++ `field, close (.forallE `field (.bvar 1) (result 1) .default)⟩] }

private def universeFamily (name : Name) : InductiveType :=
  let level := Level.param `universe
  let sort := Expr.sort (.succ level)
  let close := fun body => .forallE `type sort body .implicit
  let result := fun fields => mkApp (.const name [level]) (.bvar fields)
  { name, type := close sort
    ctors := [⟨name ++ `base, close (result 0)⟩,
      ⟨name ++ `field, close (.forallE `field (.bvar 0) (result 1) .default)⟩] }

private def expectOutcome (label : String) (actual shadow : Except Kernel.Exception Unit)
    (expected : Bool) : MetaM Unit := do
  match actual, shadow with
  | .ok (), .ok () => unless expected do throwError "{label}: unexpectedly accepted"
  | .error _, .error _ => if expected then throwError "{label}: unexpectedly rejected"
  | .ok (), .error _ => throwError "{label}: shadow rejected an actual success"
  | .error _, .ok () => throwError "{label}: rejection control unexpectedly changed"

private def checkBatch (host : Lean.Environment) (environment : Kernel.Environment)
    (label : String) (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) (safeAccepted : Bool := true) (unsafeAccepted : Bool := true) : MetaM Nat := do
  let mut outcomes := 0
  for isUnsafe in [false, true] do
    let expected := if isUnsafe then unsafeAccepted else safeAccepted
    if expected && !types.isEmpty then
      unless (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
        throwError "{label}: native kernel rejected an expected acceptance"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment
        lparams := universes
        safety := if isUnsafe then .unsafe else .safe
        allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "{label}: header staging failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default
      let shadow := headerAxiomView environment headers
      for header in headers do
        for constructor in header.ctors do
          unless (actual.find? constructor).isNone do throwError "{label}: constructor is not fresh"
      for fuel in [({} : FuelConfig), {
          recDepth := 80
          whnf := 60
          whnfEager := 50
          lazyDelta := 40
          inductiveFuel := 200 }] do
        let current := { current with env := actual, fuel }
        expectOutcome label (checkConstructors types stats isUnsafe current)
          (checkConstructors types stats isUnsafe { current with env := shadow }) expected
        outcomes := outcomes + 1
      if types.any (fun type => !type.ctors.isEmpty) then
        for fuel in [({ inductiveFuel := 0 } : FuelConfig), { recDepth := 0 }] do
          let current := { current with env := actual, fuel }
          expectOutcome (label ++ " exhausted") (checkConstructors types stats isUnsafe current)
            (checkConstructors types stats isUnsafe { current with env := shadow }) false
          outcomes := outcomes + 1
      if !types.isEmpty then
        let current := { current with env := actual }
        let parent := stats.indConsts[0]!
        expectOutcome (label ++ " positivity zero") (checkPositivity.loop stats `fuel 0 parent 0 current)
          (checkPositivity.loop stats `fuel 0 parent 0 { current with env := shadow }) false
        expectOutcome (label ++ " constructor zero") (checkConstructors.loop stats isUnsafe 0 `fuel parent 0 0 current)
          (checkConstructors.loop stats isUnsafe 0 `fuel parent 0 0 { current with env := shadow }) false
        outcomes := outcomes + 2
  return outcomes

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorTransport |
    throwError "constructor transport module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "constructor module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "constructor unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"native constructor header transport: {count} exhaustive production declarations audited"

private def auditContinuation : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorContinuation |
    throwError "constructor continuation module absent"
  let inherited ← collectAxioms ``HeaderAxiomContinuation
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "continuation module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless inherited.contains dependency do
          throwError "continuation dependency {dependency} not inherited from its strong stage input in {name}"
      logInfo m!"{name}: {axioms.size} inherited strong-stage dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"constructor continuation: {count} exhaustive production declarations audited; strong-stage baseline = {repr inherited}"

run_meta
  auditModule
  auditContinuation
  let host ← getEnv
  let environment := host.toKernelEnv
  let mut outcomes ← checkBatch host environment "empty" #[]
  outcomes := outcomes + (← checkBatch host environment "no constructors"
    #[{ name := `TransportEmpty, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch host environment "nullary"
    #[{
      name := `TransportNullary
      type := sortType
      ctors := [⟨`TransportNullary.mk, .const `TransportNullary []⟩] }])
  outcomes := outcomes + (← checkBatch host environment "recursive" #[family `TransportSingle])
  let mutualFirst := family `TransportFirst
  let mutualSecond := family `TransportSecond
  outcomes := outcomes + (← checkBatch host environment "mutual"
    #[{ mutualFirst with ctors := mutualFirst.ctors ++ [⟨`TransportFirst.cross,
        .forallE `other (.const `TransportSecond []) (.const `TransportFirst []) .default⟩] },
      { mutualSecond with ctors := mutualSecond.ctors ++ [⟨`TransportSecond.cross,
        .forallE `other (.const `TransportFirst []) (.const `TransportSecond []) .default⟩] }])
  outcomes := outcomes + (← checkBatch host environment "one parameter" #[family `TransportOneParam 1] 1)
  outcomes := outcomes + (← checkBatch host environment "parameters" #[family `TransportParams 2] 2)
  outcomes := outcomes + (← checkBatch host environment "dependent" #[dependentFamily `TransportDependent] 2)
  outcomes := outcomes + (← checkBatch host environment "universe" #[universeFamily `TransportUniverse] 1 [`universe])
  outcomes := outcomes + (← checkBatch host environment "indexed" #[indexedFamily `TransportIndexed])
  let annotated := fun carrier => mkApp (.const ``outParam [.succ .zero]) carrier
  outcomes := outcomes + (← checkBatch host environment "annotation"
    #[{
      name := `TransportAnnotated
      type := sortType
      ctors := [⟨`TransportAnnotated.mk, .forallE `value (annotated natural)
        (.const `TransportAnnotated []) .default⟩] }])
  outcomes := outcomes + (← checkBatch host environment "long spine"
    #[{
      name := `TransportLong
      type := sortType
      ctors := [⟨`TransportLong.mk, (List.range 32).foldr
        (fun _ body => .forallE `field natural body .default) (.const `TransportLong [])⟩] }])
  outcomes := outcomes + (← checkBatch host environment "parameter mismatch"
    #[{
      name := `TransportMismatch
      type := .forallE `type sortType sortType .implicit
      ctors := [⟨`TransportMismatch.mk, .forallE `value natural
        (mkApp (.const `TransportMismatch []) natural) .default⟩] }] 1
    (safeAccepted := false) (unsafeAccepted := false))
  let parent : Expr := .const `TransportNegative []
  let negative := fun constructors => (#[{ name := `TransportNegative, type := sortType, ctors := constructors }] : Array InductiveType)
  outcomes := outcomes + (← checkBatch host environment "nonpositive"
    (negative [⟨`TransportNegative.mk, .forallE `bad (.forallE `child parent natural .default) parent .default⟩])
    (safeAccepted := false))
  outcomes := outcomes + (← checkBatch host environment "wrong return"
    (negative [⟨`TransportNegative.mk, natural⟩]) (safeAccepted := false) (unsafeAccepted := false))
  outcomes := outcomes + (← checkBatch host environment "universe overflow"
    (negative [⟨`TransportNegative.mk, .forallE `large sortType parent .default⟩])
    (safeAccepted := false) (unsafeAccepted := false))
  outcomes := outcomes + (← checkBatch host environment "duplicate"
    (negative [⟨`TransportNegative.mk, parent⟩, ⟨`TransportNegative.mk, parent⟩])
    (safeAccepted := false) (unsafeAccepted := false))
  outcomes := outcomes + (← checkBatch host environment "metavariable"
    (negative [⟨`TransportNegative.mk, .mvar ⟨`unassigned⟩⟩]) (safeAccepted := false) (unsafeAccepted := false))
  outcomes := outcomes + (← checkBatch host environment "free variable"
    (negative [⟨`TransportNegative.mk, .fvar ⟨`unassigned⟩⟩]) (safeAccepted := false) (unsafeAccepted := false))
  logInfo m!"{outcomes} native constructor/shadow outcomes passed: staged loops, shared/dependent parameters, recursive/higher-order/indexed fields, safety, fuel and rejection guards"

end InductiveConstructorTransportTest
