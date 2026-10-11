import Lean4Lean.Verify.InductiveHeaderReductionTransport

namespace InductiveHeaderReductionTransportTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions Lean.Kernel.Environment.irBaseExts from Lean.Environment

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport
      (inductiveReduceRec context.env expression TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq methods)
      (inductiveReduceRec context.env expression TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq methods)
      context context state := by
  apply inductiveReduceRec.headerAxiomTransport (changed := fun _ => False)
    methods methods context context (fun _ => .inl rfl) state expression
  all_goals intros; first | rfl | exact Except.SuccessTransport.refl _

example (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods)
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods) context context state := by
  apply TypeChecker.Inner.reduceRecursor.headerAxiomTransport methods methods context context state expression cheapRec cheapProj rfl
  all_goals intros; exact Except.SuccessTransport.refl _

example (actual shadow : TypeChecker.Context) (original : Kernel.Environment)
    (agreement : HeaderAxiomLookupAgreement changed actual.env shadow.env)
    (frame : NativeValueFrame original shadow.env)
    (parents : ∀ info major, NativeRecursorEntryReceipt actual expression info major →
      ∃ header, original.constants.find? info.getMajorInduct = some (.inductInfo header)) :
    ∀ info major, NativeRecursorEntryReceipt actual expression info major →
      actual.env.find? info.getMajorInduct = shadow.env.find? info.getMajorInduct := by
  intro info major entry
  obtain ⟨header, parent⟩ := parents info major entry
  exact agreement.stableOriginalInductiveParent frame info.getMajorInduct header parent

example (stats : InductiveStats) (parameters : Nat) (types : Array InductiveType) (nested : Nat)
    (isUnsafe : Bool) (context : Context) (actual : Kernel.Environment) (headers : List InductiveVal)
    (accepted : declareInductiveTypes stats parameters types nested isUnsafe context = .ok actual) :
    actual.quotInit = (headerAxiomView context.env headers).quotInit :=
  (declareInductiveTypes.quotInit stats parameters types nested isUnsafe context actual accepted).trans
    (headerAxiomView.quotInit context.env headers).symm

private def sortType : Expr := .sort (.succ .zero)

private def family (name : Name) : InductiveType :=
  { name, type := sortType, ctors := [⟨name ++ `mk, .const name []⟩] }

private def sameState (first second : TypeChecker.State) : Bool :=
  first.ngen.namePrefix == second.ngen.namePrefix && first.ngen.idx == second.ngen.idx &&
    first.inferTypeI.toList == second.inferTypeI.toList && first.inferTypeC.toList == second.inferTypeC.toList &&
    first.whnfCoreCache.toList == second.whnfCoreCache.toList && first.whnfCache.toList == second.whnfCache.toList &&
    first.eqvManager.toNodeMap.toList == second.eqvManager.toNodeMap.toList &&
    (first.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) ==
      (second.eqvManager.uf.arr.map fun node => (node.parent, node.rank)) &&
    first.failure.toList == second.failure.toList && first.unfold.toList == second.unfold.toList

private def seededState : TypeChecker.State :=
  let (_, manager) := EquivManager.toNode (.const ``Nat []) {}
  { ngen := { namePrefix := `_recursor_reduction, idx := 43 }
    inferTypeI := ({} : InferCache).insert (.const ``Nat []) sortType
    inferTypeC := ({} : InferCache).insert (.const ``Nat []) sortType
    whnfCoreCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    whnfCache := ({} : InferCache).insert (.const ``Nat []) (.const ``Nat [])
    eqvManager := manager
    failure := ({} : Std.HashSet (Expr × Expr)).insert (.const ``Nat [], sortType)
    unfold := ({} : InferCache).insert (.const `ReductionAlias []) sortType }

private def step {resultType : Type} (value : resultType) : TypeChecker.M resultType := fun _ state =>
  let marker := .const (Name.num `_reduction_step state.ngen.idx) []
  let (_, manager) := state.eqvManager.toNode marker
  .ok (value, { state with
    ngen := { state.ngen with idx := state.ngen.idx + 1 }
    inferTypeI := state.inferTypeI.insert marker sortType
    inferTypeC := state.inferTypeC.insert marker sortType
    whnfCoreCache := state.whnfCoreCache.insert marker marker
    whnfCache := state.whnfCache.insert marker marker
    eqvManager := manager
    failure := state.failure.insert (marker, sortType)
    unfold := state.unfold.insert marker marker })

private def callbacks (normalize infer : Expr → Expr) (equal : Bool := true) : TypeChecker.Methods := {
  whnf := fun expression => step (normalize expression)
  whnfCore := fun expression _ _ => step (normalize expression)
  inferType := fun expression _ => step (infer expression)
  isDefEqCore := fun _ _ => step equal }

private def runReduction (expression : Expr) (methods : TypeChecker.Methods)
    (reader : TypeChecker.Context) (state : TypeChecker.State) :=
  inductiveReduceRec reader.env expression TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
    methods reader state

private def checkResult {resultType : Type} [BEq resultType] [Repr resultType]
    (actual shadow : Except Kernel.Exception (resultType × TypeChecker.State)) (expected : Option resultType := none) : MetaM Unit := do
  match actual, shadow with
  | .ok (first, firstState), .ok (second, secondState) =>
    unless first == second && sameState firstState secondState do
      throwError "native recursor reduction changed its result or complete state"
    if let some value := expected then
      unless first == value do throwError "recursor reduction returned {repr first}, expected {repr value}"
  | .error _, .error _ =>
    if expected.isSome then throwError "recursor reduction rejected an expected success"
  | _, _ => throwError "recursor reduction changed success/failure"

private def checkRaw (actual shadow : TypeChecker.Context) (state : TypeChecker.State)
    (expression : Expr) (methods : TypeChecker.Methods) (expected : Option Expr) (steps : Nat) : MetaM Unit := do
  let result := runReduction expression methods actual state
  checkResult result (runReduction expression methods shadow state) (some expected)
  let .ok (_, finalState) := result | throwError "raw recursor reduction failed"
  unless finalState.ngen.idx == state.ngen.idx + steps do
    throwError "recursor reduction skipped or duplicated a reached callback"

private def record (template : RecursorVal) (parent : Name) (rule : RecursorRule) : RecursorVal :=
  { template with
    name := `RawReduction.rec
    levelParams := [`rawUniverse]
    type := (List.range 4).foldr (fun _ body => .forallE `prefix sortType body .default)
      (.forallE `major (.const parent []) sortType .default)
    numParams := 1
    numMotives := 1
    numMinors := 1
    numIndices := 1
    rules := [rule]
    k := false }

private def checkCallbacks (template : RecursorVal) (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  let source := .fvar ⟨`ReductionMajor⟩
  let prefixArguments := #[.const `RawParameter [], .const `RawMotive [], .const `RawMinor [], .const `RawIndex []]
  let extra := #[.const `RawExtraFirst [], .const `RawExtraSecond []]
  let fields := #[.const `RawFieldFirst [], .const `RawFieldSecond []]
  let rhs := .const `RawReductionRhs [.param `rawUniverse]
  let base := record template ``Nat { ctor := ``Nat.succ, nfields := 2, rhs }
  let withRecord := fun (info : RecursorVal) =>
    ({ actual with env := actual.env.add (.recInfo info) }, { shadow with env := shadow.env.add (.recInfo info) })
  let expression := fun (info : RecursorVal) (levels : List Level) (tail : Array Expr) =>
    mkAppN (.const info.name levels) (prefixArguments ++ #[source] ++ tail)
  let expected := fun (levels : List Level) (arguments : Array Expr) (tail : Array Expr) =>
    some (mkAppN (.const `RawReductionRhs levels) (prefixArguments.extract 0 3 ++ arguments ++ tail))
  let ctor := mkAppN (.const ``Nat.succ []) (#[.const `RawIgnoredParameter []] ++ fields)
  let (current, shadowCurrent) := withRecord base
  let levels := [.succ .zero]
  let methods := callbacks (fun expression => if expression == source then ctor else expression) (fun _ => sortType)
  for tail in [#[], extra] do
    checkRaw current shadowCurrent state (expression base levels tail) methods (expected levels fields tail) 1
  checkRaw current shadowCurrent state (expression base [] extra) methods none 1
  for normalized in [sortType, .const ``Nat.zero [], .app (.const ``Nat.succ []) (.const ``Nat.zero [])] do
    let methods := callbacks (fun expression => if expression == source then normalized else expression) (fun _ => sortType)
    checkRaw current shadowCurrent state (expression base levels extra) methods none 1
  for value in [0, 7] do
    let constructor := if value == 0 then ``Nat.zero else ``Nat.succ
    let fields := if value == 0 then #[] else #[.lit (.natVal (value - 1))]
    let info := { base with rules := [{ ctor := constructor, nfields := fields.size, rhs }] }
    let (current, shadowCurrent) := withRecord info
    let methods := callbacks (fun expression => if expression == source then .lit (.natVal value) else expression) (fun _ => sortType)
    checkRaw current shadowCurrent state (expression info levels extra) methods (expected levels fields extra) 1
  let text := "native recursor"
  let stringConstructor := .app (.const ``String.ofList []) (.const `RawCharacters [])
  let stringInfo := record template ``String { ctor := ``String.ofList, nfields := 1, rhs }
  let (current, shadowCurrent) := withRecord stringInfo
  let methods := callbacks (fun expression =>
    if expression == source then .lit (.strVal text)
    else if expression == .strLitToConstructor text then stringConstructor else expression) (fun _ => sortType)
  checkRaw current shadowCurrent state (expression stringInfo levels extra) methods
    (expected levels #[.const `RawCharacters []] extra) 2
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[.const ``Nat [], .const ``Nat []]
  let productInfo := record template ``Prod { ctor := ``Prod.mk, nfields := 2, rhs }
  let (current, shadowCurrent) := withRecord productInfo
  let methods := callbacks id (fun expression => if expression == source then product else sortType)
  checkRaw current shadowCurrent state (expression productInfo levels extra) methods
    (expected levels #[.proj ``Prod 0 source, .proj ``Prod 1 source] extra) 5
  for inferred in [Expr.prop, .const ``Bool []] do
    let methods := callbacks id (fun expression => if expression == source then product else inferred)
    checkRaw current shadowCurrent state (expression productInfo levels extra) methods
      (if inferred == .prop then none else expected levels #[.proj ``Prod 0 source, .proj ``Prod 1 source] extra) 5
  let mismatch := callbacks id (fun _ => .const ``Bool [])
  checkRaw current shadowCurrent state (expression productInfo levels extra) mismatch none 3
  let kInfo : RecursorVal := { template with
    name := `RawKReduction.rec
    levelParams := []
    type := .forallE `major (.const ``Bool []) sortType .default
    numParams := 0, numMotives := 0, numMinors := 0, numIndices := 0
    rules := [{ ctor := ``Bool.false, nfields := 0, rhs := .const ``Nat.zero [] }]
    k := true }
  let (current, shadowCurrent) := withRecord kInfo
  for equal in [false, true] do
    let methods := callbacks id (fun _ => .const ``Bool []) equal
    checkRaw current shadowCurrent state (.app (.const kInfo.name []) source) methods
      (if equal then some (.const ``Nat.zero []) else none) 5
  let exhausted := TypeChecker.Methods.withFuel 0
  checkResult (runReduction (expression base levels extra) exhausted actual state)
    (runReduction (expression base levels extra) exhausted shadow state) (some none)
  let (current, shadowCurrent) := withRecord base
  let rejected := runReduction (expression base levels extra) exhausted current state
  checkResult rejected (runReduction (expression base levels extra) exhausted shadowCurrent state)
  let .error _ := rejected | throwError "exhausted reached callback unexpectedly succeeded"
  let accepting := callbacks (fun expression => if expression == source then ctor else expression) (fun _ => sortType)
  let .ok (some _, _) := runReduction (expression base levels extra) accepting shadowCurrent state |
    throwError "directional rejection control did not have a successful shadow"

private def checkNative (actual shadow : TypeChecker.Context) (state : TypeChecker.State) : MetaM Unit := do
  let methods := TypeChecker.Methods.withFuel 100
  let natural := .const ``Nat []
  let zero := .lit (.natVal 0)
  let natMotive := .lam `major natural natural .default
  let natMinor := .lam `predecessor natural (.lam `recursive natural (.app (.const ``Nat.succ []) (.bvar 0)) .default) .default
  let natRecursor := mkAppN (.const ``Nat.rec [.succ .zero]) #[natMotive, zero, natMinor, .lit (.natVal 3)]
  let product := mkAppN (.const ``Prod [.zero, .zero]) #[natural, natural]
  let productName : FVarId := ⟨`NativeReductionProduct⟩
  let proofName : FVarId := ⟨`NativeReductionProof⟩
  let equality := mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, zero]
  let locals := actual.lctx.mkLocalDecl productName `pair product .default |>.mkLocalDecl proofName `proof equality .default
  let actual := { actual with lctx := locals }
  let shadow := { shadow with lctx := locals }
  let productMotive := .lam `pair product natural .default
  let productMinor := .lam `first natural (.lam `second natural (.bvar 1) .default) .default
  let productRecursor := mkAppN (.const ``Prod.rec [.succ .zero, .zero, .zero])
    #[natural, natural, productMotive, productMinor, .fvar productName]
  let eqMotive := .lam `target natural
    (.lam `proof (mkAppN (.const ``Eq [.succ .zero]) #[natural, zero, .bvar 0]) natural .default) .default
  let eqRecursor := mkAppN (.const ``Eq.rec [.succ .zero, .succ .zero])
    #[natural, zero, eqMotive, zero, zero, .fvar proofName]
  for (expression, expected) in [(natRecursor, .lit (.natVal 3)),
      (productRecursor, .proj ``Prod 0 (.fvar productName)), (eqRecursor, zero)] do
    let checked := methods.inferType expression false actual state
    let shadowChecked := methods.inferType expression false shadow state
    checkResult checked shadowChecked
    let .ok (inferred, checkedState) := checked |
      throwError "native checker rejected the recursor expression {repr expression}"
    let .ok (shadowInferred, shadowCheckedState) := shadowChecked | throwError "shadow rejected the native recursor expression"
    checkResult (methods.whnf inferred actual checkedState) (methods.whnf shadowInferred shadow shadowCheckedState) (some natural)
    for flags in [(none : Option (Bool × Bool)), some (false, false), some (false, true), some (true, false), some (true, true)] do
      let run := fun reader => match flags with
        | none => runReduction expression methods reader state
        | some (cheapRec, cheapProj) => TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods reader state
      let result := run actual
      checkResult result (run shadow)
      let .ok (some reduced, finalState) := result | throwError "native recursor did not reduce {repr expression}"
      let .ok (some shadowReduced, shadowState) := run shadow | throwError "shadow native recursor failed"
      checkResult (methods.whnf reduced actual finalState) (methods.whnf shadowReduced shadow shadowState) (some expected)

private def checkDispatch (template : RecursorVal) (actual shadow : TypeChecker.Context)
    (state : TypeChecker.State) : MetaM Unit := do
  let source := .fvar ⟨`DispatchMajor⟩
  let zero := .const ``Nat.zero []
  let field := .lit (.natVal 9)
  let successor := .app (.const ``Nat.succ []) field
  let info : RecursorVal := { template with
    name := `Dispatch.rec
    levelParams := []
    type := .forallE `major (.const ``Nat []) sortType .default
    numParams := 0, numMotives := 0, numMinors := 0, numIndices := 0
    k := false
    rules := [{ ctor := ``Nat.zero, nfields := 0, rhs := zero },
      { ctor := ``Nat.succ, nfields := 1, rhs := .const `DispatchResult [] }] }
  let function := .const `QuotientFunction []
  let natural := .const ``Nat []
  let relation := .const `QuotientRelation []
  let constructor := mkAppN (.const ``Quot.mk [.succ .zero]) #[natural, relation, zero]
  let liftArgs := #[natural, relation, natural, function, .const `QuotientRespects [], source]
  let indArgs := #[natural, relation, .const `QuotientMotive [], function, source]
  let withFlag := fun (environment : Kernel.Environment) initialized =>
    Lean.Kernel.Environment.mk environment.constants initialized environment.diagnostics environment.const2ModIdx
      (Lean.Kernel.Environment.extensions environment) (Lean.Kernel.Environment.irBaseExts environment) environment.header
  for initialized in [false, true] do
    let actual := { actual with env := withFlag (actual.env.add (.recInfo info)) initialized }
    let shadow := { shadow with env := withFlag (shadow.env.add (.recInfo info)) initialized }
    let run := fun expression methods cheapRec cheapProj (reader : TypeChecker.Context) =>
      TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj methods reader state
    for cheapRec in [false, true] do
      for cheapProj in [false, true] do
        let methods : TypeChecker.Methods := {
          whnf := fun expression => step (if expression == source then successor else expression)
          whnfCore := fun expression _ cheapProj => do
            let normalized ← step (if expression == source then (if cheapProj then zero else successor) else expression)
            step normalized
          inferType := fun _ _ => throw (.other "unexpected dispatch inference")
          isDefEqCore := fun _ _ => throw (.other "unexpected dispatch comparison") }
        let expression := .app (.const info.name []) source
        let result := run expression methods cheapRec cheapProj actual
        let expected := if cheapRec && cheapProj then zero else .app (.const `DispatchResult []) field
        checkResult result (run expression methods cheapRec cheapProj shadow) (some (some expected))
        let .ok (_, finalState) := result | throwError "native dispatch callback failed"
        unless finalState.ngen.idx == state.ngen.idx + (if cheapRec then 2 else 1) do
          throwError "native dispatch selected the wrong cheap reduction callback"
        for (name, arguments) in [(``Quot.lift, liftArgs), (``Quot.ind, indArgs)] do
          let methods := callbacks (fun expression => if expression == source then constructor else expression) (fun _ => sortType)
          for tail in [#[], #[.const `QuotientExtra []]] do
            let expression := mkAppN (.const name [.succ .zero]) (arguments ++ tail)
            let result := run expression methods cheapRec cheapProj actual
            let expected := if initialized then some (mkAppN (.app function zero) tail) else none
            checkResult result (run expression methods cheapRec cheapProj shadow) (some expected)
            let .ok (_, finalState) := result | throwError "quotient dispatch callback failed"
            unless finalState.ngen.idx == state.ngen.idx + (if initialized then 1 else 0) do
              throwError "quotient reduction did not retain its full-normalization prefix"
          let wrong := callbacks id (fun _ => sortType)
          let expression := mkAppN (.const name []) arguments
          checkResult (run expression wrong cheapRec cheapProj actual) (run expression wrong cheapRec cheapProj shadow) (some none)
          let short := mkAppN (.const name []) (arguments.extract 0 (arguments.size - 1))
          let exhausted := TypeChecker.Methods.withFuel 0
          checkResult (run short exhausted cheapRec cheapProj actual) (run short exhausted cheapRec cheapProj shadow) (some none)
          if initialized then
            let rejected := run expression exhausted cheapRec cheapProj actual
            checkResult rejected (run expression exhausted cheapRec cheapProj shadow)
            let .error _ := rejected | throwError "reached quotient callback ignored exhausted fuel"
  let disabled := { actual with env := withFlag actual.env false }
  let enabled := { shadow with env := withFlag shadow.env true }
  let expression := mkAppN (.const ``Quot.lift []) liftArgs
  let methods := callbacks (fun expression => if expression == source then constructor else expression) (fun _ => sortType)
  let .ok (first, _) := TypeChecker.Inner.reduceRecursor expression false false methods disabled state |
    throwError "disabled quotient negative control failed"
  let .ok (second, _) := TypeChecker.Inner.reduceRecursor expression false false methods enabled state |
    throwError "enabled quotient negative control failed"
  unless first == none && second == some (.app function zero) do
    throwError "identical lookup classifications unexpectedly established quotient-gate agreement"

private def checkBatch (host : Lean.Environment) (env : Kernel.Environment) (types : Array InductiveType)
    (template : RecursorVal) : MetaM Unit := do
  unless (host.addDeclCore 0 (.inductDecl [] 0 types.toList false) none).isOk do
    throwError "native kernel rejected recursor reduction fixture"
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := { env, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes 0 types (fun stats => do
          let actual ← declareInductiveTypes stats 0 types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "recursor reduction header checkpoint failed"
      let headers := types.toList.map fun type =>
        match actual.find? type.name with
        | some (.inductInfo header) => header
        | _ => default
      let shadow := headerAxiomView env headers
      unless actual.quotInit == shadow.quotInit && shadow.quotInit == env.quotInit do
        throwError "native header registration changed the quotient gate"
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk &&
          (declareConstructors stats types isUnsafe { current with env := actual }).isOk do
        throwError "recursor reduction checkpoint lost accepted constructors"
      let actualReader : TypeChecker.Context := { env := actual, safety := reader.safety }
      let shadowReader := { actualReader with env := shadow }
      for state in [({} : TypeChecker.State), seededState] do
        let exhausted := TypeChecker.Methods.withFuel 0
        for expression in [.sort .zero, .fvar ⟨`NoRecursor⟩, .const `UnknownRecursor [], .const ``Nat.zero [],
            .const ``Eq.rec [.zero, .zero], .const types[0]!.name []] do
          checkRaw actualReader shadowReader state expression exhausted none 0
        checkCallbacks template actualReader shadowReader state
        let differentReader := { shadowReader with
          safety := .unsafe
          eagerReduce := true
          lparams := [`unusedUniverse]
          fuel := { recDepth := 0 } }
        checkCallbacks template actualReader differentReader state
        checkNative actualReader shadowReader state
        checkDispatch template actualReader shadowReader state

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderReductionTransport |
    throwError "recursor reduction module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "recursor reduction module-owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "recursor reduction unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"recursor reduction: {count} exhaustive production declarations audited"

run_meta
  auditModule
  let host ← getEnv
  let environment := host.toKernelEnv
  let some (.recInfo template) := environment.find? ``Eq.rec | throwError "native Eq recursor absent"
  checkBatch host environment #[family `ReductionSingle] template
  checkBatch host environment #[family `ReductionFirst, family `ReductionSecond] template
  logInfo "native recursor reduction checkpoints, full-state callbacks, literal/structure/K adaptation and rule application passed"

end InductiveHeaderReductionTransportTest
