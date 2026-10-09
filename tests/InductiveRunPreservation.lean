import Lean4Lean.Verify.InductiveRunPreservation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRunPreservationTest

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ infos current, ctx.HeaderFrame current → (next infos current).WF post) :
    (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.frame stats types elimLevel next ctx post hnext

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (ctx : Context) :
    (mkRecInfos stats types elimLevel (fun infos => do
      return (infos, ← readThe Context)) ctx).WF fun result => ctx.HeaderFrame result.2 := by
  apply mkRecInfos.frame
  intro infos current hframe
  exact .pure hframe

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunRegistration nparams types.toArray numNested ctx root constructors env :=
  AddInductive.run.safeRegistration nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun env => env.constants.WF ∧
      ∀ name info, ctx.env.find? name = some info → env.find? name = some info :=
  AddInductive.run.safePreserves nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    env.constants.WF ∧ ∃ stats : InductiveStats,
      stats.HeaderMetadata nparams types.toArray numNested false ctx.lparams env ∧
      stats.ConstructorMetadata ctx.lparams types.toArray false env ∧
      DeclaredParameterMetadata nparams types.toArray env := by
  obtain ⟨stats, root, constructors, hregistration⟩ :=
    AddInductive.run.safeRegistration nparams types numNested ctx hsafety hwf env hresult
  exact ⟨hregistration.resultWF, stats, hregistration.headerMetadata,
    hregistration.constructorMetadata, hregistration.declaredParameters⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env)
    (name : Name) (info : ConstantInfo) (hold : ctx.env.find? name = some info) :
    env.find? name = some info :=
  (AddInductive.run.safePreserves nparams types numNested ctx hsafety hwf env hresult).2 name info hold

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
      stats.SafeConstructorTraces types.toArray PositivityWHNF root ∧
      ∀ name info, root.env.find? name = some info → env.find? name = some info := by
  obtain ⟨stats, root, constructors, hregistration⟩ :=
    AddInductive.run.safeRegistration nparams types numNested ctx hsafety hwf env hresult
  obtain ⟨_, _, _, _, hframe, htraces⟩ := hregistration.registration.traces
  exact ⟨stats, root, hframe.safety.trans hsafety, htraces, fun name info hold =>
    hregistration.fromConstructors name info (hregistration.registration.fromHeaders name info hold)⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats), ∀ parent ∈ types.toArray, ∀ index ctor,
      parent.ctors[index]? = some ctor →
        env.find? ctor.name = some (.ctorInfo (declareConstructors.metadataVal stats
          ctx.lparams false parent.name index ctor)) ∧
        stats.params.size + (declareConstructors.metadataVal stats ctx.lparams false
          parent.name index ctor).numFields = declareConstructors.arity 0 ctor.type := by
  obtain ⟨stats, root, constructors, hregistration⟩ :=
    AddInductive.run.safeRegistration nparams types numNested ctx hsafety hwf env hresult
  exact ⟨stats, hregistration.constructorMetadata⟩

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def fuelValues (fuel : FuelConfig) : List Nat :=
  [fuel.whnf, fuel.whnfEager, fuel.lazyDelta, fuel.etaExpand, fuel.recDepth, fuel.inductiveFuel]

private def infoStage (nparams : Nat) (types : Array InductiveType) (numNested : Nat := 0) :
    M (InductiveStats × Context × Context × Array RecInfo) :=
  checkInductiveTypes nparams types fun stats => do
    let isUnsafe := (← readThe Context).safety != .safe
    withEnv (← declareInductiveTypes stats nparams types numNested isUnsafe) do
      checkConstructors types stats isUnsafe
      withEnv (← declareConstructors stats types isUnsafe) do
        let initial ← readThe Context
        let elimLevel ← getElimLevel stats types
        mkRecInfos stats types elimLevel fun infos => do
          return (stats, initial, ← readThe Context, infos)

private def checkPreserved (initial current : Kernel.Environment) (name : Name) : MetaM Unit := do
  let some old := initial.find? name | throwError "missing frame fixture {name}"
  let some retained := current.find? name | throwError "recursor information dropped {name}"
  unless old.name == retained.name && old.type == retained.type &&
      old.levelParams == retained.levelParams && old.isUnsafe == retained.isUnsafe do
    throwError "recursor information changed {name}"

private def checkLocals (types : Array InductiveType) (stats : InductiveStats)
    (infos : Array RecInfo) (initial current : Context) : MetaM Unit := do
  unless infos.size == types.size && initial.lctx.decls.size ≤ current.lctx.decls.size &&
      initial.ngen.namePrefix == current.ngen.namePrefix do
    throwError "incorrect recursor local-context growth"
  if !types.isEmpty && current.ngen.idx ≤ initial.ngen.idx then
    throwError "recursor information did not advance fresh names"
  for index in [:types.size] do
    let info := infos[index]!
    unless info.indices.size == stats.nindices[index]! && info.minors.size == types[index]!.ctors.length do
      throwError "incorrect recursor information counts"
    for arg in #[info.major, info.motive] ++ info.indices ++ info.minors do
      unless arg.isFVar && (current.lctx.find? arg.fvarId!).isSome do
        throwError "recursor continuation lost a local binder"

private def checkStage (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat := 0) : MetaM Unit := do
  let .ok (stats, initial, current, infos) := infoStage nparams types numNested ctx
    | throwError "recursor information stage unexpectedly failed"
  unless current.lparams == initial.lparams && current.safety == initial.safety &&
      current.allowPrimitive == initial.allowPrimitive && fuelValues current.fuel == fuelValues initial.fuel &&
      current.env.quotInit == initial.env.quotInit do
    throwError "recursor information changed immutable context fields"
  checkLocals types stats infos initial current
  for type in types do
    checkPreserved initial.env current.env type.name
    for ctor in type.ctors do checkPreserved initial.env current.env ctor.name
    if current.env.contains (mkRecName type.name) then
      throwError "recursor information prematurely registered a recursor"
  for name in [``Nat, ``Nat.zero, ``Nat.succ, ``Nat.rec, ``List, ``List.rec] do
    checkPreserved initial.env current.env name

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let interfaces := [``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Expr.eqv_eq, ``Expr.instantiate1_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``mkRecInfos.frame logical
  audit ``AddInductive.run.safeRegistration (logical ++ interfaces)
  audit ``AddInductive.run.safePreserves (logical ++ interfaces)
  audit ``InductiveStats.SafeRunRegistration.preservesOriginal logical
  audit ``InductiveStats.SafeRunRegistration.headerMetadata logical
  audit ``InductiveStats.SafeRunRegistration.constructorMetadata logical
  audit ``InductiveStats.SafeRunRegistration.declaredParameters logical
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let natType := Expr.const ``Nat []
  let zero := Expr.const `FrameZero []
  let one := Expr.const `FrameOne []
  let other := Expr.const `FrameOther []
  let two := Expr.const `FrameTwo []
  let base : Constructor := { name := `FrameZero.base, type := zero }
  let recursive : Constructor := {
    name := `FrameZero.recursive, type := .forallE `value zero zero .default }
  let higher : Constructor := {
    name := `FrameZero.higher, type := .forallE `function
      (.forallE `index natType zero .default) zero .implicit }
  let parameterOnly : Constructor := {
    name := `FrameOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterRecursive : Constructor := {
    name := `FrameOne.tail, type := closeParams 1
      (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `FrameOne.mutual, type := closeParams 1
      (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherBase : Constructor := {
    name := `FrameOther.base, type := closeParams 1 (.app other (.bvar 0)) }
  let twoBase : Constructor := {
    name := `FrameTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let indexed := Expr.const `FrameIndexed []
  let indexedType : InductiveType := {
    name := `FrameIndexed, type := closeParams 1 (.forallE `index natType sortType .default),
    ctors := [{
      name := `FrameIndexed.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }
  for seeded in [false, true] do
    for allowPrimitive in [false, true] do
      let current := if seeded then
        { ctx with
          allowPrimitive
          ngen := { namePrefix := `FrameSeed, idx := 12 }
          lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing sortType }
        else { ctx with allowPrimitive }
      checkStage current 0 #[]
      checkStage current 0 #[header `FrameZero 0 []]
      checkStage current 0 #[header `FrameZero 0 [base, recursive, higher]]
      checkStage current 1 #[header `FrameOne 1 [parameterOnly, parameterRecursive]]
      checkStage current 2 #[header `FrameTwo 2 [twoBase]]
      checkStage current 1 #[header `FrameOne 1 [parameterOnly, mutualCtor], header `FrameOther 1 [otherBase]]
      checkStage current 1 #[indexedType]
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `FramePoly [polyLevel]
  checkStage { ctx with lparams := [`u] } 1 #[{
    name := `FramePoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `FramePoly.base
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }]
  checkStage ctx 0 #[header `FrameZero 0 [base, recursive]] 2
  let negative : Constructor := {
    name := `FrameZero.negative
    type := .forallE `function (.forallE `value zero natType .default) zero .default }
  checkStage { ctx with safety := .unsafe } 0 #[header `FrameZero 0 [negative]]
  let .ok (stats, initial, _, _) := infoStage 0 #[header `FrameZero 0 [base, recursive]] 0 ctx
    | throwError "missing failure-boundary preparation"
  let .error .deepRecursion := mkRecInfos stats #[header `FrameZero 0 [base, recursive]] .zero
      (fun _ => pure ()) { initial with fuel := { initial.fuel with inductiveFuel := 0 } }
    | throwError "recursor information must propagate zero-fuel failure"
  let .error (.other message) := mkRecInfos stats #[header `FrameZero 0 [base, recursive]] .zero
      (fun _ => (throw (.other "frame continuation sentinel") : M Unit)) initial
    | throwError "recursor information must propagate continuation failure"
  unless message == "frame continuation sentinel" do throwError "incorrect continuation error"
  logInfo "31 successful recursor-information frames and two failure boundaries passed"

end InductiveRunPreservationTest
