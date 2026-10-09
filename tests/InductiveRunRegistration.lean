import Lean4Lean.Verify.InductiveRunMetadata
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRunRegistrationTest

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun _ =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeConstructorRegistration nparams types.toArray numNested ctx root constructors :=
  AddInductive.run.safeConstructorRegistration nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
      stats.SafeConstructorRegistration nparams types.toArray numNested ctx root constructors :=
  AddInductive.run.safeConstructorRegistration nparams types numNested ctx hsafety hwf _ hresult

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun _ =>
      ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
        stats.SafeConstructorTraces types.toArray PositivityWHNF root :=
  AddInductive.run.safeConstructorTraces nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
      stats.SafeConstructorTraces types.toArray PositivityWHNF root :=
  AddInductive.run.safeConstructorTraces nparams types numNested ctx hsafety hwf _ hresult

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ constructors : Kernel.Environment, constructors.constants.WF ∧
      DeclaredParameterMetadata nparams types.toArray constructors ∧
        ∀ name info, ctx.env.find? name = some info → constructors.find? name = some info := by
  obtain ⟨stats, root, constructors, hregistration⟩ :=
    AddInductive.run.safeConstructorRegistration nparams types numNested ctx hsafety hwf _ hresult
  exact ⟨constructors, hregistration.resultWF, hregistration.declaredParameters,
    hregistration.preservesOriginal⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
      ∀ parent, ∀ hparent : parent < types.toArray.size, ∀ ctor ∈ types.toArray[parent].ctors,
        ∃ terminal, ConstructorSpine ctor.type terminal ∧
          isValidIndAppIdx stats terminal parent = true := by
  obtain ⟨stats, root, hsafe, htraces⟩ :=
    AddInductive.run.safeConstructorTraces nparams types numNested ctx hsafety hwf _ hresult
  exact ⟨stats, root, hsafe, htraces.spine⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMetadata nparams types.toArray numNested ctx root constructors env :=
  AddInductive.run.safeMetadata nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
      stats.SafeRunMetadata nparams types.toArray numNested ctx root constructors env :=
  AddInductive.run.safeMetadata nparams types numNested ctx hsafety hwf env hresult

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      ∃ stats : InductiveStats,
        stats.HeaderMetadata nparams types.toArray numNested false ctx.lparams env ∧
        stats.ConstructorMetadata ctx.lparams types.toArray false env ∧
        DeclaredParameterMetadata nparams types.toArray env ∧
        stats.DeclaredRecursorCounts nparams types.toArray env :=
  AddInductive.run.safeDeclaredMetadata nparams types numNested ctx hsafety hwf

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    env.constants.WF ∧ ∃ stats : InductiveStats,
      stats.HeaderMetadata nparams types.toArray numNested false ctx.lparams env ∧
      stats.ConstructorMetadata ctx.lparams types.toArray false env ∧
      DeclaredParameterMetadata nparams types.toArray env ∧
      stats.DeclaredRecursorCounts nparams types.toArray env := by
  obtain ⟨hwf, _, stats, hheaders, hctors, hparams, hrecursors⟩ :=
    AddInductive.run.safeDeclaredMetadata nparams types numNested ctx hsafety hwf env hresult
  exact ⟨hwf, stats, hheaders, hctors, hparams, hrecursors⟩

example (stats : InductiveStats) (nparams numNested : Nat) (types : Array InductiveType)
    (original root : Context) (constructors env : Kernel.Environment)
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    stats.DeclaredRecursorCounts nparams types env :=
  hmetadata.declaredRecursors

example (stats : InductiveStats) (nparams numNested : Nat) (types : Array InductiveType)
    (original root : Context) (constructors env : Kernel.Environment)
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧
      ∀ index, index < types.size → ∃ (info : RecursorVal) (minorIndex nextIndex : Nat),
        env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
        mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
          minorIndex source = .ok (info.rules, nextIndex) :=
  hmetadata.sourceRules

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
      stats.SafeConstructorTraces types.toArray PositivityWHNF root ∧
      ∀ name info, root.env.find? name = some info → env.find? name = some info := by
  obtain ⟨stats, root, constructors, hmetadata⟩ :=
    AddInductive.run.safeMetadata nparams types numNested ctx hsafety hwf env hresult
  obtain ⟨_, _, _, _, hframe, htraces⟩ := hmetadata.registration.traces
  exact ⟨stats, root, hframe.safety.trans hsafety, htraces, fun name info hold =>
    hmetadata.fromConstructors name info (hmetadata.registration.fromHeaders name info hold)⟩

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (hresult : AddInductive.run nparams types numNested ctx = .ok env) :
    ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment)
      (elimLevel : Level) (infos : Array RecInfo) (source : Context) (isK : Bool),
      stats.SafeRunRegistration nparams types.toArray numNested ctx root constructors env ∧
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types.toArray infos ∧
      stats.RecursorMetadata types.toArray elimLevel infos ctx.lparams source.lctx isK false source env := by
  obtain ⟨stats, root, constructors, hmetadata⟩ :=
    AddInductive.run.safeMetadata nparams types numNested ctx hsafety hwf env hresult
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hrecursors⟩ := hmetadata.recursors
  exact ⟨stats, root, constructors, elimLevel, infos, source, isK,
    hmetadata.toSafeRunRegistration, hframe, hcounts, hrecursors⟩

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter sortType body .default) body

private def header (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams sortType, ctors }

private def checkRecursor (env : Kernel.Environment) (nparams : Nat)
    (types : List InductiveType) (type : InductiveType) (isUnsafe : Bool) : MetaM Unit := do
  let some (.recInfo info) := env.find? (mkRecName type.name)
    | throwError "missing recursor for {type.name}"
  let some (.inductInfo inductiveInfo) := env.find? type.name
    | throwError "missing recursor parent {type.name}"
  unless info.numParams == nparams && info.numIndices == inductiveInfo.numIndices &&
      info.numMotives == types.length && info.numMinors == (types.flatMap (·.ctors)).length &&
      info.all == types.map (·.name) && info.isUnsafe == isUnsafe &&
      info.rules.map (·.ctor) == type.ctors.map (·.name) && !info.type.hasFVar do
    throwError "incorrect recursor smoke metadata for {type.name}"
  for rule in info.rules do
    let some (.ctorInfo ctor) := env.find? rule.ctor
      | throwError "missing recursor-rule constructor {rule.ctor}"
    unless rule.nfields == ctor.numFields && !rule.rhs.hasFVar do
      throwError "incorrect recursor-rule smoke metadata for {rule.ctor}"

private def checkInstalled (ctx : Context) (env : Kernel.Environment) (nparams numNested : Nat)
    (types : List InductiveType) (type : InductiveType) : MetaM Unit := do
  let isUnsafe := ctx.safety != .safe
  let some (.inductInfo info) := env.find? type.name | throwError "missing datatype {type.name}"
  unless info.numParams == nparams && info.numNested == numNested &&
      info.levelParams == ctx.lparams && info.type == type.type && info.isUnsafe == isUnsafe do
    throwError "incorrect final datatype metadata for {type.name}"
  for index in [:type.ctors.length] do
    let ctor := type.ctors[index]!
    let some (.ctorInfo info) := env.find? ctor.name | throwError "missing constructor {ctor.name}"
    unless info.induct == type.name && info.cidx == index && info.type == ctor.type &&
        info.numParams == nparams && info.isUnsafe == isUnsafe &&
        info.numParams + info.numFields == declareConstructors.arity 0 ctor.type do
      throwError "incorrect final constructor metadata for {ctor.name}"
  checkRecursor env nparams types type isUnsafe

private def checkRun (ctx : Context) (nparams : Nat) (types : List InductiveType)
    (expected : Bool) (numNested : Nat := 0) : MetaM Unit := do
  let result := AddInductive.run nparams types numNested ctx
  unless result.isOk == expected do
    match result with
    | .error error =>
      throwError "incorrect full-run outcome for {types.map (·.name)}: \
        {error.toMessageData (← getOptions)}"
    | .ok _ => throwError "unexpected full-run success for {types.map (·.name)}"
  if let .ok env := result then
    for type in types do
      checkInstalled ctx env nparams numNested types type
    let some original := ctx.env.find? ``Nat | throwError "missing imported Nat fixture"
    let some retained := env.find? ``Nat | throwError "full run dropped imported Nat"
    unless original.type == retained.type && original.levelParams == retained.levelParams do
      throwError "full run changed imported Nat"

private def constructorPrefix (nparams : Nat) (types : List InductiveType) : M Kernel.Environment :=
  checkInductiveTypes nparams types.toArray fun stats => do
    withEnv (← declareInductiveTypes stats nparams types.toArray 0 false) do
      checkConstructors types.toArray stats false
      declareConstructors stats types.toArray false

private def audit (theoremName : Name) (interfaces := true) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allowed := logical ++ if interfaces then [
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Expr.eqv_eq, ``Expr.instantiate1_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``AddInductive.run.safeConstructorRegistration
  audit ``AddInductive.run.safeConstructorTraces
  audit ``AddInductive.run.safeMetadata
  audit ``AddInductive.run.safeDeclaredMetadata
  audit ``InductiveStats.SafeRunMetadata.declaredRecursors false
  audit ``InductiveStats.SafeRunMetadata.sourceRules false
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let natType := Expr.const ``Nat []
  let zero := Expr.const `RunWitnessZero []
  let one := Expr.const `RunWitnessOne []
  let other := Expr.const `RunWitnessOther []
  let two := Expr.const `RunWitnessTwo []
  let base : Constructor := { name := `RunWitnessZero.base, type := zero }
  let recursive : Constructor := {
    name := `RunWitnessZero.recursive, type := .forallE `value zero zero .default }
  let positive : Constructor := {
    name := `RunWitnessZero.positive, type := .forallE `function
      (.forallE `index natType zero .default) zero .implicit }
  let negative : Constructor := {
    name := `RunWitnessZero.negative, type := .forallE `function
      (.forallE `value zero natType .default) zero .default }
  let parameterOnly : Constructor := {
    name := `RunWitnessOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterRecursive : Constructor := {
    name := `RunWitnessOne.tail, type := closeParams 1
      (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let parameterField : Constructor := {
    name := `RunWitnessOne.value, type := closeParams 1
      (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let parameterNegative : Constructor := {
    name := `RunWitnessOne.negative, type := closeParams 1
      (.forallE `function (.forallE `tail (.app one (.bvar 0)) (.bvar 1) .default)
        (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `RunWitnessOne.mutual, type := closeParams 1
      (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherCtor : Constructor := {
    name := `RunWitnessOther.base, type := closeParams 1 (.app other (.bvar 0)) }
  let twoCtor : Constructor := {
    name := `RunWitnessTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  checkRun ctx 0 [] true
  checkRun ctx 0 [header `RunWitnessZero 0 []] true
  checkRun ctx 0 [header `RunWitnessZero 0 [base, recursive]] true
  checkRun ctx 0 [header `RunWitnessZero 0 [base, positive]] true
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly, parameterField, parameterRecursive]] true
  checkRun ctx 2 [header `RunWitnessTwo 2 [twoCtor]] true
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly, mutualCtor],
    header `RunWitnessOther 1 [otherCtor]] true
  checkRun ctx 0 [] true 7
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly, mutualCtor],
    header `RunWitnessMiddle 1 [], header `RunWitnessOther 1 [otherCtor]] true
  checkRun ctx 1 [header `RunWitnessOther 1 [otherCtor], header `RunWitnessMiddle 1 [],
    header `RunWitnessOne 1 [parameterOnly, mutualCtor]] true
  let numbered : List Constructor := (List.range 33).map fun ordinal => {
    name := (`RunWitnessZero.numbered).appendIndexAfter ordinal, type := zero }
  checkRun ctx 0 [header `RunWitnessZero 0 numbered] true
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } 0 [] true
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 1 } }
    0 [header `RunWitnessZero 0 []] true
  checkRun ctx 0 [header `RunWitnessZero 0 [base, recursive]] true 3
  let indexed := Expr.const `RunWitnessIndexed []
  let indexedType : InductiveType := {
    name := `RunWitnessIndexed
    type := closeParams 1 (.forallE `index natType sortType .default)
    ctors := [{
      name := `RunWitnessIndexed.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }
  checkRun ctx 1 [indexedType] true
  checkRun { ctx with
    ngen := { namePrefix := `RunWitnessSeed, idx := 12 }
    lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing sortType }
    1 [header `RunWitnessOne 1 [parameterOnly, parameterRecursive]] true
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `RunWitnessPoly [polyLevel]
  checkRun { ctx with lparams := [`u] } 1 [{
    name := `RunWitnessPoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `RunWitnessPoly.base
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }] true
  checkRun { ctx with lparams := [`u, `u] } 0 [] false
  checkRun ctx 0 [header `RunWitnessZero 0 [], header `RunWitnessZero 0 []] false
  checkRun ctx 0 [header ``Nat 0 []] false
  checkRun ctx 0 [header `RunWitnessZero 0 [base, negative]] false
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly, parameterNegative]] false
  checkRun ctx 0 [header `RunWitnessZero 0 [base, base]] false
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly], header `RunWitnessOther 1 [
    { otherCtor with name := parameterOnly.name }]] false
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly],
    header `RunWitnessOther 1 [otherCtor, { parameterOnly with name := `RunWitnessWrongParent }]] false
  checkRun ctx 1 [header `RunWitnessOne 1 [
    { name := `RunWitnessOpen, type := .app one (.fvar ⟨ctx.ngen.curr⟩) }]] false
  checkRun ctx 1 [header `RunWitnessOne 1 [parameterOnly,
    { name := `RunWitnessWrongDomain, type := .forallE `A natType (.app one natType) .default }]] false
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    0 [header `RunWitnessZero 0 [base]] false
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    1 [header `RunWitnessOne 1 [parameterOnly, parameterRecursive]] false
  checkRun { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
    1 [header `RunWitnessOne 1 [parameterOnly, parameterRecursive]] true
  let collisionType : InductiveType := header `RunWitnessLateCollision 0 [
    { name := mkRecName `RunWitnessLateCollision, type := .const `RunWitnessLateCollision [] }]
  checkRun ctx 0 [collisionType] false
  checkRun { ctx with safety := .unsafe } 0 [header `RunWitnessZero 0 [negative]] true
  unless (constructorPrefix 0 [collisionType] ctx).isOk do
    throwError "late recursor collision must follow successful constructor registration"
  let .error (.alreadyDeclared _ name) := AddInductive.run 0 [collisionType] 0 ctx
    | throwError "late boundary must reject the recursor name"
  unless name == mkRecName collisionType.name do throwError "incorrect late collision name"
  unless (constructorPrefix 0 [] { ctx with lparams := [`u, `u] }).isOk do
    throwError "constructor prefix must not include the earlier universe-name guard"
  logInfo "32 full-run outcomes, early/late boundaries, and unsafe control passed"

end InductiveRunRegistrationTest
