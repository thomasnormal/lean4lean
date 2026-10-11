import Lean4Lean.Verify.InductiveHeaderParameterUniverses

namespace InductiveHeaderParameterUniversesTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterApplications)

example (extension : UniverseNameExtension original target) :
    ∀ level ∈ UniverseNameExtension.levels original target, level.WF target.length := extension.levelsWF

example (extension : UniverseNameExtension original target)
    (translated : VLevel.ofLevel original level = some semantic) :
    VLevel.ofLevel target level = some (semantic.inst (UniverseNameExtension.levels original target)) :=
  extension.levelTranslation translated

example {levels : List Level} {values : List VLevel} (extension : UniverseNameExtension original target)
    (translated : levels.mapM (VLevel.ofLevel original) = some values) :
    levels.mapM (VLevel.ofLevel target) =
      some (values.map (VLevel.inst (UniverseNameExtension.levels original target))) :=
  extension.levelListTranslation translated

example (extension : UniverseNameExtension original target)
    (translated : TrExprS environment original virtual source semantic) :
    TrExprS environment target (virtual.instL (UniverseNameExtension.levels original target)) source
      (semantic.instL (UniverseNameExtension.levels original target)) := translated.reindexUniverses extension

example (extension : UniverseNameExtension original target)
    (translated : TrExpr environment original virtual source semantic) :
    TrExpr environment target (virtual.instL (UniverseNameExtension.levels original target)) source
      (semantic.instL (UniverseNameExtension.levels original target)) := translated.reindexUniverses extension

example (model : MLCtx) : (model.reindexLevels levels).lctx = model.lctx := MLCtx.reindexLevels.lctx model
example (model : MLCtx) : (model.reindexLevels levels).vlctx = model.vlctx.instL levels :=
  MLCtx.reindexLevels.vlctx model

example {model : MLCtx} (extension : UniverseNameExtension original target) (wellFormed : model.WF environment original) :
    (model.reindexLevels (UniverseNameExtension.levels original target)).WF environment target :=
  wellFormed.reindexUniverses extension

example (checker : TypeChecker.VContext) (extension : UniverseNameExtension checker.lparams target) :
    (checker.reindexUniverses extension).toContext = { checker.toContext with lparams := target } :=
  TypeChecker.VContext.reindexUniverses.context checker extension

example (checker : TypeChecker.VContext) (extension : UniverseNameExtension checker.lparams target) :
    (checker.reindexUniverses extension).trenv = checker.trenv := rfl

example (wellFormed : ({} : TypeChecker.VState).WF checker)
    (extension : UniverseNameExtension checker.lparams target) :
    ({} : TypeChecker.VState).WF (checker.reindexUniverses extension) := wellFormed.reindexReset extension

example (aligned : HeaderCheckerAligned checker reader) (extension : UniverseNameExtension checker.lparams target) :
    HeaderCheckerAligned (checker.reindexUniverses extension) { reader with lparams := target } :=
  aligned.reindexUniverses extension

example (extension : UniverseNameExtension original target)
    (arguments : TypedParameterApplications environment original model source replacements values result) :
    TypedParameterApplications environment target (model.reindexLevels (UniverseNameExtension.levels original target))
      (source.instL (UniverseNameExtension.levels original target)) replacements
      (values.map (VExpr.instL (UniverseNameExtension.levels original target)))
      (result.instL (UniverseNameExtension.levels original target)) := arguments.reindexUniverses extension

example (extension : UniverseNameExtension original target)
    (input : HeaderParameterApplicationInput environment original model stats source) :
    HeaderParameterApplicationInput environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats source := input.reindexUniverses extension

example (extension : UniverseNameExtension original target)
    (batch : HeaderParameterApplicationBatch environment original model stats types) :
    HeaderParameterApplicationBatch environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats types := batch.reindexUniverses extension

example (elimLevel : Level) (universes : List Name) :
    UniverseNameExtension universes (getRecLevelParams elimLevel universes) :=
  getRecLevelParams.universeExtension elimLevel universes

example : HeaderParameterApplicationBatch environment universes model stats #[] := by
  intro parent bound
  simp at bound

example : UniverseNameExtension [`universe, `universe] [`elimination, `universe] := ⟨by simp⟩
example : UniverseNameExtension [`first, `second] [`second, `elimination, `first] := ⟨by simp⟩

section Registration
variable {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
  {receipts : ConstructorSemanticReceipts stage isUnsafe}
  (registration : ConstructorConstantRegistration receipts final)

example (elimLevel : Level) :
    HeaderParameterApplicationBatch registration.semantic (getRecLevelParams elimLevel root.lparams)
      (stage.before.model.checker.mlctx.reindexLevels
        (UniverseNameExtension.levels root.lparams (getRecLevelParams elimLevel root.lparams))) stats types :=
  registration.parentParameterApplicationsInRecursorUniverses elimLevel

example (elimLevel : Level) :
    (stage.before.model.checker.mlctx.reindexLevels
      (UniverseNameExtension.levels root.lparams (getRecLevelParams elimLevel root.lparams))).WF
        registration.semantic (getRecLevelParams elimLevel root.lparams) :=
  registration.parentParameterModelWFInRecursorUniverses elimLevel

example (elimLevel : Level) :
    (stage.before.model.checker.mlctx.reindexLevels
      (UniverseNameExtension.levels root.lparams (getRecLevelParams elimLevel root.lparams))).lctx = reader.lctx :=
  (MLCtx.reindexLevels.lctx _).trans
    (stage.before.model.checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx stage.before.model.aligned))

end Registration

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          ∃ registration : ConstructorConstantRegistration receipts final, ∀ elimLevel,
            let universes := getRecLevelParams elimLevel root.lparams
            let model := stage.before.model.checker.mlctx.reindexLevels
              (UniverseNameExtension.levels root.lparams universes)
            model.WF registration.semantic universes ∧
              HeaderParameterApplicationBatch registration.semantic universes model stats types.toArray :=
  run.headerParameterUniverseContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors

private def natural : Expr := .const ``Nat []
private def universeLevel : Level := .param `universe

private def family (name : Name) (indices : Nat) (levels : List Level := [universeLevel])
    (resultLevel : Level := .max (.succ .zero) universeLevel) : InductiveType :=
  let close := fun body => .forallE `carrier (.sort universeLevel)
    (.forallE `value (.bvar 0) ((List.range indices).foldr
      (fun _ body => .forallE `index natural body .default) body) .default) .implicit
  let arguments := (List.range (2 + indices)).toArray.map fun index => Expr.bvar (1 + indices - index)
  { name, type := close (.sort resultLevel),
    ctors := [⟨name ++ `mk, close (mkAppN (.const name levels) arguments)⟩] }

private def checkBatch (types : Array InductiveType) (originalUniverses : List Name) : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let mut passed := 0
  let mut incompatible := 0
  let mut undefined := 0
  let elimination := `freshElimination
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl originalUniverses 2 types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected recursor-universe parameter controls {types.map (·.name)}"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := originalUniverses,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, registered) := checkInductiveTypes 2 types (fun stats => do
          let current ← read
          let actual ← declareInductiveTypes stats 2 types 0 isUnsafe
          withEnv actual do
            checkConstructors types stats isUnsafe
            return (stats, current, ← declareConstructors stats types isUnsafe)) reader
        | throwError "recursor-universe parameter checkpoint failed"
      let .ok final := run 2 types.toList 0 reader | throwError "recursor-universe complete run failed"
      for environment in [registered, final] do
        let original := { current with env := environment }
        let localReader := recursorIndexContext original `extra .default natural
        let saved : Context := {
          localReader with
          ngen := localReader.ngen.next
          lctx := localReader.lctx.mkLetDecl ⟨localReader.ngen.curr⟩ `saved natural (.lit (.natVal 0)) }
        for context in [original, localReader, saved] do
          for universes in [getRecLevelParams .zero originalUniverses,
              getRecLevelParams (.param elimination) originalUniverses,
              originalUniverses ++ [elimination], originalUniverses.reverse ++ [elimination]] do
            let reached := { context with lparams := universes }
            for parent in [:types.size] do
              let .ok inferred := (monadLift (TypeChecker.checkType
                  (mkAppN stats.indConsts[parent]! stats.params)) : M Expr) reached
                | throwError "compatible recursor-universe parent application failed"
              let residual := ((types[parent]!.type.bindingBody!).instantiate1 stats.params[0]!).bindingBody!
              let residual := residual.instantiate1 stats.params[1]!
              let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
                | throwError "recursor-universe exact original residual equality failed"
              let .ok kind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
                | throwError "recursor-universe residual strict checking failed"
              unless ((monadLift (TypeChecker.ensureSort kind) : M Expr) reached).isOk do
                throwError "recursor-universe residual lacks sort-valued typehood"
              passed := passed + 1
              if originalUniverses.length == 1 && universes.contains elimination then
                if ((monadLift (TypeChecker.checkType (mkAppN (.const types[parent]!.name [.param elimination])
                    stats.params)) : M Expr) reached).isOk then
                  throwError "fresh elimination level replaced an incompatible original parameter universe"
                incompatible := incompatible + 1
              let omitted := { reached with lparams := [elimination] }
              if ((monadLift (TypeChecker.checkType (mkAppN stats.indConsts[parent]! stats.params)) : M Expr)
                  omitted).isOk then throwError "missing original nominal universe acquired transport eligibility"
              undefined := undefined + 1
  return (passed, incompatible, undefined)

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderParameterUniverses
    | throwError "header-universe module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``TrExprS.instL, ``TrExpr.instL, ``TypeChecker.MLCtx.WF.monoEnv,
      ``TypeChecker.VState.WF.reset,
      ``HeaderParameterApplicationInput.application, ``ConstructorConstantRegistration.parentParameterApplications,
      ``run.headerParameterApplicationContinuation] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "header-universe module-owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "header-universe unexpected dependency {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      count := count + 1
  logInfo m!"header universes: {count} exhaustive owned declarations audited against genuine prior foundations"

run_meta
  auditModule
  let mut passed := 0
  let mut incompatible := 0
  let mut undefined := 0
  for (types, universes) in [
      (#[family `UniverseSingle 0], [`universe]),
      (#[family `UniverseIndexed 2], [`universe]),
      (#[family `UniverseMutualFirst 1, family `UniverseMutualSecond 2], [`universe]),
      (#[family `UniverseReordered 1 [universeLevel, .param `otherUniverse]
        (.max (.succ .zero) (.max universeLevel (.param `otherUniverse)))], [`universe, `otherUniverse])] do
    let (accepted, rejected, omitted) ← checkBatch types universes
    passed := passed + accepted
    incompatible := incompatible + rejected
    undefined := undefined + omitted
  logInfo m!"{passed} compatible original/fresh/reordered universe parent applications passed; {incompatible} incompatible elimination-universe substitutions and {undefined} omitted-original-universe contexts rejected; constructor-registered/full-run environments, original/local/let contexts, both safeties/primitive modes, dependent parameters and differing accumulated mutual indices checked; runtime controls do not fabricate semantic contexts"

end InductiveHeaderParameterUniversesTest
