import Lean4Lean.Verify.InductiveRecursorSignatureInputs
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ParameterPrefix TypedParameterArguments TypedParameterApplications ContextReserved)

namespace InductiveHeaderParameterApplicationsTest

example (arguments : TypedParameterArguments environment universes model source replacements values result) :
    TypedParameterApplications environment universes model source replacements values result :=
  .ofTypedArguments arguments

example (arguments : TypedParameterApplications environment universes model source replacements values result) :
    replacements.length = values.length := arguments.length

example (first : TypedParameterApplications environment universes model source replacements values middle)
    (second : TypedParameterApplications environment universes model middle more moreValues result) :
    TypedParameterApplications environment universes model source (replacements ++ more) (values ++ moreValues) result :=
  first.append second

example (arguments : TypedParameterApplications environment universes model source replacements values result)
    (increase : environment ≤ extended) :
    TypedParameterApplications extended universes model source replacements values result := arguments.monoEnv increase

example (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (targetWF : target.WF environment universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    TypedParameterApplications environment universes target (source.lift' lift) replacements
      (values.map (VExpr.lift' · lift)) (result.lift' lift) := arguments.weakFV environmentWF targetWF insertion

example (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (translated : TrExprS environment universes model.vlctx head semantic)
    (typed : environment.HasType universes.length model.vlctx.toCtx semantic source) :
    TrExprS environment universes model.vlctx (head.mkAppList replacements)
        (Lean4Lean.ElimNestedInductive.applyParameterArguments semantic values) ∧
      environment.HasType universes.length model.vlctx.toCtx
        (Lean4Lean.ElimNestedInductive.applyParameterArguments semantic values) result :=
  arguments.apply environmentWF modelWF translated typed

example (equality : environment.IsDefEqU universes.length model.vlctx.toCtx source target)
    (arguments : TypedParameterApplications environment universes model target replacements values result) :
    TypedParameterApplications environment universes model source replacements values result :=
  .convertInput equality arguments

example (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader) :
    ∃ more, finalStats.params.toList = stats.params.toList ++ more := trace.paramsAppend

example (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (complete : nparams ≤ index) : finalStats.params = stats.params := trace.paramsAfterParameters complete

example {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal sorted : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then index else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (translated : checker.TrExprS source semantic)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId) (values : List VExpr) (result : VExpr),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN identifiers.length) (finalStats.params.toList.drop index) values result :=
  trace.parameterApplications checker aligned initialWF reserved different constants definitions
    parameterCount parameters translated sortedCall

section Inputs

variable (input : HeaderParameterApplicationInput environment universes model stats source)

example : TrExprS environment universes model.vlctx source input.semantic := input.sourceTranslated
example : TypedParameterApplications environment universes model input.semantic stats.params.toList
    input.values input.result := input.arguments

example (increase : environment ≤ extended) :
    HeaderParameterApplicationInput extended universes model stats source := input.monoEnv increase

example (environmentWF : environment.WF) (targetWF : target.WF environment universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    HeaderParameterApplicationInput environment universes target stats source :=
  input.weakFV environmentWF targetWF insertion

example (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (headTranslated : TrExprS environment universes model.vlctx head headSemantic)
    (headTyped : environment.HasType universes.length model.vlctx.toCtx headSemantic input.semantic) :
    ∃ value, TrExprS environment universes model.vlctx (mkAppN head stats.params) value ∧
      environment.HasType universes.length model.vlctx.toCtx value input.result :=
  input.application environmentWF modelWF headTranslated headTyped

end Inputs

example (input : RecursorConstantInput environment universes model.vlctx name levels source)
    (parameters : HeaderParameterApplicationInput environment universes model stats source)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes) :
    ∃ value, TrExprS environment universes model.vlctx (mkAppN (.const name levels) stats.params) value ∧
      environment.HasType universes.length model.vlctx.toCtx value parameters.result :=
  input.applyHeaderParameters parameters environmentWF modelWF

example {nparams finalIndices : Nat} {stats finalStats : InductiveStats}
    {source normalized inferred terminal sorted : Expr} {name : Name} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats normalized 0 0 reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    Nonempty (HeaderParameterApplicationReceipt checker finalStats finalReader source) :=
  trace.parameterApplicationsFromSource checker aligned initialWF reserved different constants definitions
    parameterCount parameters guarded checked normalization sortedCall

example (receipt : HeaderParameterApplicationReceipt checker stats reader source) :
    HeaderCheckerAligned receipt.checker reader := receipt.aligned
example (receipt : HeaderParameterApplicationReceipt checker stats reader source) :
    ({} : TypeChecker.VState).WF receipt.checker := receipt.stateWF
example (receipt : HeaderParameterApplicationReceipt checker stats reader source) :
    ParameterPrefix checker.mlctx receipt.checker.mlctx receipt.identifiers := receipt.history
example (receipt : HeaderParameterApplicationReceipt checker stats reader source) :
    HeaderParameterApplicationInput checker.venv checker.lparams receipt.checker.mlctx stats source := receipt.input

example (receipt : HeaderParameterApplicationReceipt checker stats reader source) :
    receipt.checker.mlctx.WF checker.venv checker.lparams := receipt.modelWF

example (nparams fuel : Nat) (stats : InductiveStats) (name : Name) (source normalized inferred : Expr)
    (next : Expr → InductiveStats → Nat → M resultType) (reader : Context) (post : resultType → Prop)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (nextWF : ∀ terminal finalStats finalIndices current,
      HeaderParameterApplicationReceipt checker finalStats current source →
      reader.RecursorScopeFrame current → (next terminal finalStats finalIndices current).WF post) :
    (checkInductiveTypes.loopInd.loop nparams stats normalized 0 0 fuel (fun terminal finalStats finalIndices => do
      let _ ← (monadLift (TypeChecker.ensureSort terminal) : M Expr)
      next terminal finalStats finalIndices) reader).WF post :=
  checkInductiveTypes.loopInd.loop.withParameterApplications nparams fuel stats name source normalized inferred
    next reader post checker aligned initialWF reserved different constants definitions parameterCount parameters
    guarded checked normalization nextWF

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []
private def betaSort : Expr :=
  .app (.lam `sort (.sort (.succ (.succ .zero))) (.bvar 0) .default) sortType

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters : Nat) (domain : Expr := sortType) (mode : Nat := 0) : InductiveType :=
  let close := fun header body => (List.range parameters).foldr
    (fun index body => .forallE `carrier (if header then domain else sortType)
      (if header && index + 1 == parameters then delay body mode else body) .implicit) body
  let parent := mkAppN (.const name [])
    (((List.range parameters).toArray.map fun index => .bvar (parameters - index)).push (.bvar 0))
  { name, type := close true (.forallE `index natural sortType .default),
    ctors := [⟨name ++ `mk, close false (.forallE `index natural parent .default)⟩] }

private def consumeParameters (parameters : Array Expr) (source : Expr) (reader : Context)
    (index : Nat := 0) : Except Kernel.Exception (Expr × Nat) :=
  if index < parameters.size then
    match source with
    | .forallE _ _ body _ => do
      let opened := body.instantiate1 parameters[index]!
      let normalized ← (monadLift (TypeChecker.whnf opened) : M Expr) reader
      let (residual, changes) ← consumeParameters parameters normalized reader (index + 1)
      return (residual, changes + if opened == normalized then 0 else 1)
    | _ => .error .deepRecursion
  else .ok (source, 0)
termination_by parameters.size - index

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let environment := host.toKernelEnv
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected header-application controls {types.map (·.name)}"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, headers) := checkInductiveTypes parameters types (fun stats => do
          let headers ← declareInductiveTypes stats parameters types 1 isUnsafe
          return (stats, ← read, headers)) reader | throwError "header-application checked headers failed"
      let .ok final := run parameters types.toList 1 reader | throwError "header-application full run failed"
      for reachedEnvironment in [headers, final] do
        let original := { current with env := reachedEnvironment }
        let localReader := recursorIndexContext original `extra .default natural
        let saved : Context := {
          localReader with
          ngen := localReader.ngen.next
          lctx := localReader.lctx.mkLetDecl ⟨localReader.ngen.curr⟩ `saved natural (.lit (.natVal 0)) }
        for reached in [original, localReader, saved] do
          for parent in [:types.size] do
            let source := types[parent]!.type
            let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
              | throwError "header-application original-source normalization failed"
            let .ok (residual, prefixChanges) := consumeParameters stats.params normalized reached
              | throwError "header-application accepted source lacks complete parameters"
            let applied := mkAppN stats.indConsts[parent]! stats.params
            let .ok inferred := (monadLift (TypeChecker.checkType applied) : M Expr) reached
              | throwError "header-application compatible parameter application failed"
            let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
              | throwError "header-application residual differs from exact inferred application type"
            let .ok inferredKind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
              | throwError "header-application strict residual source checking failed"
            unless ((monadLift (TypeChecker.ensureSort inferredKind) : M Expr) reached).isOk do
              throwError "header-application residual source lacks sort-valued typehood"
            outcomes := outcomes + 1
            changes := changes + prefixChanges
            unless parameters == 0 do
              let wrongReader := recursorIndexContext reached `wrongParameter .default natural
              let wrong := stats.params.set! 0 (.fvar ⟨reached.ngen.curr⟩)
              unless wrong.all (·.isFVar) do throwError "header-application negative array is not entirely free variables"
              if ((monadLift (TypeChecker.checkType (mkAppN stats.indConsts[parent]! wrong)) : M Expr)
                  wrongReader).isOk then
                throwError "header-application wrong-domain free variables acquired typing eligibility"
              rejected := rejected + 1
  return (outcomes, changes, rejected)

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderParameterApplications
    | throwError "header-application module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``TypedParameterArguments.apply, ``TypedParameterArguments.weakFV,
      ``CheckedHeaderTrace.checkerModels, ``translatedHeaderOpeningWithSemantics,
      ``translatedReusedHeaderParameterArgument, ``acceptedSourceTranslation,
      ``acceptedHeaderNormalization, ``checkNoMVarNoFVar.WF,
      ``checkInductiveTypes.loopInd.loop.scopedTrace] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "header-application owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "header-application unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"header applications: {count} exhaustive owned declarations audited against genuine earlier foundations"

run_meta
  auditModule
  let mut outcomes := 0
  let mut changes := 0
  let mut rejected := 0
  for (types, parameters) in [
      (#[], 0), (#[{ name := `HeaderApplyEmpty, type := sortType, ctors := [] }], 0),
      (#[family `HeaderApplyZero 0], 0), (#[family `HeaderApplyOne 1], 1),
      (#[family `HeaderApplyTwo 2], 2), (#[family `HeaderApplyLet 2 betaSort 1], 2),
      (#[family `HeaderApplyBeta 2 (.mdata {} betaSort) 2], 2),
      (#[family `HeaderApplyMetadata 1 sortType 3], 1),
      (#[family `HeaderApplyMutualFirst 2 betaSort 1, family `HeaderApplyMutualSecond 2 sortType 2], 2)] do
    let (passed, changed, failed) ← checkBatch types parameters
    outcomes := outcomes + passed
    changes := changes + changed
    rejected := rejected + failed
  let dependent : InductiveType := {
    name := `HeaderApplyDependent,
    type := .forallE `carrier betaSort (.forallE `value (.bvar 0)
      (delay (.forallE `index natural sortType .default) 2) .default) .implicit,
    ctors := [⟨`HeaderApplyDependent.mk, .forallE `carrier sortType (.forallE `value (.bvar 0)
      (.forallE `index natural (mkAppN (.const `HeaderApplyDependent [])
        #[.bvar 2, .bvar 1, .bvar 0]) .default) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[dependent] 2
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  let universeLevel := Level.param `universe
  let polymorphic : InductiveType := {
    name := `HeaderApplyPolymorphic,
    type := .forallE `carrier (.sort universeLevel)
      (delay (.forallE `value (.bvar 0) (.sort universeLevel) .default) 1) .implicit,
    ctors := [⟨`HeaderApplyPolymorphic.mk, .forallE `carrier (.sort universeLevel)
      (.forallE `value (.bvar 0) (mkAppN (.const `HeaderApplyPolymorphic [universeLevel])
        #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  let (passed, changed, failed) ← checkBatch #[polymorphic] 1 [`universe]
  outcomes := outcomes + passed
  changes := changes + changed
  rejected := rejected + failed
  unless changes > 0 && rejected > 0 do throwError "header-application controls miss conversion/domain rejection"
  let host ← getEnv
  let incompatible := #[family `HeaderApplyDomainFirst 1,
    { name := `HeaderApplyDomainSecond, type := .forallE `carrier natural sortType .implicit, ctors := [] }]
  for isUnsafe in [false, true] do
    if (host.addDeclCore 0 (.inductDecl [] 1 incompatible.toList isUnsafe) none).isOk then
      throwError "native kernel accepted incompatible reused header parameter domains"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      if (checkInductiveTypes 1 incompatible (fun _ => pure ()) reader).isOk then
        throwError "incompatible reused header parameter domains acquired accepted receipt eligibility"
  logInfo m!"{outcomes} accepted header-parameter applications pass both safeties/primitive modes in header-registration/full-run environments and original/local/let contexts; {changes} nonidentity parameter-opening WHNF results; {rejected} wrong-domain all-free-variable arrays reject; exact residual type equality and strict sort-valued typehood checked; runtime controls do not fabricate semantic contexts"

end InductiveHeaderParameterApplicationsTest
