import Lean4Lean.Verify.InductiveRecursorParameterPrefixes
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (TypedParameterArguments ContextReserved)

namespace InductiveRecursorParameterPrefixesTest

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

example (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments) :
    stats.params.size ≤ afterIndex := parameterPrefix.complete
example (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments) :
    afterIndex = max index stats.params.size := parameterPrefix.count

section Typed

variable (parameters : TypedCtorParameterPrefix checker stats source index semantic)

example : RecursorCtorParameterPrefix stats source index parameters.residual parameters.afterIndex
    (stats.params.toList.drop index) := parameters.nativePrefix
example : stats.params.size ≤ parameters.afterIndex := parameters.nativePrefix.complete
example : parameters.afterIndex = max index stats.params.size := parameters.nativePrefix.count
example : TypedParameterArguments checker.venv checker.lparams checker.mlctx semantic
    (stats.params.toList.drop index) parameters.arguments parameters.residualSemantic := parameters.typedArguments
example : checker.TrExprS parameters.residual parameters.residualSemantic := parameters.translated

end Typed

example {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {source terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index source finalReader finalIndex terminal)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (parameterFVars : stats.ParamsAreFVars) (distinct : stats.params.toList.Nodup)
    (absent : stats.RemainingParamsAbsent index source)
    (translated : checker.TrExprS source semantic) :
    Nonempty (TypedCtorParameterPrefix checker stats source index semantic) :=
  trace.parameterPrefix checker aligned initialWF parameters parameterFVars distinct absent translated

example {stats : InductiveStats} {source residual terminal : Expr} {index afterIndex finalIndex : Nat}
    {arguments : List Expr} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments)
    (trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    RecursorCtorFieldTrace stats residual afterIndex fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader := parameterPrefix.fieldSuffix trace

example {environment : VEnv} {universes : List Name}
    {stats : InductiveStats} {source residual terminal : Expr} {index afterIndex finalIndex : Nat}
    {arguments : List Expr} {fields recursiveFields finalFields finalRecursive : Array Expr}
    {reader finalReader : Context}
    (parameterPrefix : RecursorCtorParameterPrefix stats source index residual afterIndex arguments)
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (supported : CtorFieldTraceAnnotationSupport environment universes trace) :
    CtorFieldTraceAnnotationSupport environment universes (parameterPrefix.fieldSuffix trace) :=
  parameterPrefix.annotationSuffix supported

example {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (parent : Nat) (bound : parent < types.size) (source : Constructor) (member : source ∈ types[parent].ctors) :
    ∃ semantic, stage.model.checker.TrExprS source.type semantic ∧
      Nonempty (TypedCtorParameterPrefix stage.model.checker stats source.type 0 semantic) :=
  receipts.parameterPrefix parent bound source member

example (arguments : TypedParameterArguments environment universes model functionType replacements semantics resultType)
    (increase : environment ≤ extended) :
    TypedParameterArguments extended universes model functionType replacements semantics resultType :=
  arguments.monoEnv increase

example {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (parent : Nat) (bound : parent < types.size) (source : Constructor) (member : source ∈ types[parent].ctors)
    (constants : CanonicalAnnotationConstants root.venv) (definitions : CanonicalAnnotationDefinitions root.venv)
    (model : MLCtx) (modelWF : model.WF registration.semantic root.lparams)
    (insertion : VLCtx.FVLift' stage.model.checker.vlctx model.vlctx 0 insertionLift 0)
    {initialReader finalReader : Context} {terminal : Expr} {finalIndex : Nat}
    {fields recursiveFields : Array Expr}
    (trace : RecursorCtorFieldTrace stats source.type 0 #[] #[] initialReader
      terminal finalIndex fields recursiveFields finalReader)
    (native : model.lctx = initialReader.lctx) (reserved : ContextReserved initialReader.lctx initialReader.ngen)
    (annotations : CtorFieldTraceAnnotationSupport registration.semantic root.lparams trace) :
    ∃ semantic finalModel,
      ParameterizedCtorFieldModelEndpoint registration.semantic root.lparams trace model finalModel semantic :=
  registration.parameterizedFields parent bound source member constants definitions model modelWF insertion
    trace native reserved annotations

example {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    (endpoint : ParameterizedCtorFieldModelEndpoint environment universes trace initial final semantic)
    (environmentWF : environment.WF) (initialWF : initial.WF environment universes)
    (input : RecursorConstantInput environment universes initial.vlctx name levels source) :
    ∃ value terminalSemantic,
      TrExprS environment universes final.vlctx
        (mkAppN (mkAppN (.const name levels) stats.params) fields) value ∧
      TrExprS environment universes final.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length final.vlctx.toCtx value terminalSemantic :=
  endpoint.constantInputApplication environmentWF initialWF input

section Endpoint

variable {environment : VEnv} {universes : List Name} {stats : InductiveStats}
  {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
  {reader finalReader : Context} {initial final : MLCtx} {semantic : VExpr}
  {fieldTrace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
    terminal finalIndex fields recursiveFields finalReader}
  (endpoint : ParameterizedCtorFieldModelEndpoint environment universes fieldTrace initial final semantic)

example : final.WF environment universes ∧ final.lctx = finalReader.lctx ∧
    TrLCtx environment universes finalReader.lctx final.vlctx := endpoint.context
example : ∃ terminalSemantic, TrExprS environment universes final.vlctx terminal terminalSemantic :=
  endpoint.terminalTranslation

end Endpoint

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def family (name : Name) (parameters : Nat := 0) : InductiveType :=
  let close := fun body => (List.range parameters).foldr
    (fun _ body => .forallE `parameter sortType body .implicit) body
  let parent := fun fields => mkAppN (.const name [])
    ((List.range parameters).toArray.map fun index => .bvar (fields + parameters - index - 1))
  { name, type := close sortType,
    ctors := [⟨name ++ `base, close (parent 0)⟩,
      ⟨name ++ `step, close (.forallE `child (parent 0) (parent 1) .default)⟩,
      ⟨name ++ `higher, close (.forallE `children (.forallE `index natural (parent 1) .default)
        (parent 1) .default)⟩] }

private def consumeParameters (parameters : Array Expr) (source : Expr) (index : Nat := 0) :
    Except String Expr :=
  if bound : index < parameters.size then
    match source with
    | .forallE _ _ body _ => consumeParameters parameters (body.instantiate1 parameters[index]) (index + 1)
    | _ => .error "constructor stopped before its complete parameter prefix"
  else .ok source
termination_by parameters.size - index

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM Nat := do
  let host ← getEnv
  let environment := host.toKernelEnv
  let mut outcomes := 0
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected parameter-prefix controls"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 1 isUnsafe
          return (stats, ← read, actual)) reader | throwError "parameter-prefix headers failed"
      unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
        throwError "parameter-prefix constructors failed checking"
      let .ok registered := declareConstructors stats types isUnsafe { current with env := actual }
        | throwError "parameter-prefix constructors failed registration"
      unless (run parameters types.toList 1 reader).isOk do throwError "parameter-prefix full run failed"
      let actualReader := { current with env := registered }
      let .ok elimLevel := getElimLevel stats types actualReader | throwError "parameter-prefix elimination failed"
      let .ok (_, motiveReader) := mkRecInfos.loopInd1 stats types elimLevel 0 #[]
          (fun infos => do return (infos, ← readThe Context)) actualReader
        | throwError "parameter-prefix actual motive pass failed"
      for reached in [actualReader, motiveReader] do
        let checkedReader := { reached with lparams := getRecLevelParams elimLevel universes }
        for type in types do
          for source in type.ctors do
            let .ok residual := consumeParameters stats.params source.type
              | throwError "accepted constructor lacks complete parameters"
            let capture := fun terminal fields recursiveFields => do
              return (terminal, fields, recursiveFields, ← readThe Context)
            let .ok (terminal, fields, recursiveFields, finalReader) :=
                mkRecInfos.loopCtorArgs stats source.type capture reached
              | throwError "parameter-prefix full field loop failed"
            let .ok (suffixTerminal, suffixFields, suffixRecursive, suffixReader) :=
                mkRecInfos.loopCtorArgs.loop stats capture residual stats.params.size #[] #[]
                  (reached.fuel.inductiveFuel - stats.params.size) reached
              | throwError "parameter-prefix exact remaining-fuel suffix failed"
            unless terminal == suffixTerminal && fields == suffixFields && recursiveFields == suffixRecursive &&
                finalReader.ngen == suffixReader.ngen &&
                localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
              throwError "parameter prefix changed field allocation, classification, terminal or reader"
            let .ok inferred := (monadLift (TypeChecker.checkType residual) : M Expr) checkedReader
              | throwError "parameter-prefix residual strict source checking failed"
            unless ((monadLift (TypeChecker.ensureSort inferred) : M Expr) checkedReader).isOk do
              throwError "parameter-prefix residual source is not a type"
            let applied := mkAppN (mkAppN (.const source.name stats.levels) stats.params) fields
            let .ok appliedType := (monadLift (TypeChecker.checkType applied) : M Expr)
                { finalReader with lparams := checkedReader.lparams }
              | throwError "parameter-prefix actual constructor application failed"
            unless appliedType == terminal do throwError "parameter-prefix application type differs from terminal"
            outcomes := outcomes + 1
      unless types.isEmpty || parameters == 0 do
        let type := types[0]!
        let incomplete := Expr.const type.name stats.levels
        unless (mkRecInfos.loopCtorArgs stats incomplete (fun _ _ _ => pure ()) actualReader).isOk do
          throwError "unchecked field-loop early-stop boundary changed"
        if (consumeParameters stats.params incomplete).isOk then throwError "incomplete parameter prefix accepted"
        let invalid := types.modify 0 fun type => { type with ctors := [⟨type.name ++ `invalid, incomplete⟩] }
        if (checkConstructors invalid stats isUnsafe { current with env := actual }).isOk then
          throwError "incomplete parameter source acquired accepted-constructor eligibility"
  return outcomes

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRecursorParameterPrefixes
    | throwError "parameter-prefix module absent"
  let logical := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut allowed := logical
  for name in [``TypeChecker.Inner.inferFVar.WF, ``acceptedHeaderParameterEquality,
      ``TrExprS.inst, ``VEnv.HasType.instN, ``TypeChecker.VContext.Δwf,
      ``ConstructorSemanticReceipts, ``TrExprS.fvarsIn, ``TrExprS.weakFV,
      ``TypedParameterArguments.weakFV, ``RecursorCtorFieldTrace.translated,
      ``TranslatedRecursorCtorFieldTrace.mixedContext, ``TranslatedRecursorCtorFieldTrace.application,
      ``RecursorConstantInput.alignedType] do
    allowed := allowed ++ (← collectAxioms name)
  let rawAllowed := logical ++ (← collectAxioms ``RecursorCtorFieldTrace) ++
    (← collectAxioms ``CtorFieldTraceAnnotationSupport)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-prefix owned axiom {name}"
      let baseline := if name.toString.startsWith "Lean4Lean.AddInductive.RecursorCtorParameterPrefix." ||
          name == ``RecursorCtorParameterPrefix then rawAllowed else allowed
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless baseline.contains dependency do throwError "parameter-prefix unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  let argumentAllowed := logical ++ (← collectAxioms ``TypeChecker.Inner.inferFVar.WF) ++
    (← collectAxioms ``acceptedHeaderParameterEquality) ++ (← collectAxioms ``TrExprS.inst) ++
    (← collectAxioms ``VEnv.HasType.instN) ++ (← collectAxioms ``TypeChecker.VContext.Δwf)
  let axioms ← collectAxioms ``translatedReusedHeaderParameterArgument
  for dependency in axioms do
    unless argumentAllowed.contains dependency do throwError "shared parameter argument unexpected {dependency}"
  logInfo m!"parameter prefixes: {count} exhaustive owned declarations and shared argument helper audited"

run_meta
  auditModule
  let mut outcomes ← checkBatch #[]
  outcomes := outcomes + (← checkBatch #[{ name := `PrefixEmpty, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch #[family `PrefixZero])
  outcomes := outcomes + (← checkBatch #[family `PrefixOne 1] 1)
  outcomes := outcomes + (← checkBatch #[family `PrefixTwo 2] 2)
  let dependent : InductiveType := {
    name := `PrefixDependent,
    type := .forallE `carrier sortType (.forallE `value (.bvar 0) sortType .default) .implicit,
    ctors := [⟨`PrefixDependent.mk, .forallE `carrier sortType
      (.forallE `value (.bvar 0)
        (mkAppN (.const `PrefixDependent []) #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  outcomes := outcomes + (← checkBatch #[dependent] 2)
  let universeLevel := Level.param `universe
  let polymorphic : InductiveType := {
    name := `PrefixPolymorphic,
    type := .forallE `carrier (.sort universeLevel) (.sort universeLevel) .implicit,
    ctors := [⟨`PrefixPolymorphic.mk, .forallE `carrier (.sort universeLevel)
      (mkApp (.const `PrefixPolymorphic [universeLevel]) (.bvar 0)) .implicit⟩,
      ⟨`PrefixPolymorphic.step, .forallE `carrier (.sort universeLevel)
        (.forallE `child (mkApp (.const `PrefixPolymorphic [universeLevel]) (.bvar 0))
          (mkApp (.const `PrefixPolymorphic [universeLevel]) (.bvar 1)) .default) .implicit⟩] }
  outcomes := outcomes + (← checkBatch #[polymorphic] 1 [`universe])
  let indexed : InductiveType := {
    name := `PrefixIndexed,
    type := .forallE `carrier sortType (.forallE `index natural sortType .default) .implicit,
    ctors := [⟨`PrefixIndexed.mk, .forallE `carrier sortType
      (.forallE `index natural
        (mkAppN (.const `PrefixIndexed []) #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  outcomes := outcomes + (← checkBatch #[indexed] 1)
  outcomes := outcomes + (← checkBatch #[family `PrefixMutualFirst 2, family `PrefixMutualSecond 2] 2)
  logInfo m!"{outcomes} parameter-prefix field controls passed both safeties and primitive modes in initial and reached actual motive readers, with exact remaining fuel, field allocation/classification/readers, residual typehood and complete constructor applications; incomplete unchecked early stops retain no accepted-prefix eligibility; native controls do not fabricate semantic contexts"

end InductiveRecursorParameterPrefixesTest
