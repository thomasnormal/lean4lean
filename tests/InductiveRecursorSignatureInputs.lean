import Lean4Lean.Verify.InductiveRecursorSignatureInputs
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)

namespace InductiveRecursorSignatureInputsTest

section Input

variable {environment : VEnv} {universes : List Name} {virtual : VLCtx}
  {name : Name} {levels : List Level} {source : Expr}
  (input : RecursorConstantInput environment universes virtual name levels source)

example : TrExprS environment universes virtual source input.semanticType := input.sourceTranslated
example : environment.IsType universes.length virtual.toCtx input.semanticType := input.sourceTypehood
example : TrExprS environment universes virtual (.const name levels) input.semanticValue := input.valueTranslated
example : environment.HasType universes.length virtual.toCtx input.semanticValue input.semanticType :=
  input.valueTyped

example (environmentWF : environment.WF) (contextWF : virtual.WF environment universes.length)
    (translated : TrExprS environment universes virtual source semantic) :
    environment.HasType universes.length virtual.toCtx input.semanticValue semantic :=
  input.alignedType environmentWF contextWF translated

end Input

example (input : RecursorConstantInput environment universes model.vlctx name levels source)
    (arguments : ElimNestedInductive.TypedParameterArguments environment universes model
      input.semanticType replacements semantics resultType) :
    TrExprS environment universes model.vlctx ((Expr.const name levels).mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments input.semanticValue semantics) ∧
    environment.HasType universes.length model.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments input.semanticValue semantics) resultType :=
  input.applyParameters arguments

section Registration

variable {root : TypeChecker.VContext} {original reader : Context} {nparams : Nat}
  {types : Array InductiveType} {stats : InductiveStats} {actual final : Kernel.Environment}
  {stage : HeaderAxiomContinuation root original nparams types stats reader actual} {isUnsafe : Bool}
  {receipts : ConstructorSemanticReceipts stage isUnsafe}
  (registration : ConstructorConstantRegistration receipts final)
  {universes : List Name} {levels : List Level} {semanticLevels : List VLevel}
  (model : MLCtx) (modelWF : model.WF registration.semantic universes)
  (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
  (arity : levels.length = root.lparams.length)

example (typeMember : type ∈ types) :
    Nonempty (RecursorConstantInput registration.semantic universes model.vlctx type.name levels
      (type.type.instantiateLevelParams root.lparams levels)) :=
  registration.headerInput typeMember model modelWF mapped arity

example (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source) :
    Nonempty (RecursorConstantInput registration.semantic universes model.vlctx source.name levels
      (source.type.instantiateLevelParams root.lparams levels)) :=
  registration.constructorInput typeMember index source sourceGet model modelWF mapped arity

example : RecursorSignatureInputs registration.semantic root.lparams types := registration.signatureInputs

example (typeMember : type ∈ types) :
    Nonempty (RecursorConstantInput registration.semantic universes model.vlctx type.name levels
      (type.type.instantiateLevelParams root.lparams levels)) ∧
    ∀ (index : Nat) (source : Constructor), type.ctors[index]? = some source →
      Nonempty (RecursorConstantInput registration.semantic universes model.vlctx source.name levels
        (source.type.instantiateLevelParams root.lparams levels)) :=
  registration.signatureInputs universes levels semanticLevels model modelWF mapped arity type typeMember

example (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source)
    {terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {fieldReader initialReader : Context} {fieldModel : MLCtx} {semantic : VExpr}
    {fieldTrace : RecursorCtorFieldTrace stats (source.type.instantiateLevelParams root.lparams levels)
      0 #[] #[] initialReader terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint registration.semantic universes fieldTrace model fieldModel semantic) :
    ∃ value terminalSemantic,
      TrExprS registration.semantic universes fieldModel.vlctx
        (mkAppN (.const source.name levels) fields) value ∧
      TrExprS registration.semantic universes fieldModel.vlctx terminal terminalSemantic ∧
      registration.semantic.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic :=
  endpoint.registeredConstructorApplication registration typeMember index source sourceGet modelWF mapped arity

end Registration

example {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {fieldTrace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace environment universes fieldTrace
      virtual semantic finalVirtual finalSemantic) :
    TrExprS environment universes virtual source semantic := history.initialTranslation

example {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context} {model fieldModel : MLCtx} {semantic : VExpr}
    {fieldTrace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint environment universes fieldTrace model fieldModel semantic)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (input : RecursorConstantInput environment universes model.vlctx name levels source) :
    ∃ value terminalSemantic,
      TrExprS environment universes fieldModel.vlctx (mkAppN (.const name levels) fields) value ∧
      TrExprS environment universes fieldModel.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic :=
  endpoint.constantInputApplication environmentWF modelWF input

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (pure ())) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          ∃ registration : ConstructorConstantRegistration receipts final,
            RecursorSignatureInputs registration.semantic root.lparams types :=
  checkInductiveTypes.recursorSignatureContinuation nparams types numNested isUnsafe
    (fun _ _ => pure ()) root reader aligned empty different constants definitions ordinary safetyBound
    constructors recursors

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
          ∃ registration : ConstructorConstantRegistration receipts final,
            RecursorSignatureInputs registration.semantic root.lparams types.toArray :=
  run.recursorSignatureContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors

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

private def checkBatch (types : Array InductiveType) (parameters : Nat := 0)
    (universes : List Name := []) : MetaM Nat := do
  let host ← getEnv
  let environment := host.toKernelEnv
  let targetUniverses := `SignatureElimination :: universes
  let levelLists := if universes.isEmpty then [[]] else
    [universes.map Level.param, List.replicate universes.length (.param `SignatureElimination),
      List.replicate universes.length (.succ .zero), universes.reverse.map Level.param]
  let mut outcomes : Nat := 0
  let mut incompatibleParameters : Nat := 0
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 0 (.inductDecl universes parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected recursor signature controls"
    let reader : Context := {
      env := environment, lparams := universes,
      safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }
    let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
        let actual ← declareInductiveTypes stats parameters types 2 isUnsafe
        return (stats, ← read, actual)) reader | throwError "signature header staging failed"
    unless (checkConstructors types stats isUnsafe { current with env := actual }).isOk do
      throwError "signature constructor checking failed"
    let .ok registered := declareConstructors stats types isUnsafe { current with env := actual }
      | throwError "signature constructor registration failed"
    let .ok completed := run parameters types.toList 2 reader | throwError "signature full run failed"
    let locals := current.lctx.mkLocalDecl ⟨`SignatureCarrier⟩ `carrier sortType .default
      |>.mkLocalDecl ⟨`SignatureValue⟩ `value (.fvar ⟨`SignatureCarrier⟩) .default
      |>.mkLetDecl ⟨`SignatureLet⟩ `letValue natural (.const ``Nat.zero []) false
    for extended in [registered, completed] do
      for localContext in [current.lctx, locals] do
        let targetReader := { current with env := extended, lctx := localContext, lparams := targetUniverses }
        for levels in levelLists do
          for type in types do
            let sources := (type.name, type.type) :: type.ctors.map fun constructor =>
              (constructor.name, constructor.type)
            for (name, source) in sources do
              let instantiated := source.instantiateLevelParams universes levels
              let .ok inferred := (monadLift (TypeChecker.checkType (.const name levels)) : M Expr) targetReader
                | throwError "recursor signature constant inference failed"
              unless inferred == instantiated do throwError "recursor signature exact instantiated type differs"
              let .ok inferredSort := (monadLift (TypeChecker.checkType instantiated) : M Expr) targetReader
                | throwError "recursor signature source checking failed"
              let .ok normalizedSort := (monadLift (TypeChecker.ensureSort inferredSort) : M Expr) targetReader
                | throwError "recursor signature source is not sort-valued"
              unless normalizedSort.isSort do throwError "recursor signature source acquired nonsort type"
              if ((monadLift (TypeChecker.checkType (.const name (levels ++ [.zero]))) : M Expr) targetReader).isOk then
                throwError "recursor signature wrong universe arity accepted"
              unless universes.isEmpty do
                let missing := List.replicate universes.length (.param `SignatureMissing)
                if ((monadLift (TypeChecker.checkType (.const name missing)) : M Expr) targetReader).isOk then
                  throwError "recursor signature unbound universe accepted"
              if levels == universes.map Level.param then
                let .ok appliedType := (monadLift (TypeChecker.checkType
                    (mkAppN (.const name levels) stats.params)) : M Expr) targetReader
                  | throwError "recursor signature actual parameter application failed"
                let .ok appliedSort := (monadLift (TypeChecker.checkType appliedType) : M Expr) targetReader
                  | throwError "recursor signature residual parameter type checking failed"
                unless ((monadLift (TypeChecker.ensureSort appliedSort) : M Expr) targetReader).isOk do
                  throwError "recursor signature residual parameter typehood failed"
              else if name == `SignaturePolyParameter || name == `SignaturePolyParameter.mk then
                if ((monadLift (TypeChecker.checkType
                    (mkAppN (.const name levels) stats.params)) : M Expr) targetReader).isOk then
                  throwError "recursor signature accepted incompatible original parameter universes"
                incompatibleParameters := incompatibleParameters + 1
              outcomes := outcomes + 1
  unless incompatibleParameters == 0 do
    logInfo m!"{incompatibleParameters} incompatible original-parameter universe applications rejected"
  return outcomes

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRecursorSignatureInputs
    | throwError "recursor signature module absent"
  let logical := #[``propext, ``Classical.choice, ``Quot.sound]
  let structural := logical ++ (← collectAxioms ``TrExprS) ++
    (← collectAxioms ``TranslatedRecursorCtorFieldTrace)
  let mut allowed := structural
  for name in [``VEnv.Ordered.constWF, ``TrExprS.instL, ``TrExpr.weakFV, ``TrExprS.uniq,
      ``VEnv.IsType.defeqU_l, ``TypeChecker.MLCtx.WF,
      ``ConstructorConstantRegistration.constructorConstant, ``ConstructorConstantRegistration.increase,
      ``ElimNestedInductive.TypedParameterArguments.apply, ``CtorFieldModelEndpoint.application,
      ``checkInductiveTypes.constructorConstantContinuation, ``run.constructorConstantContinuation] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "recursor signature owned axiom {name}"
      let baseline := if name == ``TranslatedRecursorCtorFieldTrace.initialTranslation then structural else allowed
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless baseline.contains dependency do throwError "recursor signature unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  logInfo m!"recursor signatures: {count} exhaustive owned declarations audited against earlier interfaces"

run_meta
  auditModule
  let mut outcomes ← checkBatch #[]
  outcomes := outcomes + (← checkBatch #[{ name := `SignatureEmpty, type := sortType, ctors := [] }])
  outcomes := outcomes + (← checkBatch #[family `SignatureSingle])
  outcomes := outcomes + (← checkBatch #[family `SignatureParameters 2] 2)
  let dependent : InductiveType := {
    name := `SignatureDependent,
    type := .forallE `carrier sortType (.forallE `value (.bvar 0) sortType .default) .implicit,
    ctors := [⟨`SignatureDependent.mk, .forallE `carrier sortType
      (.forallE `value (.bvar 0)
        (mkAppN (.const `SignatureDependent []) #[.bvar 1, .bvar 0]) .default) .implicit⟩] }
  outcomes := outcomes + (← checkBatch #[dependent] 2)
  let universeLevel := Level.param `universe
  let polySort := Expr.sort (.succ universeLevel)
  let polyReturn := fun name arguments => mkAppN (.const name [universeLevel]) arguments
  outcomes := outcomes + (← checkBatch #[{
    name := `SignaturePolyFirst, type := .forallE `carrier polySort polySort .default,
    ctors := [⟨`SignaturePolyFirst.base, polyReturn `SignaturePolyFirst #[.sort universeLevel]⟩] }, {
    name := `SignaturePolySecond, type := polySort,
    ctors := [⟨`SignaturePolySecond.base, polyReturn `SignaturePolySecond #[]⟩] }, {
    name := `SignaturePolyThird,
    type := .forallE `carrier polySort (.forallE `index natural polySort .default) .default,
    ctors := [⟨`SignaturePolyThird.base,
      polyReturn `SignaturePolyThird #[.sort universeLevel, .const ``Nat.zero []]⟩] }] 0 [`universe])
  let polymorphic : InductiveType := {
    name := `SignaturePolyParameter,
    type := .forallE `carrier (.sort universeLevel) (.sort universeLevel) .implicit,
    ctors := [⟨`SignaturePolyParameter.mk, .forallE `carrier (.sort universeLevel)
      (mkApp (.const `SignaturePolyParameter [universeLevel]) (.bvar 0)) .implicit⟩] }
  outcomes := outcomes + (← checkBatch #[polymorphic] 1 [`universe])
  let twoUniverses : InductiveType := {
    name := `SignatureTwoUniverses, type := .sort (.succ (.max universeLevel (.param `other))),
    ctors := [⟨`SignatureTwoUniverses.base, .const `SignatureTwoUniverses [universeLevel, .param `other]⟩] }
  outcomes := outcomes + (← checkBatch #[twoUniverses] 0 [`universe, `other])
  outcomes := outcomes + (← checkBatch #[family `SignatureMutualFirst, family `SignatureMutualSecond])
  logInfo m!"{outcomes} checked header/constructor signature instantiations passed in registered and complete-run environments, both safeties, original and dependent local/let contexts; elimination/concrete/reordered universes, exact inferred types, source/residual typehood and arity/unbound-universe rejections passed; native controls do not fabricate semantic contexts"

end InductiveRecursorSignatureInputsTest
