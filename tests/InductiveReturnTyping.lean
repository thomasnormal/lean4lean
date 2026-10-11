import Lean4Lean.Verify.InductiveConstructorCheckerModels

namespace InductiveReturnTypingTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

example (kind : VEnv.SortArity environment universes context (count + 1) functionType)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes))
    (functionTyped : environment.HasType universes context function functionType)
    (applicationTyped : environment.HasType universes context function (.forallE domain body))
    (argumentTyped : environment.HasType universes context argument domain) :
    environment.SortArity universes context count (body.inst argument) :=
  kind.apply environmentWF contextWF functionTyped applicationTyped argumentTyped

example (kind : VEnv.SortArity environment universes context 0 type)
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes))
    (typed : environment.HasType universes context semantic type) :
    environment.IsType universes context semantic :=
  kind.typedIsType environmentWF contextWF typed

example (kind : VEnv.SortArity environment universes context count type)
    (levels : List VLevel) (specializedUniverses : Nat)
    (levelsWF : ∀ level ∈ levels, level.WF specializedUniverses) :
    environment.SortArity specializedUniverses (context.map (VExpr.instL levels)) count
      (type.instL levels) :=
  kind.instL levelsWF

example (kind : VEnv.SortArity environment universes [] count type) (environmentWF : environment.WF) :
    environment.SortArity universes context count type :=
  kind.weak0 environmentWF

example (environmentWF : environment.WF) (lookup : environment.constants name = some constant)
    (kind : environment.SortArity constant.uvars [] count constant.type)
    (translated : TrExprS environment universes context (.const name levels) semantic) :
    ∃ type, environment.HasType universes.length context.toCtx semantic type ∧
      environment.SortArity universes.length context.toCtx count type :=
  translated.constantKind environmentWF lookup kind

example (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (translated : TrExprS environment universes context (function.mkAppList arguments) semantic)
    (headKind : ∀ {functionSemantic}, TrExprS environment universes context function functionSemantic →
      ∃ functionType, environment.HasType universes.length context.toCtx functionSemantic functionType ∧
        environment.SortArity universes.length context.toCtx arguments.length functionType) :
    environment.IsType universes.length context.toCtx semantic :=
  translated.saturatedIsType environmentWF contextWF headKind

example (accepted : isValidIndAppIdx stats source parent = true) :
    (source.getAppFn == stats.indConsts[parent]!) = true ∧
      source.getAppArgs.size = stats.params.size + stats.nindices[parent]! :=
  isValidIndAppIdx.headerMatches stats source parent accepted

example (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (accepted : isValidIndAppIdx stats source parent = true)
    (translated : TrExprS environment universes context source semantic)
    (headerKind : ∀ {headerSemantic},
      TrExprS environment universes context stats.indConsts[parent]! headerSemantic →
      ∃ headerType, environment.HasType universes.length context.toCtx headerSemantic headerType ∧
        environment.SortArity universes.length context.toCtx
          (stats.params.size + stats.nindices[parent]!) headerType) :
    environment.IsType universes.length context.toCtx semantic :=
  isValidIndAppIdx.isType environmentWF contextWF accepted translated headerKind

example
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (translated : TrExprS environment universes context type semantic)
    (headerKind : ∀ {headerSemantic},
      TrExprS environment universes context stats.indConsts[parent]! headerSemantic →
      ∃ headerType, environment.HasType universes.length context.toCtx headerSemantic headerType ∧
        environment.SortArity universes.length context.toCtx
          (stats.params.size + stats.nindices[parent]!) headerType) :
    environment.IsType universes.length context.toCtx semantic :=
  trace.isType environmentWF contextWF translated headerKind

example (translated : TrConstructor environment universes constructor semantic)
    (typed : environment.IsType universes.length [] semantic.type) :
    semantic.toVConstant.WF environment :=
  translated.typehoodWF typed

example (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (headerKinds : ∀ parent, parent < types.size → ∃ header ∈ receipts.declaration.types,
      stats.indConsts[parent]! = .const header.name stats.levels ∧
        stage.semantic.SortArity header.uvars []
          (stats.params.size + stats.nindices[parent]!) header.type) :
    ∀ header ∈ receipts.declaration.types, ∀ constructor ∈ header.ctors,
      constructor.toVConstant.WF stage.semantic :=
  receipts.typesWFOfHeaders headerKinds

private def checkSaturation (name : Name) (type : Expr) (indices : Array Expr)
    (parameters : Nat := 0) (universes : List Name := []) : MetaM Nat := do
  let environment := (← getEnv).toKernelEnv
  let types := #[{ name, type, ctors := [] : InductiveType }]
  for isUnsafe in [false, true] do
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := environment, lparams := universes,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, actual) := checkInductiveTypes parameters types (fun stats => do
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          return (stats, ← read, actual)) reader | throwError "return-typing header staging failed"
      let shadow := headerAxiomView environment (types.toList.map fun type =>
        match actual.find? type.name with | some (.inductInfo header) => header | _ => default)
      let arguments := stats.params ++ indices
      let returned := mkAppN stats.indConsts[0]! arguments
      unless arguments.size == parameters + stats.nindices[0]! do
        throwError "return-typing actual header arity differs"
      unless isValidIndAppIdx stats returned 0 do throwError "saturated return rejected by structural guard"
      for target in [actual, shadow] do
        let targetReader := { current with env := target }
        unless ((monadLift (TypeChecker.checkType returned) : M Expr) targetReader).isOk do
          throwError "saturated return failed checked inference"
        unless ((monadLift (TypeChecker.ensureType returned) : M Expr) targetReader).isOk do
          throwError "saturated return is not a type"
        if ((monadLift (TypeChecker.ensureSort returned) : M Expr) targetReader).isOk then
          throwError "inductive return was incorrectly treated as a sort expression"
        let excessive := mkApp returned (.const ``Nat.zero [])
        if isValidIndAppIdx stats excessive 0 then throwError "oversaturated return passed structural guard"
        if ((monadLift (TypeChecker.ensureType excessive) : M Expr) targetReader).isOk then
          throwError "oversaturated return is a type"
        unless arguments.isEmpty do
          let incomplete := mkAppN stats.indConsts[0]! (arguments.extract 0 (arguments.size - 1))
          if isValidIndAppIdx stats incomplete 0 then throwError "partial return passed structural guard"
          if ((monadLift (TypeChecker.ensureType incomplete) : M Expr) targetReader).isOk then
            throwError "partial return is a type"
        unless indices.isEmpty do
          let illTyped := mkAppN stats.indConsts[0]! (stats.params ++ indices.set! 0 (.sort .zero))
          unless isValidIndAppIdx stats illTyped 0 do
            throwError "structural guard unexpectedly checks argument typing"
          unless ((monadLift (TypeChecker.ensureType illTyped) : M Expr) targetReader).isOk do
            throwError "inference-only type formation unexpectedly checks argument typing"
          if ((monadLift (TypeChecker.checkType illTyped) : M Expr) targetReader).isOk then
            throwError "ill-typed structurally valid return passed checked inference"
  return 4

private def auditModule (moduleName : Name) (allowed : Array Name) : MetaM Nat := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "return-typing module absent"
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "return-typing owned axiom {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do throwError "return-typing unexpected {dependency} in {name}"
      logInfo m!"{name}: {axioms.size} inherited dependencies = {repr axioms}"
      count := count + 1
  return count

run_meta
  let logical := #[``propext, ``Classical.choice, ``Quot.sound]
  let theoryAllowed := logical ++ (← collectAxioms ``VEnv.IsDefEqU.forallE_inv) ++
    (← collectAxioms ``VEnv.IsDefEq.uniq)
  let returnAllowed := theoryAllowed ++ (← collectAxioms ``TrExprS.eqv)
  let theoryCount ← auditModule `Lean4Lean.Theory.SortArity theoryAllowed
  let returnCount ← auditModule `Lean4Lean.Verify.InductiveReturnTyping returnAllowed
  for name in [``TrConstructor.typehoodWF, ``AcceptedConstructorTrace.isType,
      ``ConstructorSemanticReceipts.typesWF, ``ConstructorSemanticReceipts.typesWFOfHeaders] do
    let allowed := returnAllowed ++ (← collectAxioms ``ConstructorSemanticReceipts)
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do throwError "constructor typehood unexpected {dependency} in {name}"
  let sort := Expr.sort (.succ .zero)
  let natural := Expr.const ``Nat []
  let zero := Expr.const ``Nat.zero []
  let mut controls ← checkSaturation `ReturnNullary sort #[]
  controls := controls + (← checkSaturation `ReturnIndexed (.forallE `index natural sort .default) #[zero])
  controls := controls + (← checkSaturation `ReturnDependent
    (.forallE `carrier sort (.forallE `value (.bvar 0) sort .default) .default) #[natural, zero])
  controls := controls + (← checkSaturation `ReturnParameterized
    (.forallE `carrier sort sort .implicit) #[] 1)
  controls := controls + (← checkSaturation `ReturnParameterIndex
    (.forallE `carrier sort (.forallE `index natural sort .default) .implicit) #[zero] 1)
  controls := controls + (← checkSaturation `ReturnPolymorphic (.sort (.param `universe)) #[] 0 [`universe])
  logInfo m!"{theoryCount} sort-arity / {returnCount} return-typing declarations and four constructor-WF lemmas audited; {controls} actual/shadow saturation controls distinguish typehood from sort expressions and structural acceptance from argument typing"

end InductiveReturnTypingTest
