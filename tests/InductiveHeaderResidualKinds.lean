import Lean4Lean.Verify.InductiveParentPassCheckerClosure
import Lean4Lean.Verify.InductiveIndexCountClosure
import Lean.Util.CollectAxioms

namespace InductiveHeaderResidualKindsTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive
open TypeChecker (MLCtx)
open ElimNestedInductive (TypedParameterApplications ContextReserved ParameterPrefix)

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

example
    {environment : VEnv} {universes count : Nat} {context : List VExpr} {domain body : VExpr}
    (kind : environment.SortArity universes context (count + 1) (.forallE domain body))
    (environmentWF : environment.WF) (contextWF : OnCtx context (environment.IsType universes)) :
    environment.SortArity universes (domain :: context) count body := by
  apply VEnv.SortArity.forallBody <;> assumption

example
    (arguments : TypedParameterApplications environment universes model source replacements values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (kind : environment.SortArity universes.length model.vlctx.toCtx (count + replacements.length) source) :
    environment.SortArity universes.length model.vlctx.toCtx count result := by
  apply TypedParameterApplications.resultKind <;> assumption

example
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace environment universes trace virtual semantic finalVirtual finalSemantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length virtual.toCtx
      (count + (finalIndices.size - indices.size)) semantic) :
    environment.SortArity universes.length finalVirtual.toCtx count finalSemantic := by
  apply TranslatedRecursorIndexTrace.finalKind <;> assumption

example
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    HeaderParameterKindedApplicationBatch registration.semantic root.lparams
      stage.before.model.checker.mlctx stats types := by
  exact registration.parentParameterKindedApplications

example
    (batch : HeaderParameterKindedApplicationBatch environment original model stats types)
    (extension : UniverseNameExtension original target) :
    HeaderParameterKindedApplicationBatch environment target
      (model.reindexLevels (UniverseNameExtension.levels original target)) stats types := by
  apply HeaderParameterKindedApplicationBatch.reindexUniverses <;> assumption

example
    {trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader}
    (endpoint : HeaderRecursorIndexCheckerEndpoint trace checker finalChecker semantic resultSemantic)
    (translated : checker.TrExprS (mkAppN head stats.params) value)
    (typed : checker.HasType value resultSemantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx indices.size resultSemantic) :
    ∃ finalValue, finalChecker.TrExprS (mkAppN (mkAppN head stats.params) indices) finalValue ∧
      finalChecker.IsType finalValue := by
  apply HeaderRecursorIndexCheckerEndpoint.parentTypehoodOfKind <;> assumption

example
    {stats : InductiveStats} {source terminal : Expr} {finalIndex : Nat}
    {indices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source 0 #[] reader terminal finalIndex indices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterKindedApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size) (counts : indices.size = stats.nindices[parent]!)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok source) :
    ∃ input : HeaderParameterApplicationInput checker.venv checker.lparams checker.mlctx stats types[parent].type,
      ∃ finalChecker, HeaderRecursorIndexCheckerEndpoint trace checker finalChecker input.semantic input.result ∧
        ∃ value, finalChecker.TrExprS (mkAppN (mkAppN stats.indConsts[parent]! stats.params) indices) value ∧
          finalChecker.IsType value := by
  apply RecursorIndexTrace.checkedHeaderBatchTypehood <;> assumption

example (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
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
              HeaderParameterKindedApplicationBatch registration.semantic universes model stats types.toArray := by
  apply run.headerParameterKindedUniverseContinuation <;> assumption

example
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
    {source terminal : Expr} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats source index nindices reader terminal finalStats finalIndices finalReader)
    (complete : nparams ≤ index) :
    CheckedHeaderTrace 0 stats source 0 nindices reader terminal finalStats finalIndices finalReader := by
  apply CheckedHeaderTrace.withoutParameters <;> assumption

example
    {nparams index nindices finalIndices : Nat} {stats finalStats : InductiveStats}
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
    {semantic : VExpr} (translated : checker.TrExprS source semantic)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ (finalChecker : TypeChecker.VContext) (identifiers : List FVarId)
      (values : List VExpr) (result : VExpr),
      finalChecker.venv = checker.venv ∧ finalChecker.lparams = checker.lparams ∧
      HeaderCheckerAligned finalChecker finalReader ∧ ({} : TypeChecker.VState).WF finalChecker ∧
      ParameterPrefix checker.mlctx finalChecker.mlctx identifiers ∧
      HeaderParameterModels finalStats finalChecker.vlctx ∧
      TypedParameterApplications checker.venv checker.lparams finalChecker.mlctx
        (semantic.liftN identifiers.length) (finalStats.params.toList.drop index) values result ∧
      checker.venv.SortArity checker.lparams.length finalChecker.vlctx.toCtx (finalIndices - nindices) result := by
  apply CheckedHeaderTrace.parameterApplicationsWithKind <;> assumption

example
    {nparams finalIndices : Nat} {stats finalStats : InductiveStats}
    {source normalized inferred terminal sorted : Expr} {name : Name} {reader finalReader : Context}
    (trace : CheckedHeaderTrace nparams stats normalized 0 0 reader terminal finalStats finalIndices finalReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameterCount : stats.params.size = if stats.indConsts.isEmpty then 0 else nparams)
    (parameters : HeaderParameterModels stats checker.vlctx)
    (guarded : reader.env.checkNoMVarNoFVar name source = .ok ())
    (checked : (monadLift (TypeChecker.checkType source) : M Expr) reader = .ok inferred)
    (normalization : (monadLift (TypeChecker.whnf source) : M Expr) reader = .ok normalized)
    (sortedCall : (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader = .ok sorted) :
    ∃ receipt : HeaderParameterApplicationReceipt checker finalStats finalReader source,
      receipt.indexArity = finalIndices := by
  apply CheckedHeaderTrace.parameterApplicationsFromSourceWithKind <;> assumption

example (before : CheckedHeaderContinuation root original nparams types stats reader)
    (parent : Nat) (bound : parent < types.size) :
    ∃ input : HeaderParameterApplicationInput root.venv root.lparams before.model.checker.mlctx stats types[parent].type,
      root.venv.SortArity root.lparams.length before.model.checker.vlctx.toCtx stats.nindices[parent]! input.result :=
  before.parameterApplicationKinds parent bound

example (receipt : HeaderParameterApplicationReceipt initial stats reader source) :
    initial.venv.SortArity initial.lparams.length receipt.checker.vlctx.toCtx receipt.indexArity receipt.input.result :=
  receipt.resultKind

example : HeaderParameterKindedApplicationBatch environment universes model stats #[] := by
  intro parent bound
  simp at bound

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def annotationDomain (mode : Nat) (carrier : Expr) : Expr :=
  let equivalent := Level.max .zero (.succ .zero)
  let nested := Expr.app (.const ``outParam [equivalent]) (.app (.const ``semiOutParam [.succ .zero]) carrier)
  if mode == 1 then nested
  else if mode == 2 then .app (.app (.const ``optParam [equivalent]) nested) (.lit (.natVal 0))
  else if mode == 3 then .app (.app (.const ``autoParam [equivalent]) nested) (.const ``Lean.Syntax.missing [])
  else if mode == 4 then .mdata {} nested
  else carrier

private theorem nonuniformDomain (level : VLevel) :
    ¬ UniformAnnotationUniverse [] (annotationDomain 1 natural) level := by
  intro uniform
  cases level <;> simp [annotationDomain, natural, UniformAnnotationUniverse, VLevel.ofLevel] at uniform

example {environment : VEnv} {virtual : VLCtx} {reader : Context}
    (environmentWF : environment.WF) (constants : CanonicalAnnotationConstants environment)
    (definitions : CanonicalAnnotationDefinitions environment)
    (correspondence : TrLCtx environment [] reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS environment [] virtual (.forallE name (annotationDomain 1 natural) body binder)
      (.forallE semantic bodySemantic))
    (domainTyped : environment.HasType 0 virtual.toCtx semantic (.sort level)) :
    ∃ peeled, PeeledIndexOpening environment [] reader virtual name (annotationDomain 1 natural) body binder
      semantic bodySemantic level peeled :=
  translatedForallIndexOpening_unrestricted environmentWF constants definitions correspondence reserved translated domainTyped

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters indices mode : Nat) (dependent : Bool := false)
    (levels : List Level := []) (annotationMode : Nat := 0) : InductiveType :=
  let parameterLevel := levels.headD (.succ .zero)
  let resultLevel := levels.foldl Level.max (.succ .zero)
  let suffix := fun body => (List.range indices).foldr
    (fun _ body => .forallE `index (annotationDomain annotationMode natural) body .default) body
  let close := fun wrapped body =>
    let residual := if wrapped then delay (suffix body) mode else suffix body
    if dependent then
      .forallE `carrier (.sort parameterLevel) (.forallE `value (.bvar 0) residual .default) .implicit
    else
      (List.range parameters).foldr (fun _ body => .forallE `carrier (.sort parameterLevel) body .implicit) residual
  let arguments := (List.range (parameters + indices)).toArray.map
    fun index => Expr.bvar (parameters + indices - 1 - index)
  { name, type := close true (.sort resultLevel),
    ctors := [⟨name ++ `mk, close false (mkAppN (.const name levels) arguments)⟩] }

private def dependentIndices (name : Name) (parameters : Nat) : InductiveType :=
  let close := fun annotated body =>
    let body := .forallE `indexType sortType (.forallE `indexValue
      (if annotated then annotationDomain 1 (.bvar 0) else .bvar 0) body .default) .implicit
    (List.range parameters).foldr (fun _ body => .forallE `carrier sortType body .implicit) body
  let arguments := (List.range (parameters + 2)).toArray.map fun index => Expr.bvar (parameters + 1 - index)
  { name, type := close true (.sort (.succ (.succ .zero))),
    ctors := [⟨name ++ `mk, close false (mkAppN (.const name []) arguments)⟩] }

private def consumeParameters (stats : InductiveStats) (source : Expr) (reader : Context)
    (index : Nat := 0) : Except Kernel.Exception (Expr × Nat) :=
  if index < stats.params.size then
    match source with
    | .forallE _ _ body _ => do
      let opened := body.instantiate1 stats.params[index]!
      let normalized ← (monadLift (TypeChecker.whnf opened) : M Expr) reader
      let (residual, changes) ← consumeParameters stats normalized reader (index + 1)
      return (residual, changes + if opened == normalized then 0 else 1)
    | _ => .error .deepRecursion
  else .ok (source, 0)
termination_by stats.params.size - index

private def consumeIndices (source : Expr) (arguments : List Expr) (reader : Context) :
    Except Kernel.Exception (Expr × Nat) := do
  match arguments with
  | [] => return (source, 0)
  | argument :: remaining =>
    let .forallE _ domain body _ := source | throw .deepRecursion
    let .fvar identifier := argument | throw .deepRecursion
    let some declaration := reader.lctx.find? identifier | throw .deepRecursion
    unless declaration.type == peelTypeAnnotations domain do throw .deepRecursion
    let normalized ← (monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) reader
    let (terminal, changes) ← consumeIndices normalized remaining reader
    return (terminal, changes + if domain == peelTypeAnnotations domain then 0 else 1)

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat) (originalUniverses : List Name := []) :
    MetaM (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let host ← getEnv
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  let mut peeled := 0
  let mut underapplied := 0
  let mut overapplied := 0
  let mut staleCounts := 0
  let mut parentPasses := 0
  let elimination := `freshElimination
  for isUnsafe in [false, true] do
    unless types.isEmpty || (host.addDeclCore 0 (.inductDecl originalUniverses parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected residual kinds controls {types.map (·.name)}"
    for allowPrimitive in [false, true] do
      let reader : Context := {
        env := host.toKernelEnv, lparams := originalUniverses,
        safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
      let .ok (stats, current, registered) := checkInductiveTypes parameters types (fun stats => do
          let current ← read
          let actual ← declareInductiveTypes stats parameters types 0 isUnsafe
          withEnv actual do
            checkConstructors types stats isUnsafe
            return (stats, current, ← declareConstructors stats types isUnsafe)) reader
        | throwError "residual kinds parameter registration checkpoint failed"
      unless stats.nindices.size == types.size do throwError "accepted residual-kind header count array is not total"
      let .ok final := run parameters types.toList 0 reader | throwError "residual kinds complete run failed"
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
            if ({} : TypeChecker.State).ngen.namePrefix == reached.ngen.namePrefix then
              throwError "residual kinds actual reader aliases the reset checker namespace"
            for elimLevel in [.zero, .param elimination] do
              let parentReader := if elimLevel.isParam && !reached.lparams.contains elimination then
                  { reached with lparams := getRecLevelParams elimLevel reached.lparams }
                else reached
              let captureInfos : Array RecInfo → M (Array RecInfo × Context) :=
                fun infos => do return (infos, ← readThe Context)
              let .ok (infos, finished) := mkRecInfos.loopInd1 stats types elimLevel 0 #[] captureInfos parentReader
                | throwError "actual whole parent/motive pass failed"
              unless infos.size == types.size do throwError "actual whole parent pass has wrong native record count"
              for parent in [:types.size] do
                let info := infos[parent]!
                unless info.indices.size == stats.nindices[parent]! && info.minors.isEmpty do
                  throwError "actual whole parent pass acquired stale index/minor eligibility"
                let partialParent := mkAppN stats.indConsts[parent]! stats.params
                unless ((monadLift (TypeChecker.checkType partialParent) : M Expr) finished).isOk do
                  throwError "actual whole parent pass did not preserve checked parameter applications"
                let .ok parentKind := (monadLift (TypeChecker.checkType (mkAppN partialParent info.indices)) : M Expr) finished
                  | throwError "actual whole parent pass did not preserve saturated parent typing"
                unless ((monadLift (TypeChecker.ensureSort parentKind) : M Expr) finished).isOk do
                  throwError "actual whole parent pass did not preserve saturated parent typehood"
                let .ok resultKind := (monadLift (TypeChecker.checkType
                    (.app (mkAppN info.motive info.indices) info.major)) : M Expr) finished
                  | throwError "actual whole parent pass motive lost its exact arguments"
                let .ok true := (monadLift (TypeChecker.isDefEq resultKind (.sort elimLevel)) : M Bool) finished
                  | throwError "actual whole parent pass motive lost its elimination universe"
                if ((monadLift (TypeChecker.checkType
                    (.app (mkAppN info.motive info.indices) (.lit (.natVal 0)))) : M Expr) finished).isOk then
                  throwError "actual whole parent pass motive accepted a wrong-domain major"
              parentPasses := parentPasses + 1
            for parent in [:types.size] do
              let source := types[parent]!.type
              let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
                | throwError "residual kinds original header WHNF failed"
              let .ok (residual, changes) := consumeParameters stats normalized reached
                | throwError "residual kinds accepted parameters failed normalized consumption"
              let partialParent := mkAppN stats.indConsts[parent]! stats.params
              let .ok inferred := (monadLift (TypeChecker.checkType partialParent) : M Expr) reached
                | throwError "residual kinds partial parent failed genuine domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
                | throwError "residual kinds normalized partial-parent residual mismatch"
              let .ok residualKind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
                | throwError "residual kinds normalized residual strict checking failed"
              unless ((monadLift (TypeChecker.ensureSort residualKind) : M Expr) reached).isOk do
                throwError "residual kinds normalized residual is not a type"
              let capture := fun indices => do return (indices, ← readThe Context)
              let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[]
                  reached.fuel.inductiveFuel capture reached
                | throwError "residual kinds actual binder loop failed"
              unless indices.size == stats.nindices[parent]! do
                throwError "actual index count disagrees with accepted residual sort arity"
              let stale := { stats with nindices := stats.nindices.modify parent (· + 1) }
              let .ok (staleIndices, _) := mkRecInfos.loopArgs1 stale normalized 0 #[]
                  reached.fuel.inductiveFuel capture reached
                | throwError "unchecked stale-count traversal changed"
              unless staleIndices == indices && staleIndices.size != stale.nindices[parent]! do
                throwError "unchecked stale-count traversal acquired numeric arity eligibility"
              staleCounts := staleCounts + 1
              let .ok (suffixIndices, suffixReader) := mkRecInfos.loopArgs1 stats residual stats.params.size #[]
                  (reached.fuel.inductiveFuel - stats.params.size) capture reached
                | throwError "residual kinds exact remaining-fuel suffix failed"
              unless indices == suffixIndices && finalReader.ngen == suffixReader.ngen &&
                  localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
                throwError "residual kinds parameter prefix changed actual index context"
              let .ok (terminal, peelings) := consumeIndices residual indices.toList finalReader
                | throwError "residual kinds selected indices failed normalized consumption"
              let .ok sortedTerminal := (monadLift (TypeChecker.ensureSort terminal) : M Expr) finalReader
                | throwError "actual terminal failed native sort checking for exact index-count closure"
              unless sortedTerminal.isSort do throwError "native terminal sort-check result is not a sort"
              let .ok appliedType := (monadLift (TypeChecker.checkType (mkAppN partialParent indices)) : M Expr) finalReader
                | throwError "residual kinds full parent application failed genuine index-domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq appliedType terminal) : M Bool) finalReader
                | throwError "residual kinds full application differs from actual normalized terminal"
              unless ((monadLift (TypeChecker.ensureSort appliedType) : M Expr) finalReader).isOk do
                throwError "residual kinds full parent is not a type"
              let majorDomain := recursorMajorDomain stats parent indices
              let .ok majorKind := (monadLift (TypeChecker.checkType majorDomain) : M Expr) finalReader
                | throwError "actual parent major domain checking failed"
              unless ((monadLift (TypeChecker.ensureSort majorKind) : M Expr) finalReader).isOk do
                throwError "actual parent major domain is not a type"
              let captureBinder : Expr → M (Expr × Context) := fun value => do return (value, ← readThe Context)
              let .ok (major, majorReader) := withLocalDecl `t .default majorDomain captureBinder finalReader
                | throwError "actual parent major allocation failed"
              let expectedMajor := recursorIndexContext finalReader `t .default majorDomain
              unless major == .fvar ⟨finalReader.ngen.curr⟩ && majorReader.ngen == expectedMajor.ngen &&
                  localDeclarations majorReader.lctx == localDeclarations expectedMajor.lctx do
                throwError "actual major reader or allocation differs from semantic parent model step"
              for elimLevel in [.zero, .param elimination] do
                let motiveBase := if elimLevel.isParam && !majorReader.lparams.contains elimination then
                    { majorReader with lparams := getRecLevelParams elimLevel majorReader.lparams }
                  else majorReader
                let motiveDomain := recursorMotiveDomain elimLevel indices major motiveBase
                let .ok motiveKind := (monadLift (TypeChecker.checkType motiveDomain) : M Expr) motiveBase
                  | throwError "actual parent motive domain checking failed"
                unless ((monadLift (TypeChecker.ensureSort motiveKind) : M Expr) motiveBase).isOk do
                  throwError "actual parent motive domain is not a type"
                let name := recursorMotiveName types parent
                let .ok (motive, motiveReader) := withLocalDecl name .default motiveDomain captureBinder motiveBase
                  | throwError "actual parent motive allocation failed"
                let expectedMotive := recursorMotiveContext stats parent indices
                  { finalReader with lparams := motiveBase.lparams } elimLevel name
                unless motive == .fvar ⟨majorReader.ngen.curr⟩ && motiveReader.ngen == expectedMotive.ngen &&
                    motiveReader.lparams == expectedMotive.lparams &&
                    localDeclarations motiveReader.lctx == localDeclarations expectedMotive.lctx do
                  throwError "actual motive reader or allocation differs from semantic parent model step"
                let .ok motiveResult := (monadLift (TypeChecker.checkType
                    (.app (mkAppN motive indices) major)) : M Expr) motiveReader
                  | throwError "actual parent motive rejected its exact indices and major"
                let .ok true := (monadLift (TypeChecker.isDefEq motiveResult (.sort elimLevel)) : M Bool) motiveReader
                  | throwError "actual parent motive application lost its elimination sort"
                let badDomain := recursorMotiveDomain (.param `unmappedElimination) indices major motiveBase
                if ((monadLift (TypeChecker.checkType badDomain) : M Expr) motiveBase).isOk then
                  throwError "unmapped elimination universe acquired motive domain eligibility"
              unless indices.isEmpty do
                let .ok partialKind := (monadLift (TypeChecker.checkType
                    (mkAppN partialParent (indices.extract 0 (indices.size - 1)))) : M Expr) finalReader
                  | throwError "underapplication lost genuine typing"
                if ((monadLift (TypeChecker.ensureSort partialKind) : M Expr) finalReader).isOk then
                  throwError "positive residual sort arity acquired parent typehood without all indices"
                underapplied := underapplied + 1
                if ((monadLift (TypeChecker.checkType
                    (.app (mkAppN partialParent indices) (.lit (.natVal 0)))) : M Expr) finalReader).isOk then
                  throwError "overapplication crossed the residual sort endpoint"
                overapplied := overapplied + 1
              passed := passed + 1
              peeled := peeled + peelings
              changed := changed + changes
              initialChanges := initialChanges + if source == normalized then 0 else 1
              unless parameters == 0 do
                let wrongReader := recursorIndexContext reached `wrongParameter .default natural
                let wrongStats := { stats with params := stats.params.set! 0 (.fvar ⟨reached.ngen.curr⟩) }
                unless wrongStats.params.all (·.isFVar) do throwError "wrong-domain control lost all-free-variable boundary"
                let .ok (wrongIndices, wrongFinal) := mkRecInfos.loopArgs1 wrongStats normalized 0 #[]
                    wrongReader.fuel.inductiveFuel capture wrongReader
                  | throwError "unchecked wrong-domain binder loop unexpectedly failed"
                if ((monadLift (TypeChecker.checkType
                    (mkAppN (mkAppN stats.indConsts[parent]! wrongStats.params) wrongIndices)) : M Expr) wrongFinal).isOk then
                  throwError "wrong-domain free-variable parameters acquired typed application eligibility"
                rejected := rejected + 1
  return (passed, changed, rejected, initialChanges, peeled, underapplied, overapplied, staleCounts, parentPasses)

private def rejectionControls : MetaM (Nat × Nat × Nat) := do
  let host ← getEnv
  let mut rejected := 0
  let mut nativeRejected := 0
  let mut stopped := 0
  for isUnsafe in [false, true] do
    for source in [
        .forallE `index (.app (.const ``outParam []) natural) sortType .default,
        .forallE `index (.app (.app (.const ``optParam [.succ .zero]) natural) sortType) sortType .default,
        .forallE `index (.app (.app (.const ``autoParam [.succ .zero]) natural) (.lit (.natVal 0))) sortType .default,
        natural] do
      let types : Array InductiveType := #[{ name := `ResidualKindRejected, type := source, ctors := [] }]
      if (host.addDeclCore 0 (.inductDecl [] 0 types.toList isUnsafe) none).isOk then
        throwError "native kernel accepted malformed annotation or nonsort header"
      nativeRejected := nativeRejected + 1
      for allowPrimitive in [false, true] do
        let reader : Context := {
          env := host.toKernelEnv, lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive }
        if (checkInductiveTypes 0 types (fun _ => pure ()) reader).isOk ||
            (run 0 types.toList 0 reader).isOk then
          throwError "malformed annotation or nonsort header acquired accepted eligibility"
        rejected := rejected + 1
        if source == natural then
          unless ((monadLift (TypeChecker.checkType source) : M Expr) reader).isOk do
            throwError "unchecked nonsort terminal lost its genuine source typehood"
          let stats : InductiveStats := {
            levels := [], resultLevel := .zero, indConsts := #[], params := #[], isNotZero := false }
          let .ok indices := mkRecInfos.loopArgs1 stats source 0 #[] reader.fuel.inductiveFuel pure reader
            | throwError "unchecked nonsort terminal no longer stops the native binder loop"
          unless indices.isEmpty do throwError "unchecked nonsort terminal unexpectedly allocated indices"
          if ((monadLift (TypeChecker.ensureSort source) : M Expr) reader).isOk then
            throwError "source typehood plus stopped traversal manufactured terminal-sort eligibility"
          stopped := stopped + 1
  return (rejected, nativeRejected, stopped)

private def auditModule (moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName | throwError "residual-kind audit module absent"
  let mut allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``TypeChecker.checkType.WF, ``TypeChecker.ensureSort.WF,
      ``acceptedHeaderNormalization, ``CheckedHeaderTrace.zeroParameterKind,
      ``CheckedHeaderTrace.checkerModels, ``translatedHeaderOpeningWithSemantics,
      ``translatedReusedHeaderParameterArgument, ``acceptedSourceTranslation,
      ``checkNoMVarNoFVar.WF, ``checkInductiveTypes.loopInd.loop.scopedTrace,
      ``checkConstructors.acceptedTraces, ``checkInductiveTypes.headersWF,
      ``declareInductiveTypes.strongHeaderAxiomView, ``TypeChecker.VState.WF.reset,
      ``ElimNestedInductive.ParameterPrefix.insertion, ``AcceptedConstructorTrace.domainReceipts,
      ``VEnv.SortArity.apply, ``VEnv.SortArity.instL,
      ``HeaderRecursorIndexCheckerEndpoint.applicationOfPartial,
      ``ConstructorConstantRegistration.headerInput, ``ConstructorConstantRegistration.increase] do
    allowed := allowed ++ (← collectAxioms name)
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "residual-kind owned axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "residual-kind unexpected {dependency} in {name}"
      logInfo m!"{name}: {dependencies.size} inherited dependencies = {repr dependencies}"
      count := count + 1
  logInfo m!"{moduleName}: {count} exhaustive owned declarations audited against genuine unchanged earlier foundations"

run_meta
  for moduleName in [`Lean4Lean.Verify.InductiveHeaderParameterApplications,
      `Lean4Lean.Verify.InductiveHeaderContinuation, `Lean4Lean.Verify.InductiveHeaderResidualKinds] do
    auditModule moduleName
  let mut passed := 0
  let mut changed := 0
  let mut rejected := 0
  let mut initialChanges := 0
  let mut peeled := 0
  let mut underapplied := 0
  let mut overapplied := 0
  let mut staleCounts := 0
  let mut parentPasses := 0
  for (types, parameters, universes) in [
      (#[], 0, []),
      (#[{ name := `ResidualKindNoConstructors, type := sortType, ctors := [] }], 0, []),
      (#[{ (family `ResidualKindParameterizedEmpty 2 0 0) with ctors := [] }], 2, []),
      (#[family `ResidualKindZero 0 0 0], 0, []),
      (#[family `ResidualKindZeroLet 0 1 1], 0, []),
      (#[family `ResidualKindZeroBeta 0 2 2], 0, []),
      (#[family `ResidualKindZeroMetadata 0 1 3], 0, []),
      (#[family `ResidualKindOne 1 1 0], 1, []),
      (#[family `ResidualKindTwoLet 2 2 1], 2, []),
      (#[family `ResidualKindTwoBeta 2 1 2], 2, []),
      (#[family `ResidualKindTwoMetadata 2 2 3], 2, []),
      (#[family `ResidualKindDependent 2 1 1 true], 2, []),
      (#[family `ResidualKindMutualFirst 2 1 1 true, family `ResidualKindMutualSecond 2 2 2 true], 2, []),
      (#[family `ResidualKindUniverse 2 2 1 true [.param `universe]], 2, [`universe]),
      (#[family `ResidualKindReordered 2 1 2 true [.param `universe, .param `otherUniverse]],
        2, [`universe, `otherUniverse]),
      (#[family `ResidualKindNonuniform 0 2 0 false [] 1], 0, []),
      (#[family `ResidualKindOptional 1 1 1 false [] 2], 1, []),
      (#[family `ResidualKindAutomatic 2 2 2 true [] 3], 2, []),
      (#[family `ResidualKindMetadataBarrier 2 1 3 true [] 4], 2, []),
      (#[family `ResidualKindMutualAnnotatedFirst 2 1 1 true [] 1,
          family `ResidualKindMutualAnnotatedSecond 2 2 2 true [] 2], 2, []),
      (#[dependentIndices `ResidualKindDependentIndicesZero 0], 0, []),
      (#[dependentIndices `ResidualKindDependentIndicesTwo 2], 2, [])] do
    let (accepted, conversions, failed, initial, peelings, under, over, stale, passes) ← checkBatch types parameters universes
    passed := passed + accepted
    changed := changed + conversions
    rejected := rejected + failed
    initialChanges := initialChanges + initial
    peeled := peeled + peelings
    underapplied := underapplied + under
    overapplied := overapplied + over
    staleCounts := staleCounts + stale
    parentPasses := parentPasses + passes
  unless changed > 0 && initialChanges > 0 && rejected > 0 && peeled > 0 && underapplied > 0 && overapplied > 0 do
    throwError "residual kinds controls missed conversions, zero-parameter input normalization, or rejection"
  let (malformed, nativeMalformed, nonsort) ← rejectionControls
  logInfo m!"{parentPasses} actual complete parent/motive passes preserve every original partial/saturated parent and all checked motives in the final native reader; wrong-domain majors reject; empty and differing-count mutual batches included"
  logInfo m!"{passed} accepted residual-kind parent applications and major allocations passed with exact native index counts; {passed * 2} actual motive domains, allocations and saturated applications passed at zero/fresh elimination levels and reject unmapped universes; {underapplied} typed underapplications fail typehood, {overapplied} overapplications reject and {staleCounts} unchecked stale-count traversals fail numeric arity eligibility; {changed} parameter-opening WHNF changes, {initialChanges} original-header changes, {peeled} actually peeled stored index domains and {rejected} unchecked wrong-domain free-variable arrays rejected; {malformed} malformed/nonsort header controls and {nativeMalformed} corresponding native declarations rejected; {nonsort} genuinely type-valued unchecked stopped traversals retain no terminal-sort eligibility; zero/one/two/dependent parameters, differing mutual index counts, original/fresh/reordered universes, registered/full-run environments, original/local/let contexts, both safeties/primitive modes, let/beta/metadata wrappers, nonuniform nested outParam/semiOutParam/optParam/autoParam chains, metadata barriers and dependent index domains checked; exact remaining fuel, index arrays, name generators, local declarations, residual and full-application typehood agree; runtime controls do not fabricate semantic contexts"

end InductiveHeaderResidualKindsTest
