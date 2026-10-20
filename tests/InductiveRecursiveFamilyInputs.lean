import Lean4Lean.Verify.InductiveRecursiveFamilyInputs
import Lean.Util.CollectAxioms

namespace InductiveRecursiveFamilyInputsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive
open TypeChecker (MLCtx)

deriving instance BEq for NameGenerator
deriving instance BEq for LocalDecl

/-- Recovered header inputs feed changed-index recovery after environment,
universe and local-context transport. No family input or typed indices are
premises of this bridge; native residual/domain matching remains explicit. -/
private theorem checkedInputRecoversIndices
    {trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader}
    (endpoint : HeaderRecursorIndexModelEndpoint env original trace base indexModel semantic result)
    (envWF : env.WF) (baseWF : base.WF env original)
    (partialTranslated : TrExprS env original base.vlctx
      (mkAppN stats.indConsts[parent]! stats.params) partialValue)
    (partialTyped : env.HasType original.length base.vlctx.toCtx partialValue result)
    (accepted : isValidIndAppIdx stats terminal parent = true)
    (increase : env ≤ extended) (extendedWF : extended.WF)
    (universes : UniverseNameExtension original targetUniverses)
    (ruleWF : ruleModel.WF extended targetUniverses)
    (insertion : VLCtx.FVLift'
      (base.reindexLevels (UniverseNameExtension.levels original targetUniverses)).vlctx
      ruleModel.vlctx 0 lift 0)
    (application : TrExprS extended targetUniverses ruleModel.vlctx terminal terminalSemantic)
    (domains : ∀ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex →
        NativeTelescopeDomains residual target (getIIndices stats terminal).2.toList sourceEnd targetEnd) :
    NativeTelescopeArguments extended targetUniverses ruleModel target
      (getIIndices stats terminal).2.toList targetEnd := by
  obtain ⟨residual, afterIndex, parameters, ⟨input⟩⟩ :=
    endpoint.familyIndexInput envWF baseWF partialTranslated partialTyped accepted
  let current := ((input.monoEnv increase).reindexUniverses universes).weakFV
    extendedWF ruleWF insertion
  rw [← familyIndexPrefix_apply stats terminal] at application
  exact ((domains residual afterIndex parameters).argumentsFromApplication extendedWF ruleWF
    current.sourceTranslated current.translated current.typed application).2

private theorem canonicalHeaderRecoversIndices
    {terminal : Expr}
    (trace : RecursorIndexTrace stats headerSource 0 #[] reader sortTerminal finalIndex indices indexReader)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (complete : stats.params.size ≤ finalIndex)
    (batch : HeaderParameterApplicationBatch checker.venv checker.lparams checker.mlctx stats types)
    (parent : Nat) (bound : parent < types.size)
    (normalized : (monadLift (TypeChecker.whnf types[parent].type) : M Expr) reader = .ok headerSource)
    (telescope : SortTelescope types[parent].type)
    (annotations : IndexTraceAnnotationSupport checker.venv checker.lparams trace)
    (accepted : isValidIndAppIdx stats terminal parent = true)
    (fieldTranslated : TrExprS checker.venv checker.lparams checker.vlctx terminal fieldSemantic)
    (domains : ∀ residual afterIndex,
      RecursorIndexParameterPrefix stats reader headerSource 0 residual afterIndex →
        NativeTelescopeDomains residual target (getIIndices stats terminal).2.toList sourceEnd targetEnd) :
    NativeTelescopeArguments checker.venv checker.lparams checker.mlctx target
      (getIIndices stats terminal).2.toList targetEnd := by
  obtain ⟨residual, afterIndex, parameters, ⟨input⟩⟩ :=
    trace.familyIndexInputOfSortTelescope checker aligned constants definitions reserved complete
      batch parent bound normalized telescope annotations accepted
  rw [← familyIndexPrefix_apply stats terminal] at fieldTranslated
  exact ((domains residual afterIndex parameters).argumentsFromApplication checker.Ewf
    checker.mlctx_wf input.sourceTranslated input.translated input.typed fieldTranslated).2

private def parameter (binder : BinderInfo) : Expr :=
  .lam `ignored (.const ``Nat []) (.bvar 0) binder

private theorem parameterAnnotationsDiffer : parameter .implicit ≠ parameter .default := by
  intro equality
  cases equality

private def sortType : Expr := .sort (.succ .zero)
private def natural : Expr := .const ``Nat []

private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `transparent sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `transparent sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def family (name : Name) (parameters indices mode : Nat) (dependent : Bool := false)
    (levels : List Level := []) : InductiveType :=
  let parameterLevel := levels.headD (.succ .zero)
  let resultLevel := levels.foldl Level.max (.succ .zero)
  let suffix := fun body => (List.range indices).foldr
    (fun _ body => .forallE `index natural body .default) body
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

private def consumeIndices (source : Expr) (arguments : List Expr) (reader : Context) : Except Kernel.Exception Expr := do
  match arguments with
  | [] => return source
  | argument :: remaining =>
    let .forallE _ _ body _ := source | throw .deepRecursion
    let normalized ← (monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) reader
    consumeIndices normalized remaining reader

private def localDeclarations (context : LocalContext) : Array LocalDecl :=
  context.foldl (fun declarations declaration => declarations.push declaration) #[]

private def checkBatch (types : Array InductiveType) (parameters : Nat) (originalUniverses : List Name := []) :
    MetaM (Nat × Nat × Nat × Nat) := do
  let host ← getEnv
  let mut passed : Nat := 0
  let mut changed : Nat := 0
  let mut rejected : Nat := 0
  let mut initialChanges : Nat := 0
  let elimination := `freshElimination
  for isUnsafe in [false, true] do
    unless (host.addDeclCore 0 (.inductDecl originalUniverses parameters types.toList isUnsafe) none).isOk do
      throwError "native kernel rejected family inputs controls {types.map (·.name)}"
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
        | throwError "family inputs parameter registration checkpoint failed"
      let .ok final := run parameters types.toList 0 reader | throwError "family inputs complete run failed"
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
              let source := types[parent]!.type
              let .ok normalized := (monadLift (TypeChecker.whnf source) : M Expr) reached
                | throwError "family inputs original header WHNF failed"
              let .ok (residual, changes) := consumeParameters stats normalized reached
                | throwError "family inputs accepted parameters failed normalized consumption"
              let partialParent := mkAppN stats.indConsts[parent]! stats.params
              let .ok inferred := (monadLift (TypeChecker.checkType partialParent) : M Expr) reached
                | throwError "family inputs partial parent failed genuine domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq inferred residual) : M Bool) reached
                | throwError "family inputs normalized partial-parent residual mismatch"
              let .ok residualKind := (monadLift (TypeChecker.checkType residual) : M Expr) reached
                | throwError "family inputs normalized residual strict checking failed"
              unless ((monadLift (TypeChecker.ensureSort residualKind) : M Expr) reached).isOk do
                throwError "family inputs normalized residual is not a type"
              let capture := fun indices => do return (indices, ← readThe Context)
              let .ok (indices, finalReader) := mkRecInfos.loopArgs1 stats normalized 0 #[]
                  reached.fuel.inductiveFuel capture reached
                | throwError "family inputs actual binder loop failed"
              let .ok (suffixIndices, suffixReader) := mkRecInfos.loopArgs1 stats residual stats.params.size #[]
                  (reached.fuel.inductiveFuel - stats.params.size) capture reached
                | throwError "family inputs exact remaining-fuel suffix failed"
              unless indices == suffixIndices && finalReader.ngen == suffixReader.ngen &&
                  localDeclarations finalReader.lctx == localDeclarations suffixReader.lctx do
                throwError "family inputs parameter prefix changed actual index context"
              let .ok terminal := consumeIndices residual indices.toList finalReader
                | throwError "family inputs selected indices failed normalized consumption"
              unless terminal.isSort do throwError "family inputs accepted terminal is not a sort"
              let terminalFamily := mkAppN partialParent indices
              unless isValidIndAppIdx stats terminalFamily parent do
                throwError "family inputs: actual changed-index family failed recognition"
              let actualPrefix := familyIndexPrefix stats terminalFamily
              unless partialParent == actualPrefix &&
                  actualPrefix.mkAppList (getIIndices stats terminalFamily).2.toList == terminalFamily do
                throwError "family inputs: accepted prefix failed boolean agreement/reconstruction"
              let .ok prefixType := (monadLift (TypeChecker.checkType actualPrefix) : M Expr) finalReader
                | throwError "family inputs: actual prefix failed checking"
              let .ok true := (monadLift (TypeChecker.isDefEq prefixType residual) : M Bool) finalReader
                | throwError "family inputs: actual prefix/residual index signature mismatch"
              let .ok appliedType := (monadLift (TypeChecker.checkType terminalFamily) : M Expr) finalReader
                | throwError "family inputs full parent application failed genuine index-domain checking"
              let .ok true := (monadLift (TypeChecker.isDefEq appliedType terminal) : M Bool) finalReader
                | throwError "family inputs full application differs from actual normalized terminal"
              unless ((monadLift (TypeChecker.ensureSort appliedType) : M Expr) finalReader).isOk do
                throwError "family inputs full parent is not a type"
              passed := passed + 1
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
  return (passed, changed, rejected, initialChanges)


private def annotationFixture : MetaM Unit := do
  let natural := Expr.const ``Nat []
  let functionType := Expr.forallE `n natural natural .default
  let type : InductiveType := {
    name := `FamilyAnnotationParameter
    type := .forallE `function functionType (.forallE `index natural sortType .default) .default
    ctors := [⟨`FamilyAnnotationParameter.mk,
      .forallE `function functionType
        (mkAppN (.const `FamilyAnnotationParameter []) #[.bvar 0, .const ``Nat.zero []]) .default⟩] }
  let host ← getEnv
  unless (host.addDeclCore 0 (.inductDecl [] 1 [type] false) none).isOk do
    throwError "family inputs: native annotation-parameter fixture rejected"
  let context : Context := {
    env := host.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let .ok registered := run 1 [type] 0 context
    | throwError "family inputs: annotation-parameter registration rejected"
  let reader := { context with env := registered }
  let stats : InductiveStats := { (default : InductiveStats) with
    indConsts := #[.const type.name []], params := #[parameter .implicit], nindices := #[1] }
  let actual := mkAppN (.const type.name []) #[parameter .default, .const ``Nat.zero []]
  unless isValidIndAppIdx stats actual 0 do
    throwError "family inputs: binder-annotation variation failed recognition"
  let expected := mkAppN stats.indConsts[0]! stats.params
  let actualPrefix := familyIndexPrefix stats actual
  unless expected == actualPrefix do
    throwError "family inputs: accepted binder-annotation prefixes differ by boolean equality"
  for expression in [expected, actualPrefix, actual] do
    unless ((monadLift (TypeChecker.checkType expression) : M Expr) reader).isOk do
      throwError "family inputs: accepted annotation-parameter application failed typing"
  let .ok expectedType := (monadLift (TypeChecker.checkType expected) : M Expr) reader
    | throwError "family inputs: expected prefix failed"
  let .ok actualType := (monadLift (TypeChecker.checkType actualPrefix) : M Expr) reader
    | throwError "family inputs: actual prefix failed"
  unless ((monadLift (TypeChecker.isDefEq expectedType actualType) : M Bool) reader).toOption == some true do
    throwError "family inputs: annotation-different prefix types disagree"
  let invalidStats := { stats with params := #[.sort .zero] }
  let invalid := mkAppN (.const type.name []) #[.sort .zero, .const ``Nat.zero []]
  unless isValidIndAppIdx invalidStats invalid 0 do
    throwError "family inputs: invalid-parameter control missed the syntactic-only boundary"
  if ((monadLift (TypeChecker.checkType (familyIndexPrefix invalidStats invalid)) : M Expr) reader).isOk then
    throwError "family inputs: family recognition fabricated partial-header typing"
  logInfo "family inputs: native binder-annotation parameter variation accepted; distinct native expressions share translated-prefix eligibility; invalid-domain parameter recognized syntactically but rejected by genuine checking"

#print axioms isValidIndAppIdx.familyIndexPrefixMatches
#print axioms FamilyIndexInput.monoEnv
#print axioms FamilyIndexInput.weakFV
#print axioms FamilyIndexInput.reindexUniverses
#print axioms HeaderRecursorIndexModelEndpoint.familyIndexInput
#print axioms RecursorIndexTrace.familyIndexInputOfHeaderBatch
#print axioms RecursorIndexTrace.familyIndexInputInRule
#print axioms RecursorIndexTrace.familyIndexInputOfSortTelescope
#print axioms checkedInputRecoversIndices
#print axioms canonicalHeaderRecoversIndices
#print axioms parameterAnnotationsDiffer

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "family inputs: dependency manifest changed for {name}: {repr actual}"

private def oldNormalizationControl : MetaM Unit := do
  let environment ← getEnv
  let mut pending := #[( ``acceptedHeaderNormalization, [``acceptedHeaderNormalization])]
  let mut visited : NameSet := {}
  let mut found := false
  for _ in [:1000000] do
    if pending.isEmpty then break
    let (name, path) := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if name == ``VEnv.IsDefEqU.weakN_iff then
      logInfo m!"family inputs: legacy normalization rejected by strengthening audit; dependency path: {repr path.reverse}"
      found := true
      break
    let some information := environment.find? name | throwError "missing {name}"
    let references := information.type.getUsedConstants ++
      ((information.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    for next in references do pending := pending.push (next, next :: path)
  unless found do throwError "expected old normalization obstruction absent"

private def audit : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let projection := logical ++ [``sorryAx]
  let contextInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeEquality := [``Expr.eqv_eq, ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq]
  let structural := projection ++ contextInterfaces
  let endpoint := structural ++ nativeEquality
  let checked := endpoint ++ [``Expr.instantiate1_eq]
  let allowed := checked
  for (name, expected) in [
      (``isValidIndAppIdx.familyIndexPrefixMatches, logical ++ nativeEquality),
      (``FamilyIndexInput.monoEnv, projection), (``FamilyIndexInput.weakFV, structural),
      (``FamilyIndexInput.reindexUniverses, projection),
      (``HeaderRecursorIndexModelEndpoint.familyIndexInput, endpoint),
      (``RecursorIndexTrace.familyIndexInputOfHeaderBatch, checked),
      (``RecursorIndexTrace.familyIndexInputOfSortTelescope, checked),
      (``RecursorIndexTrace.familyIndexInputInRule, checked),
      (``checkedInputRecoversIndices, endpoint), (``canonicalHeaderRecoversIndices, checked),
      (``parameterAnnotationsDiffer, [])] do
    exactAxioms name expected
  let mut pending := #[``checkedInputRecoversIndices, ``canonicalHeaderRecoversIndices,
    ``parameterAnnotationsDiffer]
  let mut count : Nat := 0
  for moduleName in #[`Lean4Lean.Verify.InductiveRecursiveFamilyInputs] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "family inputs: audited module absent {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "family inputs: owned axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "family inputs: direct admission {name}"
        let actual ← collectAxioms name
        for dependency in actual do
          unless allowed.contains dependency do
            throwError "family inputs: unexpected dependency {dependency} in {name}"
        pending := pending.push name
        count := count + 1
  unless count > 0 do throwError "family inputs: empty owned-module audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do
      throwError "family inputs: missing forbidden audit root {name}"
  let mut visited : NameSet := {}
  let mut admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "family inputs: forbidden dependency {name}"
    let some information := environment.find? name
      | throwError "family inputs: dependency absent {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then admissions := admissions.push name
      pending := pending ++ proof.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        throwError "family inputs: missing proof body {name}"
      | _ => pure ()
  unless pending.isEmpty do throwError "family inputs: dependency traversal exceeded bound"
  let expectedAdmissions := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq,
    ``TrProj.wf, ``TrProj.instL, ``TrProj.defeqDFC]
  unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
    throwError "family inputs: inherited direct admission roots changed {repr admissions}"
  for name in [``HeaderRecursorIndexModelEndpoint.familyIndexInput,
      ``RecursorIndexTrace.familyIndexInputInRule] do
    let mut rejected : Bool := false
    try
      exactAxioms name logical
    catch exception =>
      let message ← exception.toMessageData.toString
      unless message.startsWith "family inputs: dependency manifest changed" do throw exception
      rejected := true
    unless rejected do throwError "family inputs: logical-only audit accepted inherited admissions"
  for name in [``checkBatch, ``annotationFixture, ``family, ``consumeParameters, ``consumeIndices] do
    let actual ← collectAxioms name
    for dependency in actual do
      unless logical.contains dependency do
        throwError "family inputs: runtime fixture unexpectedly depends on {dependency}"
  logInfo m!"family inputs: {count} owned declarations audited; exact 10/11-axiom endpoints and seven inherited projection admission roots pinned; full theorem/opaque proof traversal excludes known-false strengthening/confluence; logical-only negative audits rejected"

run_meta
  audit
  oldNormalizationControl
  annotationFixture
  let mut passed : Nat := 0
  let mut changed : Nat := 0
  let mut rejected : Nat := 0
  let mut initialChanges : Nat := 0
  for (types, parameters, universes) in [
      (#[family `FamilyInputZero 0 1 1], 0, []),
      (#[family `FamilyInputZeroBeta 0 2 2], 0, []),
      (#[family `FamilyInputOne 1 1 0], 1, []),
      (#[family `FamilyInputTwoMetadata 2 2 3], 2, []),
      (#[family `FamilyInputDependent 2 1 1 true], 2, []),
      (#[family `FamilyInputMutualLeft 2 1 1 true, family `FamilyInputMutualRight 2 2 2 true], 2, []),
      (#[family `FamilyInputUniverse 2 2 1 true [.param `universe]], 2, [`universe]),
      (#[family `FamilyInputReordered 2 1 2 true [.param `universe, .param `otherUniverse]],
        2, [`universe, `otherUniverse])] do
    let (accepted, conversions, failed, initial) ← checkBatch types parameters universes
    passed := passed + accepted
    changed := changed + conversions
    rejected := rejected + failed
    initialChanges := initialChanges + initial
  unless changed > 0 && initialChanges > 0 && rejected > 0 do
    throwError "family inputs: missing normalization or rejection coverage"
  logInfo m!"family inputs: {passed} actual header/index prefixes passed; {changed} parameter-opening and {initialChanges} initial-header normalization changes; {rejected} wrong-domain parameter arrays rejected; zero/one/two/dependent parameters, different mutual index counts, registered/full-run environments, original/fresh/reordered universes, local/let contexts, safe/unsafe and primitive modes"

end InductiveRecursiveFamilyInputsTest
