import Lean4Lean.Verify.InductiveHeaderAxiomView
import Lean4Lean.Verify.InductiveMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix ContextReserved)
open private Lean4Lean.AddInductive.readWF Lean4Lean.AddInductive.bindWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces
open private Lean4Lean.AddInductive.typedHeaderList from Lean4Lean.Verify.InductiveMutualHeaderTyping

structure TypedHeaderReader (base : MLCtx) (stats : InductiveStats) (reader : Context) where
  checker : TypeChecker.VContext
  parameterModel : MLCtx
  parameterIdentifiers : List FVarId
  ambientIdentifiers : List FVarId
  aligned : HeaderCheckerAligned checker reader
  initialWF : ({} : TypeChecker.VState).WF checker
  parameters : ParameterPrefix base parameterModel parameterIdentifiers
  ambient : ParameterPrefix parameterModel checker.mlctx ambientIdentifiers
  statsParams : stats.params = (parameterIdentifiers.map Expr.fvar).toArray

theorem TypedHeaderReader.parameterModels (model : TypedHeaderReader base stats reader) :
    HeaderParameterModels stats model.checker.vlctx := by
  intro parameter member
  have listed : parameter ∈ stats.params.toList := Array.mem_toList_iff.mpr member
  rw [model.statsParams, List.toList_toArray] at listed
  obtain ⟨identifier, present, rfl⟩ := List.mem_map.mp listed
  refine ⟨identifier, rfl, model.ambient.insertion.fvars_sublist.subset ?_⟩
  rw [model.parameters.fvars]
  simp [present]

theorem TypedHeaderReader.history (model : TypedHeaderReader base stats reader) :
    ParameterPrefix base model.checker.mlctx (model.parameterIdentifiers ++ model.ambientIdentifiers) :=
  model.parameters.trans model.ambient

theorem TypedHeaderReader.parameterBase (model : TypedHeaderReader base stats reader) :
    model.checker.mlctx.dropN model.ambientIdentifiers.length model.ambient.bound = model.parameterModel :=
  model.ambient.drop

theorem TypedHeaderReader.parameterWF (model : TypedHeaderReader base stats reader) :
    model.parameterModel.WF model.checker.venv model.checker.lparams :=
  model.ambient.baseWF model.checker.mlctx_wf

def TypedHeaderReader.inHeaderAxiomView (model : TypedHeaderReader base stats reader)
    (shadow : Kernel.Environment) (semantic : VEnv) (increase : model.checker.venv ≤ semantic)
    (history : TrEnv model.checker.safety shadow semantic)
    (primitives : NativePrimitiveFrame model.checker.env shadow) :
    TypedHeaderReader base stats { reader with env := shadow } := {
  checker := model.checker.inHeaderAxiomView shadow semantic increase history primitives
  parameterModel := model.parameterModel
  parameterIdentifiers := model.parameterIdentifiers
  ambientIdentifiers := model.ambientIdentifiers
  aligned := by
    unfold HeaderCheckerAligned
    rw [TypeChecker.VContext.inHeaderAxiomView.context, model.aligned]
  initialWF := TypeChecker.VState.WF.headerAxiomReset model.checker shadow semantic increase history primitives
    model.initialWF
  parameters := model.parameters
  ambient := model.ambient
  statsParams := model.statsParams }

structure CheckedHeaderContinuation (root : TypeChecker.VContext) (original : Context)
    (nparams : Nat) (types : Array InductiveType) (stats : InductiveStats) (reader : Context) where
  model : TypedHeaderReader root.mlctx stats reader
  sameEnv : model.checker.venv = root.venv
  sameUniverses : model.checker.lparams = root.lparams
  frame : original.HeaderFrame reader
  readerReserved : ContextReserved reader.lctx reader.ngen
  readerDifferent : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix
  sizes : stats.HeaderSizes types.size
  parameterCount : stats.ParamsCount nparams types.size
  headers : List VInductiveType
  models : List.Forall₂ (TrInductiveHeader root.venv root.lparams) types.toList headers
  typesWF : ∀ header ∈ headers, header.toVConstant.WF root.venv

private theorem typedHeaderLoop (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M resultType) (post : resultType → Prop)
    (root : TypeChecker.VContext) (original : Context) (empty : root.mlctx = .nil)
    (processed : Nat) (stats : InductiveStats) (reader : Context)
    (model : TypedHeaderReader root.mlctx stats reader)
    (sameEnv : model.checker.venv = root.venv) (sameUniverses : model.checker.lparams = root.lparams)
    (frame : original.HeaderFrame reader) (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (withinPrefix : processed ≤ types.size)
    (indicesCount : stats.nindices.size = processed) (indCount : stats.indConsts.size = processed)
    (levelCount : stats.levels.length = reader.lparams.length)
    (parameterCount : stats.params.size = if processed = 0 then 0 else nparams)
    (firstContext : processed = 0 → model.checker.mlctx = root.mlctx)
    (typed : ∀ parent, ∀ bound : parent < types.size, parent < processed →
      ∃ header, TrInductiveHeader root.venv root.lparams types[parent] header ∧ header.toVConstant.WF root.venv)
    (continuation : ∀ stats current, CheckedHeaderContinuation root original nparams types stats current →
      (next stats current).WF post) :
    (checkInductiveTypes.loopInd nparams types next processed stats reader).WF post := by
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i within
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro checkedUnit guarded
    cases checkedUnit
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro inferred checked
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro normalized normalizedCall
    have supported := checkNoMVarNoFVar.WF reader.env types[processed].name types[processed].type () guarded
    obtain ⟨sourceSemantic, sourceTranslated⟩ := acceptedSourceTranslation model.checker reader model.aligned
      model.initialWF (supported.mono fun _ impossible => impossible.elim) checked
    obtain ⟨normalizedSemantic, normalizedTranslated, equality⟩ :=
      acceptedHeaderNormalization model.checker reader model.aligned model.initialWF
        (sourceTranslated.trExpr model.checker.Ewf.ordered model.checker.Δwf) normalizedCall
    apply checkInductiveTypes.loopInd.loop.scopedTrace
    · have native : model.checker.mlctx.lctx = reader.lctx :=
        model.checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx model.aligned)
      exact native ▸ model.checker.trlctx.1
    · exact reserved
    intro terminal finalStats count current trace scope
    have finalModel : ∃ target : TypedHeaderReader root.mlctx finalStats current,
        target.checker.venv = model.checker.venv ∧ target.checker.lparams = model.checker.lparams := by
      by_cases first : processed = 0
      · have firstHeader : stats.indConsts.isEmpty = true := by simp [Array.isEmpty, indCount, first]
        have noParameters : stats.params = #[] := by
          apply Array.eq_empty_of_size_eq_zero
          simpa only [first, if_pos] using parameterCount
        obtain ⟨parameterModel, checker, parameters, indices, env, universes, aligned, stateWF,
          parameterHistory, indexHistory, params, _, _, _, _⟩ := trace.firstModelFromSource
            model.checker model.aligned model.initialWF reserved different firstHeader noParameters
            (sameEnv ▸ constants) (sameEnv ▸ definitions) guarded checked normalizedCall
        refine ⟨{
          checker, parameterModel, parameterIdentifiers := parameters, ambientIdentifiers := indices,
          aligned, initialWF := stateWF,
          parameters := by simpa only [firstContext first] using parameterHistory,
          ambient := indexHistory,
          statsParams := Array.toList_inj.mp (by simpa only [List.toList_toArray] using params) }, env, universes⟩
      · obtain ⟨checker, identifiers, env, universes, aligned, stateWF, history, _, _⟩ :=
          trace.checkerModels model.checker model.aligned model.initialWF reserved different
            (sameEnv ▸ constants) (sameEnv ▸ definitions)
            (by simpa [Array.isEmpty, indCount] using parameterCount) model.parameterModels
            ⟨normalizedSemantic, normalizedTranslated⟩
        have unchanged := trace.paramsUnchanged (by simpa [Array.isEmpty, indCount] using first)
        exact ⟨{
          checker, parameterModel := model.parameterModel,
          parameterIdentifiers := model.parameterIdentifiers,
          ambientIdentifiers := model.ambientIdentifiers ++ identifiers,
          aligned, initialWF := stateWF, parameters := model.parameters,
          ambient := model.ambient.trans history,
          statsParams := unchanged.trans model.statsParams }, env, universes⟩
    obtain ⟨target, targetEnv, targetUniverses⟩ := finalModel
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro sorted sortedCall
    have sourceTyped := VEnv.IsType.defeqU_l model.checker.Ewf model.checker.Δwf.toCtx equality
      (trace.initialIsType model.checker model.aligned model.initialWF normalizedTranslated sortedCall)
    have headerTyped := model.history.closedHeaderWF sameEnv sameUniverses empty sourceTranslated sourceTyped supported
    obtain ⟨indicesUnchanged, constantsUnchanged, levelsUnchanged⟩ := trace.headerFields
    have finalCount : finalStats.params.size = nparams :=
      trace.paramsCount (by simpa [Array.isEmpty, indCount] using parameterCount)
    have resume (nextStats : InductiveStats)
        (nextIndices : nextStats.nindices.size = processed + 1)
        (nextCount : nextStats.indConsts.size = processed + 1)
        (nextLevels : nextStats.levels = finalStats.levels)
        (nextParameters : nextStats.params = finalStats.params) :
        (checkInductiveTypes.loopInd nparams types next (processed + 1) nextStats current).WF post := by
      let nextModel : TypedHeaderReader root.mlctx nextStats current := {
        checker := target.checker, parameterModel := target.parameterModel,
        parameterIdentifiers := target.parameterIdentifiers, ambientIdentifiers := target.ambientIdentifiers,
        aligned := target.aligned, initialWF := target.initialWF,
        parameters := target.parameters, ambient := target.ambient,
        statsParams := nextParameters.trans target.statsParams }
      apply typedHeaderLoop nparams types next post root original empty (processed + 1) nextStats current nextModel
        (targetEnv.trans sameEnv) (targetUniverses.trans sameUniverses) (frame.trans scope.toHeaderFrame)
        scope.reserved (by simpa only [trace.generatorPrefix] using different) constants definitions
        (by omega) nextIndices nextCount
        (by simpa only [nextLevels, levelsUnchanged, scope.lparams] using levelCount)
        (by simp [nextParameters, finalCount]) (by intro impossible; omega) ?_ continuation
      intro parent bound earlier
      by_cases selected : parent = processed
      · subst parent
        exact headerTyped
      · exact typed parent bound (by omega)
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      apply resume
      · simp only [Array.size_push, indicesUnchanged, indicesCount]
      · simp only [Array.size_push, constantsUnchanged, indCount]
      · rfl
      · rfl
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        apply resume
        · simp only [Array.size_push, indicesUnchanged, indicesCount]
        · simp only [Array.size_push, constantsUnchanged, indCount]
        · rfl
        · rfl
  · apply Lean4Lean.AddInductive.readWF
    have complete : processed = types.size := by omega
    obtain ⟨headers, models, typesWF⟩ := Lean4Lean.AddInductive.typedHeaderList
      types.toList root.venv root.lparams (by
        intro type member
        obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
        exact typed parent bound (by omega))
    simp only [levelCount, indicesCount, indCount, complete, beq_self_eq_true, ite_true]
    split
    · exact continuation stats reader {
        model, sameEnv, sameUniverses, frame, readerReserved := reserved, readerDifferent := different,
        sizes := ⟨indicesCount.trans complete, indCount.trans complete⟩,
        parameterCount := by simpa only [InductiveStats.ParamsCount, complete] using parameterCount,
        headers, models, typesWF }
    · have zero : types.size = 0 := by
        by_contra nonempty
        have correct : stats.params.size = nparams := by simpa [complete, nonempty] using parameterCount
        simp [correct] at ‹¬(stats.params.size == nparams) = true›
      have noParameters : stats.params = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        simpa [complete, zero] using parameterCount
      simp only [panicWithPosWithDecl, panic, panicCore]
      let fallback : TypedHeaderReader root.mlctx (default : InductiveStats) reader := {
        checker := model.checker, parameterModel := model.parameterModel,
        parameterIdentifiers := model.parameterIdentifiers, ambientIdentifiers := model.ambientIdentifiers,
        aligned := model.aligned, initialWF := model.initialWF,
        parameters := model.parameters, ambient := model.ambient,
        statsParams := model.statsParams.symm.trans noParameters |>.symm }
      exact continuation _ reader {
        model := fallback, sameEnv, sameUniverses, frame, readerReserved := reserved, readerDifferent := different,
        sizes := by
          change (0 = types.size ∧ 0 = types.size)
          exact ⟨zero.symm, zero.symm⟩,
        parameterCount := by
          change 0 = if types.size = 0 then 0 else nparams
          simp [zero],
        headers, models, typesWF }
termination_by types.size - processed
decreasing_by all_goals simp_wf; omega

theorem checkInductiveTypes.withTypedContinuation (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M resultType) (post : resultType → Prop)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (continuation : ∀ stats current, CheckedHeaderContinuation root reader nparams types stats current →
      (next stats current).WF post) :
    (checkInductiveTypes nparams types next reader).WF post := by
  have stateWF := TypeChecker.VState.WF.reset root (by simp [TypeChecker.VContext.vlctx, empty, MLCtx.vlctx])
  have nativeContext : reader.lctx = {} := by
    have native : root.mlctx.lctx = reader.lctx := root.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    rw [← native, empty]
    rfl
  have reserved : ContextReserved reader.lctx reader.ngen := by
    rw [nativeContext]
    exact ContextReserved.empty reader.ngen
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  let initial : TypedHeaderReader root.mlctx
      { (default : InductiveStats) with levels := reader.lparams.map Level.param } reader := {
    checker := root, parameterModel := root.mlctx,
    parameterIdentifiers := [], ambientIdentifiers := [],
    aligned, initialWF := stateWF, parameters := .nil, ambient := .nil, statsParams := rfl }
  exact typedHeaderLoop nparams types next post root reader empty 0 _ reader initial rfl rfl (.refl reader)
    reserved different constants definitions (Nat.zero_le _) rfl rfl (by simp) rfl (fun _ => rfl)
    (by intro parent bound impossible; omega) continuation

theorem checkInductiveTypes.typedContinuation (nparams : Nat) (types : Array InductiveType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) :
    (checkInductiveTypes nparams types (fun stats => return (stats, ← read)) reader).WF fun result =>
      Nonempty (CheckedHeaderContinuation root reader nparams types result.1 result.2) :=
  checkInductiveTypes.withTypedContinuation nparams types _ _ root reader aligned empty different constants definitions
    (fun _ _ model => .pure ⟨model⟩)

structure HeaderAxiomContinuation (root : TypeChecker.VContext) (original : Context)
    (nparams : Nat) (types : Array InductiveType) (stats : InductiveStats) (reader : Context)
    (actual : Kernel.Environment) where
  before : CheckedHeaderContinuation root original nparams types stats reader
  shadow : Kernel.Environment
  semantic : VEnv
  registered : root.venv.addInductHeaders before.headers = some semantic
  initialWF : reader.env.constants.WF
  actualWF : actual.constants.WF
  actualRegistration : FreshRegistrationTrace HeaderRegistrationRecord reader.env actual
  shadowRegistration : FreshRegistrationTrace HeaderAxiomRegistrationRecord reader.env shadow
  agreement : HeaderAxiomAgreement actual shadow
  lookups : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow
  constructorHeaders : ∀ type ∈ types, ∃ header,
    actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name
  values : NativeValueFrame reader.env shadow
  primitives : NativePrimitiveFrame reader.env shadow
  model : TypedHeaderReader root.mlctx stats { reader with env := shadow }
  semantic_eq : model.checker.venv = semantic

theorem checkInductiveTypes.withHeaderAxiomContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType) (post : resultType → Prop)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (continuation : ∀ stats current actual,
      HeaderAxiomContinuation root reader nparams types stats current actual →
      (withEnv actual (next stats actual) current).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual (next stats actual)) reader).WF post := by
  apply checkInductiveTypes.withTypedContinuation nparams types _ post root reader aligned empty
    different constants definitions
  intro stats current before
  have nativeEnv : before.model.checker.env = current.env := congrArg TypeChecker.Context.env before.model.aligned
  have currentUniverses : current.lparams = root.lparams :=
    (congrArg TypeChecker.Context.lparams before.model.aligned).symm.trans before.sameUniverses
  have safety : before.model.checker.safety = root.safety := by
    have currentSafety : before.model.checker.safety = current.safety :=
      congrArg TypeChecker.Context.safety before.model.aligned
    have initialSafety : root.safety = reader.safety := congrArg TypeChecker.Context.safety aligned
    exact currentSafety.trans (before.frame.safety.trans initialSafety.symm)
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro actual declared
  obtain ⟨shadow, semantic, registered, history, agreement, values, lookups, primitives,
    actualRegistration, shadowRegistration⟩ :=
    declareInductiveTypes.strongHeaderAxiomRegistrationView current stats nparams types numNested isUnsafe
    (nativeEnv ▸ before.model.checker.trenv) (safety ▸ safetyBound) before.sizes.1
    (by simpa only [before.sameEnv, currentUniverses] using before.models)
    (by simpa only [before.sameEnv] using before.typesWF) actual declared
  have actualWF := (declareInductiveTypes.preservesValues current stats nparams types numNested isUnsafe
    (nativeEnv ▸ before.model.checker.trenv.map_wf) actual declared).map_wf
  have metadata := (declareInductiveTypes.metadata stats nparams types numNested isUnsafe current
    (nativeEnv ▸ before.model.checker.trenv.map_wf) before.sizes.1 actual declared).2.2
  have primitiveFrame := primitives (before.frame.allowPrimitive.trans ordinary)
  have modelPrimitiveFrame : NativePrimitiveFrame before.model.checker.env shadow := nativeEnv.symm ▸ primitiveFrame
  have increase := VEnv.addInductHeaders.le registered
  exact continuation stats current actual {
    before, shadow, semantic,
    registered := by simpa only [before.sameEnv] using registered,
    initialWF := nativeEnv ▸ before.model.checker.trenv.map_wf,
    actualWF, actualRegistration, shadowRegistration, agreement, lookups,
    constructorHeaders := by
      intro type member
      obtain ⟨index, bound, rfl⟩ := Array.mem_iff_getElem.mp member
      exact ⟨_, metadata index bound, rfl⟩,
    values, primitives := primitiveFrame,
    model := before.model.inHeaderAxiomView shadow semantic increase history modelPrimitiveFrame,
    semantic_eq := rfl }

theorem checkInductiveTypes.constructorAxiomContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        next stats actual) reader).WF fun _ => ∃ stats current actual,
      ∃ _stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        checkConstructors types stats isUnsafe { current with env := actual } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { current with env := actual } := by
  refine checkInductiveTypes.withHeaderAxiomContinuation nparams types numNested isUnsafe
    (next := fun stats actual => do
      checkConstructors types stats isUnsafe
      next stats actual)
    (post := fun _ => ∃ stats current actual,
      ∃ _stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        checkConstructors types stats isUnsafe { current with env := actual } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { current with env := actual })
    root reader aligned empty different constants definitions ordinary safetyBound ?_
  intro stats current actual stage
  change ((checkConstructors types stats isUnsafe >>= fun _ => next stats actual)
    { current with env := actual }).WF _
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro checked accepted
  cases checked
  intro _ _
  exact ⟨stats, current, actual, stage, accepted,
    checkConstructors.acceptedTraces types stats isUnsafe { current with env := actual } () accepted⟩

theorem run.constructorAxiomContinuation
    (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual,
      ∃ _stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () ∧
        stats.AcceptedConstructorTraces types.toArray (reader.safety != .safe) { current with env := actual } := by
  have sameSafety : root.safety = reader.safety := congrArg TypeChecker.Context.safety aligned
  have safetyBound : root.safety ≤ if reader.safety != .safe then .unsafe else .safe := by
    rw [← sameSafety]
    cases mode : root.safety with
    | safe => decide
    | «unsafe» => decide
    | «partial» => exact False.elim (ordinarySafety mode)
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.constructorAxiomContinuation nparams types.toArray numNested
    (reader.safety != .safe) _ root reader aligned empty different constants definitions ordinary safetyBound

end Lean4Lean.AddInductive
