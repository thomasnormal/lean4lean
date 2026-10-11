import Lean4Lean.Verify.InductiveHeaderAxiomView
import Lean4Lean.Verify.InductiveMetadata
import Lean4Lean.Verify.InductiveHeaderKinds
import Lean4Lean.Verify.InductiveHeaderParameterApplications

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
  levels : types.size ≠ 0 → stats.levels = root.lparams.map Level.param
  headers : List VInductiveType
  models : List.Forall₂ (TrInductiveHeader root.venv root.lparams) types.toList headers
  typesWF : ∀ header ∈ headers, header.toVConstant.WF root.venv
  heads : ∀ parent, ∀ bound : parent < types.size,
    stats.indConsts[parent]! = .const types[parent].name stats.levels
  contextualKinds : nparams = 0 → ∀ parent, ∀ bound : parent < types.size, ∀ header,
    TrInductiveHeader root.venv root.lparams types[parent] header →
    root.venv.SortArity root.lparams.length model.checker.vlctx.toCtx stats.nindices[parent]! header.type
  parameterApplications : ∀ parent, ∀ bound : parent < types.size,
    Nonempty (HeaderParameterApplicationInput root.venv root.lparams model.checker.mlctx stats types[parent].type)

private theorem alignedPrefixIdentifiers
    {base : MLCtx} {left right : TypeChecker.VContext} {reader : Context}
    {identifiers more : List FVarId}
    (leftAligned : HeaderCheckerAligned left reader) (rightAligned : HeaderCheckerAligned right reader)
    (leftPrefix : ParameterPrefix base left.mlctx identifiers)
    (rightPrefix : ParameterPrefix base right.mlctx more) : identifiers = more := by
  have native : left.lctx = right.lctx :=
    congrArg TypeChecker.Context.lctx (leftAligned.trans rightAligned.symm)
  have native : left.lctx' = right.lctx' := left.lctx_eq.trans (native.trans right.lctx_eq.symm)
  have same : left.mlctx.vlctx.fvars = right.mlctx.vlctx.fvars :=
    left.trlctx.fvars_eq.symm.trans ((congrArg LocalContext.fvars native).trans right.trlctx.fvars_eq)
  rw [leftPrefix.fvars, rightPrefix.fvars] at same
  exact List.reverse_inj.mp (List.append_cancel_right same)

private theorem matchedHeaderMember {relation : sourceType → targetType → Prop}
    (related : List.Forall₂ relation sources targets) (member : source ∈ sources) :
    ∃ target ∈ targets, relation source target := by
  induction related with
  | nil => simp at member
  | cons head tail induction =>
    rcases List.mem_cons.mp member with equal | member
    · subst source
      exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨target, present, translated⟩ := induction member
      exact ⟨target, List.mem_cons_of_mem _ present, translated⟩

theorem CheckedHeaderContinuation.contextualHeaderKind
    (before : CheckedHeaderContinuation root original 0 types stats reader)
    (parent : Nat) (bound : parent < types.size) :
    ∃ header ∈ before.headers,
      stats.indConsts[parent]! = .const header.name stats.levels ∧
      root.venv.SortArity header.uvars before.model.checker.vlctx.toCtx
        (stats.params.size + stats.nindices[parent]!) header.type := by
  obtain ⟨header, member, translated⟩ := matchedHeaderMember before.models
    (Array.mem_toList_iff.mpr (Array.getElem_mem bound))
  have noParameters : stats.params.size = 0 := by
    simpa only [InductiveStats.ParamsCount, ite_self] using before.parameterCount
  refine ⟨header, member, ?_, ?_⟩
  · simpa only [translated.1] using before.heads parent bound
  · simpa only [noParameters, Nat.zero_add, translated.2.1] using
      before.contextualKinds rfl parent bound header translated

private theorem headerKindFromSource
    {root checker : TypeChecker.VContext} {identifiers : List FVarId} {source : InductiveType}
    (history : ParameterPrefix root.mlctx checker.mlctx identifiers)
    (sameEnv : checker.venv = root.venv) (sameUniverses : checker.lparams = root.lparams)
    (empty : root.mlctx = .nil) {semantic : VExpr} {count : Nat}
    (translated : checker.TrExprS source.type semantic)
    (kind : checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count semantic)
    {header : VInductiveType} (headerTranslated : TrInductiveHeader root.venv root.lparams source header) :
    root.venv.SortArity root.lparams.length checker.vlctx.toCtx count header.type := by
  have headerTranslation : TrExprS checker.venv checker.lparams [] source.type header.type := by
    simpa only [sameEnv, sameUniverses] using headerTranslated.2.2
  obtain ⟨_, headerWF⟩ := headerTranslation.wf checker.Ewf.ordered
    (show VLCtx.WF checker.venv checker.lparams.length [] from trivial)
  have closed := headerWF.hasType.1.closedN checker.Ewf.ordered trivial
  have insertion : VLCtx.FVLift' [] checker.vlctx 0 (.skipN .refl identifiers.length) 0 := by
    simpa only [TypeChecker.VContext.vlctx, empty, MLCtx.vlctx] using history.insertion
  have lifted := headerTranslation.weakFV' checker.Ewf.ordered insertion checker.Δwf
  have lifted : checker.TrExprS source.type header.type := by
    simpa only [closed.lift'_eq .zero] using lifted
  have equality := translated.uniq checker.Ewf (.refl checker.Ewf checker.Δwf) lifted
  simpa only [sameEnv, sameUniverses] using kind.defeq checker.Ewf checker.Δwf.toCtx equality.symm

private theorem transportHeaderKind
    {root source target : TypeChecker.VContext} {identifiers : List FVarId}
    {native : InductiveType} {header : VInductiveType} {count : Nat}
    (history : ParameterPrefix source.mlctx target.mlctx identifiers)
    (translated : TrInductiveHeader root.venv root.lparams native header)
    (kind : root.venv.SortArity root.lparams.length source.vlctx.toCtx count header.type) :
    root.venv.SortArity root.lparams.length target.vlctx.toCtx count header.type := by
  obtain ⟨_, typed⟩ := translated.2.2.wf root.Ewf.ordered
    (show VLCtx.WF root.venv root.lparams.length [] from trivial)
  have closed := typed.hasType.1.closedN root.Ewf.ordered trivial
  have insertion : Ctx.LiftN identifiers.length 0 source.vlctx.toCtx target.vlctx.toCtx :=
    Ctx.liftN_iff_lift'.mpr history.insertion.toCtx
  simpa only [closed.liftN_eq (Nat.zero_le _)] using kind.weakN root.Ewf.ordered insertion

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
    (levelEquation : stats.levels = root.lparams.map Level.param)
    (parameterCount : stats.params.size = if processed = 0 then 0 else nparams)
    (firstContext : processed = 0 → model.checker.mlctx = root.mlctx)
    (typed : ∀ parent, ∀ bound : parent < types.size, parent < processed →
      ∃ header, TrInductiveHeader root.venv root.lparams types[parent] header ∧ header.toVConstant.WF root.venv)
    (heads : ∀ parent, ∀ bound : parent < types.size, parent < processed →
      stats.indConsts[parent]! = .const types[parent].name stats.levels)
    (kinds : nparams = 0 → ∀ parent, ∀ bound : parent < types.size, parent < processed → ∀ header,
      TrInductiveHeader root.venv root.lparams types[parent] header →
      root.venv.SortArity root.lparams.length model.checker.vlctx.toCtx stats.nindices[parent]! header.type)
    (applications : ∀ parent, ∀ bound : parent < types.size, parent < processed →
      Nonempty (HeaderParameterApplicationInput root.venv root.lparams model.checker.mlctx stats types[parent].type))
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
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro sorted sortedCall
    obtain ⟨receipt⟩ := trace.parameterApplicationsFromSource model.checker model.aligned model.initialWF
      reserved different (sameEnv ▸ constants) (sameEnv ▸ definitions)
      (by simpa [Array.isEmpty, indCount] using parameterCount) model.parameterModels
      guarded checked normalizedCall sortedCall
    have finalModel : ∃ target : TypedHeaderReader root.mlctx finalStats current,
        target.checker = receipt.checker := by
      by_cases first : processed = 0
      · have firstHeader : stats.indConsts.isEmpty = true := by simp [Array.isEmpty, indCount, first]
        have noParameters : stats.params = #[] := by
          apply Array.eq_empty_of_size_eq_zero
          simpa only [first, if_pos] using parameterCount
        obtain ⟨_, checker, parameters, indices, _, _, aligned, _,
          parameterHistory, indexHistory, params, _, _, _, _⟩ := trace.firstModelFromSource
            model.checker model.aligned model.initialWF reserved different firstHeader noParameters
            (sameEnv ▸ constants) (sameEnv ▸ definitions) guarded checked normalizedCall
        have identifiers := alignedPrefixIdentifiers receipt.aligned aligned receipt.history
          (parameterHistory.trans indexHistory)
        obtain ⟨parameterModel, parameterPrefix, indexPrefix⟩ := receipt.history.splitAt parameters.length
        refine ⟨{
          checker := receipt.checker, parameterModel, parameterIdentifiers := parameters, ambientIdentifiers := indices,
          aligned := receipt.aligned, initialWF := receipt.stateWF,
          parameters := by simpa only [firstContext first, identifiers, List.take_left] using parameterPrefix,
          ambient := by simpa only [identifiers, List.drop_left] using indexPrefix,
          statsParams := Array.toList_inj.mp (by simpa only [List.toList_toArray] using params) }, rfl⟩
      ·
        have unchanged := trace.paramsUnchanged (by simpa [Array.isEmpty, indCount] using first)
        exact ⟨{
          checker := receipt.checker, parameterModel := model.parameterModel,
          parameterIdentifiers := model.parameterIdentifiers,
          ambientIdentifiers := model.ambientIdentifiers ++ receipt.identifiers,
          aligned := receipt.aligned, initialWF := receipt.stateWF, parameters := model.parameters,
          ambient := model.ambient.trans receipt.history,
          statsParams := unchanged.trans model.statsParams }, rfl⟩
    obtain ⟨target, targetChecker⟩ := finalModel
    have targetEnv : target.checker.venv = model.checker.venv := by
      simpa only [targetChecker] using receipt.sameEnv
    have targetUniverses : target.checker.lparams = model.checker.lparams := by
      simpa only [targetChecker] using receipt.sameUniverses
    have growth : ParameterPrefix model.checker.mlctx target.checker.mlctx receipt.identifiers := by
      simpa only [targetChecker] using receipt.history
    have targetWF : target.checker.mlctx.WF root.venv root.lparams := by
      simpa only [targetEnv, sameEnv, targetUniverses, sameUniverses] using target.checker.mlctx_wf
    have currentInput : HeaderParameterApplicationInput root.venv root.lparams target.checker.mlctx
        finalStats types[processed].type := by
      simpa only [targetChecker, sameEnv, sameUniverses] using receipt.input
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
        (nextParameters : nextStats.params = finalStats.params)
        (nextIndicesEq : nextStats.nindices = stats.nindices.push count)
        (nextHeadsEq : nextStats.indConsts = stats.indConsts.push (.const types[processed].name stats.levels)) :
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
        (nextLevels.trans (levelsUnchanged.trans levelEquation))
        (by simp [nextParameters, finalCount]) (by intro impossible; omega) ?_ ?_ ?_ ?_ continuation
      · intro parent bound earlier
        by_cases selected : parent = processed
        · subst parent
          exact headerTyped
        · exact typed parent bound (by omega)
      · intro parent bound earlier
        by_cases selected : parent = processed
        · subst parent
          rw [nextHeadsEq, getElem!_pos _ _ (by simp only [Array.size_push, indCount]; omega),
            Array.getElem_push]
          simp only [indCount, Nat.lt_irrefl, dite_false]
          rw [nextLevels, levelsUnchanged]
        · have previous : parent < stats.indConsts.size := by omega
          simpa only [nextHeadsEq, getElem!_pos (stats.indConsts.push (.const types[processed].name stats.levels))
              parent (by simp only [Array.size_push]; omega),
            Array.getElem_push_lt previous, ← getElem!_pos stats.indConsts parent previous,
            nextLevels, levelsUnchanged] using heads parent bound (by omega)
      · intro zero parent bound earlier header headerTranslated
        have currentKind : root.venv.SortArity root.lparams.length model.checker.vlctx.toCtx
            nextStats.nindices[parent]! header.type := by
          by_cases selected : parent = processed
          · subst parent
            have sourceKind := (zero ▸ trace).zeroParameterKind model.checker model.aligned model.initialWF
              reserved different (sameEnv ▸ constants) (sameEnv ▸ definitions) normalizedTranslated sortedCall
            have sourceKind := sourceKind.defeq model.checker.Ewf model.checker.Δwf.toCtx equality.symm
            rw [nextIndicesEq, getElem!_pos _ _ (by simp only [Array.size_push, indicesCount]; omega),
              Array.getElem_push]
            simp only [indicesCount, Nat.lt_irrefl, dite_false]
            simpa only [Nat.sub_zero] using headerKindFromSource model.history sameEnv sameUniverses
              empty sourceTranslated sourceKind headerTranslated
          · have previous : parent < stats.nindices.size := by omega
            simpa only [nextIndicesEq, getElem!_pos (stats.nindices.push count) parent
                (by simp only [Array.size_push]; omega),
              Array.getElem_push_lt previous, ← getElem!_pos stats.nindices parent previous] using
              kinds zero parent bound (by omega) header headerTranslated
        exact transportHeaderKind growth headerTranslated currentKind
      · intro parent bound earlier
        by_cases selected : parent = processed
        · subst parent
          exact ⟨currentInput.withStats nextParameters⟩
        · have previous : parent < processed := by omega
          obtain ⟨input⟩ := applications parent bound previous
          have unchanged := trace.paramsUnchanged (by simpa [Array.isEmpty, indCount] using (by omega : processed ≠ 0))
          exact ⟨(input.weakFV root.Ewf targetWF growth.insertion).withStats (nextParameters.trans unchanged)⟩
    split
    · apply Lean4Lean.AddInductive.readWF
      apply Lean4Lean.AddInductive.bindWF
      intro _
      exact resume _ (by simp only [Array.size_push, indicesUnchanged, indicesCount])
        (by simp only [Array.size_push, constantsUnchanged, indCount]) rfl rfl
        (by simp only [indicesUnchanged]) (by simp only [constantsUnchanged, levelsUnchanged])
    · split
      · exact Except.WF.throw
      · apply Lean4Lean.AddInductive.bindWF
        intro _
        exact resume _ (by simp only [Array.size_push, indicesUnchanged, indicesCount])
          (by simp only [Array.size_push, constantsUnchanged, indCount]) rfl rfl
          (by simp only [indicesUnchanged]) (by simp only [constantsUnchanged, levelsUnchanged])
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
        levels := fun _ => levelEquation,
        headers, models, typesWF,
        heads := fun parent bound => heads parent bound (by omega),
        contextualKinds := fun zero parent bound => kinds zero parent bound (by omega),
        parameterApplications := fun parent bound => applications parent bound (by omega) }
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
        levels := by simp [zero],
        headers, models, typesWF,
        heads := by intro parent bound; omega,
        contextualKinds := by intro zero parent bound; omega,
        parameterApplications := by intro parent bound; omega }
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
    reserved different constants definitions (Nat.zero_le _) rfl rfl (by simp)
    (congrArg (List.map Level.param) (congrArg TypeChecker.Context.lparams aligned).symm) rfl (fun _ => rfl)
    (by intro parent bound impossible; omega) (by intro parent bound impossible; omega)
    (by intro zero parent bound impossible; omega) (by intro parent bound impossible; omega) continuation

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
