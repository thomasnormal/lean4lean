import Lean4Lean.Verify.InductiveIndexBaseStrengthening
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexBaseStrengtheningTest

private theorem storedSourceSupportDerivesATypeInTheSmallerSemanticContext
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {lift : Lift} {domain : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF)
    (weakening : VLCtx.FVLift' smaller aligned 0 lift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (translated : TrExprS env universes original domain semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed domain 0) (supported : domain.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reduced,
      TrExprS env universes smaller domain reduced ∧
      env.HasType universes.length smaller.toCtx reduced (.sort level) ∧
      env.IsDefEq universes.length original.toCtx semantic (reduced.lift' lift) (.sort level) :=
  translated.strengthenIsType envWF weakening contexts typed closed supported

private theorem storedSupportForTheWholeOrderRestrictsToItsPrefix
    {full : LocalContext} {base ids tail : List FVarId}
    (supported : SelectedRecursorDomainFVars full base (ids ++ tail)) :
    SelectedRecursorDomainFVars full base ids := supported.appendLeft

private theorem lastStoredDomainNeedsOnlyEarlierSelectedIdentifiersAndTheSmallerBase
    {full : LocalContext} {base earlier : List FVarId} {identifier : FVarId}
    (supported : SelectedRecursorDomainFVars full base (earlier ++ [identifier]))
    {physicalIndex : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (lookup : full.find? identifier = some (.cdecl physicalIndex identifier name domain binder .default)) :
    domain.fvarsList ⊆ earlier ++ base := by
  exact supported earlier identifier [] (by simp only)
    physicalIndex name domain binder lookup

private theorem contractionDerivesTypedTransportAndAnAlignedRatherThanIdenticalEndpoint
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller : MLCtx} {ids : List FVarId} {baseLift : Lift}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (smallerWF : smaller.WF env universes)
    (weakening : VLCtx.FVLift' smaller.vlctx initial.vlctx 0 baseLift 0)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids) :
    ∃ transported aligned,
      SelectedRecursorTelescope env universes full smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned :=
  telescope.strengthenBase envWF initialWF smallerWF weakening supported

private theorem strengtheningPreservesEverySelectedNativeBinding
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller : MLCtx} {ids : List FVarId} {baseLift : Lift}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (smallerWF : smaller.WF env universes)
    (weakening : VLCtx.FVLift' smaller.vlctx initial.vlctx 0 baseLift 0)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids) :
    ∃ transported,
      SelectedRecursorTelescope env universes full smaller ids transported ∧
      transported.WF env universes ∧ SelectedCDeclBindingAgreement full transported.lctx ids := by
  obtain ⟨transported, _, transportedTelescope, transportedWF, _, _⟩ :=
    telescope.strengthenBase envWF initialWF smallerWF weakening supported
  exact ⟨transported, transportedTelescope, transportedWF,
    transportedTelescope.bindingAgreement smallerWF⟩

private theorem removalOfAnActualExtensionDerivesTheSmallerBaseWellFormedness
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final smaller : MLCtx} {ids removedIds : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (removal : IndexMLCtxExtension smaller removedIds initial)
    (supported : SelectedRecursorDomainFVars full smaller.vlctx.fvars ids) :
    ∃ transported aligned,
      SelectedRecursorTelescope env universes full smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0
        (.consN (.skipN .refl removedIds.length) ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length final.vlctx aligned :=
  telescope.strengthenExtension envWF initialWF removal supported

private theorem actualHistoryStrengtheningPreservesItsChronologyAndAlignsItsEndpoint
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (smaller : MLCtx) (smallerWF : smaller.WF env universes) (baseLift : Lift)
    (baseWeakening : VLCtx.FVLift' smaller.vlctx model.vlctx 0 baseLift 0)
    (supported : SelectedRecursorDomainFVars current.lctx smaller.vlctx.fvars
      ((finalIndices.toList.drop indices.size).map Expr.fvarId!)) :
    ∃ chronological ids transported aligned,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned :=
  history.selectedTelescopeStrengthened model modelWF native converted reserved current frame envWF
    smaller smallerWF baseLift baseWeakening supported

private theorem aDroppedStoredDependencyCannotSupplyContractionSupport
    {full : LocalContext} {base : List FVarId} {identifier dropped : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? identifier = some (.cdecl physicalIndex identifier name (.fvar dropped) binder .default))
    (missing : dropped ∉ base) (supported : SelectedRecursorDomainFVars full base [identifier]) : False := by
  have subset := supported [] identifier [] rfl physicalIndex name (.fvar dropped) binder lookup
  exact missing (subset (by simp only [Expr.fvarsList, List.mem_singleton]))

private theorem currentSelectedIdentifierIsNotAnEarlierDomainDependency
    {full : LocalContext} {base : List FVarId} {identifier : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? identifier = some (.cdecl physicalIndex identifier name (.fvar identifier) binder .default))
    (missing : identifier ∉ base) (supported : SelectedRecursorDomainFVars full base [identifier]) : False :=
  aDroppedStoredDependencyCannotSupplyContractionSupport lookup missing supported

private theorem futureSelectedIdentifierCannotRepairAnEarlierStoredDomain
    {full : LocalContext} {base : List FVarId} {first future : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? first = some (.cdecl physicalIndex first name (.fvar future) binder .default))
    (missing : future ∉ base) (supported : SelectedRecursorDomainFVars full base [first, future]) : False := by
  have subset := supported [] first [future] rfl physicalIndex name (.fvar future) binder lookup
  exact missing (subset (by simp only [Expr.fvarsList, List.mem_singleton]))

private theorem trueCutoffInverseRequiresAnActualPriorLift
    (expression : VExpr) (removed cutoff : Nat) :
    (expression.liftN removed cutoff).unliftN removed cutoff = expression := VExpr.unliftN_liftN

private theorem contractionKeepsPriorSelectedReferencesAndReducesBaseReferences :
    (VExpr.app (.bvar 0) (.bvar 5)).unliftN 3 2 = .app (.bvar 0) (.bvar 2) ∧
      (VExpr.app (.bvar 0) (.bvar 5)).unliftN 3 2 ≠ .app (.bvar 0) (.bvar 5) ∧
      (VExpr.app (.bvar 0) (.bvar 5)).unliftN 3 2 ≠
        (VExpr.app (.bvar 0) (.bvar 5)).unliftN 3 0 := by
  refine ⟨rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem aReferenceInsideTheDeletedIntervalHasNoSyntacticInverse :
    (VExpr.bvar 1).unliftN 1 1 = .sort .zero ∧ ¬ (VExpr.bvar 1).Skips 1 1 := by
  refine ⟨rfl, ?_⟩
  intro skips
  cases skips

private def variablePositions : VExpr → List Nat
  | .bvar position => [position]
  | .sort _ | .const _ _ => []
  | .app function argument | .lam function argument | .forallE function argument =>
      variablePositions function ++ variablePositions argument

private def checkCutoffInverses : MetaM Unit := do
  for removed in [1, 2, 5] do
    for earlier in [1, 2, 4] do
      let source := VExpr.app (.bvar 0) (.bvar earlier)
      let lifted := source.liftN removed earlier
      let reduced := lifted.unliftN removed earlier
      unless variablePositions reduced == [0, earlier] && variablePositions reduced != variablePositions lifted &&
          variablePositions reduced != variablePositions (lifted.unliftN removed 0) do
        throwError "index-strengthening contraction used identity or the wrong cutoff"
      let nested := VExpr.forallE (.app (.bvar 0) (.bvar earlier))
        (.lam (.bvar (earlier + 1)) (.app (.bvar 1) (.bvar (earlier + 2))))
      unless variablePositions ((nested.liftN removed earlier).unliftN removed earlier) ==
          [0, earlier, earlier + 1, 1, earlier + 2] do
        throwError "index-strengthening contraction failed the nested-binder inverse control"

private def supportsStoredDomains (full : LocalContext) (base ids : List FVarId) : Bool := Id.run do
  let mut earlier : List FVarId := []
  for identifier in ids do
    let some (.cdecl _ _ _ domain _ .default) := full.find? identifier | return false
    unless domain.fvarsList.all (fun dependency => (earlier ++ base).contains dependency) do return false
    earlier := earlier ++ [identifier]
  return true

private def nativeModels (removed : Nat) : MLCtx × MLCtx × List FVarId := Id.run do
  let retained : FVarId := ⟨`StrengtheningRetained⟩
  let first : FVarId := ⟨`StrengtheningFirst⟩
  let second : FVarId := ⟨`StrengtheningSecond⟩
  let smaller := MLCtx.vlet ⟨`StrengtheningLet⟩ `retainedLet (.const ``Nat []) (.lit (.natVal 0))
    (.const ``Nat []) (.const ``Nat.zero [])
    (.vlam ⟨`StrengtheningDependent⟩ `dependent (.fvar retained) (.bvar 0) .default
      (.vlam retained `retained (.sort (.succ .zero)) (.sort (.succ .zero)) .implicit .nil))
  let originalBase := (List.range removed).foldl (fun model position =>
    .vlam ⟨Name.num `StrengtheningDropped position⟩ `dropped (.const ``Nat []) (.const ``Nat []) .default model) smaller
  let domain := mkApp3 (.const ``Eq [.succ .zero]) (.fvar retained) (.fvar first) (.fvar first)
  let semantic := VExpr.app (.app (.app (.const ``Eq [.succ .zero]) (.bvar (removed + 2))) (.bvar 0)) (.bvar 0)
  let original := MLCtx.vlam second `witness domain semantic .instImplicit
    (.vlam first `first (.fvar retained) (.bvar (removed + 1)) .default originalBase)
  let transported := MLCtx.vlam second `witness domain (semantic.unliftN removed 1) .instImplicit
    (.vlam first `first (.fvar retained) ((VExpr.bvar (removed + 1)).unliftN removed 0) .default smaller)
  return (original, transported, [first, second])

private def checkNativeBinding (original transported : MLCtx) (identifier : FVarId)
    (removed : Nat) : MetaM Unit := do
  let some (.cdecl oldIndex oldId oldName oldDomain oldBinder .default) := original.lctx.find? identifier
    | throwError "index-strengthening original stored cdecl missing"
  let some (.cdecl newIndex newId newName newDomain newBinder .default) := transported.lctx.find? identifier
    | throwError "index-strengthening contracted stored cdecl missing"
  unless oldId == newId && oldName == newName && oldDomain == newDomain && oldBinder == newBinder &&
      oldIndex == newIndex + removed && oldDomain.fvarsList == newDomain.fvarsList do
    throwError "index-strengthening contraction changed retained native provenance"

private def checkRetainedBaseBindings (original transported : MLCtx) : MetaM Unit := do
  for identifier in [FVarId.mk `StrengtheningRetained, FVarId.mk `StrengtheningDependent,
      FVarId.mk `StrengtheningLet] do
    let some prior := original.lctx.find? identifier
      | throwError "index-strengthening original retained base binding missing"
    let some retained := transported.lctx.find? identifier
      | throwError "index-strengthening contracted retained base binding missing"
    unless prior.toExpr == retained.toExpr && prior.type == retained.type &&
        prior.value? == retained.value? && prior.index == retained.index do
      throwError "index-strengthening replaced a retained dependent/let base binding"

private def checkSupportFailures : MetaM Unit := do
  let retained : FVarId := ⟨`SupportRetained⟩
  let dropped : FVarId := ⟨`SupportDropped⟩
  let first : FVarId := ⟨`SupportFirst⟩
  let future : FVarId := ⟨`SupportFuture⟩
  let initial := ({} : LocalContext).mkLocalDecl retained `retained (.sort (.succ .zero)) .default
    |>.mkLocalDecl dropped `dropped (.const ``Nat []) .default
  for dependency in [dropped, first, future] do
    let full := initial.mkLocalDecl first `first (.fvar dependency) .default
      |>.mkLocalDecl future `future (.fvar retained) .implicit
    unless !supportsStoredDomains full [retained] [first, future] do
      throwError "index-strengthening accepted a dropped/current/future stored dependency"

private def runtimeFixtures : MetaM Unit := do
  checkCutoffInverses
  checkSupportFailures
  for removed in [0, 1, 3] do
    let (original, transported, ids) := nativeModels removed
    unless supportsStoredDomains original.lctx [⟨`StrengtheningRetained⟩] ids do
      throwError "index-strengthening rejected supported earlier-selected/native-base domains"
    for identifier in ids do checkNativeBinding original transported identifier removed
    checkRetainedBaseBindings original transported
    match transported with
    | .vlam _ _ _ semantic _ (.vlam _ _ _ firstSemantic _ _) =>
      unless variablePositions semantic == [2, 0, 0] && variablePositions firstSemantic == [1] do
        throwError "index-strengthening native contraction model used incorrect semantic references"
    | _ => throwError "index-strengthening native contraction model shape changed"
  logInfo "index-strengthening runtime: nine mixed-reference and nine nested cutoff inverses; six retained native cdecl provenance checks; nine retained dependent/let base checks; three dropped/current/future support failures; numerical/native controls do not supply independently typed models"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "index-strengthening audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-strengthening unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-strengthening audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index-strengthening new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditProvenance (name moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-strengthening provenance module absent: {moduleName}"
  unless environment.getModuleIdxFor? name == some moduleIndex do
    throwError "index-strengthening inherited provenance changed: {name} from {moduleName}"

private def auditFoundations (logical nativeInterfaces : List Name) : MetaM Unit := do
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.weakFV'_inv, `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.uniq, `Lean4Lean.Verify.Typing.Lemmas),
      (``VEnv.HasType.weak'_iff, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    auditProvenance name moduleName
    unless (← collectAxioms name).contains ``sorryAx do
      throwError "index-strengthening inherited admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  for name in nativeInterfaces do
    let some (.axiomInfo _) := (← getEnv).find? name
      | throwError "index-strengthening native interface is not an existing axiom: {name}"
    auditProvenance name `Lean4Lean.Verify.Axioms
    auditDeclaration name (logical ++ [name])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "index-strengthening forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"index-strengthening unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let inherited := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``storedSourceSupportDerivesATypeInTheSmallerSemanticContext (logical ++ [``sorryAx])
  for name in [``contractionDerivesTypedTransportAndAnAlignedRatherThanIdenticalEndpoint,
      ``strengtheningPreservesEverySelectedNativeBinding,
      ``removalOfAnActualExtensionDerivesTheSmallerBaseWellFormedness,
      ``actualHistoryStrengtheningPreservesItsChronologyAndAlignsItsEndpoint] do
    auditDeclaration name inherited
  for name in [``storedSupportForTheWholeOrderRestrictsToItsPrefix,
      ``lastStoredDomainNeedsOnlyEarlierSelectedIdentifiersAndTheSmallerBase,
      ``aDroppedStoredDependencyCannotSupplyContractionSupport,
      ``currentSelectedIdentifierIsNotAnEarlierDomainDependency,
      ``futureSelectedIdentifierCannotRepairAnEarlierStoredDomain,
      ``trueCutoffInverseRequiresAnActualPriorLift,
      ``contractionKeepsPriorSelectedReferencesAndReducesBaseReferences,
      ``aReferenceInsideTheDeletedIntervalHasNoSyntacticInverse,
      ``variablePositions, ``checkCutoffInverses, ``supportsStoredDomains, ``nativeModels,
      ``checkNativeBinding, ``checkRetainedBaseBindings, ``checkSupportFailures, ``runtimeFixtures,
      ``auditDeclaration, ``auditModule, ``auditProvenance, ``auditFoundations,
      ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveIndexDomainStrengthening (logical ++ [``sorryAx])
  auditModule `Lean4Lean.Verify.InductiveIndexBaseStrengthening inherited
  auditFoundations logical nativeInterfaces
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures
  logInfo "index-strengthening: stored chronological source support derives typed contraction with an aligned semantic endpoint, not a syntactic inverse; exhaustive module/helper audits, inherited/native provenance pins, forbidden range rejected even whitelisted"

end InductiveIndexBaseStrengtheningTest
