import Lean4Lean.Verify.InductiveIndexDomainSupport
import Lean4Lean.Verify.InductiveIndexBinderOrder
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexDomainSupportTest

private theorem selectedOrderFindsTheOriginalMixedRolePositionWithoutADistinctnessPremise
    {steps : List BinderStep} {earlier suffix : List FVarId} {identifier : FVarId}
    (split : (BinderStep.indexValues steps).map Expr.fvarId! = earlier ++ identifier :: suffix) :
    ∃ position step,
      steps[position]? = some step ∧ step.role = .index ∧ step.value.fvarId! = identifier ∧
      (BinderStep.indexValues (steps.take position)).map Expr.fvarId! = earlier :=
  BinderStep.indexIds_split split

private theorem actualStoredTypesDeriveChronologicalSelectedDomainSupport
    {params base : List FVarId} {current : Context} {steps : List BinderStep}
    (receipt : BinderStoredIndexTypeFVarsIn params current steps) (parameters : params ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base ((BinderStep.indexValues steps).map Expr.fvarId!) :=
  receipt.selectedDomains parameters

private theorem rawReceiptNeedsItsActualDeclaredStoredTypes
    {params base : List FVarId} {current : Context} {steps : List BinderStep}
    (receipt : BinderRawDomainFVarsIn params steps)
    (declared : BinderStepsIndexDeclared current steps) (parameters : params ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base ((BinderStep.indexValues steps).map Expr.fvarId!) :=
  receipt.selectedDomains declared parameters

private theorem discardingAnInitialIndexPrefixRequiresRetainingItInTheSmallerBase
    {full : LocalContext} {base largerBase earlier selected : List FVarId}
    (support : SelectedRecursorDomainFVars full base (earlier ++ selected))
    (retained : earlier ⊆ largerBase) (baseRetained : base ⊆ largerBase) :
    SelectedRecursorDomainFVars full largerBase selected :=
  support.dropPrefix retained baseRetained

private theorem actualParentHeaderReceiptsDeriveSelectedDomainsWithoutAFreshSupportPremise
    {stats : InductiveStats} {types : Array InductiveType} {parent : Nat}
    {checkedRoot current : Context} {info : RecInfo} {base : List FVarId}
    (receipt : ParentBinderIntegrity stats types parent checkedRoot current info)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    SelectedRecursorDomainFVars current.lctx base (info.indices.toList.map Expr.fvarId!) :=
  receipt.selectedIndexDomains parameters

private theorem recursorHeaderReceiptsDeriveEveryInBoundsParentsSelectedDomains
    {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo} {base : List FVarId}
    (receipt : RecursorBinderIntegrity stats types checkedRoot current infos)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    ∀ parent, parent < types.size →
      SelectedRecursorDomainFVars current.lctx base (infos[parent]!.indices.toList.map Expr.fvarId!) :=
  receipt.selectedIndexDomains parameters

private theorem actualIndexHistoryDerivesItsOwnSuffixSupportFromStoredReceipts
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
    {params : List FVarId} {steps : List BinderStep}
    (stored : BinderStoredIndexTypeFVarsIn params current steps)
    (values : BinderStep.indexValues steps = finalIndices.toList)
    (parameters : params ⊆ smaller.vlctx.fvars)
    (prefixRetained : indices.toList.map Expr.fvarId! ⊆ smaller.vlctx.fvars) :
    ∃ chronological ids transported aligned,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx smaller ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' transported.vlctx aligned 0 (.consN baseLift ids.length) 0 ∧
      VLCtx.IsDefEq env universes.length chronological.vlctx aligned :=
  history.selectedTelescopeStrengthenedOfStoredDomains model modelWF native converted reserved current frame envWF
    smaller smallerWF baseLift baseWeakening stored values parameters prefixRetained

private def optionalDomain (carrier defaultValue : Expr) : Expr :=
  .app (.app (.const ``optParam [.succ .zero]) carrier) defaultValue

private def tagged : MData := { entries := [(`IndexDomainSupportTag, .ofNat 11)] }

private theorem discardedDefaultDependenciesNeedNotBelongToTheStoredTypeBase
    {parameter discarded : FVarId} (different : discarded ≠ parameter) :
    (peelTypeAnnotations (optionalDomain (.fvar parameter) (.fvar discarded))).FVarsIn
      (· ∈ [parameter]) ∧
      ¬ (optionalDomain (.fvar parameter) (.fvar discarded)).FVarsIn (· ∈ [parameter]) := by
  simp [optionalDomain, peelTypeAnnotations, FVarsIn, Level.hasMVar', different]

private theorem metadataBarriersRetainTheDefaultDependency
    {parameter discarded : FVarId} (different : discarded ≠ parameter) :
    ¬ (peelTypeAnnotations (.mdata tagged (optionalDomain (.fvar parameter) (.fvar discarded)))).FVarsIn
      (· ∈ [parameter]) := by
  simp [optionalDomain, peelTypeAnnotations, FVarsIn, Level.hasMVar', different]

private theorem missingBaseDependenciesCannotBeSuppliedBySelectedDomainSupport
    {full : LocalContext} {base : List FVarId} {identifier missing : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? identifier = some (.cdecl physicalIndex identifier name (.fvar missing) binder .default))
    (absent : missing ∉ base) (support : SelectedRecursorDomainFVars full base [identifier]) : False := by
  have supported := support [] identifier [] rfl physicalIndex name (.fvar missing) binder lookup
  exact absent (supported (by simp only [Expr.fvarsList, List.mem_singleton]))

private theorem currentSelectedIdentifiersCannotBeTheirOwnEarlierDependencies
    {full : LocalContext} {base : List FVarId} {identifier : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? identifier = some (.cdecl physicalIndex identifier name (.fvar identifier) binder .default))
    (absent : identifier ∉ base) (support : SelectedRecursorDomainFVars full base [identifier]) : False :=
  missingBaseDependenciesCannotBeSuppliedBySelectedDomainSupport lookup absent support

private theorem futureSelectedIdentifiersCannotSupportAnEarlierStoredDomain
    {full : LocalContext} {base : List FVarId} {first future : FVarId}
    {physicalIndex : Nat} {name : Name} {binder : BinderInfo}
    (lookup : full.find? first = some (.cdecl physicalIndex first name (.fvar future) binder .default))
    (absent : future ∉ base) (support : SelectedRecursorDomainFVars full base [first, future]) : False := by
  have supported := support [] first [future] rfl physicalIndex name (.fvar future) binder lookup
  exact absent (supported (by simp only [Expr.fvarsList, List.mem_singleton]))

private def mixedSteps (parameter first second discarded : FVarId) : List BinderStep := [
  { role := .parameter, name := `parameter, domain := .sort (.succ .zero), bi := .implicit,
    value := .fvar parameter },
  { role := .index, name := `first, domain := optionalDomain (.fvar parameter) (.fvar discarded),
    bi := .default, value := .fvar first },
  { role := .parameter, name := `reusedParameter, domain := .sort (.succ .zero), bi := .implicit,
    value := .fvar parameter },
  { role := .index, name := `second, domain := mkApp3 (.const ``Eq [.succ .zero])
      (.fvar parameter) (.fvar first) (.fvar first), bi := .instImplicit, value := .fvar second },
  { role := .parameter, name := `lateParameter, domain := .sort (.succ .zero), bi := .default,
    value := .fvar parameter }]

private theorem filteringInterleavedParameterRolesPreservesTheIndexOrder
    (parameter first second discarded : FVarId) :
    (BinderStep.indexValues (mixedSteps parameter first second discarded)).map Expr.fvarId! = [first, second] := rfl

private theorem anInterleavedIndexSplitRetainsItsWholeStepPosition
    (parameter first second discarded : FVarId) :
    ∃ position step,
      (mixedSteps parameter first second discarded)[position]? = some step ∧ step.role = .index ∧
      step.value.fvarId! = second ∧
      (BinderStep.indexValues ((mixedSteps parameter first second discarded).take position)).map Expr.fvarId! =
        [first] :=
  BinderStep.indexIds_split (rfl :
    (BinderStep.indexValues (mixedSteps parameter first second discarded)).map Expr.fvarId! =
      [first] ++ second :: [])

private theorem duplicateIndexIdentifiersStillHaveAStructuralFilteredPrefix
    (parameter identifier discarded : FVarId) :
    ∃ position step,
      (mixedSteps parameter identifier identifier discarded)[position]? = some step ∧
      step.role = .index ∧ step.value.fvarId! = identifier ∧
      (BinderStep.indexValues ((mixedSteps parameter identifier identifier discarded).take position)).map
        Expr.fvarId! = [identifier] :=
  BinderStep.indexIds_split (rfl :
    (BinderStep.indexValues (mixedSteps parameter identifier identifier discarded)).map Expr.fvarId! =
      [identifier] ++ identifier :: [])

private def storedSupport (full : LocalContext) (base ids : List FVarId) : Bool := Id.run do
  let mut earlier : List FVarId := []
  for identifier in ids do
    let some (.cdecl _ _ _ domain _ .default) := full.find? identifier | return false
    unless domain.fvarsList.all (fun dependency => (earlier ++ base).contains dependency) do return false
    earlier := earlier ++ [identifier]
  return true

private def nativeFixture (initial : Context) (shift : Nat) : Context × List BinderStep := Id.run do
  let parameter : FVarId := ⟨`DomainSupportParameter⟩
  let first : FVarId := ⟨`DomainSupportFirst⟩
  let second : FVarId := ⟨`DomainSupportSecond⟩
  let discarded : FVarId := ⟨`DomainSupportDiscarded⟩
  let steps := mixedSteps parameter first second discarded
  let base := initial.lctx.mkLocalDecl parameter `parameter (.sort (.succ .zero)) .implicit
    |>.mkLetDecl ⟨`DomainSupportRetainedLet⟩ `retainedLet (.const ``Nat []) (.lit (.natVal 4)) false
    |>.mkLocalDecl discarded `discardedDefault (.fvar parameter) .default
  let shifted := (List.range shift).foldl (fun context position => context.mkLocalDecl
    ⟨Name.num `DomainSupportPadding position⟩ `padding (.const ``Nat []) .default) base
  let firstDomain := optionalDomain (.fvar parameter) (.fvar discarded)
  let secondDomain := mkApp3 (.const ``Eq [.succ .zero]) (.fvar parameter) (.fvar first) (.fvar first)
  let full := shifted.mkLocalDecl first `first (peelTypeAnnotations firstDomain) .default
    |>.mkLocalDecl second `second secondDomain .instImplicit
  return ({ initial with lctx := full }, steps)

private def checkShiftedStoredBinding (original shifted : Context) (identifier : FVarId)
    (shift : Nat) : MetaM Unit := do
  let some (.cdecl oldIndex oldId oldName oldDomain oldBinder .default) := original.lctx.find? identifier
    | throwError "index-domain support original stored cdecl missing"
  let some (.cdecl newIndex newId newName newDomain newBinder .default) := shifted.lctx.find? identifier
    | throwError "index-domain support shifted stored cdecl missing"
  unless oldId == newId && oldName == newName && oldDomain == newDomain && oldBinder == newBinder &&
      newIndex == oldIndex + shift do
    throwError "index-domain support changed retained selected-cdecl provenance"

private def checkMixedRoleFixture (initial : Context) : MetaM Unit := do
  let parameter : FVarId := ⟨`DomainSupportParameter⟩
  let discarded : FVarId := ⟨`DomainSupportDiscarded⟩
  let (original, _) := nativeFixture initial 0
  for shift in [0, 1, 3] do
    let (current, steps) := nativeFixture initial shift
    let ids := (BinderStep.indexValues steps).map Expr.fvarId!
    let some firstStep := steps[1]? | throwError "index-domain support first annotated step missing"
    unless ids == [⟨`DomainSupportFirst⟩, ⟨`DomainSupportSecond⟩] &&
        storedSupport current.lctx [parameter] ids do
      throwError "index-domain support lost mixed-role chronological order or stored support"
    unless !firstStep.domain.fvarsList.all (fun identifier => [parameter].contains identifier) &&
        !(peelTypeAnnotations (.mdata tagged firstStep.domain)).fvarsList.all
          (fun identifier => [parameter].contains identifier) &&
        (peelTypeAnnotations firstStep.domain).fvarsList == [parameter] &&
        firstStep.domain.fvarsList.contains discarded do
      throwError "index-domain support collapsed raw, peeled, and metadata-barrier dependency boundaries"
    for identifier in ids do checkShiftedStoredBinding original current identifier shift
    let duplicateSteps := steps.take 2 ++ [firstStep] ++ steps.drop 2
    let duplicateIds := (BinderStep.indexValues duplicateSteps).map Expr.fvarId!
    unless duplicateIds == [⟨`DomainSupportFirst⟩, ⟨`DomainSupportFirst⟩, ⟨`DomainSupportSecond⟩] &&
        storedSupport current.lctx [parameter] duplicateIds do
      throwError "index-domain support introduced an unjustified structural distinctness requirement"

private def checkMissingDependencyControls (initial : Context) : MetaM Unit := do
  let parameter : FVarId := ⟨`MissingParameter⟩
  let first : FVarId := ⟨`MissingFirst⟩
  let future : FVarId := ⟨`MissingFuture⟩
  let omitted : FVarId := ⟨`MissingOmitted⟩
  let base := initial.lctx.mkLocalDecl parameter `parameter (.sort (.succ .zero)) .implicit
    |>.mkLocalDecl omitted `omitted (.fvar parameter) .default
  for (dependency, retained) in [(parameter, []), (omitted, [parameter]),
      (first, [parameter]), (future, [parameter])] do
    let full := base.mkLocalDecl first `first (.fvar dependency) .default
      |>.mkLocalDecl future `future (.fvar parameter) .default
    unless !storedSupport full retained [first, future] do
      throwError "index-domain support accepted a missing parameter/omitted/current/future dependency"

private def checkInitialPrefixRetention (initial : Context) : MetaM Unit := do
  let parameter : FVarId := ⟨`PrefixParameter⟩
  let earlier : FVarId := ⟨`PrefixEarlier⟩
  let selected : FVarId := ⟨`PrefixSelected⟩
  let full := initial.lctx.mkLocalDecl parameter `parameter (.sort (.succ .zero)) .implicit
    |>.mkLocalDecl earlier `earlier (.fvar parameter) .default
    |>.mkLocalDecl selected `selected (.fvar earlier) .default
  unless storedSupport full [parameter] [earlier, selected] &&
      storedSupport full [earlier, parameter] [selected] &&
      !storedSupport full [parameter] [selected] do
    throwError "index-domain support dropped an initial-prefix dependency instead of retaining it in the base"

private def runtimeFixtures : MetaM Unit := do
  let initial : Context := {
    env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  checkMixedRoleFixture initial
  checkMissingDependencyControls initial
  checkInitialPrefixRetention initial
  logInfo "index-domain support runtime: three mixed-role annotated/stored/default-boundary controls; six shifted selected-cdecl checks; three duplicate-ID structural controls; four missing parameter/omitted/current/future rejections; initial-prefix retention positive and negative controls; native/source controls do not supply independent semantic typing"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "index-domain support audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-domain support unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-domain support audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index-domain support new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditProvenance (name moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-domain support provenance module absent: {moduleName}"
  unless environment.getModuleIdxFor? name == some moduleIndex do
    throwError "index-domain support inherited provenance changed: {name} from {moduleName}"

private def auditInheritedFoundations (logical nativeInterfaces : List Name) : MetaM Unit := do
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.weakFV'_inv, `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.uniq, `Lean4Lean.Verify.Typing.Lemmas),
      (``VEnv.HasType.weak'_iff, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    auditProvenance name moduleName
    unless (← collectAxioms name).contains ``sorryAx do
      throwError "index-domain support inherited admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  for name in nativeInterfaces do
    let some (.axiomInfo _) := (← getEnv).find? name
      | throwError "index-domain support native interface is not an existing axiom: {name}"
    auditProvenance name `Lean4Lean.Verify.Axioms
    auditDeclaration name (logical ++ [name])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "index-domain support forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"index-domain support unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let inherited := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``actualIndexHistoryDerivesItsOwnSuffixSupportFromStoredReceipts inherited
  for name in [``selectedOrderFindsTheOriginalMixedRolePositionWithoutADistinctnessPremise,
      ``actualStoredTypesDeriveChronologicalSelectedDomainSupport,
      ``rawReceiptNeedsItsActualDeclaredStoredTypes,
      ``discardingAnInitialIndexPrefixRequiresRetainingItInTheSmallerBase,
      ``actualParentHeaderReceiptsDeriveSelectedDomainsWithoutAFreshSupportPremise,
      ``recursorHeaderReceiptsDeriveEveryInBoundsParentsSelectedDomains,
      ``optionalDomain, ``tagged, ``discardedDefaultDependenciesNeedNotBelongToTheStoredTypeBase,
      ``metadataBarriersRetainTheDefaultDependency,
      ``missingBaseDependenciesCannotBeSuppliedBySelectedDomainSupport,
      ``currentSelectedIdentifiersCannotBeTheirOwnEarlierDependencies,
      ``futureSelectedIdentifiersCannotSupportAnEarlierStoredDomain,
      ``mixedSteps, ``filteringInterleavedParameterRolesPreservesTheIndexOrder,
      ``anInterleavedIndexSplitRetainsItsWholeStepPosition,
      ``duplicateIndexIdentifiersStillHaveAStructuralFilteredPrefix,
      ``storedSupport, ``nativeFixture, ``checkShiftedStoredBinding, ``checkMixedRoleFixture,
      ``checkMissingDependencyControls, ``checkInitialPrefixRetention, ``runtimeFixtures,
      ``auditDeclaration, ``auditModule, ``auditProvenance, ``auditInheritedFoundations,
      ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveIndexBinderOrder [``propext]
  auditModule `Lean4Lean.Verify.InductiveIndexDomainSupport inherited
  auditInheritedFoundations logical nativeInterfaces
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures
  logInfo "index-domain support: actual stored/raw/parent/header receipts derive selected-source support; the actual-history adapter derives retained-prefix suffix support internally; aligned semantic contraction stays conditional on the supplied smaller typed base"

end InductiveIndexDomainSupportTest
