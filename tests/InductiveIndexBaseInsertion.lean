import Lean4Lean.Verify.InductiveIndexBaseInsertion
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexBaseInsertionTest

private theorem extensionKeepsInsertedAndOriginalBaseIdentifiers
    {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.vlctx.fvars = ids.reverse ++ initial.vlctx.fvars :=
  extension.virtualFVars

private theorem insertionTypesItsOwnTransportedModelAndUsesTheSelectedCutoff
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids : List FVarId} {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (largerWF : larger.WF env universes)
    (weakening : VLCtx.FVLift initial.vlctx larger.vlctx 0 inserted 0)
    (fresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ transported, SelectedRecursorTelescope env universes full larger ids transported ∧
      transported.WF env universes ∧
      VLCtx.FVLift' final.vlctx transported.vlctx 0 (.consN (.skipN .refl inserted) ids.length) 0 :=
  telescope.insertBase envWF initialWF largerWF weakening fresh

private theorem insertionExtensionDerivesOriginalWFWithoutAnotherPremise
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids insertedIds : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (insertion : IndexMLCtxExtension initial insertedIds larger)
    (largerWF : larger.WF env universes)
    (fresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ transported, SelectedRecursorTelescope env universes full larger ids transported ∧
      transported.WF env universes ∧ VLCtx.FVLift' final.vlctx transported.vlctx 0
        (.consN (.skipN .refl insertedIds.length) ids.length) 0 :=
  telescope.insertExtension envWF insertion largerWF fresh

private theorem returnedWeakeningTranslatesFinalExpressionsAtTheSelectedSuffixCutoff
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids : List FVarId} {inserted : Nat}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (largerWF : larger.WF env universes)
    (baseWeakening : VLCtx.FVLift initial.vlctx larger.vlctx 0 inserted 0)
    (fresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars)
    {source : Expr} {semantic : VExpr}
    (translated : TrExprS env universes final.vlctx source semantic) :
    ∃ transported, SelectedRecursorTelescope env universes full larger ids transported ∧
      transported.WF env universes ∧
      TrExprS env universes transported.vlctx source (semantic.liftN inserted ids.length) := by
  obtain ⟨transported, transportedTelescope, transportedWF, weakening⟩ :=
    telescope.insertBase envWF initialWF largerWF baseWeakening fresh
  refine ⟨transported, transportedTelescope, transportedWF, ?_⟩
  simpa only [Lift.consN, VExpr.lift'_consN_skipN] using
    translated.weakFV' envWF.ordered weakening transportedWF.tr.wf

private theorem insertedTelescopeKeepsOriginalBindingsButNotTheirPhysicalIndices
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final larger : MLCtx} {ids insertedIds : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (insertion : IndexMLCtxExtension initial insertedIds larger)
    (largerWF : larger.WF env universes)
    (fresh : ∀ identifier ∈ ids, identifier ∉ larger.vlctx.fvars) :
    ∃ transported : MLCtx, transported.WF env universes ∧
      SelectedCDeclBindingAgreement full transported.lctx ids := by
  obtain ⟨transported, transportedTelescope, transportedWF, _⟩ :=
    telescope.insertExtension envWF insertion largerWF fresh
  exact ⟨transported, transportedWF, transportedTelescope.bindingAgreement largerWF⟩

private theorem selectedIdentifierCollisionCannotSupplyTheFreshnessPremise
    (ids : List FVarId) (larger : MLCtx) (identifier : FVarId)
    (selected : identifier ∈ ids) (collision : identifier ∈ larger.vlctx.fvars) :
    ¬ (∀ selectedIdentifier ∈ ids, selectedIdentifier ∉ larger.vlctx.fvars) := by
  intro fresh
  exact fresh identifier selected collision

private theorem actualHistoryKeepsItsChronologicalModelAndOnlyInsertsBelowSelectedIndices
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
    {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (model : MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) (current : Context)
    (frame : finalReader.RecursorScopeFrame current) (envWF : env.WF)
    (larger : MLCtx) (largerWF : larger.WF env universes) (inserted : Nat)
    (baseWeakening : VLCtx.FVLift model.vlctx larger.vlctx 0 inserted 0)
    (freshBase : ∀ identifier, Expr.fvar identifier ∈ finalIndices.toList.drop indices.size →
      identifier ∉ larger.vlctx.fvars) :
    ∃ chronological ids transported,
      chronological.WF env universes ∧ chronological.lctx = finalReader.lctx ∧
      chronological.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids chronological ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx larger ids transported ∧
      transported.WF env universes ∧ VLCtx.FVLift' chronological.vlctx transported.vlctx 0
        (.consN (.skipN .refl inserted) ids.length) 0 :=
  history.selectedTelescopeInserted model modelWF native converted reserved current frame envWF
    larger largerWF inserted baseWeakening freshBase

private theorem originalIndexPrefixIsNotPartOfTheSelectedFreshnessCheck
    (prefixIndices : Array Expr) (ids : List FVarId) :
    (prefixIndices.toList ++ ids.map Expr.fvar).drop prefixIndices.size = ids.map Expr.fvar := by
  rw [← Array.length_toList, List.drop_left]

private theorem insertionPreservesPriorSelectedReferencesAndMovesOriginalBaseReferences :
    (VExpr.app (.bvar 0) (.bvar 2)).liftN 3 2 = .app (.bvar 0) (.bvar 5) ∧
      (VExpr.app (.bvar 0) (.bvar 2)).liftN 3 2 ≠ .app (.bvar 0) (.bvar 2) ∧
      (VExpr.app (.bvar 0) (.bvar 2)).liftN 3 2 ≠
        (VExpr.app (.bvar 0) (.bvar 2)).liftN 3 := by
  refine ⟨rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem nestedBinderCutoffsAdvanceWithoutMovingBoundOrSelectedReferences :
    (VExpr.forallE (.app (.bvar 0) (.bvar 2))
      (.lam (.bvar 3) (.app (.bvar 1) (.bvar 4)))).liftN 3 2 =
      .forallE (.app (.bvar 0) (.bvar 5)) (.lam (.bvar 6) (.app (.bvar 1) (.bvar 7))) := rfl

private theorem insertionWeakeningUsesTheSameCutoffSensitiveSemanticLift
    (expression : VExpr) (inserted selected : Nat) :
    expression.lift' (.consN (.skipN .refl inserted) selected) = expression.liftN inserted selected :=
  VExpr.lift'_consN_skipN

private def variablePositions : VExpr → List Nat
  | .bvar position => [position]
  | .sort _ | .const _ _ => []
  | .app function argument | .lam function argument | .forallE function argument =>
      variablePositions function ++ variablePositions argument

private def checkSemanticLifting : MetaM Unit := do
  for inserted in [1, 2, 5] do
    for earlier in [1, 2, 4] do
      let mixed := VExpr.app (.bvar 0) (.bvar earlier)
      let lifted := mixed.liftN inserted earlier
      unless variablePositions lifted == [0, earlier + inserted] &&
          variablePositions lifted != variablePositions mixed &&
          variablePositions lifted != variablePositions (mixed.liftN inserted) do
        throwError "index-base insertion used identity or uniform cutoff-zero lifting"
      let nested := VExpr.forallE (.app (.bvar 0) (.bvar earlier))
        (.lam (.bvar (earlier + 1)) (.app (.bvar 1) (.bvar (earlier + 2))))
      unless variablePositions (nested.liftN inserted earlier) ==
          [0, earlier + inserted, earlier + 1 + inserted, 1, earlier + 2 + inserted] do
        throwError "index-base insertion nested cutoff or application order changed"

private def insertNativeBase (base : MLCtx) (count : Nat) : MLCtx :=
  (List.range count).foldl (fun model position =>
    .vlam ⟨Name.num `BaseInserted position⟩ (Name.num `inserted position)
      (.const ``Nat []) (.const ``Nat []) .implicit model) base

private def selectedNativeModels (inserted : Nat) : MLCtx × MLCtx × List FVarId := Id.run do
  let carrier : FVarId := ⟨`BaseOriginalCarrier⟩
  let element : FVarId := ⟨`BaseOriginalElement⟩
  let first : FVarId := ⟨`BaseSelectedFirst⟩
  let second : FVarId := ⟨`BaseSelectedSecond⟩
  let base := MLCtx.vlet ⟨`BaseOriginalLet⟩ `oldLet (.const ``Nat []) (.lit (.natVal 0))
    (.const ``Nat []) (.const ``Nat.zero [])
    (.vlam element `element (.fvar carrier) (.bvar 0) .default
      (.vlam carrier `carrier (.sort (.succ .zero)) (.sort (.succ .zero)) .implicit .nil))
  let domain := mkApp3 (.const ``Eq [.succ .zero]) (.fvar carrier) (.fvar first) (.fvar first)
  let semantic := VExpr.app (.app (.app (.const ``Eq [.succ .zero]) (.bvar 2)) (.bvar 0)) (.bvar 0)
  let original := MLCtx.vlam second `witness domain semantic .instImplicit
    (.vlam first `first (.fvar carrier) (.bvar 1) .implicit base)
  let transported := MLCtx.vlam second `witness domain (semantic.liftN inserted 1) .instImplicit
    (.vlam first `first (.fvar carrier) ((VExpr.bvar 1).liftN inserted) .implicit
      (insertNativeBase base inserted))
  return (original, transported, [first, second])

private def checkNativeBinding (original transported : MLCtx) (identifier : FVarId)
    (inserted : Nat) : MetaM Unit := do
  let some (.cdecl oldIndex oldId oldName oldDomain oldBinder .default) := original.lctx.find? identifier
    | throwError "index-base insertion original selected native cdecl missing"
  let some (.cdecl newIndex newId newName newDomain newBinder .default) := transported.lctx.find? identifier
    | throwError "index-base insertion transported selected native cdecl missing"
  unless oldId == newId && oldName == newName && oldDomain == newDomain && oldBinder == newBinder &&
      newIndex == oldIndex + inserted && oldDomain.fvarsList == newDomain.fvarsList do
    throwError "index-base insertion changed selected IDs/domains/names/binders/dependencies or failed to shift physical indices"

private def checkOriginalBaseBindings (original transported : MLCtx) : MetaM Unit := do
  for identifier in [FVarId.mk `BaseOriginalCarrier, FVarId.mk `BaseOriginalElement,
      FVarId.mk `BaseOriginalLet] do
    let some prior := original.lctx.find? identifier
      | throwError "index-base insertion original base binding missing"
    let some retained := transported.lctx.find? identifier
      | throwError "index-base insertion removed an original base binding"
    unless prior.toExpr == retained.toExpr && prior.type == retained.type &&
        prior.value? == retained.value? && prior.index == retained.index do
      throwError "index-base insertion replaced or moved an original base binding"

private def runtimeFixtures : MetaM Unit := do
  checkSemanticLifting
  for inserted in [0, 1, 3] do
    let (original, transported, ids) := selectedNativeModels inserted
    for identifier in ids do checkNativeBinding original transported identifier inserted
    checkOriginalBaseBindings original transported
    unless transported.length == original.length + inserted do
      throwError "index-base insertion replaced or removed part of the original base"
    let expectedHead := [inserted + 2, 0, 0]
    match transported with
    | .vlam _ _ _ semantic _ (.vlam _ _ _ firstSemantic _ _) =>
      unless variablePositions semantic == expectedHead && variablePositions firstSemantic == [inserted + 1] do
        throwError "index-base insertion native model retained incorrect semantic domain references"
    | _ => throwError "index-base insertion chronological selected model shape changed"
  logInfo "index-base runtime: nine mixed-reference cutoff controls and nine nested-binder controls; three native insertion sizes including zero; six exact selected cdecl checks preserve native IDs/domains/names/binders/dependencies while physical indices shift; original base retained"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "index-base audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-base unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveIndexBaseInsertion
    | throwError "index-base bridge module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "index-base new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"index-base bridge: {declarations} declarations including private/generated helpers audited"

private def auditProvenance (name moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-base provenance module absent: {moduleName}"
  unless environment.getModuleIdxFor? name == some moduleIndex do
    throwError "index-base inherited provenance changed: {name} from {moduleName}"

private def auditFoundations (logical nativeInterfaces : List Name) : MetaM Unit := do
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.weakFV', `Lean4Lean.Verify.Typing.Lemmas)] do
    auditProvenance name moduleName
    unless (← collectAxioms name).contains ``sorryAx do
      throwError "index-base inherited admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  for name in nativeInterfaces do
    let some (.axiomInfo _) := (← getEnv).find? name
      | throwError "index-base native interface is not an existing axiom: {name}"
    auditProvenance name `Lean4Lean.Verify.Axioms
    auditDeclaration name (logical ++ [name])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "index-base forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"index-base unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let inherited := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``insertionTypesItsOwnTransportedModelAndUsesTheSelectedCutoff,
      ``insertionExtensionDerivesOriginalWFWithoutAnotherPremise,
      ``returnedWeakeningTranslatesFinalExpressionsAtTheSelectedSuffixCutoff,
      ``insertedTelescopeKeepsOriginalBindingsButNotTheirPhysicalIndices,
      ``actualHistoryKeepsItsChronologicalModelAndOnlyInsertsBelowSelectedIndices] do
    auditDeclaration name inherited
  for name in [``extensionKeepsInsertedAndOriginalBaseIdentifiers,
      ``selectedIdentifierCollisionCannotSupplyTheFreshnessPremise,
      ``originalIndexPrefixIsNotPartOfTheSelectedFreshnessCheck,
      ``insertionPreservesPriorSelectedReferencesAndMovesOriginalBaseReferences,
      ``nestedBinderCutoffsAdvanceWithoutMovingBoundOrSelectedReferences,
      ``insertionWeakeningUsesTheSameCutoffSensitiveSemanticLift,
      ``variablePositions, ``checkSemanticLifting, ``insertNativeBase, ``selectedNativeModels,
      ``checkNativeBinding, ``checkOriginalBaseBindings, ``runtimeFixtures, ``auditDeclaration, ``auditModule,
      ``auditProvenance, ``auditFoundations, ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule inherited
  auditFoundations logical nativeInterfaces
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures
  logInfo "index-base insertion: chronological selected telescope transport only; no contraction/removal/reordering or motive/minor typehood claim; exhaustive bridge and named fixture dependency audits; inherited/native origins pinned and forbidden range rejected even when whitelisted"

end InductiveIndexBaseInsertionTest
