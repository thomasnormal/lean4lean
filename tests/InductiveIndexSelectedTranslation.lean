import Lean4Lean.Verify.InductiveIndexSelectedTranslation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexSelectedTranslationTest

private theorem chronologicalExtensionSuppliesItsOwnSelectedDomains
    {env : VEnv} {universes : List Name} {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) (finalWF : final.WF env universes) :
    SelectedRecursorTelescope env universes final.lctx initial ids final :=
  extension.selectedTelescope finalWF

private theorem lookupTransportDoesNotReplaceTheChronologicalModel
    {env : VEnv} {universes : List Name} {left right : LocalContext}
    {initial final : MLCtx} {ids : List FVarId}
    (telescope : SelectedRecursorTelescope env universes left initial ids final)
    (lookups : ∀ identifier ∈ ids, left.find? identifier = right.find? identifier) :
    SelectedRecursorTelescope env universes right initial ids final :=
  telescope.monoFull lookups

section History
variable {env : VEnv} {universes : List Name} {stats : InductiveStats}
  {source terminal : Expr} {index finalIndex : Nat} {indices finalIndices : Array Expr}
  {reader finalReader : Context} {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
  {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
  (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
  (model : MLCtx) (modelWF : model.WF env universes)
  (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
  (reserved : ContextReserved reader.lctx reader.ngen)

include history modelWF native converted reserved

private theorem sameHistoryDerivesSelectedSuffixWithoutIndependentFinalWF :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes finalReader.lctx model ids finalModel :=
  history.selectedTelescope model modelWF native converted reserved

private theorem laterNativeReaderDoesNotBecomeAnIndependentFinalModel
    (current : Context) (frame : finalReader.RecursorScopeFrame current) :
    ∃ finalModel ids,
      finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      finalIndices.toList = indices.toList ++ ids.map Expr.fvar ∧
      SelectedRecursorTelescope env universes current.lctx model ids finalModel :=
  history.selectedTelescopeAt model modelWF native converted reserved current frame

end History

private theorem selectedDomainsRetainExactOriginalNativeBindings
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final : MLCtx} {ids : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) :
    final.WF env universes ∧ SelectedCDeclBindingAgreement full final.lctx ids :=
  ⟨telescope.context initialWF, telescope.bindingAgreement initialWF⟩

private theorem chronologicalSuffixDoesNotSelectPreexistingPrefixLocals
    {initial final : MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.dropN ids.length extension.bound = initial ∧
      final.fvarRevList ids.length extension.bound = ids.reverse :=
  ⟨extension.drop_eq, extension.selection⟩

private theorem virtualDependenciesUseTheStoredDomainNotTheDiscardedDefault
    (identifier : FVarId) (name : Name) (domain : Expr) (semantic : VExpr)
    (binder : BinderInfo) (base : MLCtx) :
    (MLCtx.vlam identifier name domain semantic binder base).vlctx =
      (some (identifier, domain.fvarsList), .vlam semantic) :: base.vlctx := rfl

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def dependentTwo : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private def dependentThree : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``semiOutParam (.bvar 0))
    (.forallE `witness
      (.app (.app (.const ``optParam [.zero])
        (mkApp3 (.const ``Eq [.succ .zero]) (.bvar 1) (.bvar 0) (.bvar 0)))
        (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 1) (.bvar 0)))
      (.sort (.succ .zero)) .instImplicit) .implicit) .default

private def indexedTwo : Expr := .forallE `ordinal (.const ``Nat [])
  (.forallE `witness (mkApp3 (.const ``Eq [.zero]) (.const ``Nat []) (.bvar 0) (.bvar 0))
    (.sort (.succ .zero)) .default) .implicit

private def capture (source : Expr) (prefixIndices : Array Expr) : M (Array Expr × Context) :=
  mkRecInfos.loopArgs1 {
    params := #[], levels := [], resultLevel := .succ .zero
    indConsts := #[], isNotZero := true } source 0 prefixIndices 16 fun values => do
      return (values, ← read)

private def checkStoredSuffix (original current : Context) (source : Expr)
    (values : Array Expr) (prefixSize : Nat) : MetaM Unit := do
  let mut opened := source
  let mut generator := original.ngen
  for offset in [:values.size - prefixSize] do
    let .forallE name domain body binder := opened
      | throwError "index-selected source telescope exhausted early"
    let value := values[prefixSize + offset]!
    let some declaration := current.lctx.find? value.fvarId!
      | throwError "index-selected actual native declaration missing"
    let .cdecl physicalIndex identifier storedName storedDomain storedBinder .default := declaration
      | throwError "index-selected actual default-kind cdecl missing"
    unless value == .fvar ⟨generator.curr⟩ && identifier == value.fvarId! && storedName == name &&
        storedDomain == peelTypeAnnotations domain && storedBinder == binder &&
        physicalIndex == original.lctx.decls.size + offset do
      throwError "index-selected chronological ID/domain/name/binder/index mismatch"
    unless declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "index-selected stored dependencies include discarded annotation payload"
    opened := body.instantiate1 value
    generator := generator.next
  unless opened == .sort (.succ .zero) && current.ngen.curr == generator.curr do
    throwError "index-selected source terminal or final generator mismatch"

private def checkSuffix (reader : Context) (source : Expr) (count : Nat)
    (prefixIndices : Array Expr) : MetaM Unit := do
  let .ok (values, current) := capture source prefixIndices reader
    | throwError "index-selected actual loopArgs1 failed"
  unless values.size == prefixIndices.size + count && current.lctx.decls.size == reader.lctx.decls.size + count do
    throwError "index-selected chronological suffix count mismatch"
  for position in [:prefixIndices.size] do
    unless values[position]! == prefixIndices[position]! do
      throwError "index-selected preexisting index prefix changed"
  checkStoredSuffix reader current source values prefixIndices.size
  for position in [:reader.lctx.decls.size] do
    if let some prior := reader.lctx.getAt? position then
      let some retained := current.lctx.find? prior.fvarId
        | throwError "index-selected initial local missing"
      unless retained.toExpr == prior.toExpr && retained.type == prior.type &&
          retained.value? == prior.value? && retained.index == prior.index do
        throwError "index-selected preexisting local or let changed"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier : FVarId := ⟨`SelectedIndexCarrier⟩
  let element : FVarId := ⟨`SelectedIndexElement⟩
  let defaultValue : FVarId := ⟨`SelectedIndexDefault⟩
  let seeded := { reader with
    ngen := { namePrefix := `SelectedIndexSeed, idx := 71 }
    lctx := reader.lctx.mkLocalDecl carrier `carrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `element (.fvar carrier) .default
      |>.mkLetDecl defaultValue `defaultValue (.const ``Nat []) (.lit (.natVal 11)) false }
  let defaultDomain := .app (.app (.const ``optParam [.zero]) (.const ``Nat [])) (.fvar defaultValue)
  unless defaultDomain.fvarsList == [defaultValue] && (peelTypeAnnotations defaultDomain).fvarsList == [] do
    throwError "index-selected discarded default control does not separate raw and stored dependencies"
  let discardedDefault := .forallE `ordinal defaultDomain (.sort (.succ .zero)) .implicit
  for prefixIndices in [#[], #[Expr.fvar element], #[Expr.fvar carrier, Expr.fvar element],
      #[Expr.fvar element, Expr.fvar element]] do
    for (source, count) in [(dependentTwo, 2), (dependentThree, 3), (indexedTwo, 2),
        (discardedDefault, 1), (Expr.sort (.succ .zero), 0)] do
      checkSuffix seeded source count prefixIndices
  logInfo "index-selected runtime: twenty native chronological captures; thirty-two fresh cdecls; nonempty/duplicate index prefixes and seeded local/let base preserved; dependent/indexed domains, outParam/semiOutParam/optParam peeling and discarded default payload; native controls are not full recursor-domain typing"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name
    | throwError "index-selected audited declaration absent: {name}"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-selected unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-selected audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "index-selected new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditProvenance (name moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-selected provenance module absent: {moduleName}"
  unless environment.getModuleIdxFor? name == some moduleIndex do
    throwError "index-selected inherited provenance changed: {name} from {moduleName}"

private def auditFoundations (logical nativeInterfaces : List Name) : MetaM Unit := do
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas),
      (``TranslatedRecursorIndexTrace.mixedContext, `Lean4Lean.Verify.InductiveMotiveBindingFacts)] do
    auditProvenance name moduleName
    unless (← collectAxioms name).contains ``sorryAx do
      throwError "index-selected inherited admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
  for name in nativeInterfaces do
    let some (.axiomInfo _) := (← getEnv).find? name
      | throwError "index-selected native interface is not an existing axiom: {name}"
    auditProvenance name `Lean4Lean.Verify.Axioms
    auditDeclaration name (logical ++ [name])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "index-selected forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"index-selected unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let inherited := logical ++ [``sorryAx] ++ nativeInterfaces
  auditDeclaration ``SelectedRecursorTelescope.monoFull (logical ++ [``sorryAx])
  auditDeclaration ``lookupTransportDoesNotReplaceTheChronologicalModel (logical ++ [``sorryAx])
  for name in [``chronologicalExtensionSuppliesItsOwnSelectedDomains,
      ``sameHistoryDerivesSelectedSuffixWithoutIndependentFinalWF,
      ``laterNativeReaderDoesNotBecomeAnIndependentFinalModel,
      ``selectedDomainsRetainExactOriginalNativeBindings] do
    auditDeclaration name inherited
  for name in [``chronologicalSuffixDoesNotSelectPreexistingPrefixLocals,
      ``virtualDependenciesUseTheStoredDomainNotTheDiscardedDefault,
      ``unary, ``dependentTwo, ``dependentThree, ``indexedTwo, ``capture,
      ``checkStoredSuffix, ``checkSuffix, ``runtimeFixtures, ``auditDeclaration,
      ``auditModule, ``auditProvenance, ``auditFoundations, ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveIndexSelectedTranslation inherited
  auditFoundations logical nativeInterfaces
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures { env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  logInfo "index-selected: seven proof controls; complete bridge module and fixture helper dependency audits; three inherited foundations and three native interfaces pinned; forbidden range rejected even when whitelisted; chronological index block is not full sparse/reordered recursor domain support"

end InductiveIndexSelectedTranslationTest
