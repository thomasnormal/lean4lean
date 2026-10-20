import Lean4Lean.Verify.InductiveIndexDomainCorrespondence
import Lean.Util.CollectAxioms

namespace InductiveIndexReconstructionTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

private def natural : Expr := .const ``Nat []
private def sortType : Expr := .sort (.succ .zero)
private def delay (body : Expr) (mode : Nat) : Expr :=
  if mode == 1 then .letE `delay sortType natural (body.liftLooseBVars 0 1) false
  else if mode == 2 then .app (.lam `delay sortType (body.liftLooseBVars 0 1) .default) natural
  else if mode == 3 then .mdata {} body
  else body

private def source (mode : Nat) (annotated : Bool) : Expr :=
  let witness := mkApp3 (.const ``Eq [.succ .zero]) (.bvar 1) (.bvar 0) (.bvar 0)
  let witness := if annotated then mkApp2 (.const ``optParam [.zero]) witness
    (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 1) (.bvar 0)) else witness
  let element := if annotated then .app (.const ``outParam [.succ .zero]) (.bvar 0) else .bvar 0
  .forallE `carrier sortType
    (delay (.forallE `element element
      (delay (.forallE `witness witness sortType .instImplicit) mode) .implicit) mode) .default

/-- Actual annotation peeling changes a source domain structurally. -/
private theorem annotationsChangeDomain :
    (Expr.app (.const ``outParam [.succ .zero]) (.bvar 0)) ≠
      peelTypeAnnotations (.app (.const ``outParam [.succ .zero]) (.bvar 0)) := by
  intro equality
  cases equality

/-- Two dependent domains remain matched after changing the first index. -/
private theorem changedDependentPrefix (family motive : Expr) :
    NativeTelescopePrefix
      (.forallE `A sortType (.forallE `x (.bvar 0) family .implicit) .default)
      (.forallE `B sortType (.forallE `y (.bvar 0) motive .instImplicit) .strictImplicit) 2 :=
  .cons (.cons .nil)

private theorem changedDependentDomains (family motive : Expr) :
    ∃ leftEnd rightEnd, NativeTelescopeDomains
      (.forallE `A sortType (.forallE `x (.bvar 0) family .implicit) .default)
      (.forallE `B sortType (.forallE `y (.bvar 0) motive .instImplicit) .strictImplicit)
      [natural, .const ``Nat.zero []] leftEnd rightEnd :=
  (changedDependentPrefix family motive).domains _ rfl

private theorem unequalDomainsRejected :
    ¬ NativeTelescopePrefix (.forallE `A sortType sortType .default)
      (.forallE `A (.sort .zero) sortType .default) 1 := by
  intro shared
  cases shared

private def compareDomains (left right : Expr) (arguments : Array Expr) (reader : Context) :
    MetaM (Expr × Expr) := do
  let mut left := left
  let mut right := right
  for argument in arguments do
    let .forallE _ leftDomain leftBody _ := left | throwError "source exhausted before actual index arity"
    let .forallE _ rightDomain rightBody _ := right | throwError "target exhausted before actual index arity"
    unless leftDomain == rightDomain do throwError "actual substituted index domains differ"
    for domain in [leftDomain, rightDomain] do
      let .ok inferred := (monadLift (TypeChecker.checkType argument) : M Expr) reader
        | throwError "changed index failed genuine typing"
      unless ((monadLift (TypeChecker.isDefEq inferred domain) : M Bool) reader).toOption == some true do
        throwError "changed index failed dependent-domain checking"
    left := leftBody.instantiate1 argument
    right := rightBody.instantiate1 argument
  return (left, right)

private def openingChanges (source : Expr) (indices : Array Expr) (reader : Context) :
    MetaM (Nat × Nat) := do
  let mut current := source
  let mut normalized := 0
  let mut peeled := 0
  for index in indices do
    let .forallE _ domain body _ := current | throwError "normalization census exhausted source"
    let some declaration := reader.lctx.find? index.fvarId! | throwError "actual index declaration missing"
    unless declaration.type == peelTypeAnnotations domain do
      throwError "actual stored domain differs from peeled source"
    peeled := peeled + if domain == declaration.type then 0 else 1
    let opened := body.instantiate1 index
    let .ok next := (monadLift (TypeChecker.whnf opened) : M Expr) reader
      | throwError "actual opened body normalization failed"
    normalized := normalized + if opened == next then 0 else 1
    current := next
  unless current == sortType do throwError "normalized source terminal changed"
  return (normalized, peeled)

private def runtime : MetaM Unit := do
  let host ← getEnv
  let mut count := 0
  let mut normalized := 0
  let mut peeled := 0
  let mut rejected := 0
  for mode in [:4] do
    for annotated in [false, true] do
      let name := (`IndexReconstruction).appendIndexAfter (mode * 2 + if annotated then 1 else 0)
      let type : InductiveType := { name, type := source mode annotated, ctors := [] }
      for isUnsafe in [false, true] do
        unless (host.addDeclCore 0 (.inductDecl [] 0 [type] isUnsafe) none).isOk do
          throwError "native kernel rejected source reconstruction fixture {name}"
        for primitive in [false, true] do
          let original : Context := {
            env := host.toKernelEnv, lparams := [],
            safety := if isUnsafe then .unsafe else .safe, allowPrimitive := primitive }
          let .ok (stats, base, headers) := checkInductiveTypes 0 #[type] (fun stats => do
              let base ← readThe Context
              let headers ← declareInductiveTypes stats 0 #[type] 0 isUnsafe
              return (stats, base, headers)) original
            | throwError "checked source/header registration failed"
          let .ok complete := run 0 [type] 0 original | throwError "complete inductive run failed"
          for environment in [headers, complete] do
            let base := { base with env := environment }
            let localReader := recursorIndexContext base `extra .default natural
            let saved : Context := { localReader with
              ngen := localReader.ngen.next
              lctx := localReader.lctx.mkLetDecl ⟨localReader.ngen.curr⟩ `saved natural (.const ``Nat.zero []) }
            for reader in [base, localReader, saved] do
              for elimination in [Level.zero, .param `elimination] do
                let reader := { reader with lparams := getRecLevelParams elimination [] }
                let .ok (indices, indexReader) := mkRecInfos.loopArgs1 stats type.type 0 #[]
                    reader.fuel.inductiveFuel (fun indices => do return (indices, ← readThe Context)) reader
                  | throwError "actual checked index-opening loop failed"
                unless indices.size == 3 do throwError "dependent index arity changed"
                let (normalizationChanges, annotationChanges) ← openingChanges type.type indices indexReader
                let reconstructed := indexReader.lctx.mkForall indices sortType
                for expression in [type.type, reconstructed] do
                  unless ((monadLift (TypeChecker.checkType expression) : M Expr) reader).isOk do
                    throwError "source or reconstructed telescope failed genuine checking"
                unless ((monadLift (TypeChecker.isDefEq type.type reconstructed) : M Bool) reader).toOption == some true do
                  throwError "reconstructed signature is not definitionally equal to original source"
                let .ok (infos, full) := mkRecInfos stats #[type] elimination
                    (fun infos => do return (infos, ← readThe Context)) reader
                  | throwError "actual recursor info generation failed"
                let info := infos[0]!
                unless info.indices == indices do throwError "actual generator selected different index identifiers"
                let tail := full.lctx.mkForall #[info.major] (recursorTypeBody infos 0)
                let target := full.lctx.mkForall info.indices tail
                let expectedRaw := full.lctx.mkForall (infos.map (·.motive)) target
                unless expectedRaw == recursorRawType stats infos 0 full.lctx do
                  throwError "target does not reconstruct actual raw recursor type"
                let changed := #[natural, .const ``Nat.zero [], mkApp2 (.const ``Eq.refl [.succ .zero]) natural (.const ``Nat.zero [])]
                let (sourceEnd, targetEnd) ← compareDomains reconstructed target changed full
                unless sourceEnd == sortType do throwError "reconstructed sort tail changed after actual substitution"
                let family := mkAppN stats.indConsts[0]! changed
                let expectedTail := Expr.forallE `t family
                  (.app ((mkAppN info.motive changed).liftLooseBVars 0 1) (.bvar 0)) .default
                unless targetEnd == expectedTail do throwError "actual canonical major/motive tail failed changed-index substitution"
                let wrong := mkAppN stats.indConsts[0]! #[natural, .sort .zero, changed[2]!]
                if ((monadLift (TypeChecker.checkType wrong) : M Expr) full).isOk then
                  throwError "wrong dependent index accepted"
                count := count + 1
                normalized := normalized + normalizationChanges
                peeled := peeled + annotationChanges
                rejected := rejected + 1
  unless normalized > 0 && peeled > 0 do throwError "missing normalization or annotation coverage"
  logInfo m!"index reconstruction: {count} actual source/recursor telescopes; {normalized} normalized body edges; {peeled} peeled dependent domains; changed indices yield exact canonical major/motive tail; {rejected} malformed dependent applications rejected"

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "index reconstruction: manifest changed for {name}: {repr actual}"

private def audit : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let structural := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let nativeBinding := logical ++ [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let semantic := structural ++ [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  for (name, expected) in [
      (``IndexMLCtxExtension.mkForall'_outer, [``propext, ``Quot.sound]),
      (``TranslatedRecursorIndexTrace.reconstructedModel, structural),
      (``FamilyIndexInput.reconstruct, semantic),
      (``NativeTelescopePrefix.domains, [``propext]),
      (``mkForall_selected_prefix, nativeBinding), (``mkForall_selected_domains, nativeBinding),
      (``UArgModelEndpoint.indexArgumentsFromSelectedTrace, semantic),
      (``changedDependentPrefix, []),
      (``changedDependentDomains, [``propext]), (``unequalDomainsRejected, [])] do
    exactAxioms name expected
  let mut pending := #[``annotationsChangeDomain, ``changedDependentPrefix,
    ``changedDependentDomains, ``unequalDomainsRejected]
  let mut count := 0
  for moduleName in #[`Lean4Lean.Verify.InductiveIndexReconstruction,
      `Lean4Lean.Verify.InductiveIndexDomainCorrespondence] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "audited module absent"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "owned direct admission {name}"
        let actual ← collectAxioms name
        for dependency in actual do
          unless semantic.contains dependency do throwError "unexpected interface {dependency} in {name}"
        pending := pending.push name
        count := count + 1
  unless count > 0 do throwError "empty owned audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do throwError "forbidden audit root absent {name}"
  let mut visited : NameSet := {}
  let mut admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden dependency {name}"
    let some information := environment.find? name | throwError "dependency absent {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then admissions := admissions.push name
      pending := pending ++ proof.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => throwError "missing proof body {name}"
      | _ => pure ()
  unless pending.isEmpty do throwError "dependency traversal exceeded bound"
  let expected := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq, ``TrProj.wf]
  unless admissions.size == expected.length && expected.all admissions.contains do
    throwError "inherited direct roots changed {repr admissions}"
  for name in [``TranslatedRecursorIndexTrace.reconstructedModel, ``FamilyIndexInput.reconstruct,
      ``UArgModelEndpoint.indexArgumentsFromSelectedTrace] do
    let mut rejected := false
    try exactAxioms name logical
    catch exception =>
      let message ← exception.toMessageData.toString
      unless message.startsWith "index reconstruction: manifest changed" do throw exception
      rejected := true
    unless rejected do throwError "logical-only negative audit accepted inherited admissions"
  for name in [``source, ``delay, ``runtime, ``compareDomains, ``openingChanges, ``annotationsChangeDomain] do
    for dependency in (← collectAxioms name) do
      unless logical.contains dependency do throwError "runtime depends on semantic interface {dependency}"
  logInfo m!"index reconstruction: {count} owned declarations; exact 7/11-axiom semantic manifests and five inherited projection roots; full proof/opaque traversal excludes known-false strengthening/confluence; logical-only negative audits rejected"

run_meta
  audit
  runtime

end InductiveIndexReconstructionTest
