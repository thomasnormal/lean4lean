import Lean4Lean.Verify.Environment.Primitive.Recursion
import Lean.Util.CollectAxioms

namespace UnusedNatTranslationTest
open Lean Lean4Lean Lean4Lean.TypeChecker

abbrev baseId : FVarId := ⟨`base⟩
abbrev firstId : FVarId := ⟨`first⟩
abbrev secondId : FVarId := ⟨`second⟩
abbrev base : VLCtx := [(some (baseId, []), .vlam (.sort .zero))]
abbrev extended : VLCtx := (some (firstId, []), .vlam (.sort (.succ (.succ .zero)))) :: base

theorem closesBaseVariable : TrExprS VEnv.empty [] base (.fvar baseId) (.bvar 0) := by
  have witness : TrExprS VEnv.empty [] base (.sort (.succ .zero)) (.sort (.succ .zero)) := .sort rfl
  have source : TrExprS VEnv.empty [] extended (.fvar baseId) (.bvar 1) := .fvar rfl
  have result := TrExprS.close_unused_fvar .empty witness (.sort trivial) .zero .zero source
    trivial (by change baseId ≠ firstId; simp [baseId, firstId])
  exact result

-- The retained domain is the base proposition, lifted across the removed binder.
theorem closesUnderDependentBinder :
    TrExprS VEnv.empty [] ((none, .vlam (.bvar 0)) :: base) (.bvar 0) (.bvar 0) := by
  have witness : TrExprS VEnv.empty [] base (.sort (.succ .zero)) (.sort (.succ .zero)) := .sort rfl
  have source : TrExprS VEnv.empty [] ((none, .vlam (.bvar 1)) :: extended)
      (.bvar 0) (.bvar 0) := .bvar rfl
  exact TrExprS.close_unused_fvar .empty witness (.sort trivial) (.succ .zero) (.succ .zero)
    source (by change 0 < 1; decide) trivial

theorem closesUnderTwoBinders :
    TrExprS VEnv.empty [] ((none, .vlam (.sort .zero)) :: (none, .vlam (.sort .zero)) :: base)
      (.bvar 1) (.bvar 1) := by
  have witness : TrExprS VEnv.empty [] base (.sort (.succ .zero)) (.sort (.succ .zero)) := .sort rfl
  have source : TrExprS VEnv.empty []
      ((none, .vlam (.sort .zero)) :: (none, .vlam (.sort .zero)) :: extended)
      (.bvar 1) (.bvar 1) := .bvar rfl
  exact TrExprS.close_unused_fvar .empty witness (.sort trivial)
    (.succ (.succ .zero)) (.succ (.succ .zero)) source (by change 1 < 2; decide) trivial

abbrev baseModel : MLCtx := .vlam baseId `p (.sort .zero) (.sort .zero) .default .nil
abbrev firstModel : MLCtx := .vlam firstId `first (.const ``Nat []) .nat .default baseModel
abbrev secondModel : MLCtx := .vlam secondId `second (.const ``Nat []) .nat .default firstModel

section
variable {environment : VEnv} (ordered : environment.Ordered)
  (primitives : environment.HasPrimitives) (natPresent : environment.contains ``Nat)
include ordered primitives natPresent

theorem modelWF : secondModel.WF environment [] := by
  have nilWF : MLCtx.WF environment [] .nil := trivial
  have baseWF : baseModel.WF environment [] :=
    ⟨nilWF, nilWF.tr.find?_eq_none.2 (by simp [MLCtx.vlctx, VLCtx.fvars]),
      .sort rfl, _, .sort trivial⟩
  have firstWF : firstModel.WF environment [] :=
    ⟨baseWF, baseWF.tr.find?_eq_none.2 (by simp [MLCtx.vlctx, VLCtx.fvars, baseId, firstId]),
      primitives.trNat ordered natPresent,
      primitives.natIsType ordered natPresent baseWF.tr.wf.toCtx⟩
  exact ⟨firstWF, firstWF.tr.find?_eq_none.2 (by
      simp [MLCtx.vlctx, VLCtx.fvars, baseId, firstId, secondId]),
    primitives.trNat ordered natPresent,
    primitives.natIsType ordered natPresent firstWF.tr.wf.toCtx⟩

theorem closesTwoNatBinders :
    ∃ result, TrExprS environment [] baseModel.vlctx (.fvar baseId) result := by
  have source : TrExprS environment [] secondModel.vlctx (.fvar baseId) (.bvar 2) := .fvar rfl
  exact MLCtx.WF.dropNat_trS ordered primitives natPresent (n := 2) (hn := by decide)
    (modelWF ordered primitives natPresent) rfl source trivial (by change baseId ∈ [baseId]; simp)

theorem closesNatUnderDependentBinder :
    ∃ result, TrExprS environment [] ((none, .vlam (.bvar 0)) :: baseModel.vlctx)
      (.bvar 0) result := by
  have source : TrExprS environment [] ((none, .vlam (.bvar 2)) :: secondModel.vlctx)
      (.bvar 0) (.bvar 0) := .bvar rfl
  exact MLCtx.WF.dropNat_trS_under ordered primitives natPresent
    (n := 2) (hn := by decide) (domain := .bvar 0)
    (modelWF ordered primitives natPresent) rfl source (by change 0 < 1; decide) trivial

theorem emptyNatTelescope :
    ∃ result, TrExprS environment [] secondModel.vlctx (.fvar baseId) result := by
  have source : TrExprS environment [] secondModel.vlctx (.fvar baseId) (.bvar 2) := .fvar rfl
  exact MLCtx.WF.dropNat_trS ordered primitives natPresent (n := 0) (hn := by decide)
    (modelWF ordered primitives natPresent) rfl source trivial (by change baseId ∈ [secondId, firstId, baseId]; simp)

end

run_meta
  let environment ← getEnv
  let helpers := #[``TrExprS.close_unused_fvar, ``MLCtx.WF.dropNat_trS,
    ``MLCtx.WF.dropNat_trS_under]
  let witnesses := #[``closesBaseVariable, ``closesUnderDependentBinder,
    ``closesUnderTwoBinders, ``modelWF, ``closesTwoNatBinders,
    ``closesNatUnderDependentBinder, ``emptyNatTelescope]
  let logical := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let native := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  for name in helpers ++ witnesses do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "new unused-binder axiom {name}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "unused-binder proof absent {name}"
    if proof.hasSorry then throwError "direct unused-binder admission {name}"
    let allowed := if name == ``TrExprS.close_unused_fvar || (witnesses.toList.take 3).contains name
      then logical else logical ++ native
    for dependency in (← collectAxioms name) do
      unless allowed.contains dependency do throwError "unexpected dependency {dependency} in {name}"
    logInfo m!"{name}: {repr (← collectAxioms name)}"
  let forbidden := [``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``VEnv.IsDefEqU.weakN_iff, ``VEnv.IsDefEq.weakN_iff, ``VEnv.HasType.weakN_iff,
    ``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj]
  -- Unlike the previous six pure telescope helpers, native translation inherits
  -- these three pre-existing projection admissions. Pin their exact provenance.
  let inherited := [``TrProj, ``TrProj.instN, ``TrProj.weak']
  let mut pending := helpers ++ witnesses
  let mut visited : NameSet := {}
  let mut foundAdmissions : Array Name := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden unused-binder dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then
          unless inherited.contains name do throwError "unapproved inherited admission {name}"
          foundAdmissions := foundAdmissions.push name
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "unused-binder traversal exceeded bound"
  unless inherited.all foundAdmissions.contains && foundAdmissions.size == inherited.length do
    throwError "projection admission manifest changed: {repr foundAdmissions}"
  let helperCount := visited.size
  -- Aligning the retained domain is a separate existing conversion obligation.
  let bridgeInherited := [``TrProj, ``TrProj.defeqDFC, ``TrProj.uniq, ``TrProj.wf,
    ``VEnv.IsDefEqU.sort_inv, ``VEnv.IsDefEqU.forallE_inv_stratified]
  pending := #[``TrExprS.defeqDFC]
  visited := {}
  foundAdmissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden unused-binder dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then
          unless bridgeInherited.contains name do throwError "unapproved inherited admission {name}"
          foundAdmissions := foundAdmissions.push name
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "unused-binder traversal exceeded bound"
  unless bridgeInherited.all foundAdmissions.contains && foundAdmissions.size == bridgeInherited.length do
    throwError "retained-domain admission manifest changed: {repr foundAdmissions}"
  let consumer := ``Primitive.unfoldNatWellFounded.WF'
  let some proof := (← getConstInfo consumer).value? (allowOpaque := true)
    | throwError "actual recursion consumer absent"
  if proof.hasSorry then throwError "direct recursion admission"
  let direct := proof.getUsedConstants
  for required in [``MLCtx.WF.dropNat_trS, ``MLCtx.WF.dropNat_trS_under,
      ``VEnv.HasType.weakN_inv_of_argsTyped, ``VEnv.IsDefEqU.weakN_inv_of_argsTyped_under] do
    unless direct.contains required do throwError "actual consumer lost {required}"
  unless direct.contains ``TrExprS.weakFV_inv do
    throwError "reassess the remaining fuel-binder extraction trust account"
  logInfo m!"{helperCount} helper and {visited.size} domain-conversion dependencies traversed: no general strengthening/confluence; exact three- and six-admission provenance manifests"
  logInfo "actual guarded Nat context extractions use typed zero closing; the separate fuel-binder extraction and enclosing consumer admissions remain"

end UnusedNatTranslationTest
