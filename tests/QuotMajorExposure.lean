import Lean4Lean.Theory.Typing.QuotMajorExposure
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotMajorExposureTest
open Lean Lean4Lean Lean4Lean.VEnv
open Lean4Lean.VEnv.QuotPropReduction

def equalityEnvironment : VEnv := {
  constants name := if ``Eq = name then some eqConst else none
  defeqs _ := False }
def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem quotientEnvironmentWF : quotientEnvironment.WF := by
  have added : VEnv.empty.addConst ``Eq eqConst = some equalityEnvironment := rfl
  have equalityWF : equalityEnvironment.WF := by
    refine ⟨_, .decl (.axiom (ci := ⟨eqConst, ``Eq⟩) ?_ added) .empty⟩
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : equalityEnvironment.QuotReady := by simp [QuotReady, equalityEnvironment]
  obtain ⟨_, checked⟩ := equalityWF
  exact ⟨_, .decl (.quot ready (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)) checked⟩

theorem quotientRegistered : quotientEnvironment.defeqs quotDefEq :=
  addQuot_defeq (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)

local instance : Params := quotientEnvironmentWF.reductionParams 0

def one : VLevel := .succ .zero
def alternate : VLevel := .max .zero one

def context : List VExpr :=
  [.bvar 1, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort one]

def quotientType : VExpr := .app (.app (.const ``Quot [one]) (.bvar 2)) (.bvar 1)
def constructor (level : VLevel) : VExpr :=
  .app (.app (.app (.const ``Quot.mk [level]) (.bvar 2)) (.bvar 1)) (.bvar 0)

theorem contextWF : OnCtx context (quotientEnvironment.IsType 0) := by
  unfold context one
  exact ⟨⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩

theorem domainTyped : quotientEnvironment.HasType 0 context (.bvar 2) (.sort one) := by
  unfold context one
  type_tac

theorem relationTyped : quotientEnvironment.HasType 0 context (.bvar 1)
    (.forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero))) := by
  unfold context one
  type_tac

theorem valueTyped : quotientEnvironment.HasType 0 context (.bvar 0) (.bvar 2) := by
  unfold context one
  type_tac

theorem quotientTypeTyped : quotientEnvironment.HasType 0 context quotientType (.sort one) := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context one quotientType
  type_tac

theorem constructorTyped : quotientEnvironment.HasType 0 context (constructor one) quotientType := by
  obtain ⟨_, _, _, hmk, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold constructor context one quotientType
  type_tac

theorem headNormal : NormalEq context (.const ``Quot.mk [one]) (.const ``Quot.mk [alternate]) := by
  obtain ⟨_, _, _, hmk, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact .constDF hmk (by simp [one, VLevel.WF]) (by simp [alternate, one, VLevel.WF])
    rfl (.cons (VLevel.equiv_def.mpr fun _ => by simp [one, alternate, VLevel.eval]) .nil)

def etaHead : VExpr :=
  .lam (.sort one) (.app (.const ``Quot.mk [one]) (.bvar 0))

def etaMajor : VExpr := applyArguments etaHead [.bvar 2, .bvar 1, .bvar 0]

theorem headTyped : quotientEnvironment.HasType 0 context (.const ``Quot.mk [one])
    (quotMkConst.type.instL [one]) := by
  obtain ⟨_, _, _, hmk, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact .const hmk (by simp [one, VLevel.WF]) rfl

theorem etaNormal : NormalEq context etaHead (.const ``Quot.mk [one]) := by
  have typed := headTyped
  simp [quotMkConst, VExpr.instL, VLevel.inst] at typed
  exact .etaL typed (.refl (etaBody_hasType quotientEnvironmentWF.ordered typed))

theorem etaMajorTyped : quotientEnvironment.HasType 0 context etaMajor quotientType := by
  have arguments : List.Forall₂ (NormalEq context)
      [VExpr.bvar 2, .bvar 1, .bvar 0] [.bvar 2, .bvar 1, .bvar 0] :=
    .cons (.refl domainTyped) (.cons (.refl relationTyped) (.cons (.refl valueTyped) .nil))
  have normal := normal_spine_congr (arguments := [.bvar 2, .bvar 1, .bvar 0]) contextWF constructorTyped
    (etaNormal.symm contextWF) arguments
  exact ((normal.defeq contextWF).of_l quotientEnvironmentWF contextWF constructorTyped).hasType.2

theorem majorNormal : NormalEq context etaMajor (constructor alternate) := by
  have arguments : List.Forall₂ (NormalEq context)
      [VExpr.bvar 2, .bvar 1, .bvar 0] [.bvar 2, .bvar 1, .bvar 0] :=
    .cons (.refl domainTyped) (.cons (.refl relationTyped) (.cons (.refl valueTyped) .nil))
  have etaAlternate : NormalEq context etaHead (.const ``Quot.mk [alternate]) := by
    have alternateTyped := ((headNormal.defeq contextWF).of_l quotientEnvironmentWF contextWF headTyped).hasType.2
    have rightHeadTyped := alternateTyped
    simp [quotMkConst, VExpr.instL, VLevel.inst] at alternateTyped
    have bodies := NormalEq.appDF
      (headTyped.weak quotientEnvironmentWF.ordered) (rightHeadTyped.weak quotientEnvironmentWF.ordered)
      (HasType.bvar .zero) (HasType.bvar .zero)
      (headNormal.weakN (Ctx.LiftN.one (A := .sort one))) (.refl (HasType.bvar .zero))
    exact .etaL alternateTyped bodies
  exact normal_spine_congr (arguments := [.bvar 2, .bvar 1, .bvar 0]) contextWF etaMajorTyped etaAlternate arguments

-- The left has a real beta redex in the constructor prefix. Exposure must
-- follow original core steps; the right universe is syntactically different.
theorem majorExposure :
    (∃ leftUniverse leftDomain leftRelation leftValue,
      ParRedS context etaMajor
        (.app (.app (.app (.const ``Quot.mk [leftUniverse]) leftDomain) leftRelation) leftValue) ∧
      leftUniverse ≈ alternate ∧
      NormalEq context leftDomain (.bvar 2) ∧
      NormalEq context leftRelation (.bvar 1) ∧
      NormalEq context leftValue (.bvar 0) ∧
      quotientEnvironment.HasType 0 context
        (.app (.app (.app (.const ``Quot.mk [leftUniverse]) leftDomain) leftRelation) leftValue)
        (.app (.app (.const ``Quot [one]) (.bvar 2)) (.bvar 1))) ∨
    (∃ binder body codomain,
      ParRedS context etaMajor (.lam binder body) ∧
      NormalEq context (.lam binder body)
        (.app (.app (.app (.const ``Quot.mk [alternate]) (.bvar 2))
          (.bvar 1)) (.bvar 0)) ∧
      quotientEnvironment.HasType 0 context (.lam binder body)
        (.app (.app (.const ``Quot [one]) (.bvar 2)) (.bvar 1)) ∧
      quotientEnvironment.IsDefEqU 0 context
        (.app (.app (.const ``Quot [one]) (.bvar 2)) (.bvar 1)) (.forallE binder codomain)) := normal_quot_major_expose quotientRegistered contextWF
  (show zeroLike one = false from rfl) etaMajorTyped majorNormal

theorem betaPath : ParRedS context etaMajor (constructor one) := by
  exact .tail .rfl (.app (.app (.beta .rfl .rfl) .rfl) .rfl)

theorem universeRecovered : one ≈ alternate := by
  have rightTyped := ((majorNormal.defeq contextWF).of_l quotientEnvironmentWF contextWF etaMajorTyped).hasType.2
  exact quotMk_source_eq (environmentWF := quotientEnvironmentWF) quotientRegistered contextWF rightTyped

def delayedRelation : VExpr :=
  .app (.lam (.forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero))) (.bvar 0)) (.bvar 1)

theorem relationEquality : quotientEnvironment.IsDefEq 0 context delayedRelation (.bvar 1)
    (.forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero))) := by
  simpa [delayedRelation, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) relationTyped

theorem quotientTypesEqual : quotientEnvironment.IsDefEqU 0 context quotientType
    (.app (.app (.const ``Quot [alternate]) (.bvar 2)) delayedRelation) := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF hquot (ls := [one]) (ls' := [alternate])
    (by simp [one, VLevel.WF]) (by simp [alternate, one, VLevel.WF]) rfl
    (.cons (VLevel.equiv_def.mpr fun _ => by simp [one, alternate, VLevel.eval]) .nil)
    (Γ := context) (uvars := 0)
  simp [quotConst, VExpr.instL, VLevel.inst] at head
  have applied := head.appDF domainTyped
  simp [VExpr.inst, VExpr.instVar] at applied
  exact (applied.appDF relationEquality.symm).toU

theorem sourceUniverseFromDifferentTypes : one ≈ alternate := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact quot_source_eq (environmentWF := quotientEnvironmentWF) hquot contextWF quotientTypesEqual

theorem differentRelations : delayedRelation ≠ VExpr.bvar 1 := by intro equal; cases equal

-- Neutral proof majors force zero, without any constructor shape.
open Lean4Lean.VEnv.QuotConfluenceObstruction in
 theorem neutralProofSource : zeroLike VLevel.zero = true := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact quot_proof_source (environmentWF := quotientEnvironmentWF) hquot
    (localsWF quotientEnvironmentWF quotientRegistered) majorTyped
    (majorTypeTyped quotientEnvironmentWF quotientRegistered) majorTyped

namespace ZeroSource
open Lean4Lean.VEnv.QuotConfluenceObstruction

def alternateZero : VLevel := .max .zero .zero

theorem quotientTypesEqual : quotientEnvironment.IsDefEqU 0 locals majorType
    (.app (.app (.const ``Quot [alternateZero]) (.bvar 5)) (.bvar 4)) := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have domainTyped : quotientEnvironment.HasType 0 locals (.bvar 5) (.sort .zero) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  have relationTyped : quotientEnvironment.HasType 0 locals (.bvar 4)
      (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  have head := IsDefEq.constDF hquot (ls := [.zero]) (ls' := [alternateZero])
    (by simp [VLevel.WF]) (by simp [alternateZero, VLevel.WF]) rfl
    (.cons (VLevel.equiv_def.mpr fun _ => rfl) .nil) (Γ := locals) (uvars := 0)
  simp [quotConst, VExpr.instL, VLevel.inst] at head
  have applied := head.appDF domainTyped
  simp [VExpr.inst, VExpr.instVar] at applied
  exact (applied.appDF relationTyped).toU

theorem alternateMajorTyped : quotientEnvironment.HasType 0 locals (.bvar 0)
    (.app (.app (.const ``Quot [alternateZero]) (.bvar 5)) (.bvar 4)) :=
  (quotientTypesEqual.of_l quotientEnvironmentWF
    (localsWF quotientEnvironmentWF quotientRegistered)
    (majorTypeTyped quotientEnvironmentWF quotientRegistered)).defeq majorTyped

-- The same neutral proof inhabits the quotient at a syntactically different
-- zero-equivalent source. The theorem derives the Boolean source check.
theorem neutralProofSource : zeroLike alternateZero = true := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  exact quot_proof_source (environmentWF := quotientEnvironmentWF) hquot
    (localsWF quotientEnvironmentWF quotientRegistered) alternateMajorTyped
    (majorTypeTyped quotientEnvironmentWF quotientRegistered) majorTyped

theorem sourceNotLiteral : alternateZero ≠ VLevel.zero := by intro equal; cases equal

end ZeroSource

theorem noNonzeroProof {proposition : VExpr}
    (propTyped : quotientEnvironment.HasType 0 context proposition (.sort .zero))
    (proofTyped : quotientEnvironment.HasType 0 context etaMajor proposition) : False := by
  obtain ⟨_, _, _, _, hquot, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have zero := quot_proof_source (environmentWF := quotientEnvironmentWF) hquot contextWF
    etaMajorTyped propTyped proofTyped
  change false = true at zero
  cases zero

theorem differentUniverses : one ≠ alternate := by intro equal; cases equal

theorem etaPrefixIsLambda : ∃ domain body, etaHead = .lam domain body := ⟨_, _, rfl⟩

run_meta
  let environment ← getEnv
  let roots := [``quot_source_eq, ``quot_proof_source, ``quotMk_source_eq, ``normal_quot_major_expose, ``quotientEnvironmentWF, ``quotientRegistered, ``contextWF, ``domainTyped, ``relationTyped, ``valueTyped, ``quotientTypeTyped, ``constructorTyped, ``headNormal, ``headTyped, ``etaNormal, ``etaMajorTyped, ``majorNormal, ``majorExposure, ``betaPath, ``universeRecovered, ``relationEquality, ``quotientTypesEqual, ``sourceUniverseFromDifferentTypes, ``differentRelations, ``neutralProofSource, ``noNonzeroProof, ``differentUniverses, ``etaPrefixIsLambda, ``ZeroSource.quotientTypesEqual, ``ZeroSource.alternateMajorTyped, ``ZeroSource.neutralProofSource, ``ZeroSource.sourceNotLiteral]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.sort_forallE_inv, ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``HasType.weakN_iff,
    ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC, ``NormalEq.trans,
    ``ParRed.weakN_inv, ``ParRedExt.parRed_beta, ``hasType_app_bvar0,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.quot_source_eq, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.quot_proof_source, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.quotMk_source_eq, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_expose, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientEnvironmentWF, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientRegistered, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.contextWF, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.domainTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.relationTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.valueTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientTypeTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.constructorTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.headNormal, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.headTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.etaNormal, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.etaMajorTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.majorNormal, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.majorExposure, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.betaPath, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.universeRecovered, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.relationEquality, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientTypesEqual, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.sourceUniverseFromDifferentTypes, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.differentRelations, [], []),
    (`QuotMajorExposureTest.neutralProofSource, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.noNonzeroProof, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.differentUniverses, [], []),
    (`QuotMajorExposureTest.etaPrefixIsLambda, [], []),
    (`QuotMajorExposureTest.ZeroSource.quotientTypesEqual, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.ZeroSource.alternateMajorTyped, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.ZeroSource.neutralProofSource, [], [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.ZeroSource.sourceNotLiteral, [], [])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing major-exposure manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new major-exposure axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing major-exposure proof {root}"
    if proof.hasSorry then throwError "direct major-exposure admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "major-exposure axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden major-exposure dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then throwError "admitted type {name} in {root}"
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unexpected major-exposure admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "major-exposure traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "major-exposure admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``quot_source_eq then [``quot_inv, ``IsDefEq.uniqU, ``IsDefEqU.sort_inv]
      else if root == ``quot_proof_source then [``quot_inv, ``IsDefEq.uniqU, ``zeroLike_iff]
      else if root == ``quotMk_source_eq then [``quotMk_inv, ``quot_source_eq]
      else if root == ``normal_quot_major_expose then
        [``normal_spine_expose, ``quot_proof_source, ``RigidSpine.normalEq, ``IsDefEq.uniqU]
      else if root == ``majorExposure then [``normal_quot_major_expose, ``majorNormal, ``etaMajorTyped]
      else if root == ``universeRecovered then [``quotMk_source_eq, ``majorNormal]
      else if root == ``sourceUniverseFromDifferentTypes then [``quot_source_eq, ``quotientTypesEqual]
      else if root == ``neutralProofSource then [``quot_proof_source, ``QuotConfluenceObstruction.majorTyped]
      else if root == ``ZeroSource.neutralProofSource then [``quot_proof_source, ``ZeroSource.alternateMajorTyped]
      else if root == ``noNonzeroProof then [``quot_proof_source, ``etaMajorTyped]
      else if root == ``betaPath then [``ParRed.beta, ``ParRed.app]
      else []
    unless required.all visited.contains do
      throwError "major-exposure control bypassed required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"

end QuotMajorExposureTest
