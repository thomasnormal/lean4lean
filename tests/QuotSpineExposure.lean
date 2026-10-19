import Lean4Lean.Theory.Typing.QuotSpineExposure
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotSpineExposureTest
open Lean Lean4Lean Lean4Lean.VEnv
open Lean4Lean.VEnv.QuotConfluenceObstruction
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

def delay (type value : VExpr) : VExpr := .app (.lam type (.bvar 0)) value

theorem delayEqual {context : List VExpr} {type value : VExpr}
    (typed : quotientEnvironment.HasType 0 context value type) :
    quotientEnvironment.IsDefEq 0 context (delay type value) value type := by
  simpa [delay, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) typed

theorem delayReduction {context : List VExpr} (type value : VExpr) : ParRed context (delay type value) value := by
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := type :: context)) (ParRed.rfl (e := value)))



theorem explicitNormal {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) : NormalEq context expression expression := by
  cases expression with
  | app function argument =>
    obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv quotientEnvironmentWF.ordered contextWF
    exact .appDF functionTyped functionTyped argumentTyped argumentTyped (.refl functionTyped) (.refl argumentTyped)
  | _ => exact .refl typed

def etaTree : Nat → VExpr → VExpr → VExpr
  | 0, expression, _ => expression
  | depth + 1, expression, .forallE domain body =>
    .lam domain (etaTree depth (.app expression.lift (.bvar 0)) body)
  | _ + 1, expression, _ => expression

theorem etaTreeNormal {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) (depth : Nat) :
    NormalEq context (etaTree depth expression type) expression := by
  induction depth generalizing context expression type with
  | zero => exact explicitNormal contextWF typed
  | succ depth induction =>
    cases type <;> try exact .refl typed
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := typed.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    exact .etaL typed (induction ⟨contextWF, _, domainTyped⟩
      (etaBody_hasType quotientEnvironmentWF.ordered typed))


theorem domainTyped : quotientEnvironment.HasType 0 locals (.bvar 5) (.sort .zero) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem relationTyped : quotientEnvironment.HasType 0 locals (.bvar 4)
    (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem functionTyped : quotientEnvironment.HasType 0 locals (.bvar 3)
    (.forallE (.bvar 5) (.sort .zero)) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

theorem respectTyped : quotientEnvironment.HasType 0 locals (.bvar 2) (respectType.liftN 3) := by
  unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
  type_tac

def basePrefix : VExpr := applyArguments (.const ``Quot.lift [.zero, .succ .zero]) [.bvar 5, .bvar 4]
def baseType : VExpr := (applyType (quotLiftConst.type.instL [.zero, .succ .zero])
  [.bvar 5, .bvar 4]).getD (.sort .zero)

theorem baseTyped : quotientEnvironment.HasType 0 locals basePrefix baseType := by
  obtain ⟨_, _, liftObject, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := HasType.const liftObject (ls := [.zero, .succ .zero]) (by simp [VLevel.WF]) (by rfl)
    (Γ := locals) (U := 0)
  simp [quotLiftConst, VExpr.instL, VLevel.inst] at head
  have first := head.app domainTyped
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.app relationTyped
  simpa [HasType, basePrefix, baseType, applyArguments, applyType, quotLiftConst,
    VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar] using second

def deepEta : VExpr := etaTree 3 basePrefix baseType
def etaFunction : VExpr := .lam (.bvar 5) (.app (VExpr.bvar 3).lift (.bvar 0))
def pending : List VExpr := [.sort .zero, .bvar 3, .bvar 2, .bvar 0]
def pending' : List VExpr := [.sort .zero, etaFunction, .bvar 2, constructor]

theorem functionNormal : NormalEq locals (.bvar 3) etaFunction :=
  .etaR functionTyped (.refl (etaBody_hasType quotientEnvironmentWF.ordered functionTyped))

theorem pendingNormal : List.Forall₂ (NormalEq locals) pending pending' :=
  .cons (.refl (HasType.sort (by trivial))) (.cons functionNormal
    (.cons (.refl respectTyped) (.cons
      (.proofIrrel (majorTypeTyped quotientEnvironmentWF quotientRegistered)
        majorTyped (constructorTyped quotientEnvironmentWF quotientRegistered)) .nil)))

theorem samePending : List.Forall₂ (NormalEq locals) pending pending :=
  .cons (.refl (HasType.sort (by trivial))) (.cons (.refl functionTyped)
    (.cons (.refl respectTyped) (.cons (.refl majorTyped) .nil)))

def originalType : VExpr := delay (.sort (.succ .zero)) (.sort .zero)

theorem sourceTyped : quotientEnvironment.HasType 0 locals (applyArguments deepEta pending) originalType := by
  have contextWF := localsWF quotientEnvironmentWF quotientRegistered
  have normal := normal_spine_congr contextWF
    (show quotientEnvironment.HasType 0 locals (applyArguments basePrefix pending) (.sort .zero) from
      neutralTyped quotientEnvironmentWF quotientRegistered)
    ((etaTreeNormal contextWF baseTyped 3).symm contextWF) samePending
  have typed := ((normal.defeq contextWF).of_l quotientEnvironmentWF contextWF
    (neutralTyped quotientEnvironmentWF quotientRegistered)).hasType.2
  exact (delayEqual (HasType.sort (by trivial))).symm.defeq typed

-- Three dependent eta binders are consumed by actual core beta. The supplied
-- function arguments differ outside Prop, and the major changes by proof
-- irrelevance. The original result type is syntactically delayed.
theorem dependentPrefixExposure : ∃ result,
    ParRedS locals (applyArguments deepEta pending) result ∧
    RigidSpine quotientEnvironmentWF 0 ``Quot.lift [.zero, .succ .zero] locals result
      ([.bvar 5, .bvar 4] ++ pending') ∧
    NormalEq locals result (applyArguments (.const ``Quot.lift [.zero, .succ .zero])
      ([.bvar 5, .bvar 4] ++ pending')) ∧
    quotientEnvironment.HasType 0 locals result originalType ∧
    quotientEnvironment.HasType 0 locals
      (applyArguments (.const ``Quot.lift [.zero, .succ .zero]) ([.bvar 5, .bvar 4] ++ pending')) originalType :=
  normal_spine_expose_applications (localsWF quotientEnvironmentWF quotientRegistered)
    (etaTreeNormal (localsWF quotientEnvironmentWF quotientRegistered) baseTyped 3)
    pendingNormal sourceTyped

theorem retainedDependentBinder : ∃ result,
    ParRedS (.bvar 5 :: locals) (applyArguments deepEta pending).lift result.lift ∧
    NormalEq (.bvar 5 :: locals) result.lift
      (applyArguments (.const ``Quot.lift [.zero, .succ .zero]) ([.bvar 5, .bvar 4] ++ pending')).lift ∧
    ParRedS locals (applyArguments deepEta pending) result := by
  obtain ⟨result, path, _, normal, _, _⟩ := dependentPrefixExposure
  have retained := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  exact ⟨result, retained, retainedNormal,
    by simpa only [VExpr.inst_lift] using (ParRedS.inst
      (localsWF quotientEnvironmentWF quotientRegistered) witness retained .rfl)⟩

example : pending ≠ pending' := by intro equal; cases equal
example : deepEta ≠ basePrefix := by intro equal; cases equal
example : originalType ≠ VExpr.sort .zero := by intro equal; cases equal

theorem threeEtaBinders : ∃ first second third body,
    deepEta = .lam first (.lam second (.lam third body)) := ⟨_, _, _, _, rfl⟩

theorem firstActualBeta : ∃ domain body,
    deepEta = .lam domain body ∧
    ParRed locals (.app deepEta (.sort .zero)) (body.inst (.sort .zero)) := by
  refine ⟨_, _, rfl, ?_⟩
  exact .beta .rfl .rfl

def typeContext : List VExpr := .sort (.succ .zero) :: locals
def constructorPrefix : VExpr := .app (.const ``Quot.mk [.succ .zero]) (.bvar 0)
def constructorType : VExpr := (applyType (quotMkConst.type.instL [.succ .zero])
  [.bvar 0]).getD (.sort .zero)

theorem typeContextWF : OnCtx typeContext (quotientEnvironment.IsType 0) :=
  ⟨localsWF quotientEnvironmentWF quotientRegistered, _, HasType.sort (by trivial)⟩

theorem constructorPrefixTyped : quotientEnvironment.HasType 0 typeContext constructorPrefix constructorType := by
  obtain ⟨_, _, _, constructorObject, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := HasType.const constructorObject (ls := [.succ .zero]) (by simp [VLevel.WF]) (by rfl)
    (Γ := typeContext) (U := 0)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at head
  have typed := head.app (HasType.bvar (Γ := typeContext) .zero)
  simpa [HasType, constructorPrefix, constructorType, applyType, quotMkConst,
    VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar] using typed

theorem constructorEtaTyped : quotientEnvironment.HasType 0 typeContext
    (etaTree 2 constructorPrefix constructorType) constructorType :=
  (((etaTreeNormal typeContextWF constructorPrefixTyped 2).defeq typeContextWF).symm.of_l
    quotientEnvironmentWF typeContextWF constructorPrefixTyped).hasType.2

theorem changedTypes : NormalEq locals (.sort .zero) (.sort (.max .zero .zero)) :=
  .sortDF (by trivial) (by trivial) (VLevel.equiv_def.mpr (by intro values; rfl))

-- The retained variable ACTUALLY appears in dependent eta binder domains.
-- Its two substituted images are syntactically different non-proof types.
theorem substitutedDependentDomains : ∃ result,
    ParRedS locals ((etaTree 2 constructorPrefix constructorType).inst (.sort .zero)) result ∧
    RigidSpine quotientEnvironmentWF 0 ``Quot.mk [.succ .zero] locals result [.sort (.max .zero .zero)] ∧
    NormalEq locals result (.app (.const ``Quot.mk [.succ .zero]) (.sort (.max .zero .zero))) ∧
    quotientEnvironment.HasType 0 locals result (constructorType.inst (.sort .zero)) ∧
    quotientEnvironment.HasType 0 locals (.app (.const ``Quot.mk [.succ .zero]) (.sort (.max .zero .zero)))
      (constructorType.inst (.sort .zero)) := by
  have contextWF := localsWF quotientEnvironmentWF quotientRegistered
  obtain ⟨result, path, exposed⟩ := normal_spine_expose (name := ``Quot.mk)
    (levels := [.succ .zero]) (arguments := [.bvar 0]) typeContextWF
    (etaTreeNormal typeContextWF constructorPrefixTyped 2)
  have leftType : quotientEnvironment.HasType 0 locals (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial)
  have domainTyped : quotientEnvironment.HasType 0 locals (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    HasType.sort (by trivial)
  have final := exposed.instDF contextWF domainTyped leftType changedTypes
  have normal := final.normalEq contextWF
  have typed := (path.hasType typeContextWF constructorEtaTyped).instN quotientEnvironmentWF.ordered
    Ctx.InstN.zero leftType
  refine ⟨_, ParRedS.inst contextWF leftType path .rfl, ?_, ?_, typed, ?_⟩
  · simpa only [List.map_cons, List.map_nil, VExpr.inst, VExpr.instVar_zero] using final
  · simpa only [List.map_cons, List.map_nil, VExpr.inst, VExpr.instVar_zero, applyArguments] using normal
  · exact ((normal.defeq contextWF).of_l quotientEnvironmentWF contextWF typed).hasType.2

example : constructorType.inst (.sort .zero) ≠ constructorType.inst (.sort (.max .zero .zero)) := by
  intro equal; cases equal

namespace ProofHead

def proofConstant : VConstant := ⟨0, .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))⟩
def proofEnvironment : VEnv := {
  constants name := if `proofId = name then some proofConstant else none
  defeqs _ := False }

theorem environmentWF : proofEnvironment.WF := by
  have added : VEnv.empty.addConst `proofId proofConstant = some proofEnvironment := rfl
  refine ⟨_, .decl (.axiom (ci := ⟨proofConstant, `proofId⟩) ?_ added) .empty⟩
  exact ⟨_, by unfold proofConstant; type_tac⟩

local instance : Params := environmentWF.reductionParams 0

theorem propositionTyped {context : List VExpr} :
    proofEnvironment.HasType 0 context proofConstant.type (.sort .zero) := by
  have natural : proofEnvironment.HasType 0 context proofConstant.type
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) := by
    dsimp only [proofConstant]
    apply HasType.forallE (HasType.sort (by trivial))
    apply HasType.forallE (HasType.bvar .zero)
    exact HasType.bvar (.succ .zero)
  exact IsDefEq.defeq (.sortDF (by trivial) (by trivial) ((zeroLike_iff _).mp rfl)) natural

theorem constantTyped {context : List VExpr} :
    proofEnvironment.HasType 0 context (.const `proofId []) proofConstant.type := by
  have typed := HasType.const (show proofEnvironment.constants `proofId = some proofConstant from rfl)
    (ls := []) (by simp) (by rfl) (Γ := context) (U := 0)
  simpa [proofConstant, VExpr.instL, VLevel.inst] using typed

def context : List VExpr := [proofConstant.type]
theorem contextWF : OnCtx context (proofEnvironment.IsType 0) := ⟨trivial, _, propositionTyped⟩

theorem variableTyped : proofEnvironment.HasType 0 context (.bvar 0) proofConstant.type := by
  unfold context proofConstant
  type_tac

theorem sourceTyped : proofEnvironment.HasType 0 context
    (.app (.app (.bvar 0) proofConstant.type) (.const `proofId [])) proofConstant.type := by
  have first := variableTyped.app propositionTyped
  simp [proofConstant, VExpr.inst, VExpr.instVar] at first
  simpa [proofConstant, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using first.app constantTyped

-- Actual proof-headed application, with two supplied arguments, exercises
-- the proof alternative and proves that the original result type is Prop.
theorem proofExposure : ∃ result,
    ParRedS context (.app (.app (.bvar 0) proofConstant.type) (.const `proofId [])) result ∧
    RigidSpine environmentWF 0 `proofId [] context result [proofConstant.type, .const `proofId []] ∧
    NormalEq context result (.app (.app (.const `proofId []) proofConstant.type) (.const `proofId [])) ∧
    proofEnvironment.HasType 0 context result proofConstant.type ∧
    proofEnvironment.HasType 0 context
      (.app (.app (.const `proofId []) proofConstant.type) (.const `proofId [])) proofConstant.type :=
  normal_spine_expose_applications contextWF
    (show NormalEq context (.bvar 0) (applyArguments (.const `proofId []) []) from
      .proofIrrel propositionTyped variableTyped constantTyped)
    (.cons (.refl propositionTyped) (.cons (.refl constantTyped) .nil)) sourceTyped

end ProofHead

run_meta
  let environment ← getEnv
  let roots := [``applyArguments_subst, ``applyArguments_liftN, ``applyArguments_inst, ``HasType.spine_head, ``normal_spine_congr, ``RigidSpine.normalEq, ``RigidSpine.substDF, ``RigidSpine.instDF, ``RigidSpine.apply, ``RigidSpine.refl, ``normal_spine_expose, ``ParRedS.applyArguments, ``RigidSpine.applyArguments, ``normal_spine_expose_applications, ``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual, ``delayReduction, ``explicitNormal, ``etaTreeNormal, ``domainTyped, ``relationTyped, ``functionTyped, ``respectTyped, ``baseTyped, ``functionNormal, ``pendingNormal, ``samePending, ``sourceTyped, ``dependentPrefixExposure, ``retainedDependentBinder, ``threeEtaBinders, ``firstActualBeta, ``typeContextWF, ``constructorPrefixTyped, ``constructorEtaTyped, ``changedTypes, ``substitutedDependentDomains, ``ProofHead.environmentWF, ``ProofHead.propositionTyped, ``ProofHead.constantTyped, ``ProofHead.contextWF, ``ProofHead.variableTyped, ``ProofHead.sourceTyped, ``ProofHead.proofExposure]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``HasType.weakN_iff,
    ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC, ``NormalEq.trans,
    ``ParRed.weakN_inv, ``ParRedExt.parRed_beta, ``hasType_app_bvar0,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.applyArguments_subst, [], []),
    (`Lean4Lean.VEnv.QuotPropReduction.applyArguments_liftN, [], []),
    (`Lean4Lean.VEnv.QuotPropReduction.applyArguments_inst, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.HasType.spine_head, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_spine_congr, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.normalEq, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.substDF, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.instDF, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.apply, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.refl, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_spine_expose, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.ParRedS.applyArguments, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.RigidSpine.applyArguments, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_spine_expose_applications, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.quotientEnvironmentWF, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.quotientRegistered, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.delayEqual, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.delayReduction, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.explicitNormal, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.etaTreeNormal, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.domainTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.relationTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.functionTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.respectTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.baseTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.functionNormal, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.pendingNormal, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.samePending, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.sourceTyped, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.dependentPrefixExposure, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.retainedDependentBinder, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.threeEtaBinders, [], [`propext]),
    (`QuotSpineExposureTest.firstActualBeta, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.typeContextWF, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.constructorPrefixTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.constructorEtaTyped, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.changedTypes, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.substitutedDependentDomains, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx]),
    (`QuotSpineExposureTest.ProofHead.environmentWF, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.propositionTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.constantTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.contextWF, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.variableTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.sourceTyped, [], [`Quot.sound, `propext]),
    (`QuotSpineExposureTest.ProofHead.proofExposure, [`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, `Lean4Lean.VEnv.IsDefEqU.sort_inv], [`Quot.sound, `propext, `sorryAx])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing spine exposure manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new spine exposure axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing spine exposure proof {root}"
    if proof.hasSorry then throwError "direct spine exposure admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "spine exposure axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden spine exposure dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then throwError "admitted type {name} in {root}"
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved spine exposure admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "spine exposure traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "spine exposure admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``normal_spine_congr then
        [``HasType.spine_head, ``NormalEq.appDF, ``NormalEq.defeq]
      else if root == ``RigidSpine.normalEq then
        [``RigidSpine.rec, ``normal_spine_congr, ``NormalEq.etaL]
      else if root == ``RigidSpine.substDF then
        [``RigidSpine.rec, ``NormalEq.substDF, ``NormalSubstitution.lift, ``IsDefEq.substDF]
      else if root == ``RigidSpine.instDF then
        [``RigidSpine.substDF, ``NormalSubstitution.one]
      else if root == ``RigidSpine.apply then
        [``RigidSpine.instDF, ``ParRed.beta, ``NormalEq.proofIrrel]
      else if root == ``normal_spine_expose then
        [``VExpr.brecOn, ``RigidSpine.apply, ``RigidSpine.refl, ``ParRedS.app, ``ParRedS.lam, ``ParRedS.hasType]
      else if root == ``RigidSpine.applyArguments then
        [``RigidSpine.apply, ``ParRedS.applyArguments, ``ParRedS.hasType]
      else if root == ``normal_spine_expose_applications then
        [``normal_spine_expose, ``RigidSpine.applyArguments, ``RigidSpine.normalEq,
          ``ParRedS.applyArguments, ``ParRedS.hasType]
      else if root == ``dependentPrefixExposure then
        [``normal_spine_expose_applications, ``etaTreeNormal, ``pendingNormal, ``sourceTyped]
      else if root == ``retainedDependentBinder then
        [``dependentPrefixExposure, ``ParRedS.weakN, ``ParRedS.inst, ``NormalEq.weakN]
      else if root == ``substitutedDependentDomains then
        [``normal_spine_expose, ``RigidSpine.instDF, ``RigidSpine.normalEq, ``changedTypes,
          ``constructorEtaTyped, ``ParRedS.inst]
      else if root == ``ProofHead.proofExposure then
        [``normal_spine_expose_applications, ``NormalEq.proofIrrel,
          ``ProofHead.environmentWF, ``ProofHead.propositionTyped, ``ProofHead.sourceTyped]
      else if root == ``firstActualBeta then [``ParRed.beta]
      else []
    unless required.all visited.contains do
      throwError "spine exposure control bypassed a required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"

end QuotSpineExposureTest
