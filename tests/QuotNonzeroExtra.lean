import Lean4Lean.Theory.Typing.QuotNonzeroExtra
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

end QuotMajorExposureTest

namespace NonzeroReplayTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open Lean4Lean.VEnv.QuotPropReduction QuotMajorExposureTest

local instance : Params := quotientEnvironmentWF.reductionParams 0

def levels : List VLevel := [one, one]
def domains : List VExpr := (quotLiftDoms.take 5 ++ [VExpr.bvar 4]).map (·.instL levels)
def locals : List VExpr := domains.reverse

theorem localsWF : OnCtx locals (quotientEnvironment.IsType 0) := by
  have eqLookup : quotientEnvironment.constants ``Eq = some eqConst := rfl
  unfold locals domains quotLiftDoms levels one
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩,
    _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩

def original : quotLiftPattern.Path → VExpr
  | .inl none => .bvar 1
  | .inl (some none) => .bvar 2
  | .inl (some (some none)) => .bvar 3
  | .inl (some (some (some none))) => .bvar 4
  | .inl (some (some (some (some none)))) => .bvar 5
  | .inr none => .bvar 0
  | .inr (some none) => .bvar 4
  | .inr (some (some none)) => .bvar 5

def argumentTypes : quotLiftPattern.Path → VExpr
  | .inl none => ((quotLiftDoms[4]!).instL levels).liftN 2
  | .inl (some none) => .forallE (.bvar 5) (.bvar 4)
  | .inl (some (some none)) => .sort one
  | .inl (some (some (some none))) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inl (some (some (some (some none)))) => .sort one
  | .inr none => .bvar 5
  | .inr (some none) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inr (some (some none)) => .sort one

theorem argumentsTyped (path : quotLiftPattern.Path) :
    quotientEnvironment.HasType 0 locals (original path) (argumentTypes path) := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (unfold original argumentTypes locals domains quotLiftDoms levels one; type_tac)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (unfold original argumentTypes locals domains quotLiftDoms levels one; type_tac)

def delay (type value : VExpr) : VExpr := .app (.lam type (.bvar 0)) value

theorem delayEqual (typed : quotientEnvironment.HasType 0 Γ value type) :
    quotientEnvironment.IsDefEq 0 Γ (delay type value) value type := by
  simpa [delay, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) typed

theorem delayReduction (type value : VExpr) : ParRed Γ (delay type value) value := by
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := type :: Γ)) (ParRed.rfl (e := value)))

def values : quotLiftPattern.Path → VExpr
  | .inr (some path) => delay (argumentTypes (.inr (some path)))
      (delay (argumentTypes (.inr (some path))) (original (.inr (some path))))
  | path => delay (argumentTypes path) (original path)

theorem valueEqual (path : quotLiftPattern.Path) :
    quotientEnvironment.IsDefEq 0 locals (values path) (original path) (argumentTypes path) := by
  rcases path with path | path
  · cases path <;> exact delayEqual (argumentsTyped _)
  · cases path with
    | none => exact delayEqual (argumentsTyped _)
    | some path => exact (delayEqual (delayEqual (argumentsTyped _)).hasType.1).trans (delayEqual (argumentsTyped _))

def liftPrefix : VExpr := .app (.app (.app (.app (.app (.const ``Quot.lift levels)
    (values (.inl (some (some (some (some none)))))))
    (values (.inl (some (some (some none)))))) (values (.inl (some (some none)))))
    (values (.inl (some none)))) (values (.inl none))
def major : VExpr := .app (.app (.app (.const ``Quot.mk [one])
    (values (.inr (some (some none))))) (values (.inr (some none)))) (values (.inr none))
def right : VExpr := .app liftPrefix major

theorem rightTyped : quotientEnvironment.HasType 0 locals right (.bvar 3) := by
  obtain ⟨_, _, liftRegistered, constructorRegistered, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF (uvars := 0) liftRegistered (ls := levels) (ls' := levels)
    (by simp [levels, one, VLevel.WF]) (by simp [levels, one, VLevel.WF]) rfl
    (.cons rfl (.cons rfl .nil)) (Γ := locals)
  simp [quotLiftConst, VExpr.instL, VLevel.inst, levels] at head
  have first := head.appDF (valueEqual (.inl (some (some (some (some none)))))).symm
  simp [VExpr.inst, VExpr.instVar, original] at first
  have second := first.appDF (valueEqual (.inl (some (some (some none))))).symm
  simp [VExpr.inst, VExpr.instVar, original] at second
  have third := second.appDF (valueEqual (.inl (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar, original] at third
  have fourth := third.appDF (valueEqual (.inl (some none))).symm
  simp [VExpr.inst, VExpr.instVar, original] at fourth
  have fifth := fourth.appDF (valueEqual (.inl none)).symm
  simp [VExpr.inst, original] at fifth
  have ctor := IsDefEq.constDF (uvars := 0) constructorRegistered (ls := [one]) (ls' := [one])
    (by simp [one, VLevel.WF]) (by simp [one, VLevel.WF]) rfl (.cons rfl .nil) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at ctor
  have c1 := ctor.appDF (valueEqual (.inr (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar, original] at c1
  have c2 := c1.appDF (valueEqual (.inr (some none))).symm
  simp [VExpr.inst, VExpr.instVar, VExpr.inst_lift, original] at c2
  have c3 := c2.appDF (valueEqual (.inr none)).symm
  simpa [HasType, liftPrefix, major, right, levels, original, VExpr.liftN,
    VExpr.inst, VExpr.instVar, VExpr.inst_lift] using (fifth.appDF c3).hasType.2

theorem matched : quotLiftPattern.Matches right levels values := by
  have hf := Pattern.Matches.const (c := ``Quot.lift) (ls := levels)
    |>.var (a' := values (.inl (some (some (some (some none))))))
    |>.var (a' := values (.inl (some (some (some none)))))
    |>.var (a' := values (.inl (some (some none))))
    |>.var (a' := values (.inl (some none))) |>.var (a' := values (.inl none))
  have hm := Pattern.Matches.const (c := ``Quot.mk) (ls := [one])
    |>.var (a' := values (.inr (some (some none))))
    |>.var (a' := values (.inr (some none))) |>.var (a' := values (.inr none))
  rw [(_ : values = _)]
  · exact hf.app hm
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem checked : quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 locals) levels values :=
  ⟨((valueEqual (.inl (some (some (some (some none)))))).trans
      (valueEqual (.inr (some (some none)))).symm).toU,
    ((valueEqual (.inl (some (some (some none))))).trans
      (valueEqual (.inr (some none))).symm).toU, trivial⟩

theorem argumentsReduce (path : quotLiftPattern.Path) : ParRed locals (values path) (original path) := by
  rcases path with path | path
  · cases path <;> exact delayReduction _ _
  · cases path with
    | none => exact delayReduction _ _
    | some path =>
      simpa [values, delay, VExpr.inst, VExpr.instVar] using
        (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := argumentTypes (.inr (some path)) :: locals))
          (delayReduction (argumentTypes (.inr (some path))) (original (.inr (some path)))))

def majorType : VExpr := .app (.app (.const ``Quot [one])
  (values (.inl (some (some (some (some none))))))) (values (.inl (some (some (some none)))))

theorem majorTyped : quotientEnvironment.HasType 0 locals major majorType := by
  obtain ⟨_, _, hlift, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  obtain ⟨u, v, hs, _, _, _, _, _, _, _, hm, _⟩ := quotLift_inv quotientEnvironmentWF localsWF hlift rightTyped
  have ⟨rfl, hs⟩ := List.cons.inj hs
  have ⟨rfl, _⟩ := List.cons.inj hs
  exact hm

def left : VExpr := .app liftPrefix (delay majorType major)

theorem leftTyped : quotientEnvironment.HasType 0 locals left (.bvar 3) := by
  obtain ⟨_, _, hf, ha⟩ := rightTyped.app_inv quotientEnvironmentWF.ordered localsWF
  have eq := hf.appDF ((delayEqual majorTyped).toU.of_r quotientEnvironmentWF localsWF ha).symm
  exact (eq.toU.of_l quotientEnvironmentWF localsWF rightTyped).hasType.2

theorem majorSimulation : CoreSimulates quotientEnvironmentWF 0 locals (delay majorType major) major := by
  intro result reduction
  exact ⟨result, (ReflTransGen.tail .rfl (.core (delayReduction majorType major))).trans
    (.tail .rfl (.core reduction)), .refl (reduction.hasType localsWF majorTyped)⟩

theorem replay : ∃ joined,
    ParRed locals right (.app (.bvar 2) (.bvar 0)) ∧
    Steps quotientEnvironmentWF 0 locals left joined ∧
    NormalEq locals joined (.app (.bvar 2) (.bvar 0)) ∧
    quotientEnvironment.HasType 0 locals joined (.bvar 3) ∧
    quotientEnvironment.HasType 0 locals (.app (.bvar 2) (.bvar 0)) (.bvar 3) := by
  exact CoreSimulates.quot_nonzero_extra (values := values) (reducedValues := original)
    quotientRegistered localsWF leftTyped rightTyped rfl
    (.refl (valueEqual _).hasType.1) (.refl (valueEqual _).hasType.1)
    (CoreSimulates.refl localsWF (valueEqual _).hasType.1) majorSimulation matched checked argumentsReduce

theorem leftDoesNotMatch {ls captures} : ¬ quotLiftPattern.Matches left ls captures := by
  intro h
  cases h with
  | app _ h => cases h with
    | var h => cases h

theorem differentDomainParameters : values (.inl (some (some (some (some none))))) ≠
    values (.inr (some (some none))) := by intro h; cases h

theorem differentRelationParameters : values (.inl (some (some (some none)))) ≠
    values (.inr (some none)) := by intro h; cases h

theorem allCapturesChange (path : quotLiftPattern.Path) : values path ≠ original path := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (intro h; cases h)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (intro h; cases h)

theorem retainedReplay :
    OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) ∧
    ∃ joined : VExpr, Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) left.lift joined.lift ∧
      NormalEq (.bvar 5 :: locals) joined.lift (.app (.bvar 3) (.bvar 1)) ∧
      quotientEnvironment.HasType 0 (.bvar 5 :: locals) joined.lift (.bvar 4) := by
  obtain ⟨joined, _, path, normal, typed, _⟩ := replay
  exact ⟨⟨localsWF, _, argumentsTyped (.inl (some (some (some (some none)))))⟩,
    joined, path.weakN (Ctx.LiftN.one (A := .bvar 5)),
    normal.weakN (Ctx.LiftN.one (A := .bvar 5)),
    typed.weakN quotientEnvironmentWF.ordered (Ctx.LiftN.one (A := .bvar 5))⟩

/-- The original eta exposure now has an unconditional constructor result. -/
theorem etaConstructor : ∃ l A r a,
    ParRedS context etaMajor (.app (.app (.app (.const ``Quot.mk [l]) A) r) a) ∧
    l ≈ alternate ∧ NormalEq context A (.bvar 2) ∧ NormalEq context r (.bvar 1) ∧
    NormalEq context a (.bvar 0) ∧ quotientEnvironment.HasType 0 context
      (.app (.app (.app (.const ``Quot.mk [l]) A) r) a) quotientType :=
  normal_quot_major_constructor quotientRegistered contextWF rfl etaMajorTyped majorNormal

end NonzeroReplayTest

namespace NonzeroReplayAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.IsDefEqU.rigidApp_forallE_inv,
    `Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor,
    `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_nonzero_extra,
    (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotNonzeroExtra") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedConstructorShape"),
    `QuotMajorExposureTest.equalityEnvironment,
    `QuotMajorExposureTest.quotientEnvironment,
    `QuotMajorExposureTest.quotientEnvironmentWF,
    `QuotMajorExposureTest.quotientRegistered,
    `QuotMajorExposureTest.one,
    `QuotMajorExposureTest.alternate,
    `QuotMajorExposureTest.context,
    `QuotMajorExposureTest.quotientType,
    `QuotMajorExposureTest.constructor,
    `QuotMajorExposureTest.contextWF,
    `QuotMajorExposureTest.domainTyped,
    `QuotMajorExposureTest.relationTyped,
    `QuotMajorExposureTest.valueTyped,
    `QuotMajorExposureTest.quotientTypeTyped,
    `QuotMajorExposureTest.constructorTyped,
    `QuotMajorExposureTest.headNormal,
    `QuotMajorExposureTest.etaHead,
    `QuotMajorExposureTest.etaMajor,
    `QuotMajorExposureTest.headTyped,
    `QuotMajorExposureTest.etaNormal,
    `QuotMajorExposureTest.etaMajorTyped,
    `QuotMajorExposureTest.majorNormal,
    `QuotMajorExposureTest.majorExposure,
    `QuotMajorExposureTest.betaPath,
    `QuotMajorExposureTest.universeRecovered,
    `QuotMajorExposureTest.delayedRelation,
    `QuotMajorExposureTest.relationEquality,
    `QuotMajorExposureTest.quotientTypesEqual,
    `QuotMajorExposureTest.sourceUniverseFromDifferentTypes,
    `QuotMajorExposureTest.differentRelations,
    `NonzeroReplayTest.levels,
    `NonzeroReplayTest.domains,
    `NonzeroReplayTest.locals,
    `NonzeroReplayTest.localsWF,
    `NonzeroReplayTest.original,
    `NonzeroReplayTest.argumentTypes,
    `NonzeroReplayTest.argumentsTyped,
    `NonzeroReplayTest.delay,
    `NonzeroReplayTest.delayEqual,
    `NonzeroReplayTest.delayReduction,
    `NonzeroReplayTest.values,
    `NonzeroReplayTest.valueEqual,
    `NonzeroReplayTest.liftPrefix,
    `NonzeroReplayTest.major,
    `NonzeroReplayTest.right,
    `NonzeroReplayTest.rightTyped,
    `NonzeroReplayTest.matched,
    `NonzeroReplayTest.checked,
    `NonzeroReplayTest.argumentsReduce,
    `NonzeroReplayTest.majorType,
    `NonzeroReplayTest.majorTyped,
    `NonzeroReplayTest.left,
    `NonzeroReplayTest.leftTyped,
    `NonzeroReplayTest.majorSimulation,
    `NonzeroReplayTest.replay,
    `NonzeroReplayTest.leftDoesNotMatch,
    `NonzeroReplayTest.differentDomainParameters,
    `NonzeroReplayTest.differentRelationParameters,
    `NonzeroReplayTest.allCapturesChange,
    `NonzeroReplayTest.retainedReplay,
    `NonzeroReplayTest.etaConstructor]

  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.IsDefEqU.rigidApp_forallE_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_nonzero_extra, [`Quot.sound, `propext]),
    ((Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotNonzeroExtra") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedConstructorShape"), []),
    (`QuotMajorExposureTest.equalityEnvironment, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientEnvironment, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientEnvironmentWF, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientRegistered, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.one, []),
    (`QuotMajorExposureTest.alternate, []),
    (`QuotMajorExposureTest.context, []),
    (`QuotMajorExposureTest.quotientType, []),
    (`QuotMajorExposureTest.constructor, []),
    (`QuotMajorExposureTest.contextWF, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.domainTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.relationTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.valueTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientTypeTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.constructorTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.headNormal, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.etaHead, []),
    (`QuotMajorExposureTest.etaMajor, []),
    (`QuotMajorExposureTest.headTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.etaNormal, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.etaMajorTyped, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.majorNormal, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.majorExposure, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.betaPath, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.universeRecovered, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.delayedRelation, []),
    (`QuotMajorExposureTest.relationEquality, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.quotientTypesEqual, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.sourceUniverseFromDifferentTypes, [`Quot.sound, `propext]),
    (`QuotMajorExposureTest.differentRelations, []),
    (`NonzeroReplayTest.levels, []),
    (`NonzeroReplayTest.domains, [`propext]),
    (`NonzeroReplayTest.locals, [`propext]),
    (`NonzeroReplayTest.localsWF, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.original, []),
    (`NonzeroReplayTest.argumentTypes, [`propext]),
    (`NonzeroReplayTest.argumentsTyped, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.delay, []),
    (`NonzeroReplayTest.delayEqual, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.delayReduction, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.values, [`propext]),
    (`NonzeroReplayTest.valueEqual, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.liftPrefix, [`propext]),
    (`NonzeroReplayTest.major, [`propext]),
    (`NonzeroReplayTest.right, [`propext]),
    (`NonzeroReplayTest.rightTyped, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.matched, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.checked, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.argumentsReduce, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.majorType, [`propext]),
    (`NonzeroReplayTest.majorTyped, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.left, [`propext]),
    (`NonzeroReplayTest.leftTyped, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.majorSimulation, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.replay, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.leftDoesNotMatch, [`propext]),
    (`NonzeroReplayTest.differentDomainParameters, [`propext]),
    (`NonzeroReplayTest.differentRelationParameters, [`propext]),
    (`NonzeroReplayTest.allCapturesChange, [`propext]),
    (`NonzeroReplayTest.retainedReplay, [`Quot.sound, `propext]),
    (`NonzeroReplayTest.etaConstructor, [`Quot.sound, `propext])]
  unless roots.length == manifests.length do throwError "nonzero-replay manifest count changed"
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.quot_inj,
    `Lean4Lean.VEnv.IsDefEqU.weakN_iff, `Lean4Lean.VEnv.HasType.weakN_iff,
    `Lean4Lean.VEnv.NormalEq.weakN_iff, `Lean4Lean.VEnv.NormalEq.weakN_inv_DFC,
    `Lean4Lean.VEnv.NormalEq.trans, `Lean4Lean.VEnv.ParRed.weakN_inv,
    `Lean4Lean.TrProj, `Classical.choice]
  let environment ← getEnv
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing nonzero-replay manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new nonzero-replay axiom {root}"
    let some proof := info.value? | throwError "missing nonzero-replay proof {root}"
    if proof.hasSorry then throwError "direct nonzero-replay admission {root}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut axioms : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden nonzero-replay dependency {name} in {root}"
      let some declaration := environment.find? name
        | throwError "missing nonzero-replay dependency {name} in {root}"
      if declaration matches .axiomInfo _ then axioms := axioms.push name
      if declaration.type.hasSorry then throwError "admitted nonzero-replay type {name} in {root}"
      pending := pending ++ declaration.type.getUsedConstants
      if let .inductInfo ii := declaration then pending := pending ++ ii.ctors.toArray
      if let some value := declaration.value? then
        if value.hasSorry then throwError "nonzero-replay admission {name} in {root}"
        pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "nonzero-replay traversal exceeded bound"
    unless axioms.all (fun n => [`propext, `Quot.sound].contains n) do
      throwError "unexpected nonzero-replay axiom in {root}: {repr axioms}"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "nonzero-replay axiom manifest changed for {root}: {repr axioms}"
    let required : List Name :=
      if root == `Lean4Lean.VEnv.IsDefEqU.rigidApp_forallE_inv then [`Lean4Lean.VEnv.Model.forallE_rigid, `Lean4Lean.VEnv.WF.soundEnv, `Lean4Lean.VEnv.IsDefEqU.of_l]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_expose, `Lean4Lean.VEnv.IsDefEqU.rigidApp_forallE_inv, `Lean4Lean.VEnv.Model.quotient_rigid, `Lean4Lean.VEnv.IsDefEq.isType]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_nonzero_extra then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor, (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotNonzeroExtra") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedConstructorShape"), (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotHereditaryExtra") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "reduceMatchedCaptures"), `Lean4Lean.VEnv.HasType.matches_inv, `Lean4Lean.VEnv.ParRed.extra, `Lean4Lean.VEnv.quotLift_inv, `Lean4Lean.VEnv.quotMk_inv, `Lean4Lean.VEnv.IsDefEqU.trans, `Lean4Lean.VEnv.NormalEq.appDF, `Lean4Lean.VEnv.QuotPropReduction.Steps.core]
      else if root == `NonzeroReplayTest.replay then [`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_nonzero_extra, `NonzeroReplayTest.majorSimulation, `NonzeroReplayTest.checked, `NonzeroReplayTest.argumentsReduce, `NonzeroReplayTest.leftTyped, `QuotMajorExposureTest.quotientEnvironmentWF]
      else if root == `NonzeroReplayTest.retainedReplay then [`NonzeroReplayTest.replay, `Lean4Lean.VEnv.QuotPropReduction.Steps.weakN, `Lean4Lean.VEnv.NormalEq.weakN]
      else if root == `NonzeroReplayTest.etaConstructor then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor, `QuotMajorExposureTest.majorNormal, `QuotMajorExposureTest.etaNormal]
      else []
    unless required.all visited.contains do
      throwError "nonzero-replay proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

  logInfo m!"NONZERO_REPLAY_AUDIT_COMPLETE {roots.length}"

end NonzeroReplayAudit
