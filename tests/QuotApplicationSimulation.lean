import Lean4Lean.Theory.Typing.QuotApplicationSimulation
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

namespace ApplicationSimulationTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.QuotPropReduction
open QuotMajorExposureTest NonzeroReplayTest
open private applicationArgumentTyped from Lean4Lean.Theory.Typing.QuotInjectivity

local instance : Params := quotientEnvironmentWF.reductionParams 0

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
  | zero => exact .refl typed
  | succ depth induction =>
    cases type <;> try exact .refl typed
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := typed.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    exact .etaL typed (induction ⟨contextWF, _, domainTyped⟩
      (etaBody_hasType quotientEnvironmentWF.ordered typed))


def prefixType : VExpr := .forallE
  (.app (.app (.const ``Quot [one]) (.bvar 5)) (.bvar 4)) (.bvar 4)

theorem prefixTyped : quotientEnvironment.HasType 0 locals liftPrefix prefixType := by
  obtain ⟨_, _, liftRegistered, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
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
  simpa [HasType, liftPrefix, prefixType, levels, original, VExpr.liftN, VExpr.inst, VExpr.instVar] using fifth.hasType.2

def constructorHeadType : VExpr := quotMkConst.type.instL [one]
def constructorArguments : List VExpr :=
  [values (.inr (some (some none))), values (.inr (some none)), values (.inr none)]
def etaMajor : VExpr := applyArguments
  (etaTree 3 (.const ``Quot.mk [one]) constructorHeadType) constructorArguments

theorem constructorHeadTyped : quotientEnvironment.HasType 0 locals
    (.const ``Quot.mk [one]) constructorHeadType := by
  exact HasType.const (quotientEnvironmentWF.quotientObjects quotientRegistered).2.2.2.1
    (by simp [one, VLevel.WF]) rfl

theorem etaMajorNormal : NormalEq locals etaMajor major := by
  have argumentsNormal : List.Forall₂ (NormalEq locals) constructorArguments constructorArguments :=
    .cons (.refl (valueEqual _).hasType.1)
      (.cons (.refl (valueEqual _).hasType.1) (.cons (.refl (valueEqual _).hasType.1) .nil))
  exact (normal_spine_congr (function := .const ``Quot.mk [one])
    (arguments := constructorArguments) localsWF majorTyped
    ((etaTreeNormal localsWF constructorHeadTyped 3).symm localsWF) argumentsNormal).symm localsWF

def etaPrefix : VExpr := etaTree 1 liftPrefix prefixType

theorem etaPrefixNormal : NormalEq locals etaPrefix liftPrefix := etaTreeNormal localsWF prefixTyped 1

def etaLeft : VExpr := .app etaPrefix etaMajor

theorem etaLeftNormal : NormalEq locals etaLeft right := by
  have argumentTyped := applicationArgumentTyped quotientEnvironmentWF localsWF rightTyped prefixTyped
  exact .appDF
    (((etaPrefixNormal.defeq localsWF).of_r quotientEnvironmentWF localsWF prefixTyped).hasType.1)
    prefixTyped
    (((etaMajorNormal.defeq localsWF).of_r quotientEnvironmentWF localsWF argumentTyped).hasType.1)
    argumentTyped etaPrefixNormal etaMajorNormal

theorem etaLeftTyped : quotientEnvironment.HasType 0 locals etaLeft (.bvar 3) :=
  ((etaLeftNormal.defeq localsWF).of_r quotientEnvironmentWF localsWF rightTyped).hasType.1

theorem neitherMatches :
    (∀ {ls captures}, ¬ quotLiftPattern.Matches etaLeft ls captures) ∧
    (∀ {ls captures}, ¬ (Pattern.varN (.const ``Quot.mk) 3).Matches etaMajor ls captures) := by
  constructor
  · intro ls captures h
    cases h with
    | app h _ => cases h
  · intro ls captures h
    cases h with
    | var h => cases h with
      | var h => cases h with
        | var h => cases h

theorem actualNonzeroStep : ParRed locals right (.app (.bvar 2) (.bvar 0)) :=
  .extra (.quot quotientRegistered) matched checked argumentsReduce

theorem arbitraryFunctionExtra : ∃ joined,
    Steps quotientEnvironmentWF 0 locals etaLeft joined ∧
    NormalEq locals joined (.app (.bvar 2) (.bvar 0)) ∧
    quotientEnvironment.HasType 0 locals joined (.bvar 3) ∧
    quotientEnvironment.HasType 0 locals (.app (.bvar 2) (.bvar 0)) (.bvar 3) :=
  normal_parRed_join quotientRegistered localsWF etaLeftTyped etaLeftNormal actualNonzeroStep

theorem finiteExtraBeta : ∃ joined,
    Steps quotientEnvironmentWF 0 locals etaLeft joined ∧
    NormalEq locals joined (.app (.bvar 2) (.bvar 0)) ∧
    quotientEnvironment.HasType 0 locals joined (.bvar 3) ∧
    quotientEnvironment.HasType 0 locals (.app (.bvar 2) (.bvar 0)) (.bvar 3) :=
  normal_parRedS_join quotientRegistered localsWF etaLeftTyped etaLeftNormal
    (.tail (.tail .rfl (.extra (.quot quotientRegistered) matched checked (fun _ => .rfl)))
      (.app (argumentsReduce (.inl (some none))) (argumentsReduce (.inr none))))

theorem retainedSimulation : ∃ joined,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) etaLeft.lift joined ∧
    NormalEq (.bvar 5 :: locals) joined (.app (.bvar 3) (.bvar 1)) ∧
    quotientEnvironment.HasType 0 (.bvar 5 :: locals) joined (.bvar 4) ∧
    quotientEnvironment.HasType 0 (.bvar 5 :: locals) (.app (.bvar 3) (.bvar 1)) (.bvar 4) := by
  exact normal_parRed_join quotientRegistered
    (show OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) from
      ⟨localsWF, _, argumentsTyped (.inl (some (some (some (some none)))))⟩)
    (etaLeftTyped.weakN quotientEnvironmentWF.ordered Ctx.LiftN.one)
    (etaLeftNormal.weakN Ctx.LiftN.one) (actualNonzeroStep.weakN Ctx.LiftN.one)


theorem beneathLambda : ∃ joined,
    Steps quotientEnvironmentWF 0 locals (.lam (.bvar 5) etaLeft.lift) joined ∧
    NormalEq locals joined (.lam (.bvar 5) (.app (.bvar 3) (.bvar 1))) ∧
    quotientEnvironment.HasType 0 locals joined (.forallE (.bvar 5) (.bvar 4)) ∧
    quotientEnvironment.HasType 0 locals (.lam (.bvar 5) (.app (.bvar 3) (.bvar 1)))
      (.forallE (.bvar 5) (.bvar 4)) := by
  have domainTyped := argumentsTyped (.inl (some (some (some (some none)))))
  exact normal_parRed_join quotientRegistered localsWF
    (domainTyped.lam (etaLeftTyped.weak quotientEnvironmentWF.ordered))
    (.lamDF domainTyped domainTyped (etaLeftNormal.weakN Ctx.LiftN.one))
    (.lam .rfl (actualNonzeroStep.weakN Ctx.LiftN.one))

def identity : VExpr := .lam (.bvar 5) (.bvar 0)
def identityType : VExpr := .forallE (.bvar 5) (.bvar 6)

theorem identityTyped : quotientEnvironment.HasType 0 locals identity identityType :=
  (argumentsTyped (.inl (some (some (some (some none)))))).lam (HasType.bvar .zero)

theorem betaJoin : ∃ joined,
    Steps quotientEnvironmentWF 0 locals
      (.app (etaTree 1 identity identityType) (.bvar 0)) joined ∧
    NormalEq locals joined (.bvar 0) ∧
    quotientEnvironment.HasType 0 locals joined (.bvar 5) ∧
    quotientEnvironment.HasType 0 locals (.bvar 0) (.bvar 5) := by
  have normal : NormalEq locals (.app (etaTree 1 identity identityType) (.bvar 0))
      (.app identity (.bvar 0)) :=
    .appDF (((etaTreeNormal localsWF identityTyped 1).defeq localsWF).of_r
      quotientEnvironmentWF localsWF identityTyped).hasType.1 identityTyped
      (argumentsTyped (.inr none)) (argumentsTyped (.inr none))
      (etaTreeNormal localsWF identityTyped 1) (.refl (argumentsTyped (.inr none)))
  have typed := ((normal.defeq localsWF).of_r quotientEnvironmentWF localsWF
    (identityTyped.app (argumentsTyped (.inr none)))).hasType.1
  exact normal_parRed_join quotientRegistered localsWF typed normal (.beta .rfl .rfl)

end ApplicationSimulationTest

namespace ObstructionSimulationTest
open private inert inert.not_constructor from Lean4Lean.Theory.Typing.QuotConfluenceObstruction
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.QuotPropReduction
open Lean4Lean.VEnv.QuotConfluenceObstruction QuotMajorExposureTest

local instance : Params := quotientEnvironmentWF.reductionParams 0

theorem repairedCounterexample : ∃ joined,
    Steps quotientEnvironmentWF 0 locals neutral joined ∧ NormalEq locals joined reduced ∧
    quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
    quotientEnvironment.HasType 0 locals reduced (.sort .zero) :=
  normal_parRed_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    (neutralTyped quotientEnvironmentWF quotientRegistered)
    (normalEq quotientEnvironmentWF quotientRegistered) (reduction quotientEnvironmentWF quotientRegistered)


theorem beneathForall : ∃ joined,
    Steps quotientEnvironmentWF 0 locals (.forallE (.sort .zero) neutral.lift) joined ∧
    NormalEq locals joined (.forallE (.sort .zero) reduced.lift) ∧
    quotientEnvironment.HasType 0 locals joined (.sort (.imax (.succ .zero) .zero)) ∧
    quotientEnvironment.HasType 0 locals (.forallE (.sort .zero) reduced.lift)
      (.sort (.imax (.succ .zero) .zero)) := by
  have wf := localsWF quotientEnvironmentWF quotientRegistered
  have typed := neutralTyped quotientEnvironmentWF quotientRegistered
  have bodies := (normalEq quotientEnvironmentWF quotientRegistered).weakN
    (Ctx.LiftN.one (A := .sort .zero))
  exact normal_parRed_join quotientRegistered wf
    ((HasType.sort (by trivial)).forallE (typed.weak quotientEnvironmentWF.ordered))
    (.forallEDF (HasType.sort (by trivial)) (.refl (HasType.sort (by trivial)))
      (typed.weak quotientEnvironmentWF.ordered) bodies)
    (.forallE .rfl ((reduction quotientEnvironmentWF quotientRegistered).weakN Ctx.LiftN.one))


/-- Decidable closed-name membership avoids the newer library string simp
proof's incidental choice dependency in the historical obstruction helper. -/
theorem inertStep {context source target} (step : ParRed context source target)
    (shape : inert source) : target = source := by
  induction step with
  | bvar | sort | const => rfl
  | app _ _ functionIH argumentIH => rw [functionIH shape.1, argumentIH shape.2]
  | lam | forallE => cases shape
  | beta => cases shape.1
  | extra rule matched _ _ =>
    exfalso
    cases rule with
    | delta closed definitionRegistered =>
      cases matched
      exact quotientEnvironmentWF.rewriteMetadata.quotientNames definitionRegistered quotientRegistered
        ``Quot.lift (by decide) shape
    | quot =>
      cases matched with
      | app _ majorMatched => exact inert.not_constructor shape.2 majorMatched

theorem neutralPath (steps : ParRedS locals neutral target) : target = neutral := by
  induction steps with
  | rfl => rfl
  | tail _ step induction =>
    subst induction
    exact inertStep step (by trivial)

theorem originalTargetStillRefuted : ¬∃ joined,
    ParRedS locals neutral joined ∧ NormalEq locals joined reduced := by
  rintro ⟨joined, steps, compared⟩
  have same := neutralPath steps
  subst joined
  exact not_normalEq_reduced quotientEnvironmentWF quotientRegistered compared

end ObstructionSimulationTest

namespace ApplicationSimulationAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.QuotPropReduction.normal_quot_nonzero_root,
    `Lean4Lean.VEnv.QuotPropReduction.normal_quot_root,
    (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidQuotJoin"),
    `Lean4Lean.VEnv.QuotPropReduction.normal_quot_join,
    `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_quot_extra,
    (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedLiftLevels"),
    `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app,
    `Lean4Lean.VEnv.QuotPropReduction.normal_core_simulates,
    `Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join,
    `Lean4Lean.VEnv.QuotPropReduction.normal_parRedS_join,
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
    `NonzeroReplayTest.etaConstructor,
    `ApplicationSimulationTest.etaTree,
    `ApplicationSimulationTest.etaTreeNormal,
    `ApplicationSimulationTest.prefixType,
    `ApplicationSimulationTest.prefixTyped,
    `ApplicationSimulationTest.constructorHeadType,
    `ApplicationSimulationTest.constructorArguments,
    `ApplicationSimulationTest.etaMajor,
    `ApplicationSimulationTest.constructorHeadTyped,
    `ApplicationSimulationTest.etaMajorNormal,
    `ApplicationSimulationTest.etaPrefix,
    `ApplicationSimulationTest.etaPrefixNormal,
    `ApplicationSimulationTest.etaLeft,
    `ApplicationSimulationTest.etaLeftNormal,
    `ApplicationSimulationTest.etaLeftTyped,
    `ApplicationSimulationTest.neitherMatches,
    `ApplicationSimulationTest.actualNonzeroStep,
    `ApplicationSimulationTest.arbitraryFunctionExtra,
    `ApplicationSimulationTest.finiteExtraBeta,
    `ApplicationSimulationTest.retainedSimulation,
    `ApplicationSimulationTest.beneathLambda,
    `ApplicationSimulationTest.identity,
    `ApplicationSimulationTest.identityType,
    `ApplicationSimulationTest.identityTyped,
    `ApplicationSimulationTest.betaJoin,
    `ObstructionSimulationTest.repairedCounterexample,
    `ObstructionSimulationTest.beneathForall,
    `ObstructionSimulationTest.inertStep,
    `ObstructionSimulationTest.neutralPath,
    `ObstructionSimulationTest.originalTargetStillRefuted]

  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_nonzero_root, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_root, [`Quot.sound, `propext]),
    ((Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidQuotJoin"), [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_join, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_quot_extra, [`Quot.sound, `propext]),
    ((Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedLiftLevels"), [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_core_simulates, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_parRedS_join, [`Quot.sound, `propext]),
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
    (`NonzeroReplayTest.etaConstructor, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.etaTree, [`propext]),
    (`ApplicationSimulationTest.etaTreeNormal, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.prefixType, []),
    (`ApplicationSimulationTest.prefixTyped, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.constructorHeadType, [`propext]),
    (`ApplicationSimulationTest.constructorArguments, [`propext]),
    (`ApplicationSimulationTest.etaMajor, [`propext]),
    (`ApplicationSimulationTest.constructorHeadTyped, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.etaMajorNormal, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.etaPrefix, [`propext]),
    (`ApplicationSimulationTest.etaPrefixNormal, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.etaLeft, [`propext]),
    (`ApplicationSimulationTest.etaLeftNormal, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.etaLeftTyped, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.neitherMatches, [`propext]),
    (`ApplicationSimulationTest.actualNonzeroStep, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.arbitraryFunctionExtra, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.finiteExtraBeta, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.retainedSimulation, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.beneathLambda, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.identity, []),
    (`ApplicationSimulationTest.identityType, []),
    (`ApplicationSimulationTest.identityTyped, [`Quot.sound, `propext]),
    (`ApplicationSimulationTest.betaJoin, [`Quot.sound, `propext]),
    (`ObstructionSimulationTest.repairedCounterexample, [`Quot.sound, `propext]),
    (`ObstructionSimulationTest.beneathForall, [`Quot.sound, `propext]),
    (`ObstructionSimulationTest.inertStep, [`Quot.sound, `propext]),
    (`ObstructionSimulationTest.neutralPath, [`Quot.sound, `propext]),
    (`ObstructionSimulationTest.originalTargetStillRefuted, [`Quot.sound, `propext])]
  unless roots.length == manifests.length do throwError "application-simulation manifest count changed"
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.quot_inj,
    `Lean4Lean.VEnv.IsDefEqU.weakN_iff, `Lean4Lean.VEnv.HasType.weakN_iff,
    `Lean4Lean.VEnv.NormalEq.weakN_iff, `Lean4Lean.VEnv.NormalEq.weakN_inv_DFC,
    `Lean4Lean.VEnv.NormalEq.trans, `Lean4Lean.VEnv.ParRed.weakN_inv,
    `Lean4Lean.TrProj, `Classical.choice]
  let environment ← getEnv
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing application-simulation manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new application-simulation axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing application-simulation proof {root}"
    if proof.hasSorry then throwError "direct application-simulation admission {root}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut axioms : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden application-simulation dependency {name} in {root}"
      let some declaration := environment.find? name
        | throwError "missing application-simulation dependency {name} in {root}"
      if declaration matches .axiomInfo _ then axioms := axioms.push name
      if declaration.type.hasSorry then throwError "admitted application-simulation type {name} in {root}"
      pending := pending ++ declaration.type.getUsedConstants
      if let .inductInfo ii := declaration then pending := pending ++ ii.ctors.toArray
      if let some value := declaration.value? (allowOpaque := true) then
        if value.hasSorry then throwError "application-simulation admission {name} in {root}"
        pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "application-simulation traversal exceeded bound"
    unless axioms.all (fun n => [`propext, `Quot.sound].contains n) do
      throwError "unexpected application-simulation axiom in {root}: {repr axioms}"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "application-simulation axiom manifest changed for {root}: {repr axioms}"
    let required : List Name :=
      if root == `Lean4Lean.VEnv.QuotPropReduction.normal_quot_nonzero_root then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_major_constructor, `Lean4Lean.VEnv.IsDefEqU.trans, `Lean4Lean.VEnv.ParRed.extra, `Lean4Lean.VEnv.QuotPropReduction.Steps.core]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_quot_root then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_nonzero_root, `Lean4Lean.VEnv.QuotPropReduction.normal_quot_prop_root]
      else if root == (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidQuotJoin") then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_root, `Lean4Lean.VEnv.QuotPropReduction.RigidSpine.rec, `Lean4Lean.Pattern.Check.OK.weakN]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_quot_join then [(Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidQuotJoin"), `Lean4Lean.VEnv.QuotPropReduction.normal_spine_expose_applications]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_quot_extra then [`Lean4Lean.VEnv.QuotPropReduction.normal_quot_join, (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotHereditaryExtra") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "reduceMatchedCaptures"), `Lean4Lean.VEnv.HasType.matches_inv, `Lean4Lean.VEnv.IsDefEqU.trans, `Lean4Lean.VEnv.ParRed.extra]
      else if root == (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedLiftLevels") then [`Lean4Lean.VEnv.quotLift_inv, `Lean4Lean.VEnv.WF.quotientObjects]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app then [`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_quot_extra, (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotApplicationSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "matchedLiftLevels"), `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_congr, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_beta]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_core_simulates then [`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.refl, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.sortDF, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.constDF, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.lamDF, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.forallEDF, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.etaL, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.etaR, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.proofIrrel]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join then [`Lean4Lean.VEnv.QuotPropReduction.normal_core_simulates, `Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.typed]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_parRedS_join then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `ReflTransGen.rec]
      else if root == `ApplicationSimulationTest.arbitraryFunctionExtra then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `ApplicationSimulationTest.etaLeftNormal, `ApplicationSimulationTest.actualNonzeroStep, `ApplicationSimulationTest.etaMajorNormal]
      else if root == `ApplicationSimulationTest.finiteExtraBeta then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRedS_join, `Lean4Lean.VEnv.ParRed.extra, `Lean4Lean.VEnv.ParRed.app, `NonzeroReplayTest.argumentsReduce]
      else if root == `ApplicationSimulationTest.retainedSimulation then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.NormalEq.weakN, `Lean4Lean.VEnv.ParRed.weakN]
      else if root == `ApplicationSimulationTest.beneathLambda then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.NormalEq.lamDF, `Lean4Lean.VEnv.ParRed.lam]
      else if root == `ApplicationSimulationTest.betaJoin then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.NormalEq.etaL, `Lean4Lean.VEnv.ParRed.beta]
      else if root == `ObstructionSimulationTest.repairedCounterexample then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.QuotConfluenceObstruction.normalEq, `Lean4Lean.VEnv.QuotConfluenceObstruction.reduction, `QuotMajorExposureTest.quotientEnvironmentWF]
      else if root == `ObstructionSimulationTest.beneathForall then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.NormalEq.forallEDF, `Lean4Lean.VEnv.ParRed.forallE]
      else if root == `ObstructionSimulationTest.originalTargetStillRefuted then [`Lean4Lean.VEnv.QuotConfluenceObstruction.not_normalEq_reduced, `ObstructionSimulationTest.neutralPath, `ObstructionSimulationTest.inertStep]
      else []
    unless required.all visited.contains do
      throwError "application-simulation proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

  logInfo m!"APPLICATION_SIMULATION_AUDIT_COMPLETE {roots.length}"

end ApplicationSimulationAudit
