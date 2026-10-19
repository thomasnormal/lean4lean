import Lean4Lean.Theory.Typing.QuotNormalExtra
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotNormalExtraTest
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

theorem delayEqual {type value : VExpr}
    (typed : quotientEnvironment.HasType 0 locals value type) :
    quotientEnvironment.IsDefEq 0 locals (delay type value) value type := by
  simpa [delay, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) typed

theorem delayReduction (type value : VExpr) : ParRed locals (delay type value) value := by
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := type :: locals)) (ParRed.rfl (e := value)))

def originalValues : quotLiftPattern.Path → VExpr
  | .inl none => .bvar 2
  | .inl (some none) => .bvar 3
  | .inl (some (some none)) => .sort .zero
  | .inl (some (some (some none))) => .bvar 4
  | .inl (some (some (some (some none)))) => .bvar 5
  | .inr none => .bvar 1
  | .inr (some none) => .bvar 4
  | .inr (some (some none)) => .bvar 5

def argumentTypes : quotLiftPattern.Path → VExpr
  | .inl none => respectType.liftN 3
  | .inl (some none) => .forallE (.bvar 5) (.sort .zero)
  | .inl (some (some none)) => .sort (.succ .zero)
  | .inl (some (some (some none))) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inl (some (some (some (some none)))) => .sort .zero
  | .inr none => .bvar 5
  | .inr (some none) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inr (some (some none)) => .sort .zero

theorem argumentsTyped (path : quotLiftPattern.Path) :
    quotientEnvironment.HasType 0 locals (originalValues path) (argumentTypes path) := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (unfold originalValues argumentTypes locals respectType functionType relationType Lean4Lean.VEnv.QuotConfluenceObstruction.quotient; type_tac)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (unfold originalValues argumentTypes locals respectType functionType relationType Lean4Lean.VEnv.QuotConfluenceObstruction.quotient; type_tac)

-- Every matched argument beta reduces. Constructor parameters use two
-- identity applications, so both actual equality checks are non-reflexive.
def delayedValues (path : quotLiftPattern.Path) : VExpr :=
  delay (argumentTypes path) (originalValues path)

def values : quotLiftPattern.Path → VExpr
  | .inr (some path) => delay (argumentTypes (.inr (some path))) (delayedValues (.inr (some path)))
  | path => delayedValues path

theorem valueEqual (path : quotLiftPattern.Path) :
    quotientEnvironment.IsDefEq 0 locals (values path) (originalValues path) (argumentTypes path) := by
  rcases path with path | path
  · cases path <;> exact delayEqual (argumentsTyped _)
  · cases path with
    | none => exact delayEqual (argumentsTyped _)
    | some path => exact (delayEqual (delayEqual (argumentsTyped _)).hasType.1).trans (delayEqual (argumentsTyped _))

def sourceAt (sourceUniverse constructorUniverse : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, .succ .zero])
    (values (.inl (some (some (some (some none)))))))
    (values (.inl (some (some (some none))))))
    (values (.inl (some (some none)))))
    (values (.inl (some none)))) (values (.inl none)))
    (.app (.app (.app (.const ``Quot.mk [constructorUniverse])
      (values (.inr (some (some none))))) (values (.inr (some none))))
      (values (.inr none)))

def source : VExpr := sourceAt .zero .zero

theorem sourceAtTyped {sourceUniverse constructorUniverse : VLevel}
    (sourceWF : sourceUniverse.WF 0) (constructorWF : constructorUniverse.WF 0)
    (sourceZero : sourceUniverse ≈ .zero) (constructorZero : constructorUniverse ≈ .zero) :
    quotientEnvironment.HasType 0 locals (sourceAt sourceUniverse constructorUniverse) (.sort .zero) := by
  obtain ⟨_, _, liftRegistered, constructorRegistered, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF liftRegistered (ls := [.zero, .succ .zero])
    (ls' := [sourceUniverse, .succ .zero]) (by simp [VLevel.WF])
    (by simpa [VLevel.WF] using sourceWF) (by rfl) (.cons sourceZero.symm (.cons rfl .nil)) (Γ := locals)
  simp [quotLiftConst, VExpr.instL, VLevel.inst] at head
  have first := head.appDF (valueEqual (.inl (some (some (some (some none)))))).symm
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.appDF (valueEqual (.inl (some (some (some none))))).symm
  simp [VExpr.inst, VExpr.instVar] at second
  have third := second.appDF (valueEqual (.inl (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at third
  have fourth := third.appDF (valueEqual (.inl (some none))).symm
  simp [VExpr.inst, VExpr.instVar] at fourth
  have fifth := fourth.appDF (valueEqual (.inl none)).symm
  simp [VExpr.inst] at fifth
  have ctor := IsDefEq.constDF constructorRegistered (ls := [.zero])
    (ls' := [constructorUniverse]) (by simp [VLevel.WF])
    (by simpa using constructorWF) (by rfl) (.cons constructorZero.symm .nil) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at ctor
  have ctorFirst := ctor.appDF (valueEqual (.inr (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at ctorFirst
  have ctorSecond := ctorFirst.appDF (valueEqual (.inr (some none))).symm
  simp [VExpr.inst, VExpr.instVar, VExpr.inst_lift] at ctorSecond
  have ctorFinal := ctorSecond.appDF (valueEqual (.inr none)).symm
  simpa [HasType, VExpr.liftN, sourceAt, originalValues, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    (fifth.appDF ctorFinal).hasType.2

theorem sourceTyped : quotientEnvironment.HasType 0 locals source (.sort .zero) :=
  sourceAtTyped (by trivial) (by trivial) rfl rfl

theorem matchedAt (sourceUniverse constructorUniverse : VLevel) :
    quotLiftPattern.Matches (sourceAt sourceUniverse constructorUniverse) [sourceUniverse, .succ .zero] values := by
  have liftMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [sourceUniverse, .succ .zero])
    |>.var (a' := values (.inl (some (some (some (some none))))))
    |>.var (a' := values (.inl (some (some (some none)))))
    |>.var (a' := values (.inl (some (some none))))
    |>.var (a' := values (.inl (some none))) |>.var (a' := values (.inl none))
  have ctorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [constructorUniverse])
    |>.var (a' := values (.inr (some (some none))))
    |>.var (a' := values (.inr (some none))) |>.var (a' := values (.inr none))
  rw [(_ : values = _)]
  · exact liftMatched.app ctorMatched
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem matched : quotLiftPattern.Matches source [.zero, .succ .zero] values := matchedAt .zero .zero

theorem checked (levels : List VLevel) :
    quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 locals) levels values :=
  ⟨((valueEqual (.inl (some (some (some (some none)))))).trans
      (valueEqual (.inr (some (some none)))).symm).toU,
    ((valueEqual (.inl (some (some (some none))))).trans
      (valueEqual (.inr (some none))).symm).toU, trivial⟩

theorem argumentsReduce (path : quotLiftPattern.Path) : ParRed locals (values path) (originalValues path) := by
  rcases path with path | path
  · cases path <;> exact delayReduction _ _
  · cases path with
    | none => exact delayReduction _ _
    | some path =>
      simpa [values, delayedValues, delay, VExpr.inst, VExpr.instVar] using
        (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := argumentTypes (.inr (some path)) :: locals))
          (delayReduction (argumentTypes (.inr (some path))) (originalValues (.inr (some path)))))

def etaFunction : VExpr := .lam (.bvar 5)
  (.app (values (.inl (some none))).lift (.bvar 0))

theorem appNormal {context : List VExpr} {function function' argument argument' type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context (.app function argument) type)
    (functions : NormalEq context function function') (arguments : NormalEq context argument argument') :
    NormalEq context (.app function argument) (.app function' argument') := by
  obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv quotientEnvironmentWF.ordered contextWF
  exact .appDF functionTyped
    ((functions.defeq contextWF).of_l quotientEnvironmentWF contextWF functionTyped).hasType.2
    argumentTyped ((arguments.defeq contextWF).of_l quotientEnvironmentWF contextWF argumentTyped).hasType.2
    functions arguments

theorem etaFunctionNormal : NormalEq locals etaFunction (values (.inl (some none))) :=
  .etaL (valueEqual (.inl (some none))).hasType.1
    (.refl (etaBody_hasType quotientEnvironmentWF.ordered (valueEqual (.inl (some none))).hasType.1))

theorem etaFunctionEqual : quotientEnvironment.IsDefEq 0 locals (.bvar 3) etaFunction
    (.forallE (.bvar 5) (.sort .zero)) :=
  (valueEqual (.inl (some none))).symm.trans
    ((etaFunctionNormal.defeq (localsWF quotientEnvironmentWF quotientRegistered)).symm.of_l
      quotientEnvironmentWF (localsWF quotientEnvironmentWF quotientRegistered)
      (valueEqual (.inl (some none))).hasType.1)

-- The left function has a different eta shape. Its simulation follows EVERY
-- actual core successor of the delayed right function capture.
theorem etaFunctionSimulation : CoreSimulates quotientEnvironmentWF 0 locals
    etaFunction (values (.inl (some none))) :=
  CoreSimulates.etaL (localsWF quotientEnvironmentWF quotientRegistered)
    (valueEqual (.inl (some none))).hasType.1
    (CoreSimulates.refl
      (show OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) from
        ⟨localsWF quotientEnvironmentWF quotientRegistered, _,
          argumentsTyped (.inl (some (some (some (some none)))))⟩)
      (etaBody_hasType quotientEnvironmentWF.ordered (valueEqual (.inl (some none))).hasType.1))

def leftAt (sourceUniverse : VLevel) (major : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, .succ .zero])
    (values (.inl (some (some (some (some none)))))))
    (values (.inl (some (some (some none))))))
    (values (.inl (some (some none))))) etaFunction) (values (.inl none))) major

theorem leftAtTyped {sourceUniverse : VLevel}
    (sourceWF : sourceUniverse.WF 0) (sourceZero : sourceUniverse ≈ .zero)
    {major : VExpr} (typed : quotientEnvironment.HasType 0 locals major majorType) :
    quotientEnvironment.HasType 0 locals (leftAt sourceUniverse major) (.sort .zero) := by
  obtain ⟨_, _, liftRegistered, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF liftRegistered (ls := [.zero, .succ .zero])
    (ls' := [sourceUniverse, .succ .zero]) (by simp [VLevel.WF])
    (by simpa [VLevel.WF] using sourceWF) (by rfl) (.cons sourceZero.symm (.cons rfl .nil)) (Γ := locals)
  simp [quotLiftConst, VExpr.instL, VLevel.inst] at head
  have first := head.appDF (valueEqual (.inl (some (some (some (some none)))))).symm
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.appDF (valueEqual (.inl (some (some (some none))))).symm
  simp [VExpr.inst, VExpr.instVar] at second
  have third := second.appDF (valueEqual (.inl (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at third
  have fourth := third.appDF etaFunctionEqual
  simp [VExpr.inst, VExpr.instVar] at fourth
  have fifth := fourth.appDF (valueEqual (.inl none)).symm
  simp [VExpr.inst] at fifth
  simpa [HasType, VExpr.liftN, leftAt, originalValues, majorType, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    (fifth.appDF typed).hasType.2

def originalType : VExpr := delay (.sort (.succ .zero)) (.sort .zero)

theorem retainOriginalType {expression : VExpr}
    (typed : quotientEnvironment.HasType 0 locals expression (.sort .zero)) :
    quotientEnvironment.HasType 0 locals expression originalType :=
  (delayEqual (HasType.sort (by trivial))).symm.defeq typed

-- The left major is NEUTRAL; the right major is a constructor with different
-- parameters. All EIGHT right captures beta reduce, both checks are nontrivial,
-- the functions have different eta shapes, and all three universes differ.
theorem neutralPropExtra : ∃ joined,
    ParRed locals (sourceAt (.imax (.succ .zero) .zero) .zero) reduced ∧
    Steps quotientEnvironmentWF 0 locals (leftAt (.max .zero .zero) (.bvar 0)) joined ∧
    NormalEq locals joined reduced ∧
    quotientEnvironment.HasType 0 locals joined originalType ∧
    quotientEnvironment.HasType 0 locals reduced originalType := by
  exact CoreSimulates.quot_prop_extra quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered)
    (retainOriginalType (leftAtTyped (by trivial) ((zeroLike_iff _).mp rfl) majorTyped))
    (retainOriginalType (sourceAtTyped (by trivial) (by trivial) ((zeroLike_iff _).mp rfl) rfl))
    rfl (.refl (valueEqual (.inl (some (some (some (some none)))))).hasType.1)
    etaFunctionSimulation (matchedAt _ _) (checked _) argumentsReduce

theorem retainedDependentBinder : ∃ joined,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals)
      (leftAt (.max .zero .zero) (.bvar 0)).lift joined.lift ∧
    NormalEq (.bvar 5 :: locals) joined.lift reduced.lift ∧
    Steps quotientEnvironmentWF 0 locals (leftAt (.max .zero .zero) (.bvar 0)) joined ∧
    NormalEq locals joined reduced := by
  obtain ⟨joined, _, path, normal, _, _⟩ := neutralPropExtra
  have retainedPath := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  exact ⟨joined, retainedPath, retainedNormal,
    by simpa only [VExpr.inst_lift] using retainedPath.instN Ctx.InstN.zero (argumentsTyped (.inr none)),
    by simpa only [VExpr.inst_lift] using retainedNormal.instN (argumentsTyped (.inr none)) Ctx.InstN.zero⟩

theorem neutralNormal : NormalEq locals (leftAt (.max .zero .zero) (.bvar 0))
    (sourceAt (.imax (.succ .zero) .zero) .zero) := by
  have contextWF := localsWF quotientEnvironmentWF quotientRegistered
  have leftTyped := leftAtTyped (sourceUniverse := .max .zero .zero) (by trivial)
    ((zeroLike_iff _).mp rfl) majorTyped
  obtain ⟨_, _, p5, leftMajor⟩ := leftTyped.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p4, respect⟩ := p5.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p3, function⟩ := p4.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p2, target⟩ := p3.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p1, relation⟩ := p2.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, _, domain⟩ := p1.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, liftObject, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have heads : NormalEq locals (.const ``Quot.lift [.max .zero .zero, .succ .zero])
      (.const ``Quot.lift [.imax (.succ .zero) .zero, .succ .zero]) :=
    .constDF liftObject (by simp [VLevel.WF]) (by simp [VLevel.WF]) rfl
      (.cons (VLevel.equiv_def.mpr (by intro values; rfl)) (.cons rfl .nil))
  have n1 := appNormal contextWF p1 heads (.refl domain)
  have n2 := appNormal contextWF p2 n1 (.refl relation)
  have n3 := appNormal contextWF p3 n2 (.refl target)
  have n4 := appNormal contextWF p4 n3 etaFunctionNormal
  have n5 := appNormal contextWF p5 n4 (.refl respect)
  have rightTyped := sourceAtTyped (sourceUniverse := .imax (.succ .zero) .zero)
    (constructorUniverse := .zero) (by trivial) (by trivial) ((zeroLike_iff _).mp rfl) rfl
  obtain ⟨_, _, rightPrefix, rightMajor⟩ := rightTyped.app_inv quotientEnvironmentWF.ordered contextWF
  have rightPrefixAtLeft := ((n5.defeq contextWF).of_l quotientEnvironmentWF contextWF p5).hasType.2
  obtain ⟨⟨_, domains⟩, _⟩ := (rightPrefix.uniqU quotientEnvironmentWF contextWF rightPrefixAtLeft).forallE_inv
    quotientEnvironmentWF contextWF
  have alignedMajor := domains.defeq rightMajor
  have majorProposition := (majorTypeTyped quotientEnvironmentWF quotientRegistered).defeqU_l
    quotientEnvironmentWF contextWF (majorTyped.uniqU quotientEnvironmentWF contextWF leftMajor)
  exact .appDF p5 rightPrefixAtLeft leftMajor alignedMajor n5
    (.proofIrrel majorProposition leftMajor alignedMajor)

example : etaFunction ≠ values (.inl (some none)) := by intro equal; cases equal
example : originalType ≠ VExpr.sort .zero := by intro equal; cases equal

theorem neutralDoesNotMatch {levels : List VLevel} {captures : quotLiftPattern.Path → VExpr} :
    ¬quotLiftPattern.Matches (leftAt (.max .zero .zero) (.bvar 0)) levels captures := by
  intro matched
  cases matched with
  | app _ major => cases major

theorem allCapturesChange (path : quotLiftPattern.Path) : values path ≠ originalValues path := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (intro equal; cases equal)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (intro equal; cases equal)

theorem distinctDomainParameters : values (.inl (some (some (some (some none))))) ≠
    values (.inr (some (some none))) := by intro equal; cases equal

theorem distinctRelationParameters : values (.inl (some (some (some none)))) ≠
    values (.inr (some none)) := by intro equal; cases equal

namespace TypeSource

-- Here A is a TYPE, so the payload cannot be joined by proof irrelevance.
def quotient (domain relation : VExpr) : VExpr :=
  .app (.app (.const ``Quot [.succ .zero]) domain) relation

def locals : List VExpr :=
  quotient (.bvar 4) (.bvar 3) :: .bvar 3 :: respectType :: functionType :: relationType :: [.sort (.succ .zero)]

theorem contextWF : OnCtx locals (quotientEnvironment.IsType 0) := by
  have equal := equalityRegistered quotientEnvironmentWF quotientRegistered
  obtain ⟨_, _, _, _, quotientObject, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold locals quotient respectType functionType relationType
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩,
    _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩

def delay (type value : VExpr) : VExpr := .app (.lam type (.bvar 0)) value

theorem delayEqual {type value : VExpr}
    (typed : quotientEnvironment.HasType 0 locals value type) :
    quotientEnvironment.IsDefEq 0 locals (delay type value) value type := by
  simpa [delay, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    IsDefEq.beta (HasType.bvar .zero) typed

theorem delayReduction (type value : VExpr) : ParRed locals (delay type value) value := by
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := type :: locals)) (ParRed.rfl (e := value)))

def originalValues : quotLiftPattern.Path → VExpr
  | .inl none => .bvar 2
  | .inl (some none) => .bvar 3
  | .inl (some (some none)) => .sort .zero
  | .inl (some (some (some none))) => .bvar 4
  | .inl (some (some (some (some none)))) => .bvar 5
  | .inr none => .bvar 1
  | .inr (some none) => .bvar 4
  | .inr (some (some none)) => .bvar 5

def argumentTypes : quotLiftPattern.Path → VExpr
  | .inl none => respectType.liftN 3
  | .inl (some none) => .forallE (.bvar 5) (.sort .zero)
  | .inl (some (some none)) => .sort (.succ .zero)
  | .inl (some (some (some none))) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inl (some (some (some (some none)))) => .sort (.succ .zero)
  | .inr none => .bvar 5
  | .inr (some none) => .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  | .inr (some (some none)) => .sort (.succ .zero)

theorem argumentsTyped (path : quotLiftPattern.Path) :
    quotientEnvironment.HasType 0 locals (originalValues path) (argumentTypes path) := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (unfold originalValues argumentTypes locals respectType functionType relationType QuotNormalExtraTest.TypeSource.quotient; type_tac)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (unfold originalValues argumentTypes locals respectType functionType relationType QuotNormalExtraTest.TypeSource.quotient; type_tac)

-- Every matched argument beta reduces. Constructor parameters use two
-- identity applications, so both actual equality checks are non-reflexive.
def delayedValues (path : quotLiftPattern.Path) : VExpr :=
  delay (argumentTypes path) (originalValues path)

def values : quotLiftPattern.Path → VExpr
  | .inr (some path) => delay (argumentTypes (.inr (some path))) (delayedValues (.inr (some path)))
  | path => delayedValues path

theorem valueEqual (path : quotLiftPattern.Path) :
    quotientEnvironment.IsDefEq 0 locals (values path) (originalValues path) (argumentTypes path) := by
  rcases path with path | path
  · cases path <;> exact delayEqual (argumentsTyped _)
  · cases path with
    | none => exact delayEqual (argumentsTyped _)
    | some path => exact (delayEqual (delayEqual (argumentsTyped _)).hasType.1).trans (delayEqual (argumentsTyped _))

def sourceAt (sourceUniverse constructorUniverse : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, .succ .zero])
    (values (.inl (some (some (some (some none)))))))
    (values (.inl (some (some (some none))))))
    (values (.inl (some (some none)))))
    (values (.inl (some none)))) (values (.inl none)))
    (.app (.app (.app (.const ``Quot.mk [constructorUniverse])
      (values (.inr (some (some none))))) (values (.inr (some none))))
      (values (.inr none)))

def source : VExpr := sourceAt (.succ .zero) (.succ .zero)

theorem sourceAtTyped {sourceUniverse constructorUniverse : VLevel}
    (sourceWF : sourceUniverse.WF 0) (constructorWF : constructorUniverse.WF 0)
    (sourceZero : sourceUniverse ≈ .succ .zero) (constructorZero : constructorUniverse ≈ .succ .zero) :
    quotientEnvironment.HasType 0 locals (sourceAt sourceUniverse constructorUniverse) (.sort .zero) := by
  obtain ⟨_, _, liftRegistered, constructorRegistered, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF liftRegistered (ls := [.succ .zero, .succ .zero])
    (ls' := [sourceUniverse, .succ .zero]) (by simp [VLevel.WF])
    (by simpa [VLevel.WF] using sourceWF) (by rfl) (.cons sourceZero.symm (.cons rfl .nil)) (Γ := locals)
  simp [quotLiftConst, VExpr.instL, VLevel.inst] at head
  have first := head.appDF (valueEqual (.inl (some (some (some (some none)))))).symm
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.appDF (valueEqual (.inl (some (some (some none))))).symm
  simp [VExpr.inst, VExpr.instVar] at second
  have third := second.appDF (valueEqual (.inl (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at third
  have fourth := third.appDF (valueEqual (.inl (some none))).symm
  simp [VExpr.inst, VExpr.instVar] at fourth
  have fifth := fourth.appDF (valueEqual (.inl none)).symm
  simp [VExpr.inst] at fifth
  have ctor := IsDefEq.constDF constructorRegistered (ls := [.succ .zero])
    (ls' := [constructorUniverse]) (by simp [VLevel.WF])
    (by simpa using constructorWF) (by rfl) (.cons constructorZero.symm .nil) (Γ := locals)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at ctor
  have ctorFirst := ctor.appDF (valueEqual (.inr (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at ctorFirst
  have ctorSecond := ctorFirst.appDF (valueEqual (.inr (some none))).symm
  simp [VExpr.inst, VExpr.instVar, VExpr.inst_lift] at ctorSecond
  have ctorFinal := ctorSecond.appDF (valueEqual (.inr none)).symm
  simpa [HasType, VExpr.liftN, sourceAt, originalValues, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    (fifth.appDF ctorFinal).hasType.2

theorem sourceTyped : quotientEnvironment.HasType 0 locals source (.sort .zero) :=
  sourceAtTyped (by trivial) (by trivial) rfl rfl

theorem matchedAt (sourceUniverse constructorUniverse : VLevel) :
    quotLiftPattern.Matches (sourceAt sourceUniverse constructorUniverse) [sourceUniverse, .succ .zero] values := by
  have liftMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [sourceUniverse, .succ .zero])
    |>.var (a' := values (.inl (some (some (some (some none))))))
    |>.var (a' := values (.inl (some (some (some none)))))
    |>.var (a' := values (.inl (some (some none))))
    |>.var (a' := values (.inl (some none))) |>.var (a' := values (.inl none))
  have ctorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [constructorUniverse])
    |>.var (a' := values (.inr (some (some none))))
    |>.var (a' := values (.inr (some none))) |>.var (a' := values (.inr none))
  rw [(_ : values = _)]
  · exact liftMatched.app ctorMatched
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem matched : quotLiftPattern.Matches source [.succ .zero, .succ .zero] values := matchedAt (.succ .zero) (.succ .zero)

theorem checked (levels : List VLevel) :
    quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 locals) levels values :=
  ⟨((valueEqual (.inl (some (some (some (some none)))))).trans
      (valueEqual (.inr (some (some none)))).symm).toU,
    ((valueEqual (.inl (some (some (some none))))).trans
      (valueEqual (.inr (some none))).symm).toU, trivial⟩

theorem argumentsReduce (path : quotLiftPattern.Path) : ParRed locals (values path) (originalValues path) := by
  rcases path with path | path
  · cases path <;> exact delayReduction _ _
  · cases path with
    | none => exact delayReduction _ _
    | some path =>
      simpa [values, delayedValues, delay, VExpr.inst, VExpr.instVar] using
        (ParRed.beta (ParRed.rfl (e := .bvar 0) (Γ := argumentTypes (.inr (some path)) :: locals))
          (delayReduction (argumentTypes (.inr (some path))) (originalValues (.inr (some path)))))


def etaFunction : VExpr := .lam (.bvar 5)
  (.app (values (.inl (some none))).lift (.bvar 0))

theorem etaFunctionNormal : NormalEq locals etaFunction (values (.inl (some none))) :=
  .etaL (valueEqual (.inl (some none))).hasType.1
    (.refl (etaBody_hasType quotientEnvironmentWF.ordered (valueEqual (.inl (some none))).hasType.1))

theorem etaFunctionSimulation : CoreSimulates quotientEnvironmentWF 0 locals
    etaFunction (values (.inl (some none))) :=
  CoreSimulates.etaL contextWF (valueEqual (.inl (some none))).hasType.1
    (CoreSimulates.refl
      (show OnCtx (.bvar 5 :: locals) (quotientEnvironment.IsType 0) from
        ⟨contextWF, _, argumentsTyped (.inl (some (some (some (some none)))))⟩)
      (etaBody_hasType quotientEnvironmentWF.ordered (valueEqual (.inl (some none))).hasType.1))

def leftValues : quotLiftPattern.Path → VExpr
  | .inl (some none) => etaFunction
  | path => values path

def leftSource : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift [.succ .zero, .succ .zero])
    (leftValues (.inl (some (some (some (some none)))))))
    (leftValues (.inl (some (some (some none))))))
    (leftValues (.inl (some (some none)))))
    (leftValues (.inl (some none)))) (leftValues (.inl none)))
    (.app (.app (.app (.const ``Quot.mk [.succ .zero])
      (leftValues (.inr (some (some none))))) (leftValues (.inr (some none))))
      (leftValues (.inr none)))

theorem leftSourceTyped : quotientEnvironment.HasType 0 locals leftSource (.sort .zero) := by
  obtain ⟨_, _, respectPrefixTyped, majorTyped⟩ := sourceTyped.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, functionPrefixTyped, respectTyped⟩ := respectPrefixTyped.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, targetPrefixTyped, functionTyped⟩ := functionPrefixTyped.app_inv quotientEnvironmentWF.ordered contextWF
  have changedFunction := (etaFunctionNormal.defeq contextWF).symm.of_l quotientEnvironmentWF contextWF functionTyped
  have first := functionPrefixTyped.trans_l quotientEnvironmentWF contextWF
    (targetPrefixTyped.appDF changedFunction)
  have second := respectPrefixTyped.trans_l quotientEnvironmentWF contextWF (first.appDF respectTyped)
  have changed := sourceTyped.trans_l quotientEnvironmentWF contextWF (second.appDF majorTyped)
  simpa [source, sourceAt, leftSource, leftValues] using changed.hasType.2

theorem leftMatched : quotLiftPattern.Matches leftSource [.succ .zero, .succ .zero] leftValues := by
  have liftMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [.succ .zero, .succ .zero])
    |>.var (a' := leftValues (.inl (some (some (some (some none))))))
    |>.var (a' := leftValues (.inl (some (some (some none)))))
    |>.var (a' := leftValues (.inl (some (some none))))
    |>.var (a' := leftValues (.inl (some none))) |>.var (a' := leftValues (.inl none))
  have ctorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [.succ .zero])
    |>.var (a' := leftValues (.inr (some (some none))))
    |>.var (a' := leftValues (.inr (some none))) |>.var (a' := leftValues (.inr none))
  rw [(_ : leftValues = _)]
  · exact liftMatched.app ctorMatched
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem sourceNormal : NormalEq locals leftSource source := by
  obtain ⟨_, _, p5, major⟩ := leftSourceTyped.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p4, respect⟩ := p5.app_inv quotientEnvironmentWF.ordered contextWF
  obtain ⟨_, _, p3, _⟩ := p4.app_inv quotientEnvironmentWF.ordered contextWF
  have n4 := appNormal contextWF p4 (.refl p3) etaFunctionNormal
  have n5 := appNormal contextWF p5 n4 (.refl respect)
  exact appNormal contextWF leftSourceTyped n5 (.refl major)

theorem capturesNormal (path : quotLiftPattern.Path) : NormalEq locals (leftValues path) (values path) := by
  rcases path with path | path
  · cases path with
    | none => exact .refl (valueEqual (.inl none)).hasType.1
    | some path =>
      cases path with
      | none => exact etaFunctionNormal
      | some path => exact .refl (valueEqual (.inl (some (some path)))).hasType.1
  · exact .refl (valueEqual (.inr path)).hasType.1

-- A genuine Type-source rule: both sides match, the checks are DERIVED on the
-- left, all right captures reduce, and only function/payload IHs are supplied.
theorem constructorExtra : ∃ joined,
    ParRed locals source reduced ∧
    ParRed locals leftSource (quotLiftPatternResult.apply [.succ .zero, .succ .zero] leftValues) ∧
    Steps quotientEnvironmentWF 0 locals leftSource joined ∧ NormalEq locals joined reduced ∧
    quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
    quotientEnvironment.HasType 0 locals reduced (.sort .zero) :=
  CoreSimulates.quot_constructor_extra quotientRegistered contextWF leftSourceTyped sourceTyped
    leftMatched matched capturesNormal etaFunctionSimulation
    (CoreSimulates.refl contextWF (valueEqual (.inr none)).hasType.1)
    (checked _) argumentsReduce

theorem retainedDependentBinder : ∃ joined,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) leftSource.lift joined.lift ∧
    NormalEq (.bvar 5 :: locals) joined.lift reduced.lift ∧
    Steps quotientEnvironmentWF 0 locals leftSource joined ∧ NormalEq locals joined reduced := by
  obtain ⟨joined, _, _, path, normal, _, _⟩ := constructorExtra
  have retainedPath := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  exact ⟨joined, retainedPath, retainedNormal,
    by simpa only [VExpr.inst_lift] using retainedPath.instN Ctx.InstN.zero (argumentsTyped (.inr none)),
    by simpa only [VExpr.inst_lift] using retainedNormal.instN (argumentsTyped (.inr none)) Ctx.InstN.zero⟩

theorem rightCannotUnfold : QuotPropReduction.unfold source = none := rfl
theorem leftCannotUnfold : QuotPropReduction.unfold leftSource = none := rfl
example : leftValues (.inl (some none)) ≠ values (.inl (some none)) := by intro equal; cases equal

theorem allCapturesChange (path : quotLiftPattern.Path) : values path ≠ originalValues path := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | (intro equal; cases equal)
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | (intro equal; cases equal)

theorem distinctDomainParameters : values (.inl (some (some (some (some none))))) ≠
    values (.inr (some (some none))) := by intro equal; cases equal

theorem distinctRelationParameters : values (.inl (some (some (some none)))) ≠
    values (.inr (some none)) := by intro equal; cases equal

end TypeSource

run_meta
  let environment ← getEnv
  let roots := [``CoreSimulates.quot_constructor_extra, ``CoreSimulates.quot_prop_extra, ``quotientEnvironmentWF, ``quotientRegistered, ``delayEqual, ``delayReduction, ``argumentsTyped, ``valueEqual, ``sourceAtTyped, ``sourceTyped, ``matchedAt, ``matched, ``checked, ``argumentsReduce, ``appNormal, ``etaFunctionNormal, ``etaFunctionEqual, ``etaFunctionSimulation, ``leftAtTyped, ``retainOriginalType, ``neutralPropExtra, ``retainedDependentBinder, ``neutralNormal, ``neutralDoesNotMatch, ``allCapturesChange, ``distinctDomainParameters, ``distinctRelationParameters, ``TypeSource.contextWF, ``TypeSource.delayEqual, ``TypeSource.delayReduction, ``TypeSource.argumentsTyped, ``TypeSource.valueEqual, ``TypeSource.sourceAtTyped, ``TypeSource.sourceTyped, ``TypeSource.matchedAt, ``TypeSource.matched, ``TypeSource.checked, ``TypeSource.argumentsReduce, ``TypeSource.etaFunctionNormal, ``TypeSource.etaFunctionSimulation, ``TypeSource.leftSourceTyped, ``TypeSource.leftMatched, ``TypeSource.sourceNormal, ``TypeSource.capturesNormal, ``TypeSource.constructorExtra, ``TypeSource.retainedDependentBinder, ``TypeSource.rightCannotUnfold, ``TypeSource.leftCannotUnfold, ``TypeSource.allCapturesChange, ``TypeSource.distinctDomainParameters, ``TypeSource.distinctRelationParameters]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``HasType.weakN_iff,
    ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC, ``NormalEq.trans,
    ``ParRed.weakN_inv, ``ParRedExt.parRed_beta, ``hasType_app_bvar0,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_constructor_extra, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.quot_prop_extra, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.quotientEnvironmentWF, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.quotientRegistered, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.delayEqual, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.delayReduction, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.argumentsTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.valueEqual, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.sourceAtTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.sourceTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.matchedAt, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.matched, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.checked, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.argumentsReduce, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.appNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.etaFunctionNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.etaFunctionEqual, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.etaFunctionSimulation, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.leftAtTyped, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.retainOriginalType, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.neutralPropExtra, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.retainedDependentBinder, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.neutralNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.neutralDoesNotMatch, [], [`propext]),
    (`QuotNormalExtraTest.allCapturesChange, [], [`propext]),
    (`QuotNormalExtraTest.distinctDomainParameters, [], [`propext]),
    (`QuotNormalExtraTest.distinctRelationParameters, [], [`propext]),
    (`QuotNormalExtraTest.TypeSource.contextWF, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.delayEqual, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.delayReduction, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.argumentsTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.valueEqual, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.sourceAtTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.sourceTyped, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.matchedAt, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.matched, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.checked, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.argumentsReduce, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.etaFunctionNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.etaFunctionSimulation, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.leftSourceTyped, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.leftMatched, [], [`propext, `Quot.sound]),
    (`QuotNormalExtraTest.TypeSource.sourceNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.capturesNormal, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.constructorExtra, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.retainedDependentBinder, [`Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `Quot.sound, `sorryAx]),
    (`QuotNormalExtraTest.TypeSource.rightCannotUnfold, [], [`propext]),
    (`QuotNormalExtraTest.TypeSource.leftCannotUnfold, [], [`propext]),
    (`QuotNormalExtraTest.TypeSource.allCapturesChange, [], [`propext]),
    (`QuotNormalExtraTest.TypeSource.distinctDomainParameters, [], [`propext]),
    (`QuotNormalExtraTest.TypeSource.distinctRelationParameters, [], [`propext])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing EXTRA manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new EXTRA axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing EXTRA proof {root}"
    if proof.hasSorry then throwError "direct EXTRA admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "EXTRA axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden EXTRA dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then throwError "admitted type {name} in {root}"
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved EXTRA admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "EXTRA traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "EXTRA admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``CoreSimulates.quot_constructor_extra then
        [``ParRed.extra, ``IsDefEqU.trans, ``NormalEq.defeq, ``Steps.app, ``Steps.hasType, ``ParRed.hasType]
      else if root == ``CoreSimulates.quot_prop_extra then
        [``ParRed.extra, ``Step.unfold, ``selector_hasType, ``NormalEq.proofIrrel,
          ``quotLift_inv, ``quotMk_inv, ``NormalEq.defeq, ``Steps.app, ``Steps.hasType, ``ParRed.hasType]
      else if root == ``neutralPropExtra then
        [``CoreSimulates.quot_prop_extra, ``leftAtTyped, ``sourceAtTyped, ``matchedAt,
          ``checked, ``argumentsReduce, ``etaFunctionSimulation, ``retainOriginalType]
      else if root == ``neutralNormal then
        [``appNormal, ``NormalEq.constDF, ``NormalEq.proofIrrel, ``etaFunctionNormal]
      else if root == ``retainedDependentBinder then
        [``neutralPropExtra, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN, ``NormalEq.instN]
      else if root == ``TypeSource.sourceNormal then
        [``appNormal, ``TypeSource.etaFunctionNormal, ``TypeSource.leftSourceTyped]
      else if root == ``TypeSource.constructorExtra then
        [``CoreSimulates.quot_constructor_extra, ``TypeSource.contextWF, ``TypeSource.sourceTyped,
          ``TypeSource.leftSourceTyped, ``TypeSource.leftMatched, ``TypeSource.matched,
          ``TypeSource.capturesNormal, ``TypeSource.etaFunctionSimulation,
          ``TypeSource.checked, ``TypeSource.argumentsReduce]
      else if root == ``TypeSource.retainedDependentBinder then
        [``TypeSource.constructorExtra, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN, ``NormalEq.instN]
      else []
    unless required.all visited.contains do
      throwError "EXTRA control bypassed a required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"


end QuotNormalExtraTest
