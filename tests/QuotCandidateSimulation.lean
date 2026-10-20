import Lean4Lean.Theory.Typing.QuotCandidateSimulation
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotHereditaryExtraTest
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
    (by simpa [VLevel.WF] using sourceWF) (by rfl) (.cons sourceZero.symm (.cons rfl .nil)) (Γ := locals) (uvars := 0)
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
    (by simpa using constructorWF) (by rfl) (.cons constructorZero.symm .nil) (Γ := locals) (uvars := 0)
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
    (by simpa [VLevel.WF] using sourceWF) (by rfl) (.cons sourceZero.symm (.cons rfl .nil)) (Γ := locals) (uvars := 0)
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


theorem etaTreeSimulation {context : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type) (depth : Nat) :
    CoreSimulates quotientEnvironmentWF 0 context (etaTree depth expression type) expression := by
  induction depth generalizing context expression type with
  | zero => exact CoreSimulates.refl contextWF typed
  | succ depth induction =>
    cases type <;> try exact CoreSimulates.refl contextWF typed
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := typed.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    exact CoreSimulates.etaL contextWF typed (induction
      (show OnCtx (domain :: context) (quotientEnvironment.IsType 0) from ⟨contextWF, _, domainTyped⟩)
      (etaBody_hasType quotientEnvironmentWF.ordered typed))

def rightPrefix : VExpr := applyArguments (.const ``Quot.lift [.zero, .succ .zero])
  [values (.inl (some (some (some (some none))))), values (.inl (some (some (some none)))),
    values (.inl (some (some none))), values (.inl (some none)), values (.inl none)]
def rightMajor : VExpr := .app (.app (.app (.const ``Quot.mk [.zero])
  (values (.inr (some (some none))))) (values (.inr (some none)))) (values (.inr none))
def prefixType : VExpr := .forallE majorType (.sort .zero)

theorem rightPrefixTyped : quotientEnvironment.HasType 0 locals rightPrefix prefixType := by
  obtain ⟨_, _, liftRegistered, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have head := IsDefEq.constDF liftRegistered (ls := [.zero, .succ .zero])
    (ls' := [.zero, .succ .zero]) (by simp [VLevel.WF]) (by simp [VLevel.WF])
    (by rfl) (.cons rfl (.cons rfl .nil)) (Γ := locals) (uvars := 0)
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
  simpa [HasType, rightPrefix, prefixType, majorType, QuotConfluenceObstruction.quotient,
    originalValues, applyArguments, VExpr.liftN, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using fifth.hasType.2

theorem rightMajorTyped : quotientEnvironment.HasType 0 locals rightMajor majorType := by
  obtain ⟨_, _, _, constructorRegistered, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have ctor := IsDefEq.constDF constructorRegistered (ls := [.zero]) (ls' := [.zero])
    (by simp [VLevel.WF]) (by simp [VLevel.WF]) (by rfl) (.cons rfl .nil) (Γ := locals) (uvars := 0)
  simp [quotMkConst, VExpr.instL, VLevel.inst] at ctor
  have first := ctor.appDF (valueEqual (.inr (some (some none)))).symm
  simp [VExpr.inst, VExpr.instVar] at first
  have second := first.appDF (valueEqual (.inr (some none))).symm
  simp [VExpr.inst, VExpr.instVar, VExpr.inst_lift] at second
  simpa [HasType, rightMajor, majorType, QuotConfluenceObstruction.quotient,
    originalValues, VExpr.liftN, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
    (second.appDF (valueEqual (.inr none)).symm).hasType.2

def wrappedPrefix : VExpr := etaTree 1 rightPrefix prefixType

theorem wrappedTyped : quotientEnvironment.HasType 0 locals (.app wrappedPrefix (.bvar 0)) originalType := by
  have wf := localsWF quotientEnvironmentWF quotientRegistered
  have prefixTyped := ((etaTreeNormal wf rightPrefixTyped 1).defeq wf).symm.of_l
    quotientEnvironmentWF wf rightPrefixTyped
  apply retainOriginalType
  simpa [wrappedPrefix, prefixType, VExpr.inst, VExpr.instVar] using prefixTyped.hasType.2.app majorTyped

theorem wrappedNormal : NormalEq locals (.app wrappedPrefix (.bvar 0)) source := by
  have wf := localsWF quotientEnvironmentWF quotientRegistered
  exact appNormal wf wrappedTyped (etaTreeNormal wf rightPrefixTyped 1)
    (.proofIrrel (majorTypeTyped quotientEnvironmentWF quotientRegistered) majorTyped rightMajorTyped)

theorem hereditaryJoin : ∃ joined,
    ParRed locals source (quotLiftPatternResult.apply [.zero, .succ .zero] values) ∧
    Steps quotientEnvironmentWF 0 locals (.app wrappedPrefix (.bvar 0)) joined ∧
    NormalEq locals joined (quotLiftPatternResult.apply [.zero, .succ .zero] values) ∧
    quotientEnvironment.HasType 0 locals joined originalType ∧
    quotientEnvironment.HasType 0 locals (quotLiftPatternResult.apply [.zero, .succ .zero] values) originalType :=
  normal_quot_prop_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    rfl wrappedNormal (List.Forall₂.nil : List.Forall₂ (NormalEq locals) [] [])
    wrappedTyped matched (checked _)

theorem applicationExtra : ∃ joined,
    ParRed locals source reduced ∧
    Steps quotientEnvironmentWF 0 locals (.app wrappedPrefix (.bvar 0)) joined ∧
    NormalEq locals joined reduced ∧
    quotientEnvironment.HasType 0 locals joined originalType ∧
    quotientEnvironment.HasType 0 locals reduced originalType :=
  CoreSimulates.app_quot_prop_extra quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    wrappedTyped (retainOriginalType sourceTyped)
    (etaTreeSimulation (localsWF quotientEnvironmentWF quotientRegistered) rightPrefixTyped 1)
    (CoreSimulates.proofIrrel (localsWF quotientEnvironmentWF quotientRegistered)
      (majorTypeTyped quotientEnvironmentWF quotientRegistered) majorTyped rightMajorTyped)
    rfl matched (checked _) argumentsReduce

theorem retainedJoin : ∃ joined,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) (VExpr.app wrappedPrefix (.bvar 0)).lift joined.lift ∧
    NormalEq (.bvar 5 :: locals) joined.lift reduced.lift ∧
    Steps quotientEnvironmentWF 0 locals (.app wrappedPrefix (.bvar 0)) joined := by
  obtain ⟨joined, _, path, normal, _, _⟩ := applicationExtra
  have retained := path.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType QuotConfluenceObstruction.quotient
    type_tac
  exact ⟨joined, retained, normal.weakN (Ctx.LiftN.one (A := .bvar 5)),
    by simpa only [VExpr.inst_lift] using retained.instN Ctx.InstN.zero witness⟩

example : wrappedPrefix ≠ rightPrefix := by intro equal; cases equal
example : originalType ≠ VExpr.sort .zero := by intro equal; cases equal

theorem etaTreeAgainst {context : List VExpr} {expression right type : VExpr}
    (contextWF : OnCtx context (quotientEnvironment.IsType 0))
    (typed : quotientEnvironment.HasType 0 context expression type)
    (rightTyped : quotientEnvironment.HasType 0 context right type)
    (normal : NormalEq context expression right) (depth : Nat) :
    NormalEq context (etaTree depth expression type) right := by
  induction depth generalizing context expression right type with
  | zero => exact normal
  | succ depth induction =>
    cases type <;> try exact normal
    rename_i domain body
    obtain ⟨_, typeTyped⟩ := rightTyped.isType quotientEnvironmentWF.ordered contextWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv quotientEnvironmentWF.ordered
    apply NormalEq.etaL rightTyped
    apply induction (show OnCtx (domain :: context) (quotientEnvironment.IsType 0)
      from ⟨contextWF, _, domainTyped⟩)
      (etaBody_hasType quotientEnvironmentWF.ordered typed)
      (etaBody_hasType quotientEnvironmentWF.ordered rightTyped)
    exact .appDF (typed.weak quotientEnvironmentWF.ordered) (rightTyped.weak quotientEnvironmentWF.ordered)
      (.bvar .zero) (.bvar .zero) (normal.weakN Ctx.LiftN.one) (.refl (.bvar .zero))

namespace RetainedEta

def target : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.sort .zero))

theorem targetTyped {context : List VExpr} :
    quotientEnvironment.HasType 0 context target (.sort (.succ .zero)) := by
  have natural : quotientEnvironment.HasType 0 context target
      (.sort (.imax (.succ .zero) (.imax .zero (.succ .zero)))) :=
    HasType.forallE (HasType.sort (by trivial))
      (HasType.forallE (HasType.bvar .zero) (HasType.sort (by trivial)))
  exact IsDefEq.defeq (.sortDF (by trivial) (by trivial)
    (VLevel.equiv_def.mpr (by intro values; rfl))) natural

syntax "higher_type_tac" : tactic
macro_rules | `(tactic| higher_type_tac) => `(tactic|
  first
  | exact targetTyped
  | refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_ <;> [skip; skip; higher_type_tac; higher_type_tac]
  | refine HasType.sort ?_; decide
  | refine HasType.bvar ?_; lookup_tac
  | refine HasType.app' (A := ?_) (B := ?_) ?_ ?_ ?_ <;> [skip; skip; higher_type_tac; higher_type_tac; exact rfl]
  | refine HasType.const' (ci := ?_) ?_ ?_ ?_ ?_ <;> [skip; assumption; decide; decide; exact rfl]
  | refine HasType.lam (u := ?_) ?_ ?_ <;> [skip; higher_type_tac; higher_type_tac]
)
def functionType : VExpr := .forallE (.bvar 1) target
def respectType : VExpr :=
  .forallE (.bvar 2) (.forallE (.bvar 3)
    (.forallE (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.succ .zero]) target)
        (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1)))))
def context : List VExpr :=
  QuotConfluenceObstruction.quotient (.bvar 4) (.bvar 3) :: .bvar 3 ::
    respectType :: functionType :: relationType :: [.sort .zero]
def prefixTerm : VExpr := applyArguments (.const ``Quot.lift [.zero, .succ .zero])
  [.bvar 5, .bvar 4, target, .bvar 3, .bvar 2]
def leftRoot : VExpr := .app prefixTerm (.bvar 0)
def rightRoot : VExpr := .app prefixTerm constructor
def etaRoot : VExpr := etaTree 2 leftRoot target
def resultType : VExpr := .forallE (.bvar 5) (.sort .zero)
def suppliedType : VExpr := delay (.sort (.succ .zero)) resultType

theorem contextWF : OnCtx context (quotientEnvironment.IsType 0) := by
  have equal := equalityRegistered quotientEnvironmentWF quotientRegistered
  obtain ⟨_, _, _, _, quotientObject, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by higher_type_tac⟩, _, by higher_type_tac⟩, _, by higher_type_tac⟩,
    _, by higher_type_tac⟩, _, by higher_type_tac⟩, _, by higher_type_tac⟩

theorem prefixTyped : quotientEnvironment.HasType 0 context prefixTerm (.forallE majorType target) := by
  obtain ⟨_, _, liftObject, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context prefixTerm applyArguments majorType respectType functionType relationType target
    QuotConfluenceObstruction.quotient
  higher_type_tac

theorem domainTyped : quotientEnvironment.HasType 0 context (.bvar 5) (.sort .zero) := by
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  higher_type_tac

theorem relationTyped : quotientEnvironment.HasType 0 context (.bvar 4)
    (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  higher_type_tac

theorem majorTypeTyped : quotientEnvironment.HasType 0 context majorType (.sort .zero) := by
  obtain ⟨_, _, _, _, quotientObject, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context majorType respectType functionType relationType target QuotConfluenceObstruction.quotient
  higher_type_tac

theorem majorTyped : quotientEnvironment.HasType 0 context (.bvar 0) majorType := by
  unfold context majorType QuotConfluenceObstruction.quotient
  higher_type_tac

theorem constructorTyped : quotientEnvironment.HasType 0 context constructor majorType := by
  obtain ⟨_, _, _, constructorObject, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context constructor majorType respectType functionType relationType target QuotConfluenceObstruction.quotient
  higher_type_tac

theorem leftTyped : quotientEnvironment.HasType 0 context leftRoot target := by
  simpa [leftRoot, target, VExpr.inst, VExpr.instVar] using prefixTyped.app majorTyped

theorem rightTyped : quotientEnvironment.HasType 0 context rightRoot target := by
  simpa [rightRoot, target, VExpr.inst, VExpr.instVar] using prefixTyped.app constructorTyped

theorem rootNormal : NormalEq context leftRoot rightRoot :=
  .appDF prefixTyped prefixTyped majorTyped constructorTyped (.refl prefixTyped)
    (.proofIrrel majorTypeTyped majorTyped constructorTyped)

theorem etaNormal : NormalEq context etaRoot rightRoot :=
  etaTreeAgainst contextWF leftTyped rightTyped rootNormal 2

theorem sourceTyped : quotientEnvironment.HasType 0 context (.app etaRoot (.bvar 5)) suppliedType := by
  have etaTyped := ((etaNormal.defeq contextWF).symm.of_l quotientEnvironmentWF contextWF rightTyped).hasType.2
  have natural : quotientEnvironment.HasType 0 context (.app etaRoot (.bvar 5)) resultType := by
    simpa [target, resultType, VExpr.inst, VExpr.instVar] using etaTyped.app domainTyped
  have resultTyped : quotientEnvironment.HasType 0 context resultType (.sort (.succ .zero)) := by
    have natural : quotientEnvironment.HasType 0 context resultType (.sort (.imax .zero (.succ .zero))) :=
      HasType.forallE domainTyped (HasType.sort (by trivial))
    exact IsDefEq.defeq (.sortDF (by trivial) (by trivial)
      (VLevel.equiv_def.mpr (by intro values; rfl))) natural
  exact (delayEqual resultTyped).symm.defeq natural

def values : quotLiftPattern.Path → VExpr
  | .inl none => .bvar 2
  | .inl (some none) => .bvar 3
  | .inl (some (some none)) => target
  | .inl (some (some (some none))) => .bvar 4
  | .inl (some (some (some (some none)))) => .bvar 5
  | .inr none => .bvar 1
  | .inr (some none) => .bvar 4
  | .inr (some (some none)) => .bvar 5

theorem matched : quotLiftPattern.Matches rightRoot [.zero, .succ .zero] values := by
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [.zero, .succ .zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := target)
    |>.var (a' := .bvar 3) |>.var (a' := .bvar 2)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [.zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .bvar 1)
  rw [(_ : values = _)]
  · exact functionMatched.app constructorMatched
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem checked : quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 context)
    [.zero, .succ .zero] values := ⟨⟨_, domainTyped⟩, ⟨_, relationTyped⟩, trivial⟩

-- One pending application consumes the first eta binder; the second dependent
-- binder is retained around the actual quotient firing and its normal join.
theorem firing : ∃ joined,
    ParRed context (.app rightRoot (.bvar 5)) (.app reduced (.bvar 5)) ∧
    Steps quotientEnvironmentWF 0 context (.app etaRoot (.bvar 5)) joined ∧
    NormalEq context joined (.app reduced (.bvar 5)) ∧
    quotientEnvironment.HasType 0 context joined suppliedType ∧
    quotientEnvironment.HasType 0 context (.app reduced (.bvar 5)) suppliedType :=
  normal_quot_prop_join quotientRegistered contextWF rfl etaNormal
    (.cons (.refl domainTyped) .nil) sourceTyped matched checked

theorem twoDependentEtaBinders : ∃ first second body,
    etaRoot = .lam first (.lam second body) := ⟨_, _, _, rfl⟩

example : suppliedType ≠ resultType := by intro equal; cases equal
example : leftRoot ≠ rightRoot := by intro equal; cases equal

end RetainedEta

namespace ProofCase

def target : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))

theorem targetTyped {context : List VExpr} :
    quotientEnvironment.HasType 0 context target (.sort .zero) := by
  have natural : quotientEnvironment.HasType 0 context target
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
    HasType.forallE (HasType.sort (by trivial))
      (HasType.forallE (HasType.bvar .zero) (HasType.bvar (.succ .zero)))
  exact IsDefEq.defeq (.sortDF (by trivial) (by trivial)
    (VLevel.equiv_def.mpr (by intro values; rfl))) natural

syntax "proof_type_tac" : tactic
macro_rules | `(tactic| proof_type_tac) => `(tactic|
  first
  | exact targetTyped
  | refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_ <;> [skip; skip; proof_type_tac; proof_type_tac]
  | refine HasType.sort ?_; decide
  | refine HasType.bvar ?_; lookup_tac
  | refine HasType.app' (A := ?_) (B := ?_) ?_ ?_ ?_ <;> [skip; skip; proof_type_tac; proof_type_tac; exact rfl]
  | refine HasType.const' (ci := ?_) ?_ ?_ ?_ ?_ <;> [skip; assumption; decide; decide; exact rfl]
  | refine HasType.lam (u := ?_) ?_ ?_ <;> [skip; proof_type_tac; proof_type_tac]
)
def functionType : VExpr := .forallE (.bvar 1) target
def respectType : VExpr :=
  .forallE (.bvar 2) (.forallE (.bvar 3)
    (.forallE (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.zero]) target)
        (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1)))))
def context : List VExpr :=
  QuotConfluenceObstruction.quotient (.bvar 4) (.bvar 3) :: .bvar 3 ::
    respectType :: functionType :: relationType :: [.sort .zero]
def prefixTerm : VExpr := applyArguments (.const ``Quot.lift [.zero, .zero])
  [.bvar 5, .bvar 4, target, .bvar 3, .bvar 2]
def leftRoot : VExpr := .app prefixTerm (.bvar 0)
def rightRoot : VExpr := .app prefixTerm constructor

theorem contextWF : OnCtx context (quotientEnvironment.IsType 0) := by
  have equal := equalityRegistered quotientEnvironmentWF quotientRegistered
  obtain ⟨_, _, _, _, quotientObject, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by proof_type_tac⟩, _, by proof_type_tac⟩, _, by proof_type_tac⟩,
    _, by proof_type_tac⟩, _, by proof_type_tac⟩, _, by proof_type_tac⟩

theorem prefixTyped : quotientEnvironment.HasType 0 context prefixTerm (.forallE majorType target) := by
  obtain ⟨_, _, liftObject, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context prefixTerm applyArguments majorType respectType functionType relationType target
    QuotConfluenceObstruction.quotient
  proof_type_tac

theorem domainTyped : quotientEnvironment.HasType 0 context (.bvar 5) (.sort .zero) := by
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  proof_type_tac

theorem relationTyped : quotientEnvironment.HasType 0 context (.bvar 4)
    (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
  unfold context respectType functionType relationType target QuotConfluenceObstruction.quotient
  proof_type_tac

theorem majorTypeTyped : quotientEnvironment.HasType 0 context majorType (.sort .zero) := by
  obtain ⟨_, _, _, _, quotientObject, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context majorType respectType functionType relationType target QuotConfluenceObstruction.quotient
  proof_type_tac

theorem majorTyped : quotientEnvironment.HasType 0 context (.bvar 0) majorType := by
  unfold context majorType QuotConfluenceObstruction.quotient
  proof_type_tac

theorem constructorTyped : quotientEnvironment.HasType 0 context constructor majorType := by
  obtain ⟨_, _, _, constructorObject, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  unfold context constructor majorType respectType functionType relationType target QuotConfluenceObstruction.quotient
  proof_type_tac

theorem leftTyped : quotientEnvironment.HasType 0 context leftRoot target := by
  simpa [leftRoot, target, VExpr.inst, VExpr.instVar] using prefixTyped.app majorTyped

theorem rightTyped : quotientEnvironment.HasType 0 context rightRoot target := by
  simpa [rightRoot, target, VExpr.inst, VExpr.instVar] using prefixTyped.app constructorTyped


def values : quotLiftPattern.Path → VExpr
  | .inl none => .bvar 2
  | .inl (some none) => .bvar 3
  | .inl (some (some none)) => target
  | .inl (some (some (some none))) => .bvar 4
  | .inl (some (some (some (some none)))) => .bvar 5
  | .inr none => .bvar 1
  | .inr (some none) => .bvar 4
  | .inr (some (some none)) => .bvar 5

theorem matched : quotLiftPattern.Matches rightRoot [.zero, .zero] values := by
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [.zero, .zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := target)
    |>.var (a' := .bvar 3) |>.var (a' := .bvar 2)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [.zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .bvar 1)
  rw [(_ : values = _)]
  · exact functionMatched.app constructorMatched
  · funext path
    rcases path with path | path
    · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
      all_goals first | cases impossible | rfl
    · rcases path with _ | (_ | (_ | impossible))
      all_goals first | cases impossible | rfl

theorem checked : quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 context)
    [.zero, .zero] values := ⟨⟨_, domainTyped⟩, ⟨_, relationTyped⟩, trivial⟩


def proofContext : List VExpr := target :: context

theorem proofContextWF : OnCtx proofContext (quotientEnvironment.IsType 0) :=
  ⟨contextWF, _, targetTyped⟩

theorem variableTyped : quotientEnvironment.HasType 0 proofContext (.bvar 0) target := by
  simpa [HasType, proofContext, target, VExpr.lift, VExpr.liftN, liftVar] using
    (HasType.bvar (env := quotientEnvironment) (U := 0) (Lookup.zero (ty := target) (Γ := context)))

theorem rightLiftTyped : quotientEnvironment.HasType 0 proofContext rightRoot.lift target := by
  simpa [HasType, proofContext, target, VExpr.lift, VExpr.liftN, liftVar] using rightTyped.weak quotientEnvironmentWF.ordered (A := target)

theorem proofNormal : NormalEq proofContext (.bvar 0) rightRoot.lift :=
  .proofIrrel targetTyped variableTyped rightLiftTyped

theorem liftedMatched : quotLiftPattern.Matches rightRoot.lift [.zero, .zero]
    (fun path => (values path).lift) :=
  Pattern.matches_liftN.mpr ⟨values, matched, fun _ => rfl⟩

theorem liftedChecked : quotLiftPatternCheck.OK (quotientEnvironment.IsDefEqU 0 proofContext)
    [.zero, .zero] (fun path => (values path).lift) :=
  Pattern.Check.OK.weakN (W := Ctx.LiftN.one (A := target)) quotLiftPatternCheck checked

-- A neutral proof variable takes the actual proof alternative. The right
-- quotient redex still supplies a real match and both actual rule checks.
theorem proofFiring : ∃ joined,
    ParRed proofContext rightRoot.lift reduced.lift ∧
    Steps quotientEnvironmentWF 0 proofContext (.bvar 0) joined ∧
    NormalEq proofContext joined reduced.lift ∧
    quotientEnvironment.HasType 0 proofContext joined target ∧
    quotientEnvironment.HasType 0 proofContext reduced.lift target :=
  normal_quot_prop_join quotientRegistered proofContextWF rfl proofNormal
    (List.Forall₂.nil : List.Forall₂ (NormalEq proofContext) [] [])
    variableTyped liftedMatched liftedChecked

end ProofCase

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

theorem neutralDoesNotMatch {levels : List VLevel} {captures : quotLiftPattern.Path → VExpr} :
    ¬quotLiftPattern.Matches (.app wrappedPrefix (.bvar 0)) levels captures := by
  intro matched
  cases matched with
  | app _ major => cases major

theorem wrappedIsEta : ∃ domain body, wrappedPrefix = .lam domain body := ⟨_, _, rfl⟩
theorem originalTypeDelayed : originalType ≠ VExpr.sort .zero := by intro equal; cases equal

end QuotHereditaryExtraTest

namespace CandidateSimulationTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.QuotPropReduction
open Lean4Lean.VEnv.QuotConfluenceObstruction
open QuotHereditaryExtraTest

local instance : Params := quotientEnvironmentWF.reductionParams 0

theorem delayCandidate {context : List VExpr} (type value : VExpr) :
    Step quotientEnvironmentWF 0 context (delay type value) value := by
  apply Step.core
  simpa [delay, VExpr.inst, VExpr.instVar] using
    (ParRed.beta (Γ := context) (A := type) (ParRed.rfl (e := .bvar 0)) (ParRed.rfl (e := value)))

abbrev wf := localsWF quotientEnvironmentWF quotientRegistered
abbrev neutralType := neutralTyped quotientEnvironmentWF quotientRegistered

def neutralResult : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))
def redexResult : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) constructor)

theorem neutralUnfolds : unfold neutral = some neutralResult := rfl
theorem redexUnfolds : unfold redex = some redexResult := rfl

def wrappedNeutral : VExpr := .app
  (etaTree 1 eliminator (.forallE majorType (.sort .zero))) (.bvar 0)

theorem wrappedNeutralNormal : NormalEq locals wrappedNeutral neutral :=
  .appDF
    (((etaTreeNormal wf (prefixTyped quotientEnvironmentWF quotientRegistered) 1).defeq wf).of_r
      quotientEnvironmentWF wf (prefixTyped quotientEnvironmentWF quotientRegistered)).hasType.1
    (prefixTyped quotientEnvironmentWF quotientRegistered) majorTyped majorTyped
    (etaTreeNormal wf (prefixTyped quotientEnvironmentWF quotientRegistered) 1) (.refl majorTyped)

theorem wrappedNeutralTyped : quotientEnvironment.HasType 0 locals wrappedNeutral (.sort .zero) :=
  ((wrappedNeutralNormal.defeq wf).of_r quotientEnvironmentWF wf neutralType).hasType.1

theorem neutralHereditaryUnfold : ∃ joined,
    Steps quotientEnvironmentWF 0 locals wrappedNeutral joined ∧ NormalEq locals joined neutralResult ∧
    quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
    quotientEnvironment.HasType 0 locals neutralResult (.sort .zero) :=
  normal_step_join quotientRegistered wf wrappedNeutralTyped wrappedNeutralNormal (.unfold neutralUnfolds)

theorem originalObstruction : ∃ joined,
    Steps quotientEnvironmentWF 0 locals neutral joined ∧ NormalEq locals joined reduced ∧
    quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
    quotientEnvironment.HasType 0 locals reduced (.sort .zero) :=
  normal_step_join quotientRegistered wf neutralType
    (normalEq quotientEnvironmentWF quotientRegistered) (.core (reduction quotientEnvironmentWF quotientRegistered))

-- A lambda domain beta-reduces while its body performs actual unfolding.
def delayedSort : VExpr := delay (.sort (.succ .zero)) (.sort .zero)

theorem delayedSortEqual : quotientEnvironment.IsDefEq 0 locals delayedSort (.sort .zero)
    (.sort (.succ .zero)) := delayEqual (HasType.sort (by trivial))

theorem lambdaNormal : NormalEq locals (.lam (.sort .zero) neutral.lift)
    (.lam delayedSort redex.lift) :=
  .lamDF (HasType.sort (by trivial)) delayedSortEqual.symm
    ((normalEq quotientEnvironmentWF quotientRegistered).weakN Ctx.LiftN.one)

theorem lambdaStep : Step quotientEnvironmentWF 0 locals (.lam delayedSort redex.lift)
    (.lam (.sort .zero) redexResult.lift) :=
  .lam (delayCandidate _ _) (.unfold (unfold_liftN redexUnfolds 1 0))

theorem changingLambdaDomain : ∃ joined,
    Steps quotientEnvironmentWF 0 locals (.lam (.sort .zero) neutral.lift) joined ∧
    NormalEq locals joined (.lam (.sort .zero) redexResult.lift) ∧
    quotientEnvironment.HasType 0 locals joined (.forallE (.sort .zero) (.sort .zero)) ∧
    quotientEnvironment.HasType 0 locals (.lam (.sort .zero) redexResult.lift)
      (.forallE (.sort .zero) (.sort .zero)) :=
  normal_step_join quotientRegistered wf
    ((HasType.sort (by trivial)).lam (neutralType.weak quotientEnvironmentWF.ordered)) lambdaNormal lambdaStep

theorem forallNormal : NormalEq locals (.forallE delayedSort neutral.lift)
    (.forallE delayedSort redex.lift) :=
  .forallEDF delayedSortEqual.symm (.refl delayedSortEqual.hasType.1)
    (neutralType.weak quotientEnvironmentWF.ordered)
    ((normalEq quotientEnvironmentWF quotientRegistered).weakN Ctx.LiftN.one)

theorem forallStep : Step quotientEnvironmentWF 0 locals (.forallE delayedSort redex.lift)
    (.forallE (.sort .zero) redexResult.lift) :=
  .forallE (delayCandidate _ _) (.unfold (unfold_liftN redexUnfolds 1 0))

theorem changingForallDomain : ∃ joined,
    Steps quotientEnvironmentWF 0 locals (.forallE delayedSort neutral.lift) joined ∧
    NormalEq locals joined (.forallE (.sort .zero) redexResult.lift) :=
  normal_candidate_simulates quotientRegistered wf forallNormal forallStep

namespace Retained
open QuotHereditaryExtraTest.RetainedEta

def unfoldedNeutral : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) (.bvar 0))
def unfoldedConstructor : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) constructor)

theorem neutralUnfolds : unfold leftRoot = some unfoldedNeutral := rfl
theorem constructorUnfolds : unfold rightRoot = some unfoldedConstructor := rfl

theorem etaNeutralNormal : NormalEq context etaRoot leftRoot := etaTreeNormal contextWF leftTyped 2

theorem retainedNeutralUnfold : ∃ joined,
    Steps quotientEnvironmentWF 0 context (.app etaRoot (.bvar 5)) joined ∧
    NormalEq context joined (.app unfoldedNeutral (.bvar 5)) ∧
    quotientEnvironment.HasType 0 context joined suppliedType ∧
    quotientEnvironment.HasType 0 context (.app unfoldedNeutral (.bvar 5)) suppliedType :=
  normal_unfold_join (left := etaRoot) (pending := [.bvar 5]) (pending' := [.bvar 5])
    quotientRegistered contextWF RetainedEta.sourceTyped etaNeutralNormal
    (.cons (.refl domainTyped) .nil) neutralUnfolds

theorem retainedConstructorUnfold : ∃ joined,
    Steps quotientEnvironmentWF 0 context (.app etaRoot (.bvar 5)) joined ∧
    NormalEq context joined (.app unfoldedConstructor (.bvar 5)) ∧
    quotientEnvironment.HasType 0 context joined suppliedType ∧
    quotientEnvironment.HasType 0 context (.app unfoldedConstructor (.bvar 5)) suppliedType :=
  normal_step_join quotientRegistered contextWF sourceTyped
    (appNormal contextWF sourceTyped etaNormal (.refl domainTyped))
    (.app (.unfold constructorUnfolds) (.core .bvar))

theorem retainedRootUnfold : ∃ joined,
    Steps quotientEnvironmentWF 0 context etaRoot joined ∧ NormalEq context joined unfoldedNeutral :=
  normal_candidate_simulates quotientRegistered contextWF etaNeutralNormal (.unfold neutralUnfolds)

theorem etaRightNormal : NormalEq context leftRoot etaRoot := etaNeutralNormal.symm contextWF

theorem etaRightStructural : ∃ joined,
    Steps quotientEnvironmentWF 0 context leftRoot joined ∧
    NormalEq context joined (.lam (.sort .zero)
      (.lam (.bvar 0) (.app (.app unfoldedNeutral.lift.lift (.bvar 1)) (.bvar 0)))) :=
  normal_candidate_simulates quotientRegistered contextWF etaRightNormal
    (.lam (.core .rfl) (.lam (.core .rfl)
      (.app (.app (.unfold (unfold_liftN neutralUnfolds 2 0)) (.core .bvar)) (.core .bvar))))

theorem etaRootStep : Step quotientEnvironmentWF 0 context leftRoot
    (.lam (.sort .zero) (.app leftRoot.lift (.bvar 0))) := .funEta leftTyped

theorem mixedPath : Steps quotientEnvironmentWF 0 context rightRoot
    (.lam (.sort .zero) (.app unfoldedConstructor.lift (.bvar 0))) := by
  have unfoldedTyped := (Step.unfold (environmentWF := quotientEnvironmentWF) constructorUnfolds).hasType
    quotientRegistered contextWF rightTyped
  exact .tail (.tail .rfl (.unfold constructorUnfolds)) (.funEta unfoldedTyped)

theorem mixedCandidatePath : ∃ joined,
    Steps quotientEnvironmentWF 0 context etaRoot joined ∧
    NormalEq context joined (.lam (.sort .zero) (.app unfoldedConstructor.lift (.bvar 0))) ∧
    quotientEnvironment.HasType 0 context joined target ∧
    quotientEnvironment.HasType 0 context (.lam (.sort .zero) (.app unfoldedConstructor.lift (.bvar 0))) target :=
  normal_steps_join quotientRegistered contextWF
    (((etaNormal.defeq contextWF).of_r quotientEnvironmentWF contextWF rightTyped).hasType.1)
    etaNormal mixedPath


-- Eta-right simulation retains the actual changing binder domain.
theorem etaRightChangingDomain : ∃ joined,
    Steps quotientEnvironmentWF 0 context leftRoot joined ∧
    NormalEq context joined (.lam (.sort .zero) (.app unfoldedNeutral.lift (.bvar 0))) ∧
    quotientEnvironment.HasType 0 context joined target ∧
    quotientEnvironment.HasType 0 context (.lam (.sort .zero) (.app unfoldedNeutral.lift (.bvar 0))) target := by
  have sortTyped : quotientEnvironment.HasType 0 context (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial)
  have bodyTyped : quotientEnvironment.HasType 0 (.sort .zero :: context)
      (.forallE (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    HasType.forallE (HasType.bvar .zero) (HasType.sort (by trivial))
  have convertedType := IsDefEq.forallEDF (delayEqual sortTyped).symm bodyTyped
  have convertedFunction := convertedType.defeq leftTyped
  have normal := NormalEq.etaR convertedFunction
    (.refl (etaBody_hasType quotientEnvironmentWF.ordered convertedFunction))
  exact normal_step_join quotientRegistered contextWF leftTyped normal
    (.lam (delayCandidate _ _)
      (.app (.unfold (unfold_liftN neutralUnfolds 1 0)) (.core .bvar)))

-- Three changing candidate steps: unfolding, eta in the function, then beta.
theorem unfoldEtaBetaPath : Steps quotientEnvironmentWF 0 context (.app rightRoot (.bvar 5))
    (.app unfoldedConstructor (.bvar 5)) := by
  have unfoldedTyped := (Step.unfold (environmentWF := quotientEnvironmentWF) constructorUnfolds).hasType
    quotientRegistered contextWF rightTyped
  have beta : ParRed context
      (.app (.lam (.sort .zero) (.app unfoldedConstructor.lift (.bvar 0))) (.bvar 5))
      (.app unfoldedConstructor (.bvar 5)) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar, Nat.lt_irrefl,
      if_false, if_true, VExpr.liftN_zero] using
      (ParRed.beta (A := .sort .zero) (Γ := context)
        (ParRed.rfl (e := .app unfoldedConstructor.lift (.bvar 0))) (ParRed.rfl (e := .bvar 5)))
  exact .tail (.tail (.tail .rfl (.app (.unfold constructorUnfolds) (.core .bvar)))
    (.app (.funEta unfoldedTyped) (.core .bvar))) (.core beta)

theorem mixedWithCore : ∃ joined,
    Steps quotientEnvironmentWF 0 context (.app etaRoot (.bvar 5)) joined ∧
    NormalEq context joined (.app unfoldedConstructor (.bvar 5)) ∧
    quotientEnvironment.HasType 0 context joined suppliedType ∧
    quotientEnvironment.HasType 0 context (.app unfoldedConstructor (.bvar 5)) suppliedType :=
  normal_steps_join quotientRegistered contextWF sourceTyped
    (appNormal contextWF sourceTyped etaNormal (.refl domainTyped)) unfoldEtaBetaPath

end Retained

namespace Proof
open QuotHereditaryExtraTest.ProofCase

def unfoldedProof : VExpr := .app (.bvar 3) (selector (.bvar 5) (.bvar 4) constructor)

theorem proofUnfolds : unfold rightRoot.lift = some unfoldedProof.lift :=
  unfold_liftN (show unfold rightRoot = some unfoldedProof from rfl) 1 0

theorem neutralProofUnfold : ∃ joined,
    Steps quotientEnvironmentWF 0 proofContext (.bvar 0) joined ∧
    NormalEq proofContext joined unfoldedProof.lift ∧
    quotientEnvironment.HasType 0 proofContext joined target ∧
    quotientEnvironment.HasType 0 proofContext unfoldedProof.lift target :=
  normal_step_join quotientRegistered proofContextWF variableTyped proofNormal (.unfold proofUnfolds)

end Proof

end CandidateSimulationTest

namespace CandidateSimulationAudit
open Lean

run_meta
  let roots : List Name := [
    (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "liftSelectorTyped"),
    `Lean4Lean.VEnv.QuotPropReduction.normal_unfold_root,
    (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidUnfoldJoin"),
    `Lean4Lean.VEnv.QuotPropReduction.normal_unfold_join,
    `Lean4Lean.VEnv.QuotPropReduction.normal_funEta_join,
    `Lean4Lean.VEnv.QuotPropReduction.CandidateSimulates,
    `Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates,
    `Lean4Lean.VEnv.QuotPropReduction.normal_step_join,
    `Lean4Lean.VEnv.QuotPropReduction.normal_steps_join,
    `QuotHereditaryExtraTest.equalityEnvironment,
    `QuotHereditaryExtraTest.quotientEnvironment,
    `QuotHereditaryExtraTest.quotientEnvironmentWF,
    `QuotHereditaryExtraTest.quotientRegistered,
    `QuotHereditaryExtraTest.delay,
    `QuotHereditaryExtraTest.delayEqual,
    `QuotHereditaryExtraTest.delayReduction,
    `QuotHereditaryExtraTest.originalValues,
    `QuotHereditaryExtraTest.argumentTypes,
    `QuotHereditaryExtraTest.argumentsTyped,
    `QuotHereditaryExtraTest.delayedValues,
    `QuotHereditaryExtraTest.values,
    `QuotHereditaryExtraTest.valueEqual,
    `QuotHereditaryExtraTest.sourceAt,
    `QuotHereditaryExtraTest.source,
    `QuotHereditaryExtraTest.sourceAtTyped,
    `QuotHereditaryExtraTest.sourceTyped,
    `QuotHereditaryExtraTest.matchedAt,
    `QuotHereditaryExtraTest.matched,
    `QuotHereditaryExtraTest.checked,
    `QuotHereditaryExtraTest.argumentsReduce,
    `QuotHereditaryExtraTest.etaFunction,
    `QuotHereditaryExtraTest.appNormal,
    `QuotHereditaryExtraTest.etaFunctionNormal,
    `QuotHereditaryExtraTest.etaFunctionEqual,
    `QuotHereditaryExtraTest.etaFunctionSimulation,
    `QuotHereditaryExtraTest.leftAt,
    `QuotHereditaryExtraTest.leftAtTyped,
    `QuotHereditaryExtraTest.originalType,
    `QuotHereditaryExtraTest.retainOriginalType,
    `QuotHereditaryExtraTest.etaTree,
    `QuotHereditaryExtraTest.etaTreeNormal,
    `QuotHereditaryExtraTest.etaTreeSimulation,
    `QuotHereditaryExtraTest.rightPrefix,
    `QuotHereditaryExtraTest.rightMajor,
    `QuotHereditaryExtraTest.prefixType,
    `QuotHereditaryExtraTest.rightPrefixTyped,
    `QuotHereditaryExtraTest.rightMajorTyped,
    `QuotHereditaryExtraTest.wrappedPrefix,
    `QuotHereditaryExtraTest.wrappedTyped,
    `QuotHereditaryExtraTest.wrappedNormal,
    `QuotHereditaryExtraTest.hereditaryJoin,
    `QuotHereditaryExtraTest.applicationExtra,
    `QuotHereditaryExtraTest.retainedJoin,
    `QuotHereditaryExtraTest.etaTreeAgainst,
    `QuotHereditaryExtraTest.RetainedEta.target,
    `QuotHereditaryExtraTest.RetainedEta.targetTyped,
    `QuotHereditaryExtraTest.RetainedEta.functionType,
    `QuotHereditaryExtraTest.RetainedEta.respectType,
    `QuotHereditaryExtraTest.RetainedEta.context,
    `QuotHereditaryExtraTest.RetainedEta.prefixTerm,
    `QuotHereditaryExtraTest.RetainedEta.leftRoot,
    `QuotHereditaryExtraTest.RetainedEta.rightRoot,
    `QuotHereditaryExtraTest.RetainedEta.etaRoot,
    `QuotHereditaryExtraTest.RetainedEta.resultType,
    `QuotHereditaryExtraTest.RetainedEta.suppliedType,
    `QuotHereditaryExtraTest.RetainedEta.contextWF,
    `QuotHereditaryExtraTest.RetainedEta.prefixTyped,
    `QuotHereditaryExtraTest.RetainedEta.domainTyped,
    `QuotHereditaryExtraTest.RetainedEta.relationTyped,
    `QuotHereditaryExtraTest.RetainedEta.majorTypeTyped,
    `QuotHereditaryExtraTest.RetainedEta.majorTyped,
    `QuotHereditaryExtraTest.RetainedEta.constructorTyped,
    `QuotHereditaryExtraTest.RetainedEta.leftTyped,
    `QuotHereditaryExtraTest.RetainedEta.rightTyped,
    `QuotHereditaryExtraTest.RetainedEta.rootNormal,
    `QuotHereditaryExtraTest.RetainedEta.etaNormal,
    `QuotHereditaryExtraTest.RetainedEta.sourceTyped,
    `QuotHereditaryExtraTest.RetainedEta.values,
    `QuotHereditaryExtraTest.RetainedEta.matched,
    `QuotHereditaryExtraTest.RetainedEta.checked,
    `QuotHereditaryExtraTest.RetainedEta.firing,
    `QuotHereditaryExtraTest.RetainedEta.twoDependentEtaBinders,
    `QuotHereditaryExtraTest.ProofCase.target,
    `QuotHereditaryExtraTest.ProofCase.targetTyped,
    `QuotHereditaryExtraTest.ProofCase.functionType,
    `QuotHereditaryExtraTest.ProofCase.respectType,
    `QuotHereditaryExtraTest.ProofCase.context,
    `QuotHereditaryExtraTest.ProofCase.prefixTerm,
    `QuotHereditaryExtraTest.ProofCase.leftRoot,
    `QuotHereditaryExtraTest.ProofCase.rightRoot,
    `QuotHereditaryExtraTest.ProofCase.contextWF,
    `QuotHereditaryExtraTest.ProofCase.prefixTyped,
    `QuotHereditaryExtraTest.ProofCase.domainTyped,
    `QuotHereditaryExtraTest.ProofCase.relationTyped,
    `QuotHereditaryExtraTest.ProofCase.majorTypeTyped,
    `QuotHereditaryExtraTest.ProofCase.majorTyped,
    `QuotHereditaryExtraTest.ProofCase.constructorTyped,
    `QuotHereditaryExtraTest.ProofCase.leftTyped,
    `QuotHereditaryExtraTest.ProofCase.rightTyped,
    `QuotHereditaryExtraTest.ProofCase.values,
    `QuotHereditaryExtraTest.ProofCase.matched,
    `QuotHereditaryExtraTest.ProofCase.checked,
    `QuotHereditaryExtraTest.ProofCase.proofContext,
    `QuotHereditaryExtraTest.ProofCase.proofContextWF,
    `QuotHereditaryExtraTest.ProofCase.variableTyped,
    `QuotHereditaryExtraTest.ProofCase.rightLiftTyped,
    `QuotHereditaryExtraTest.ProofCase.proofNormal,
    `QuotHereditaryExtraTest.ProofCase.liftedMatched,
    `QuotHereditaryExtraTest.ProofCase.liftedChecked,
    `QuotHereditaryExtraTest.ProofCase.proofFiring,
    `QuotHereditaryExtraTest.allCapturesChange,
    `QuotHereditaryExtraTest.distinctDomainParameters,
    `QuotHereditaryExtraTest.distinctRelationParameters,
    `QuotHereditaryExtraTest.neutralDoesNotMatch,
    `QuotHereditaryExtraTest.wrappedIsEta,
    `QuotHereditaryExtraTest.originalTypeDelayed,
    `CandidateSimulationTest.delayCandidate,
    `CandidateSimulationTest.wf,
    `CandidateSimulationTest.neutralType,
    `CandidateSimulationTest.neutralResult,
    `CandidateSimulationTest.redexResult,
    `CandidateSimulationTest.neutralUnfolds,
    `CandidateSimulationTest.redexUnfolds,
    `CandidateSimulationTest.wrappedNeutral,
    `CandidateSimulationTest.wrappedNeutralNormal,
    `CandidateSimulationTest.wrappedNeutralTyped,
    `CandidateSimulationTest.neutralHereditaryUnfold,
    `CandidateSimulationTest.originalObstruction,
    `CandidateSimulationTest.delayedSort,
    `CandidateSimulationTest.delayedSortEqual,
    `CandidateSimulationTest.lambdaNormal,
    `CandidateSimulationTest.lambdaStep,
    `CandidateSimulationTest.changingLambdaDomain,
    `CandidateSimulationTest.forallNormal,
    `CandidateSimulationTest.forallStep,
    `CandidateSimulationTest.changingForallDomain,
    `CandidateSimulationTest.Retained.unfoldedNeutral,
    `CandidateSimulationTest.Retained.unfoldedConstructor,
    `CandidateSimulationTest.Retained.neutralUnfolds,
    `CandidateSimulationTest.Retained.constructorUnfolds,
    `CandidateSimulationTest.Retained.etaNeutralNormal,
    `CandidateSimulationTest.Retained.retainedNeutralUnfold,
    `CandidateSimulationTest.Retained.retainedConstructorUnfold,
    `CandidateSimulationTest.Retained.retainedRootUnfold,
    `CandidateSimulationTest.Retained.etaRightNormal,
    `CandidateSimulationTest.Retained.etaRightStructural,
    `CandidateSimulationTest.Retained.etaRootStep,
    `CandidateSimulationTest.Retained.mixedPath,
    `CandidateSimulationTest.Retained.mixedCandidatePath,
    `CandidateSimulationTest.Retained.etaRightChangingDomain,
    `CandidateSimulationTest.Retained.unfoldEtaBetaPath,
    `CandidateSimulationTest.Retained.mixedWithCore,
    `CandidateSimulationTest.Proof.unfoldedProof,
    `CandidateSimulationTest.Proof.proofUnfolds,
    `CandidateSimulationTest.Proof.neutralProofUnfold]

  let manifests : List (Name × List Name) := [
    ((Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "liftSelectorTyped"), [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_unfold_root, [`Quot.sound, `propext]),
    ((Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidUnfoldJoin"), [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_unfold_join, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_funEta_join, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.CandidateSimulates, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_steps_join, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.equalityEnvironment, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.quotientEnvironment, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.quotientEnvironmentWF, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.quotientRegistered, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.delay, []),
    (`QuotHereditaryExtraTest.delayEqual, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.delayReduction, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.originalValues, []),
    (`QuotHereditaryExtraTest.argumentTypes, []),
    (`QuotHereditaryExtraTest.argumentsTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.delayedValues, []),
    (`QuotHereditaryExtraTest.values, [`propext]),
    (`QuotHereditaryExtraTest.valueEqual, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.sourceAt, [`propext]),
    (`QuotHereditaryExtraTest.source, [`propext]),
    (`QuotHereditaryExtraTest.sourceAtTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.sourceTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.matchedAt, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.matched, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.checked, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.argumentsReduce, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaFunction, [`propext]),
    (`QuotHereditaryExtraTest.appNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaFunctionNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaFunctionEqual, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaFunctionSimulation, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.leftAt, [`propext]),
    (`QuotHereditaryExtraTest.leftAtTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.originalType, []),
    (`QuotHereditaryExtraTest.retainOriginalType, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTree, [`propext]),
    (`QuotHereditaryExtraTest.etaTreeNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTreeSimulation, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.rightPrefix, [`propext]),
    (`QuotHereditaryExtraTest.rightMajor, [`propext]),
    (`QuotHereditaryExtraTest.prefixType, []),
    (`QuotHereditaryExtraTest.rightPrefixTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.rightMajorTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.wrappedPrefix, [`propext]),
    (`QuotHereditaryExtraTest.wrappedTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.wrappedNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.hereditaryJoin, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.applicationExtra, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.retainedJoin, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTreeAgainst, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.target, []),
    (`QuotHereditaryExtraTest.RetainedEta.targetTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.functionType, []),
    (`QuotHereditaryExtraTest.RetainedEta.respectType, []),
    (`QuotHereditaryExtraTest.RetainedEta.context, []),
    (`QuotHereditaryExtraTest.RetainedEta.prefixTerm, []),
    (`QuotHereditaryExtraTest.RetainedEta.leftRoot, []),
    (`QuotHereditaryExtraTest.RetainedEta.rightRoot, []),
    (`QuotHereditaryExtraTest.RetainedEta.etaRoot, [`propext]),
    (`QuotHereditaryExtraTest.RetainedEta.resultType, []),
    (`QuotHereditaryExtraTest.RetainedEta.suppliedType, []),
    (`QuotHereditaryExtraTest.RetainedEta.contextWF, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.prefixTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.domainTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.relationTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.majorTypeTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.majorTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.constructorTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.leftTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.rightTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.rootNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.etaNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.sourceTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.values, []),
    (`QuotHereditaryExtraTest.RetainedEta.matched, [`Quot.sound]),
    (`QuotHereditaryExtraTest.RetainedEta.checked, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.firing, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.twoDependentEtaBinders, [`propext]),
    (`QuotHereditaryExtraTest.ProofCase.target, []),
    (`QuotHereditaryExtraTest.ProofCase.targetTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.functionType, []),
    (`QuotHereditaryExtraTest.ProofCase.respectType, []),
    (`QuotHereditaryExtraTest.ProofCase.context, []),
    (`QuotHereditaryExtraTest.ProofCase.prefixTerm, []),
    (`QuotHereditaryExtraTest.ProofCase.leftRoot, []),
    (`QuotHereditaryExtraTest.ProofCase.rightRoot, []),
    (`QuotHereditaryExtraTest.ProofCase.contextWF, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.prefixTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.domainTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.relationTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.majorTypeTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.majorTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.constructorTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.leftTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.rightTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.values, []),
    (`QuotHereditaryExtraTest.ProofCase.matched, [`Quot.sound]),
    (`QuotHereditaryExtraTest.ProofCase.checked, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofContext, []),
    (`QuotHereditaryExtraTest.ProofCase.proofContextWF, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.variableTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.rightLiftTyped, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofNormal, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.liftedMatched, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.liftedChecked, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofFiring, [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.allCapturesChange, [`propext]),
    (`QuotHereditaryExtraTest.distinctDomainParameters, [`propext]),
    (`QuotHereditaryExtraTest.distinctRelationParameters, [`propext]),
    (`QuotHereditaryExtraTest.neutralDoesNotMatch, [`propext]),
    (`QuotHereditaryExtraTest.wrappedIsEta, [`propext]),
    (`QuotHereditaryExtraTest.originalTypeDelayed, []),
    (`CandidateSimulationTest.delayCandidate, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.wf, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.neutralType, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.neutralResult, []),
    (`CandidateSimulationTest.redexResult, []),
    (`CandidateSimulationTest.neutralUnfolds, [`propext]),
    (`CandidateSimulationTest.redexUnfolds, [`propext]),
    (`CandidateSimulationTest.wrappedNeutral, [`propext]),
    (`CandidateSimulationTest.wrappedNeutralNormal, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.wrappedNeutralTyped, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.neutralHereditaryUnfold, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.originalObstruction, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.delayedSort, []),
    (`CandidateSimulationTest.delayedSortEqual, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.lambdaNormal, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.lambdaStep, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.changingLambdaDomain, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.forallNormal, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.forallStep, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.changingForallDomain, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.unfoldedNeutral, []),
    (`CandidateSimulationTest.Retained.unfoldedConstructor, []),
    (`CandidateSimulationTest.Retained.neutralUnfolds, [`propext]),
    (`CandidateSimulationTest.Retained.constructorUnfolds, [`propext]),
    (`CandidateSimulationTest.Retained.etaNeutralNormal, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.retainedNeutralUnfold, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.retainedConstructorUnfold, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.retainedRootUnfold, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.etaRightNormal, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.etaRightStructural, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.etaRootStep, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.mixedPath, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.mixedCandidatePath, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.etaRightChangingDomain, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.unfoldEtaBetaPath, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Retained.mixedWithCore, [`Quot.sound, `propext]),
    (`CandidateSimulationTest.Proof.unfoldedProof, []),
    (`CandidateSimulationTest.Proof.proofUnfolds, [`propext]),
    (`CandidateSimulationTest.Proof.neutralProofUnfold, [`Quot.sound, `propext])]
  unless roots.length == manifests.length do throwError "candidate-simulation manifest count changed"
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.quot_inj,
    `Lean4Lean.VEnv.IsDefEqU.weakN_iff, `Lean4Lean.VEnv.HasType.weakN_iff,
    `Lean4Lean.VEnv.NormalEq.weakN_iff, `Lean4Lean.VEnv.NormalEq.weakN_inv_DFC,
    `Lean4Lean.VEnv.NormalEq.trans, `Lean4Lean.VEnv.ParRed.weakN_inv,
    `Lean4Lean.TrProj, `Classical.choice, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.ParRedExt.parRed_beta, `Lean4Lean.VEnv.hasType_app_bvar0]
  let environment ← getEnv
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing candidate-simulation manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new candidate-simulation axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing candidate-simulation proof {root}"
    if proof.hasSorry then throwError "direct candidate-simulation admission {root}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut axioms : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden candidate-simulation dependency {name} in {root}"
      let some declaration := environment.find? name
        | throwError "missing candidate-simulation dependency {name} in {root}"
      if declaration matches .axiomInfo _ then axioms := axioms.push name
      if declaration.type.hasSorry then throwError "admitted candidate-simulation type {name} in {root}"
      pending := pending ++ declaration.type.getUsedConstants
      if let .inductInfo ii := declaration then pending := pending ++ ii.ctors.toArray
      if let some value := declaration.value? (allowOpaque := true) then
        if value.hasSorry then throwError "candidate-simulation admission {name} in {root}"
        pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "candidate-simulation traversal exceeded bound"
    unless axioms.all (fun n => [`propext, `Quot.sound].contains n) do
      throwError "unexpected candidate-simulation axiom in {root}: {repr axioms}"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "candidate-simulation axiom manifest changed for {root}: {repr axioms}"
    let required : List Name :=
      if root == (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "liftSelectorTyped") then [`Lean4Lean.VEnv.WF.quotientObjects, `Lean4Lean.VEnv.quotLift_inv, `Lean4Lean.VEnv.QuotPropReduction.selector_hasType, `Lean4Lean.VEnv.IsDefEq.sortDF]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_unfold_root then [(Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "liftSelectorTyped"), `Lean4Lean.VEnv.NormalEq.proofIrrel, `Lean4Lean.VEnv.NormalEq.appDF]
      else if root == (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidUnfoldJoin") then [`Lean4Lean.VEnv.QuotPropReduction.normal_unfold_root, `Lean4Lean.VEnv.QuotPropReduction.RigidSpine.rec, `Lean4Lean.VEnv.QuotPropReduction.Steps.applyArguments, `Lean4Lean.VEnv.NormalEq.etaL]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_unfold_join then [(Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str (Name.anonymous) "_private") "Lean4Lean") "Theory") "Typing") "QuotCandidateSimulation") 0) "Lean4Lean") "VEnv") "QuotPropReduction") "rigidUnfoldJoin"), `Lean4Lean.VEnv.QuotPropReduction.normal_spine_expose_applications, `Lean4Lean.VEnv.QuotPropReduction.Steps.core]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_funEta_join then [`Lean4Lean.VEnv.QuotPropReduction.Step.funEta, `Lean4Lean.VEnv.NormalEq.weakN, `Lean4Lean.VEnv.NormalEq.lamDF]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates then [`Lean4Lean.VEnv.QuotPropReduction.normal_parRed_join, `Lean4Lean.VEnv.QuotPropReduction.normal_unfold_join, `Lean4Lean.VEnv.QuotPropReduction.normal_funEta_join, `Lean4Lean.VEnv.QuotPropReduction.Step.defeqDFC, `Lean4Lean.VEnv.QuotPropReduction.Steps.defeqDFC, `Lean4Lean.VEnv.QuotPropReduction.Steps.forallE, `Lean4Lean.VEnv.QuotPropReduction.Step.weakN, `Lean4Lean.VEnv.NormalEq.rec]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_step_join then [`Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates, `Lean4Lean.VEnv.QuotPropReduction.Steps.hasType]
      else if root == `Lean4Lean.VEnv.QuotPropReduction.normal_steps_join then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `ReflTransGen.rec]
      else if root == `CandidateSimulationTest.neutralHereditaryUnfold then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `CandidateSimulationTest.wrappedNeutralNormal, `CandidateSimulationTest.neutralUnfolds]
      else if root == `CandidateSimulationTest.originalObstruction then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `Lean4Lean.VEnv.QuotConfluenceObstruction.normalEq, `Lean4Lean.VEnv.QuotConfluenceObstruction.reduction]
      else if root == `CandidateSimulationTest.changingLambdaDomain then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `CandidateSimulationTest.lambdaNormal, `CandidateSimulationTest.lambdaStep, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold, `Lean4Lean.VEnv.NormalEq.lamDF]
      else if root == `CandidateSimulationTest.changingForallDomain then [`Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates, `CandidateSimulationTest.forallNormal, `CandidateSimulationTest.forallStep, `Lean4Lean.VEnv.NormalEq.forallEDF]
      else if root == `CandidateSimulationTest.Retained.retainedNeutralUnfold then [`Lean4Lean.VEnv.QuotPropReduction.normal_unfold_join, `QuotHereditaryExtraTest.RetainedEta.sourceTyped, `CandidateSimulationTest.Retained.etaNeutralNormal]
      else if root == `CandidateSimulationTest.Retained.retainedConstructorUnfold then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `Lean4Lean.VEnv.QuotPropReduction.Step.app, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold, `QuotHereditaryExtraTest.RetainedEta.etaNormal]
      else if root == `CandidateSimulationTest.Retained.etaRightStructural then [`Lean4Lean.VEnv.QuotPropReduction.normal_candidate_simulates, `CandidateSimulationTest.Retained.etaRightNormal, `Lean4Lean.VEnv.QuotPropReduction.Step.lam, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold]
      else if root == `CandidateSimulationTest.Retained.etaRightChangingDomain then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `Lean4Lean.VEnv.NormalEq.etaR, `CandidateSimulationTest.delayCandidate, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold, `Lean4Lean.VEnv.IsDefEq.forallEDF]
      else if root == `CandidateSimulationTest.Retained.mixedCandidatePath then [`Lean4Lean.VEnv.QuotPropReduction.normal_steps_join, `CandidateSimulationTest.Retained.mixedPath, `Lean4Lean.VEnv.QuotPropReduction.Step.funEta, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold]
      else if root == `CandidateSimulationTest.Retained.mixedWithCore then [`Lean4Lean.VEnv.QuotPropReduction.normal_steps_join, `CandidateSimulationTest.Retained.unfoldEtaBetaPath, `Lean4Lean.VEnv.QuotPropReduction.Step.funEta, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold, `Lean4Lean.VEnv.ParRed.beta]
      else if root == `CandidateSimulationTest.Proof.neutralProofUnfold then [`Lean4Lean.VEnv.QuotPropReduction.normal_step_join, `QuotHereditaryExtraTest.ProofCase.proofNormal, `Lean4Lean.VEnv.NormalEq.proofIrrel, `Lean4Lean.VEnv.QuotPropReduction.Step.unfold]
      else []
    unless required.all visited.contains do
      throwError "candidate-simulation proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

  logInfo m!"CANDIDATE_SIMULATION_AUDIT_COMPLETE {roots.length}"

end CandidateSimulationAudit
