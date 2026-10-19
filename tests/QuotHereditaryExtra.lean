import Lean4Lean.Theory.Typing.QuotHereditaryExtra
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

open private proofSpineType constantNormalCases rigidPropJoin matchedLiftSpine reduceMatchedCaptures
  from Lean4Lean.Theory.Typing.QuotHereditaryExtra

run_meta
  let environment ← getEnv
  let roots := [``normal_quot_prop_root, ``Steps.applyArguments, ``ParRed.applyArguments, ``normal_quot_prop_join, ``CoreSimulates.app_quot_prop_extra, ``proofSpineType, ``constantNormalCases, ``rigidPropJoin, ``matchedLiftSpine, ``reduceMatchedCaptures, ``quotientEnvironmentWF, ``quotientRegistered, ``argumentsTyped, ``valueEqual, ``sourceTyped, ``matched, ``checked, ``argumentsReduce, ``etaTreeNormal, ``etaTreeSimulation, ``rightPrefixTyped, ``rightMajorTyped, ``wrappedTyped, ``wrappedNormal, ``hereditaryJoin, ``applicationExtra, ``retainedJoin, ``etaTreeAgainst, ``RetainedEta.targetTyped, ``RetainedEta.contextWF, ``RetainedEta.prefixTyped, ``RetainedEta.domainTyped, ``RetainedEta.relationTyped, ``RetainedEta.majorTypeTyped, ``RetainedEta.majorTyped, ``RetainedEta.constructorTyped, ``RetainedEta.leftTyped, ``RetainedEta.rightTyped, ``RetainedEta.rootNormal, ``RetainedEta.etaNormal, ``RetainedEta.sourceTyped, ``RetainedEta.matched, ``RetainedEta.checked, ``RetainedEta.firing, ``RetainedEta.twoDependentEtaBinders, ``ProofCase.targetTyped, ``ProofCase.contextWF, ``ProofCase.prefixTyped, ``ProofCase.rightTyped, ``ProofCase.proofContextWF, ``ProofCase.variableTyped, ``ProofCase.rightLiftTyped, ``ProofCase.proofNormal, ``ProofCase.liftedMatched, ``ProofCase.liftedChecked, ``ProofCase.proofFiring, ``allCapturesChange, ``distinctDomainParameters, ``distinctRelationParameters, ``neutralDoesNotMatch, ``wrappedIsEta, ``originalTypeDelayed]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.sort_forallE_inv, ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``HasType.weakN_iff,
    ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC, ``NormalEq.trans,
    ``ParRed.weakN_inv, ``ParRedExt.parRed_beta, ``hasType_app_bvar0,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_prop_root, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.Steps.applyArguments, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.ParRed.applyArguments, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.normal_quot_prop_join, [], [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.QuotPropReduction.CoreSimulates.app_quot_prop_extra, [], [`Quot.sound, `propext]),
    (``proofSpineType, [], [`Quot.sound, `propext]),
    (``constantNormalCases, [], [`Quot.sound, `propext]),
    (``rigidPropJoin, [], [`Quot.sound, `propext]),
    (``matchedLiftSpine, [], []),
    (``reduceMatchedCaptures, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.quotientEnvironmentWF, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.quotientRegistered, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.argumentsTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.valueEqual, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.sourceTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.matched, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.checked, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.argumentsReduce, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTreeNormal, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTreeSimulation, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.rightPrefixTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.rightMajorTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.wrappedTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.wrappedNormal, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.hereditaryJoin, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.applicationExtra, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.retainedJoin, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.etaTreeAgainst, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.targetTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.contextWF, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.prefixTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.domainTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.relationTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.majorTypeTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.majorTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.constructorTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.leftTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.rightTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.rootNormal, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.etaNormal, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.sourceTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.matched, [], [`Quot.sound]),
    (`QuotHereditaryExtraTest.RetainedEta.checked, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.firing, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.RetainedEta.twoDependentEtaBinders, [], [`propext]),
    (`QuotHereditaryExtraTest.ProofCase.targetTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.contextWF, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.prefixTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.rightTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofContextWF, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.variableTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.rightLiftTyped, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofNormal, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.liftedMatched, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.liftedChecked, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.ProofCase.proofFiring, [], [`Quot.sound, `propext]),
    (`QuotHereditaryExtraTest.allCapturesChange, [], [`propext]),
    (`QuotHereditaryExtraTest.distinctDomainParameters, [], [`propext]),
    (`QuotHereditaryExtraTest.distinctRelationParameters, [], [`propext]),
    (`QuotHereditaryExtraTest.neutralDoesNotMatch, [], [`propext]),
    (`QuotHereditaryExtraTest.wrappedIsEta, [], [`propext]),
    (`QuotHereditaryExtraTest.originalTypeDelayed, [], [])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing hereditary EXTRA manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new hereditary EXTRA axiom {root}"
    let some proof := info.value? | throwError "missing hereditary EXTRA proof {root}"
    if proof.hasSorry then throwError "direct hereditary EXTRA admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "hereditary EXTRA axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden hereditary EXTRA dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then throwError "admitted type {name} in {root}"
        if let some value := declaration.value? then
          if value.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unapproved hereditary EXTRA admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "hereditary EXTRA traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "hereditary EXTRA admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``normal_quot_prop_root then
        [``Step.unfold, ``selector_hasType, ``NormalEq.proofIrrel, ``quotLift_inv, ``quotMk_inv]
      else if root == ``proofSpineType then [``HasType.spine_head]
      else if root == ``rigidPropJoin then
        [``RigidSpine.rec, ``normal_quot_prop_root, ``proofSpineType, ``constantNormalCases,
          ``Pattern.Check.OK.weakN, ``Steps.lam, ``NormalEq.etaL, ``ParRed.hasType]
      else if root == ``normal_quot_prop_join then
        [``normal_spine_expose_applications, ``rigidPropJoin, ``matchedLiftSpine,
          ``Steps.core, ``ParRed.extra, ``Steps.hasType]
      else if root == ``reduceMatchedCaptures then
        [``Pattern.Matches.rec, ``ParRed.app, ``ParRed.const]
      else if root == ``CoreSimulates.app_quot_prop_extra then
        [``HasType.matches_inv, ``ParRed.defeq, ``reduceMatchedCaptures,
          ``normal_quot_prop_join, ``NormalEq.appDF, ``ParRed.extra, ``Steps.app]
      else if root == ``hereditaryJoin then
        [``normal_quot_prop_join, ``wrappedNormal, ``wrappedTyped, ``matched, ``checked]
      else if root == ``applicationExtra then
        [``CoreSimulates.app_quot_prop_extra, ``etaTreeSimulation, ``argumentsReduce, ``wrappedTyped]
      else if root == ``retainedJoin then
        [``applicationExtra, ``Steps.weakN, ``Steps.instN, ``NormalEq.weakN]
      else if root == ``RetainedEta.firing then
        [``normal_quot_prop_join, ``RetainedEta.etaNormal, ``RetainedEta.sourceTyped,
          ``RetainedEta.matched, ``RetainedEta.checked, ``etaTreeAgainst]
      else if root == ``ProofCase.proofFiring then
        [``normal_quot_prop_join, ``ProofCase.proofNormal, ``NormalEq.proofIrrel,
          ``ProofCase.liftedMatched, ``ProofCase.liftedChecked]
      else []
    unless required.all visited.contains do
      throwError "hereditary EXTRA control bypassed required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"


end QuotHereditaryExtraTest
