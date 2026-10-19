import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotUnfoldingOverlapTest
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
  simpa [HasType, sourceAt, originalValues, VExpr.liftN, VExpr.inst, VExpr.instVar, VExpr.inst_lift] using
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

def unfolded : VExpr := (QuotPropReduction.unfold source).getD (.sort .zero)

theorem computes : QuotPropReduction.unfold source = some unfolded := rfl

theorem checkedOverlap : ∃ joined,
    ParRed locals source reduced ∧ Step quotientEnvironmentWF 0 locals unfolded joined ∧
    NormalEq locals joined reduced ∧ quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
    quotientEnvironment.HasType 0 locals reduced (.sort .zero) :=
  unfold_extra_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
    sourceTyped computes matched (checked _) argumentsReduce

theorem retainedDependentBinder : ∃ joined,
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) source.lift joined.lift ∧
    Steps quotientEnvironmentWF 0 (.bvar 5 :: locals) source.lift reduced.lift ∧
    NormalEq (.bvar 5 :: locals) joined.lift reduced.lift ∧
    Steps quotientEnvironmentWF 0 locals source joined ∧
    Steps quotientEnvironmentWF 0 locals source reduced ∧ NormalEq locals joined reduced := by
  obtain ⟨joined, originalStep, unfoldedStep, normal, _, _⟩ := checkedOverlap
  have unfoldingPath : Steps quotientEnvironmentWF 0 locals source joined :=
    .tail (.tail .rfl (.unfold computes)) unfoldedStep
  have originalPath : Steps quotientEnvironmentWF 0 locals source reduced := .tail .rfl (.core originalStep)
  have retainedPath := unfoldingPath.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedOriginal := originalPath.weakN (Ctx.LiftN.one (A := .bvar 5))
  have retainedNormal := normal.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness := argumentsTyped (.inr none)
  have restoredPath := retainedPath.instN Ctx.InstN.zero witness
  have restoredOriginal := retainedOriginal.instN Ctx.InstN.zero witness
  have restoredNormal := retainedNormal.instN witness Ctx.InstN.zero
  exact ⟨joined, retainedPath, retainedOriginal, retainedNormal,
    by simpa only [VExpr.inst_lift] using restoredPath,
    by simpa only [VExpr.inst_lift] using restoredOriginal,
    by simpa only [VExpr.inst_lift] using restoredNormal⟩

theorem alternateUniverses {sourceUniverse constructorUniverse : VLevel}
    (sourceWF : sourceUniverse.WF 0) (constructorWF : constructorUniverse.WF 0)
    (sourceZero : zeroLike sourceUniverse = true) (constructorZero : zeroLike constructorUniverse = true) :
    ∃ unfolded joined,
      QuotPropReduction.unfold (sourceAt sourceUniverse constructorUniverse) = some unfolded ∧
      ParRed locals (sourceAt sourceUniverse constructorUniverse) reduced ∧
      Step quotientEnvironmentWF 0 locals unfolded joined ∧ NormalEq locals joined reduced ∧
      quotientEnvironment.HasType 0 locals joined (.sort .zero) ∧
      quotientEnvironment.HasType 0 locals reduced (.sort .zero) := by
  have computed : ∃ unfolded, QuotPropReduction.unfold (sourceAt sourceUniverse constructorUniverse) = some unfolded := by
    simp [sourceAt, QuotPropReduction.unfold, sourceZero]
  obtain ⟨unfolded, computed⟩ := computed
  obtain ⟨joined, originalStep, unfoldedStep, normal, joinedTyped, resultTyped⟩ :=
    unfold_extra_join quotientRegistered (localsWF quotientEnvironmentWF quotientRegistered)
      (sourceAtTyped sourceWF constructorWF ((zeroLike_iff _).mp sourceZero)
        ((zeroLike_iff _).mp constructorZero)) computed
      (matchedAt sourceUniverse constructorUniverse) (checked _) argumentsReduce
  exact ⟨unfolded, joined, computed, originalStep, unfoldedStep, normal, joinedTyped, resultTyped⟩

-- Nonliteral source and constructor universes need not use identical syntax.
example := alternateUniverses (sourceUniverse := .max .zero .zero)
  (constructorUniverse := .imax (.succ .zero) .zero) (by trivial) (by trivial) rfl rfl

theorem prefixAlgorithmComputes : unfoldPrefix source = some unfolded := rfl

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

theorem allArgumentsChange (path : quotLiftPattern.Path) : values path ≠ originalValues path := by
  rcases path with path | path
  · rcases path with _ | (_ | (_ | (_ | (_ | impossible))))
    all_goals first | cases impossible | decide
  · rcases path with _ | (_ | (_ | impossible))
    all_goals first | cases impossible | decide

example : values (.inl (some (some (some (some none))))) ≠ values (.inr (some (some none))) := by decide
example : values (.inl (some (some (some none)))) ≠ values (.inr (some none)) := by decide

run_meta
  let environment ← getEnv
  let roots := [``unfold_extra_join, ``quotientEnvironmentWF, ``quotientRegistered,
    ``delayEqual, ``delayReduction, ``argumentsTyped, ``valueEqual, ``sourceAtTyped,
    ``sourceTyped, ``matchedAt, ``matched, ``checked, ``argumentsReduce, ``computes,
    ``checkedOverlap, ``retainedDependentBinder, ``alternateUniverses, ``allArgumentsChange,
    ``prefixAlgorithmComputes]
  let usesTyping := [``unfold_extra_join, ``delayReduction, ``argumentsReduce,
    ``checkedOverlap, ``retainedDependentBinder, ``alternateUniverses]
  let onlyPropext := [``computes, ``prefixAlgorithmComputes]
  let typingAdmissions := [``IsDefEqU.sort_inv, ``IsDefEqU.forallE_inv_stratified]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  for root in roots do
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new unfolding-overlap axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing unfolding-overlap proof {root}"
    if proof.hasSorry then throwError "direct unfolding-overlap admission {root}"
    let expectedAdmissions := if usesTyping.contains root then typingAdmissions else []
    let expectedAxioms := if onlyPropext.contains root then [``propext]
      else if usesTyping.contains root then [``propext, ``Quot.sound, ``sorryAx]
      else [``propext, ``Quot.sound]
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "unfolding-overlap axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden unfolding-overlap dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved unfolding-overlap admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "unfolding-overlap traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "unfolding-overlap admission manifest changed for {root}: {repr admissions}"
    if root == ``unfold_extra_join then
      unless [``ParRed.extra, ``ParRed.hasType, ``quotLift_inv, ``quotMk_inv,
          ``unfold_sound, ``unfolding_join, ``selector_hasType].all visited.contains do
        throwError "unfolding overlap bypassed the actual rewrite, inversion, selector, or preservation"
    if root == ``checkedOverlap then
      unless [``unfold_extra_join, ``sourceTyped, ``matched, ``checked, ``argumentsReduce].all visited.contains do
        throwError "concrete overlap bypassed checked inputs or argument reductions"
    if root == ``retainedDependentBinder then
      unless [``checkedOverlap, ``NormalEq.weakN, ``NormalEq.instN,
          ``Steps.weakN, ``Steps.instN].all visited.contains do
        throwError "dependent control bypassed typed binder transport"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}; exact axioms {repr axioms}"

end QuotUnfoldingOverlapTest
