import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotPrefixApplicationTest
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

def arguments : List VExpr := [.bvar 5, .bvar 4, .sort .zero, .bvar 3, .bvar 2, .bvar 0]
def head : VExpr := .const ``Quot.lift [.zero, .succ .zero]
def sourcePrefix (count : Nat) : VExpr := applyArguments head (arguments.take count)
def argument (count : Nat) : VExpr := arguments[count]!
def canonicalType (count : Nat) : VExpr :=
  (applyType (quotLiftConst.type.instL [.zero, .succ .zero]) (arguments.take count)).getD (.sort .zero)

theorem applicationsTyped (count : Nat) (bounded : count < 6) :
    quotientEnvironment.HasType 0 locals (VExpr.app (sourcePrefix count) (argument count)) (canonicalType (count + 1)) := by
  obtain ⟨_, _, liftRegistered, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 ∨ count = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [canonicalType, sourcePrefix, head, arguments, argument, locals, respectType, functionType,
      relationType, Lean4Lean.VEnv.QuotConfluenceObstruction.quotient]
    type_tac

theorem allSixJoin (count : Nat) (bounded : count < 6) :
    ∃ result domain body, unfoldPrefix (sourcePrefix count) = some result ∧ result = .lam domain body ∧
      unfoldPrefix (VExpr.app (sourcePrefix count) (argument count)) = some (body.inst (argument count)) ∧
      Steps quotientEnvironmentWF 0 locals (VExpr.app (sourcePrefix count) (argument count)) (VExpr.app result (argument count)) ∧
      @ParRed (quotientEnvironmentWF.reductionParams 0) locals
        (VExpr.app result (argument count)) (body.inst (argument count)) ∧
      Steps quotientEnvironmentWF 0 locals (VExpr.app (sourcePrefix count) (argument count)) (body.inst (argument count)) ∧
      quotientEnvironment.HasType 0 locals (body.inst (argument count)) (canonicalType (count + 1)) := by
  have prefixBound : (arguments.take count).length < 6 := Nat.lt_of_le_of_lt (List.length_take_le ..) bounded
  have complete := unfoldPrefix_complete (arguments := arguments.take count)
    (sourceUniverse := VLevel.zero) (targetUniverse := VLevel.succ .zero) rfl (Nat.le_of_lt prefixBound)
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp complete
  obtain ⟨domain, body, shape, nextComputed, firstPath, beta, secondPath, endpointTyped⟩ :=
    prefix_apply_join (environmentWF := quotientEnvironmentWF) quotientRegistered
      (localsWF quotientEnvironmentWF quotientRegistered) prefixBound (applicationsTyped count bounded) computed
  exact ⟨result, domain, body, computed, shape, nextComputed, firstPath, beta, secondPath, endpointTyped⟩

-- A dependent ambient local can be retained, then instantiated at its checked
-- proof. Both reduction paths still reach the identical substituted endpoint.
theorem retainedDependentBinder (count : Nat) (bounded : count < 6) :
    ∃ result body : VExpr,
      Steps quotientEnvironmentWF 0 (.bvar 5 :: locals)
        (VExpr.app (sourcePrefix count) (argument count)).lift (VExpr.app result (argument count)).lift ∧
      Steps quotientEnvironmentWF 0 (.bvar 5 :: locals)
        (VExpr.app result (argument count)).lift (body.inst (argument count)).lift ∧
      Steps quotientEnvironmentWF 0 locals
        (VExpr.app (sourcePrefix count) (argument count)) (body.inst (argument count)) := by
  obtain ⟨result, _, body, _, _, _, firstPath, beta, _, _⟩ := allSixJoin count bounded
  have betaPath : Steps quotientEnvironmentWF 0 locals (VExpr.app result (argument count))
      (body.inst (argument count)) := .tail .rfl (.core beta)
  have firstRetained := firstPath.weakN (Ctx.LiftN.one (A := .bvar 5))
  have betaRetained := betaPath.weakN (Ctx.LiftN.one (A := .bvar 5))
  have witness : quotientEnvironment.HasType 0 locals (.bvar 1) (.bvar 5) := by
    unfold locals respectType functionType relationType Lean4Lean.VEnv.QuotConfluenceObstruction.quotient
    type_tac
  have restored := Steps.instN Ctx.InstN.zero witness (firstRetained.trans betaRetained)
  exact ⟨result, body, firstRetained, betaRetained, by simpa only [VExpr.inst_lift] using restored⟩

deriving instance BEq for VLevel
deriving instance BEq for VExpr

def computationControls : Bool :=
  ([VLevel.zero, .max .zero .zero, .imax (.param 0) .zero].all fun sourceUniverse =>
    [VLevel.zero, .succ .zero, .max (.succ .zero) .zero].all fun targetUniverse =>
      (List.range 6).all fun count =>
        let source := applyArguments (.const ``Quot.lift [sourceUniverse, targetUniverse]) (arguments.take count)
        match unfoldPrefix source with
        | some (.lam _ body) => unfoldPrefix (VExpr.app source (argument count)) == some (body.inst (argument count))
        | _ => false)

example : computationControls = true := by decide +kernel
example : unfoldPrefix (VExpr.app neutral (.bvar 0)) = none := rfl
example : expand 1 (.bvar 0) (.sort .zero) = none := rfl

run_meta
  let environment ← getEnv
  let roots := [``spine_applyArguments, ``applyType_append, ``expand_inst, ``expand_apply,
    ``unfoldPrefix_apply, ``expand_apply_join, ``prefix_apply_join, ``quotientEnvironmentWF,
    ``quotientRegistered, ``applicationsTyped, ``allSixJoin, ``retainedDependentBinder, ``computationControls]
  let usesTyping := [``expand_apply_join, ``prefix_apply_join, ``allSixJoin, ``retainedDependentBinder]
  let onlyPropext := [``spine_applyArguments, ``applyType_append, ``computationControls]
  let typingAdmissions : List Name := []
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN]
  for root in roots do
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new prefix application axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing prefix application proof {root}"
    if proof.hasSorry then throwError "direct prefix application admission {root}"
    let expectedAdmissions := if usesTyping.contains root then typingAdmissions else []
    let expectedAxioms := if onlyPropext.contains root then [``propext]
      else if usesTyping.contains root then [``propext, ``Quot.sound]
      else [``propext, ``Quot.sound]
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "prefix application axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden prefix application dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved prefix application admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "prefix application traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "prefix application admission manifest changed for {root}: {repr admissions}"
    if root == ``prefix_apply_join then
      unless [``unfoldPrefix_apply, ``prefix_steps, ``ParRed.beta, ``Steps.hasType].all visited.contains do
        throwError "prefix application bypassed the algorithm, beta, or preservation proof"
    if root == ``expand_apply_join then
      unless [``expand_apply, ``expand_steps, ``ParRed.beta, ``Steps.hasType].all visited.contains do
        throwError "generic application bypassed expansion, beta, or preservation"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}; exact axioms {repr axioms}"

end QuotPrefixApplicationTest
