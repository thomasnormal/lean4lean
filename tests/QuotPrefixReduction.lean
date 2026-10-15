import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Lean4Lean.Theory.Typing.QuotConfluenceObstruction
import Lean.Util.CollectAxioms

namespace QuotPrefixReductionTest
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

def head : VExpr := .const ``Quot.lift [.zero, .succ .zero]

def sources : List VExpr :=
  [head, .app head (.bvar 5), .app (.app head (.bvar 5)) (.bvar 4),
    .app (.app (.app head (.bvar 5)) (.bvar 4)) (.sort .zero),
    .app (.app (.app (.app head (.bvar 5)) (.bvar 4)) (.sort .zero)) (.bvar 3),
    eliminator, neutral]

def canonicalType (source : VExpr) : VExpr :=
  (applyType (quotLiftConst.type.instL [.zero, .succ .zero]) (spine source).2).getD (.sort .zero)

theorem sourcesTyped : ∀ source ∈ sources,
    quotientEnvironment.HasType 0 locals source (canonicalType source) := by
  obtain ⟨_, _, liftRegistered, _, _, _⟩ := quotientEnvironmentWF.quotientObjects quotientRegistered
  intro source member
  simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [canonicalType, head, eliminator, neutral, locals, respectType, functionType, relationType,
      Lean4Lean.VEnv.QuotConfluenceObstruction.quotient]
    type_tac

theorem allPrefixesCompute : ∀ source ∈ sources, (unfoldPrefix source).isSome = true := by
  intro source member
  simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem allPrefixesReduce : ∀ source ∈ sources,
    ∃ result, unfoldPrefix source = some result ∧
      Steps quotientEnvironmentWF 0 locals source result ∧
      quotientEnvironment.IsDefEq 0 locals source result (canonicalType source) := by
  intro source member
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp (allPrefixesCompute source member)
  have steps := prefix_steps (environmentWF := quotientEnvironmentWF) quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered) (sourcesTyped source member) computed
  exact ⟨result, computed, steps, steps.defeq quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered) (sourcesTyped source member)⟩

example : unfoldPrefix (.bvar 0) = none := rfl

example : unfoldPrefix (.app neutral (.bvar 0)) = none := rfl

example : unfoldPrefix (.const ``Quot.lift [.succ .zero, .succ .zero]) = none := rfl

example : (unfoldPrefix (.const ``Quot.lift [.imax (.param 0) .zero, .succ .zero])).isSome = true := by
  decide +kernel

example : expand 1 (.bvar 0) (.sort .zero) = none := rfl

example : unfoldPrefix neutral = unfold neutral := rfl

example : unfoldPrefix eliminator = some (.lam majorType
    (.app (.bvar 4) (selector (.bvar 6) (.bvar 5) (.bvar 0)))) := rfl

example (steps : Steps quotientEnvironmentWF 0 locals source result) :
    Steps quotientEnvironmentWF 0 locals source result := by
  have weakened := steps.weakN (Ctx.LiftN.one (A := .sort (.succ .zero)))
  have restored := weakened.instN Ctx.InstN.zero (HasType.sort (l := .zero) (by trivial))
  simpa only [VExpr.inst_lift] using restored

example (typed : quotientEnvironment.HasType 0 locals source type)
    (steps : Steps quotientEnvironmentWF 0 locals source result) :
    Steps quotientEnvironmentWF 0 (.sort (.max .zero .zero) :: locals) source.lift result.lift := by
  have conversion : IsDefEqCtx quotientEnvironment 0 locals
      (.sort .zero :: locals) (.sort (.max .zero .zero) :: locals) :=
    .succ .zero (.sortDF (by trivial) (by trivial) (VLevel.equiv_def.mpr fun _ => rfl))
  exact (steps.weakN (Ctx.LiftN.one (A := .sort .zero))).defeqDFC quotientRegistered
    (localsWF quotientEnvironmentWF quotientRegistered) conversion (typed.weak quotientEnvironmentWF.ordered)

run_meta
  let environment ← getEnv
  let mut pending : Array Name := #[``allPrefixesReduce]
  let mut owned : Nat := 0
  for moduleName in [`Lean4Lean.Theory.Typing.QuotPropReduction,
      `Lean4Lean.Theory.Typing.QuotPrefixReduction] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "quotient prefix module absent {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "new prefix axiom {name}"
        if let some proof := information.value? then
          if proof.hasSorry then throwError "direct prefix admission {name}"
        for dependency in (← collectAxioms name) do
          unless [``propext, ``Quot.sound, ``sorryAx].contains dependency do
            throwError "unexpected prefix axiom {dependency} in {name}"
        pending := pending.push name
        owned := owned + 1
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    ``IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff]
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden prefix dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? then pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "prefix dependency traversal exceeded its bound"
  for theoremName in [``etaBody_hasType, ``applyArguments_headTyped, ``unfoldPrefix_complete,
      ``sourcesTyped, ``allPrefixesCompute] do
    for dependency in (← collectAxioms theoremName) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "constructive prefix typing theorem gained {dependency}"
  for theoremName in [``expand_steps, ``prefix_steps, ``prefix_sound, ``prefix_reduces,
      ``sourcesTyped, ``allPrefixesReduce] do
    logInfo m!"{theoremName}: axioms = {repr (← collectAxioms theoremName)}"
  logInfo m!"{owned} owned reduction/prefix declarations audited; all seven quotient-lift prefixes from zero to six supplied arguments compute and reduce at their original types without confluence, strengthening, choice, or new admissions"

end QuotPrefixReductionTest
