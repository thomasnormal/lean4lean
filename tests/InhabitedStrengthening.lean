import Lean4Lean.Verify.Primitive
import Lean.Util.CollectAxioms

namespace InhabitedStrengtheningTest
open Lean Lean4Lean Lean4Lean.VEnv

theorem emptyOrdered : VEnv.empty.Ordered := .empty

theorem propTyped : VEnv.empty.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) := .sort trivial

example : VEnv.empty.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  HasType.weak_inv_of_hasType emptyOrdered propTyped (propTyped.weak emptyOrdered)

example : VEnv.empty.IsDefEqU 0 [] (.sort .zero) (.sort .zero) :=
  IsDefEqU.weak_inv_of_hasType emptyOrdered propTyped ⟨_, propTyped.weak emptyOrdered⟩

example : VEnv.empty.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := by
  have insertion : Ctx.LiftN 1 1 [.sort .zero] [.sort .zero, .sort (.succ .zero)] := .succ .one
  exact HasType.weakN_inv_of_hasType emptyOrdered insertion rfl propTyped (.bvar .zero)

example : VEnv.empty.IsDefEqU 0 [.sort .zero] (.bvar 0) (.bvar 0) := by
  have insertion : Ctx.LiftN 1 1 [.sort .zero] [.sort .zero, .sort (.succ .zero)] := .succ .one
  exact IsDefEqU.weakN_inv_of_hasType emptyOrdered insertion rfl propTyped ⟨_, .bvar .zero⟩

example : VEnv.empty.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) :=
  HasType.weak_inv_of_hasType emptyOrdered (HasType.bvar .zero) (.bvar (.succ .zero))

-- Keep p : P while removing an interior Prop binder, using P from the outer
-- context as its inhabitant. The retained binder's domain shifts across it.
example : VEnv.empty.HasType 0 [.bvar 0, .sort .zero] (.bvar 0) (.bvar 1) := by
  have insertion : Ctx.LiftN 1 1 [.bvar 0, .sort .zero]
      [.bvar 1, .sort .zero, .sort .zero] := .succ .one
  exact HasType.weakN_inv_of_hasType emptyOrdered insertion rfl
    (HasType.bvar .zero) (.bvar .zero)

run_meta
  let environment ← getEnv
  let pureNames := #[``Ctx.LiftN.instN, ``IsDefEq.weakN_inv_of_hasType,
    ``IsDefEq.weak_inv_of_hasType, ``IsDefEqU.weakN_inv_of_hasType,
    ``IsDefEqU.weak_inv_of_hasType, ``HasType.weakN_inv_of_hasType, ``HasType.weak_inv_of_hasType]
  let baseline := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let mut names := pureNames.push ``Environment.Reflection.ite_carrier
  let mut helperCount : Nat := 0
  for (name, _) in environment.constants do
    if match name with
        | .str _ "tr_boundApp_domains" | .str _ "tr_boundApp_arg_inhabited" => true
        | _ => false then
      names := names.push name
      helperCount := helperCount + 1
  unless helperCount == 2 do throwError "inhabited primitive helpers absent or ambiguous"
  for name in names do
    let some information := environment.find? name | throwError "missing inhabited proof {name}"
    if information matches .axiomInfo _ then throwError "new inhabited axiom {name}"
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then throwError "direct inhabited admission {name}"
    for dependency in (← collectAxioms name) do
      unless baseline.contains dependency do throwError "inhabited proof gained {dependency}"
  for name in pureNames do
    for dependency in (← collectAxioms name) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "inhabited substitution gained {dependency}"
  let forbidden := [``IsDefEqU.weakN_iff, ``NormalEq.parRed, ``NormalEq.parRedS,
    ``IsDefEq.church_rosser, ``IsDefEqU.quot_inj]
  let mut pending := names.map fun name => (name, ([] : List Name))
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let (name, path) := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden inhabited dependency {name}: {path.reverse}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants.map (fun dependency => (dependency, name :: path))
      if let some proof := information.value? (allowOpaque := true) then
        pending := pending ++ proof.getUsedConstants.map (fun dependency => (dependency, name :: path))
  unless pending.isEmpty do throwError "inhabited dependency traversal exceeded its bound"
  for name in names do
    logInfo m!"{name}: axioms = {repr (← collectAxioms name)}"
  logInfo "inhabited inverse weakening uses substitution only; actual Reflection.ite_carrier uses Prop as its Type inhabitant and no false strengthening or confluence; other primitive proof-binder strengthening uses remain explicitly outside this repair"

end InhabitedStrengtheningTest
