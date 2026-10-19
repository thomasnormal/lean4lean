import Lean4Lean.Verify.Environment.Primitive.Recursion
import Lean.Util.CollectAxioms

/-! Inverse weakening needs inhabitants, even for expressions that omit the removed
variables. Exercise the typed-substitution replacement on a dependent telescope,
a nonempty base context, and a retained binder depending on that base context. -/
namespace InhabitedTelescopeTest
open Lean Lean4Lean

abbrev base : List VExpr := [.sort .zero]
abbrev domains : List VExpr := [.sort (.succ (.succ .zero)), .bvar 0]
abbrev arguments : List VExpr := [.sort (.succ .zero), .sort .zero]

theorem baseWF : OnCtx base (VEnv.empty.IsType 0) :=
  ⟨trivial, _, .sort trivial⟩

theorem extendedWF : OnCtx (domains.reverse ++ base) (VEnv.empty.IsType 0) :=
  ⟨⟨baseWF, _, .sort trivial⟩, _, .bvar .zero⟩

-- The second domain is a variable, instantiated by the first actual argument.
theorem argumentsTyped : VExpr.ArgsTyped VEnv.empty 0 base domains .id arguments := by
  refine .cons ?_ (.cons ?_ .nil)
  · exact .sort trivial
  · exact .sort trivial

-- A base variable really shifts across both domains; use a beta equality so the
-- equality transport also exercises distinct endpoints.
theorem dependentEquality : VEnv.empty.IsDefEq 0 base
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.bvar 0) (.sort .zero) := by
  apply VEnv.IsDefEq.weakN_inv_of_argsTyped .empty extendedWF argumentsTyped
  exact .beta (.bvar .zero) (.bvar (.succ (.succ .zero)))

theorem dependentTyping : VEnv.empty.HasType 0 base (.bvar 0) (.sort .zero) := by
  apply VEnv.HasType.weakN_inv_of_argsTyped .empty extendedWF argumentsTyped
  exact .bvar (.succ (.succ .zero))

-- Retain a binder of type p, where p is the base context's proposition. Removing
-- the inserted telescope must preserve the new variable and renumber its type.
theorem retainedDependentBinder : VEnv.empty.IsDefEqU 0 (.bvar 0 :: base)
    (.bvar 0) (.bvar 0) := by
  apply VEnv.IsDefEqU.weakN_inv_of_argsTyped_under .empty extendedWF argumentsTyped
    (domain := .bvar 0) (u := .zero) (.bvar .zero)
  exact ⟨.bvar 3, .bvar .zero⟩

theorem emptyTelescope : VEnv.empty.HasType 0 base (.bvar 0) (.sort .zero) := by
  apply VEnv.HasType.weakN_inv_of_argsTyped .empty
    (As := []) (vs := []) baseWF .nil
  exact .bvar .zero

theorem twoRetainedBinders (expression : VExpr) :
    (expression.liftN 2 2).subst ((VExpr.Subst.id.consN arguments).liftN 2) = expression :=
  VExpr.liftN_subst_consN_liftN expression arguments 2

run_meta
  let environment ← getEnv
  let helpers := #[``VExpr.Subst.lift_l_consN_liftN, ``VExpr.liftN_subst_consN_liftN,
    ``VExpr.ArgsTyped.length_eq, ``VEnv.IsDefEq.weakN_inv_of_argsTyped,
    ``VEnv.HasType.weakN_inv_of_argsTyped, ``VEnv.IsDefEqU.weakN_inv_of_argsTyped_under]
  let witnesses := #[``baseWF, ``extendedWF, ``argumentsTyped, ``dependentEquality,
    ``dependentTyping, ``retainedDependentBinder, ``emptyTelescope, ``twoRetainedBinders]
  for name in helpers ++ witnesses do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "new telescope axiom {name}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "telescope proof absent: {name}"
    if proof.hasSorry then throwError "direct telescope admission: {name}"
    for dependency in (← collectAxioms name) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "telescope proof gained {dependency} in {name}"
    logInfo m!"{name}: {repr (← collectAxioms name)}"
  let forbidden := [``VEnv.IsDefEqU.weakN_iff, ``VEnv.IsDefEq.weakN_iff,
    ``VEnv.HasType.weakN_iff,
    ``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser]
  let mut pending := helpers ++ witnesses
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden telescope dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "telescope dependency traversal exceeded its bound"
  let consumer := ``Primitive.unfoldNatWellFounded.WF'
  let information ← getConstInfo consumer
  let some proof := information.value? (allowOpaque := true)
    | throwError "actual recursion consumer proof absent"
  if proof.hasSorry then throwError "direct recursion consumer admission"
  let direct := proof.getUsedConstants
  for name in [``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv] do
    if direct.contains name then throwError "direct general context extraction remains: {name}"
  for required in [``VEnv.HasType.weakN_inv_of_argsTyped,
      ``VEnv.IsDefEqU.weakN_inv_of_argsTyped_under] do
    unless direct.contains required do throwError "actual consumer no longer uses {required}"
  for name in forbidden do
    if direct.contains name then throwError "direct false strengthening/confluence call {name}"
  -- Pre-change axiom manifest, measured from d0f7742's actual Recursion source.
  -- These are inherited dependencies, not a soundness claim for the consumer.
  let baseline : Array String := #["Classical.choice",
    "Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7",
    "Lean.Expr.abstractRange_eq",
    "Lean.Expr.abstract_eq",
    "Lean.Expr.eqv_eq",
    "Lean.Expr.hasLooseBVar_eq",
    "Lean.Expr.instantiate1_eq",
    "Lean.Expr.instantiateRange_eq",
    "Lean.Expr.instantiateRevRange_eq",
    "Lean.Expr.instantiateRev_eq",
    "Lean.Expr.instantiate_eq",
    "Lean.Expr.looseBVarRange_eq",
    "Lean.Expr.lowerLooseBVars_eq",
    "Lean.Expr.mkAppData_eq",
    "Lean.Expr.mkData_eq",
    "Lean.Expr.replace_eq",
    "Lean.Level.hasMVar_eq",
    "Lean.Level.hasParam_eq",
    "Lean.Level.instLawfulBEqLevel",
    "Lean.Level.isExplicitSubsumedAux_eq",
    "Lean.Level.normalize_eq",
    "Lean.PersistentArray.toList'_push",
    "Lean.PersistentHashMap.WF.find?_eq",
    "Lean.PersistentHashMap.WF.toList'_insert",
    "Lean.PersistentHashMap.findAux_isSome",
    "Lean.Syntax.structEq_eq",
    "Lean4Lean.ptrEqConstantInfo_eq",
    "Lean4Lean.ptrEqExpr_eq",
    "Quot.sound",
    "Std.TreeMap.all_eq_all_toList",
    "_private.Lean4Lean.Verify.Expr.0.Lean.Expr.mkData_flags._native.bv_decide.ax_1_12",
    "propext",
    "sorryAx"]
  for name in #[consumer, ``Primitive.unfoldNatWellFounded.WF,
      ``Primitive.unfoldNatWellFounded.WF₂] do
    let actual ← collectAxioms name
    let names := actual.map Name.toString
    unless names.size == baseline.size && names.all baseline.contains && baseline.all names.contains do
      throwError "recursion axiom manifest changed: {name}: {repr actual}"
    logInfo m!"{name}: unchanged {actual.size}-axiom inherited manifest (includes sorryAx)"
  logInfo "six typed telescope helpers and dependent witnesses exclude admissions, choice, false strengthening and confluence; actual recursion consumer uses both transports directly; its inherited admissions remain"

end InhabitedTelescopeTest
