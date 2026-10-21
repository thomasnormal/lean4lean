import Lean4Lean.Verify.Environment.Primitive.Condition
import Lean.Util.CollectAxioms

/-! Close a dependent proof telescope using actual witnesses. Audit the complete
conditional-gadget extraction, while retaining the recognizer's wider trust limits.
The production construction follows upstream draft PR #53 (5a8c0d5). -/
namespace ReflectionGadgetInhabitantsTest
open Lean Lean4Lean Lean4Lean.TypeChecker Lean4Lean.Primitive

abbrev proposition : Expr := .forallE `P (.sort .zero)
  (.forallE `h (.bvar 0) (.bvar 1) .default) .default
abbrev propositionModel : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
abbrev proof : Expr := .lam `P (.sort .zero)
  (.lam `h (.bvar 0) (.bvar 0) .default) .default
abbrev proofModel : VExpr := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

-- The proposition and its proof exist in the empty environment. In particular,
-- the proof binder is closed using its own witness, rather than an arbitrary zero.
theorem propositionTyped : VEnv.empty.HasType 0 [] propositionModel (.sort .zero) := by
  have inner : VEnv.empty.HasType 0 [(.sort .zero)]
      (.forallE (.bvar 0) (.bvar 1)) (.sort .zero) := by
    exact .defeq (.sortDF (by exact ⟨trivial, trivial⟩) (by trivial) VLevel.imax_zero)
      (.forallE (.bvar .zero) (.bvar (.succ .zero)))
  exact .defeq (.sortDF (by exact ⟨trivial, trivial⟩) (by trivial) VLevel.imax_zero)
    (.forallE (.sort trivial) inner)

theorem propositionTranslation : TrExprS VEnv.empty [] [] proposition propositionModel :=
  .forallE ⟨_, .sort trivial⟩ ⟨_, .forallE (.bvar .zero) (.bvar (.succ .zero))⟩
    (.sort rfl) (.forallE ⟨_, .bvar .zero⟩ ⟨_, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl))

theorem proofTyped : VEnv.empty.HasType 0 [] proofModel propositionModel :=
  .lam (.sort trivial) (.lam (.bvar .zero) (.bvar .zero))

theorem proofTranslation : TrExprS VEnv.empty [] [] proof proofModel :=
  .lam ⟨_, .sort trivial⟩ (.sort rfl)
    (.lam ⟨_, .bvar .zero⟩ (.bvar rfl) (.bvar rfl))

abbrev telescope : VLCtx := [(none, .vlam (.bvar 0)), (none, .vlam (.sort .zero))]
abbrev afterProposition : VLCtx := [(none, .vlam propositionModel)]

-- A lambda and an anonymous let remain above both removed ambient binders.
abbrev nested : Expr := .lam `P (.sort .zero)
  (.letE `alias (.sort .zero) (.bvar 0) (.bvar 0) false) .default
abbrev nestedModel : VExpr := .lam (.sort .zero) (.bvar 0)

theorem nestedTranslation : TrExprS VEnv.empty [] telescope nested nestedModel :=
  .lam ⟨_, .sort trivial⟩ (.sort rfl)
    (.letE (.bvar .zero) (.sort rfl) (.bvar rfl) (.bvar rfl))

theorem retainedDependentProofBinder :
    TrExprS VEnv.empty [] afterProposition nested nestedModel := by
  have result := TrExprS.peel_outer (env := VEnv.empty) (Us := []) .empty (x := nested) rfl
    propositionTranslation propositionTyped (.succ (d := .vlam (.bvar 0)) .zero)
    nestedTranslation rfl rfl
  simpa [VLocalDecl.inst, VLocalDecl.depth, VExpr.inst, VExpr.instVar,
    VExpr.liftN, liftVar, nestedModel, afterProposition, propositionModel] using result

theorem closeActualProof : TrExprS VEnv.empty [] [] nested nestedModel := by
  have result := TrExprS.peel_outer (env := VEnv.empty) (Us := []) .empty (x := nested) rfl proofTranslation proofTyped .zero
    retainedDependentProofBinder rfl rfl
  simpa [VExpr.inst, VExpr.instVar, nestedModel] using result

run_meta
  let environment ← getEnv
  let forbidden := [``TrExprS.ofClosed, ``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``VEnv.IsDefEqU.weakN_iff, ``VEnv.IsDefEq.weakN_iff, ``VEnv.HasType.weakN_iff,
    ``VEnv.IsType.weakN_iff, ``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj,
    ``TrProj.weak', ``TrProj.instN, ``TrProj.wf, ``TrExprS.instN, ``TrExprS.instN_var,
    ``TrExprS.weakBV, ``TrExprS.wf]
  let projection := [``TrProj]
  let typing : List Name := []
  let witnesses := [``propositionTyped, ``propositionTranslation, ``proofTyped,
    ``proofTranslation, ``nestedTranslation, ``retainedDependentProofBinder, ``closeActualProof]
  let transport := [``TrExprS.weakBV_noProj, ``TrExprS.instN_var_noProj,
    ``TrExprS.instN_noProj, ``TrExprS.wf_noProj, ``TrExprS.closedN_nil_noProj]
  let roots := [``noProj_liftLooseBVars, ``TrExprS.peel_outer, ``Condition.check.gadget_types_of_closed_decision,
    ``Condition.check.gadget_types, ``Condition.check.gadget_pieces] ++ transport ++ witnesses
  for root in roots do
    let information ← getConstInfo root
    if information matches .axiomInfo _ then throwError "new gadget axiom {root}"
    let some value := information.value? (allowOpaque := true)
      | throwError "missing gadget proof {root}"
    if value.hasSorry then throwError "direct gadget gap {root}"
    let expected := if root == ``Condition.check.gadget_pieces then
        projection ++ typing
      else if root == ``Condition.check.gadget_types_of_closed_decision ||
          root == ``Condition.check.gadget_types then typing
      else if transport.contains root || root == ``TrExprS.peel_outer || root == ``retainedDependentProofBinder ||
          root == ``closeActualProof then projection
      else []
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden gadget dependency {name} in {root}"
      if let some info := environment.find? name then
        pending := pending ++ info.type.getUsedConstants
        if let some body := info.value? (allowOpaque := true) then
          if body.hasSorry then
            unless expected.contains name do throwError "unexpected gadget gap {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ body.getUsedConstants
    unless pending.isEmpty do throwError "gadget dependency traversal exceeded bound"
    unless expected.length == admissions.size && expected.all admissions.contains do
      throwError "gadget gap manifest changed for {root}: {repr admissions}"
    let axioms ← collectAxioms root
    let expectedAxioms := if root == ``proofTyped || root == ``noProj_liftLooseBVars then [``propext]
      else if root == ``propositionTyped then [``propext, ``Quot.sound]
      else [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "gadget axiom manifest changed for {root}: {repr axioms}"
    logInfo m!"{root}: {visited.size} dependencies; exact gaps {repr admissions}; axioms {repr axioms}"
  let some consumer := (← getConstInfo ``Condition.check.gadget_pieces).value? (allowOpaque := true)
    | throwError "missing actual gadget consumer"
  let direct := consumer.getUsedConstants
  for required in [``TrExprS.peel_outer, ``Condition.check.gadget_types_of_closed_decision] do
    unless direct.contains required do throwError "actual gadget lost checked-witness construction {required}"
  let some recognizer := (← getConstInfo ``Condition.check.WF).value? (allowOpaque := true)
    | throwError "missing actual conditional recognizer"
  unless recognizer.getUsedConstants.contains ``Condition.check.gadget_pieces do
    throwError "recognizer disconnected from gadget extraction"
  if recognizer.hasSorry then throwError "direct recognizer gap"
  let recognizerAxioms ← collectAxioms ``Condition.check.WF
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
  let names := recognizerAxioms.map Name.toString
  unless names.size == baseline.size && names.all baseline.contains && baseline.all names.contains do
    throwError "recognizer's inherited trust boundary changed: {repr recognizerAxioms}"
  logInfo m!"actual recognizer retains {recognizerAxioms.size} inherited axioms; broader checker gaps remain"

end ReflectionGadgetInhabitantsTest
