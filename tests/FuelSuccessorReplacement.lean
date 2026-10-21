import Lean4Lean.Verify.Environment.Primitive.Recursion
import Lean.Util.CollectAxioms

/-! Same-context replacement needs no inhabitant outside a removed binder.
The construction and successor-closing identity follow upstream PR #53.
Keep arbitrary proof binders in scope, and audit the actual recursion consumer. -/
namespace FuelSuccessorReplacementTest
open Lean Lean4Lean Lean4Lean.TypeChecker

abbrev propositionId : FVarId := ⟨`proposition⟩
abbrev proofId : FVarId := ⟨`proof⟩
abbrev base : VLCtx := [(some (propositionId, []), .vlam (.sort .zero))]
abbrev context : VLCtx := (some (proofId, []), .vlam (.bvar 0)) :: base

theorem contextWF : VLCtx.WF VEnv.empty 0 context := by
  have baseWF : VLCtx.WF VEnv.empty 0 base := by
    refine ⟨trivial, ?_, _, .sort trivial⟩
    intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars]
  refine ⟨baseWF, ?_, _, .bvar .zero⟩
  intro fv deps equal
  cases Option.some.inj equal
  simp [VLCtx.fvars, base, propositionId, proofId]

-- The only witness supplied is the proof variable already in the same context.
-- No proof of the arbitrary base proposition is assumed in the outer context.
theorem replacementUnderProofBinder :
    TrExprS VEnv.empty [] context (.fvar propositionId) (.bvar 1) := by
  have source : TrExprS VEnv.empty [] context (.fvar propositionId) (.bvar 1) := .fvar rfl
  have witness : TrExprS VEnv.empty [] context (.fvar proofId) (.bvar 0) := .fvar rfl
  exact TrExprS.replace_unused_fvar (Us := []) .empty contextWF witness (.bvar .zero) source trivial
    (by change propositionId ≠ proofId; simp [propositionId, proofId])

theorem replacementBeneathLambda : TrExprS VEnv.empty [] context
    (.lam `x (.fvar propositionId) (.bvar 0) .default) (.lam (.bvar 1) (.bvar 0)) := by
  have source : TrExprS VEnv.empty [] context
      (.lam `x (.fvar propositionId) (.bvar 0) .default) (.lam (.bvar 1) (.bvar 0)) :=
    .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl) (.bvar rfl)
  have witness : TrExprS VEnv.empty [] context (.fvar proofId) (.bvar 0) := .fvar rfl
  exact TrExprS.replace_unused_fvar (Us := []) .empty contextWF witness (.bvar .zero) source
    ⟨trivial, by change 0 < 1; decide⟩
    ⟨by change propositionId ≠ proofId; simp [propositionId, proofId], trivial⟩

-- The actual fuel replacement, over a nonempty base, closes at adjacent numerals.
section
variable {env : VEnv} (ordered : env.Ordered) (primitives : env.HasPrimitives)
  (natPresent : env.contains ``Nat)
include ordered primitives natPresent
abbrev fuelContext : VLCtx := (some (proofId, []), .vlam .nat) :: base

theorem fuelContextWF : VLCtx.WF env 0 fuelContext := by
  have baseWF : VLCtx.WF env 0 base := by
    refine ⟨trivial, ?_, _, .sort trivial⟩
    intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars]
  refine ⟨baseWF, ?_, primitives.natIsType (Us := []) (Δ := base) ordered natPresent baseWF.toCtx⟩
  intro fv deps equal
  cases Option.some.inj equal
  simp [VLCtx.fvars, base, propositionId, proofId]

theorem successorReplacement : TrExprS env [] fuelContext (.fvar propositionId)
    (((VExpr.bvar 1).liftN 1 1).inst (.app .natSucc (.bvar 0))) := by
  have fuel : TrExprS env [] fuelContext (.fvar proofId) (.bvar 0) := .fvar rfl
  have fuelTyped : env.HasType 0 fuelContext.toCtx (.bvar 0) .nat := .bvar .zero
  have successor := TrExprS.natSucc (Us := []) (Δ := fuelContext) primitives natPresent
  exact TrExprS.replace_unused_fvar ordered (fuelContextWF ordered primitives natPresent)
    (.app successor.2 fuelTyped successor.1 fuel) (.app successor.2 fuelTyped)
    (.fvar rfl) trivial (by change propositionId ≠ proofId; simp [propositionId, proofId])
end

theorem adjacentClosings (expression : VExpr) (tail : VExpr.Subst) (fuel : Nat) :
    ((expression.liftN 1 1).inst (.app .natSucc (.bvar 0))).subst
      (tail.cons (.natLit fuel)) = expression.subst (tail.cons (.natLit (fuel + 1))) := by
  simpa only [VExpr.subst_app, VExpr.subst_natSucc, VExpr.subst_bvar, VExpr.Subst.cons,
    VExpr.natLit] using (VExpr.liftN_one_one_inst_subst_cons
    (e := expression) (u := .app .natSucc (.bvar 0)) (k := .natLit fuel) (B := tail))

run_meta
  let environment ← getEnv
  let roots := #[``TrExprS.replace_unused_fvar, ``VExpr.liftN_one_one_inst_subst_cons,
    ``contextWF, ``replacementUnderProofBinder, ``replacementBeneathLambda,
    ``fuelContextWF, ``successorReplacement, ``adjacentClosings]
  let forbidden := [``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``VEnv.IsDefEqU.weakN_iff, ``VEnv.IsDefEq.weakN_iff, ``VEnv.HasType.weakN_iff,
    ``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser,
    ``VEnv.IsDefEqU.quot_inj]
  for name in roots do
    let info ← getConstInfo name
    if info matches .axiomInfo _ then throwError "new fuel replacement axiom {name}"
    let some value := info.value? (allowOpaque := true) | throwError "missing fuel replacement proof {name}"
    if value.hasSorry then throwError "direct fuel replacement admission {name}"
    let pure := [``VExpr.liftN_one_one_inst_subst_cons, ``adjacentClosings]
    let allowed := if pure.contains name then [``propext, ``Quot.sound]
      else if name == ``contextWF then [``propext, ``Classical.choice, ``Quot.sound]
      else [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    for dependency in (← collectAxioms name) do
      unless allowed.contains dependency do throwError "unexpected fuel replacement axiom {dependency} in {name}"
    logInfo m!"{name}: {repr (← collectAxioms name)}"
  let inherited := [``TrProj, ``TrProj.instN, ``TrProj.weak']
  let mut pending := roots
  let mut visited : NameSet := {}
  let mut admissions : Array Name := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden fuel replacement dependency {name}"
    if let some info := environment.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        if value.hasSorry then
          unless inherited.contains name do throwError "unapproved fuel replacement admission {name}"
          admissions := admissions.push name
        pending := pending ++ value.getUsedConstants
  unless pending.isEmpty do throwError "fuel replacement traversal exceeded bound"
  unless inherited.all admissions.contains && admissions.size == inherited.length do
    throwError "fuel replacement admission manifest changed: {repr admissions}"
  logInfo m!"{visited.size} same-context replacement dependencies; exact inherited direct admissions {repr admissions}"
  -- Translation uniqueness is a separate inherited equality obligation.
  let bridgeInherited := [``TrProj, ``TrProj.uniq, ``TrProj.wf]
  pending := #[``TrExprS.uniq]
  visited := {}
  admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden translation uniqueness dependency {name}"
    if let some info := environment.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        if value.hasSorry then
          unless bridgeInherited.contains name do throwError "unapproved translation uniqueness admission {name}"
          admissions := admissions.push name
        pending := pending ++ value.getUsedConstants
  unless pending.isEmpty do throwError "translation uniqueness traversal exceeded bound"
  unless bridgeInherited.all admissions.contains && admissions.size == bridgeInherited.length do
    throwError "translation uniqueness admission manifest changed: {repr admissions}"
  for dependency in (← collectAxioms ``TrExprS.uniq) do
    unless [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains dependency do
      throwError "unexpected translation uniqueness axiom {dependency}"
  logInfo m!"{visited.size} translation uniqueness dependencies; exact inherited direct admissions {repr admissions}"
  let some consumer := (← getConstInfo ``Primitive.unfoldNatWellFounded.WF').value? (allowOpaque := true)
    | throwError "missing actual recursion proof"
  let direct := consumer.getUsedConstants
  unless direct.contains ``TrExprS.replace_unused_fvar do throwError "actual consumer lost same-context replacement"
  for name in forbidden do
    if direct.contains name then throwError "actual consumer directly uses {name}"
  if consumer.hasSorry then throwError "actual consumer gained direct admission"
  logInfo "actual recursion producer uses same-context fuel replacement; no direct general extraction or strengthening"

end FuelSuccessorReplacementTest
