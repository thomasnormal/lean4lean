import Lean4Lean.Theory.Typing.Strong
import Lean.Elab.Command

namespace StrongSubstitutionTest

open Lean Lean.Elab Lean.Elab.Command Lean4Lean Lean4Lean.VExpr Lean4Lean.VEnv

variable {environment : VEnv} {universes : Nat}
  {sourceContext targetContext : List VExpr} {leftSubstitution rightSubstitution : VExpr.Subst}
  {leftExpression rightExpression domain : VExpr}

example (ordered : environment.Ordered)
    (sourceWF : OnCtx sourceContext (environment.IsType universes))
    (targetWF : OnCtx targetContext (environment.IsType universes))
    (substituted : Ctx.SubstEq environment universes targetContext
      leftSubstitution rightSubstitution sourceContext)
    (equation : environment.IsDefEq universes sourceContext leftExpression rightExpression domain) :
    environment.IsDefEq universes targetContext
      (leftExpression.subst leftSubstitution) (rightExpression.subst rightSubstitution)
      (domain.subst leftSubstitution) :=
  equation.substDF ordered sourceWF targetWF substituted

example (ordered : environment.Ordered)
    (sourceWF : CtxStrong environment universes sourceContext)
    (targetWF : CtxStrong environment universes targetContext)
    (substituted : Ctx.SubstEq environment universes targetContext
      leftSubstitution rightSubstitution sourceContext)
    (equation : environment.IsDefEqStrong universes sourceContext
      leftExpression rightExpression domain) :
    environment.IsDefEqStrong universes targetContext
      (leftExpression.subst leftSubstitution) (rightExpression.subst rightSubstitution)
      (domain.subst leftSubstitution) :=
  equation.subst ordered sourceWF targetWF substituted

example (ordered : environment.Ordered)
    (sourceWF : OnCtx sourceContext (environment.IsType universes)) :
    Ctx.SubstEq environment universes sourceContext .id .id sourceContext :=
  Ctx.SubstEq.id ordered sourceWF

example (ordered : environment.Ordered)
    (targetWF : OnCtx targetContext (environment.IsType universes))
    (substituted : Ctx.SubstEq environment universes targetContext
      leftSubstitution leftSubstitution sourceContext)
    (typed : environment.HasType universes sourceContext leftExpression domain) :
    environment.HasType universes targetContext
      (leftExpression.subst leftSubstitution) (domain.subst leftSubstitution) :=
  typed.subst ordered substituted targetWF

example (ordered : environment.Ordered)
    (targetWF : OnCtx targetContext (environment.IsType universes))
    (equation : environment.IsDefEq universes [] leftExpression rightExpression domain) :
    environment.IsDefEq universes targetContext
      (leftExpression.subst leftSubstitution) (rightExpression.subst rightSubstitution)
      (domain.subst leftSubstitution) :=
  equation.substDF (sourceContext := []) ordered trivial targetWF .nil

example : Ctx.SubstEq environment 0 []
    (Subst.id.cons (.sort .zero))
    (Subst.id.cons (.sort (.max .zero .zero))) [.sort (.succ .zero)] := by
  refine .cons .nil (.sort (by trivial)) ?_
  exact .sortDF (by trivial) (by trivial) VLevel.max_self.symm

example (ordered : environment.Ordered) :
    environment.IsDefEq 0 [] (.sort .zero) (.sort (.max .zero .zero)) (.sort (.succ .zero)) := by
  have substituted : Ctx.SubstEq environment 0 []
      (Subst.id.cons (.sort .zero))
      (Subst.id.cons (.sort (.max .zero .zero))) [.sort (.succ .zero)] :=
    .cons .nil (.sort (by trivial)) (.sortDF (by trivial) (by trivial) VLevel.max_self.symm)
  have variableTyped : environment.IsDefEq 0 [.sort (.succ .zero)]
      (.bvar 0) (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  simpa using variableTyped.substDF (targetContext := []) ordered substituted.wf trivial substituted

example (ordered : environment.Ordered) :
    environment.IsDefEq 0 []
      ((VExpr.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)).subst leftSubstitution)
      ((VExpr.sort .zero).subst rightSubstitution)
      ((VExpr.sort (.succ .zero)).subst leftSubstitution) := by
  have bodyTyped : environment.HasType 0 [.sort (.succ .zero)]
      (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have argumentTyped : environment.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    .sort (by trivial)
  have beta : environment.IsDefEq 0 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) := bodyTyped.beta argumentTyped
  exact beta.substDF (sourceContext := []) (targetContext := []) ordered trivial trivial .nil

example (ordered : environment.Ordered)
    (substituted : Ctx.SubstEq environment universes targetContext
      leftSubstitution rightSubstitution sourceContext)
    (domainTyped : environment.HasType universes sourceContext domain (.sort domainLevel)) :
    Ctx.SubstEq environment universes (domain.subst leftSubstitution :: targetContext)
      leftSubstitution.lift rightSubstitution.lift (domain :: sourceContext) :=
  substituted.lift ordered domainTyped

run_meta
  let ownedTheorems := #[``subst_bvar, ``subst_sort, ``subst_const, ``subst_app,
    ``Subst.comp_lift, ``subst_subst,
    ``Subst.cons_head, ``Subst.cons_tail, ``Subst.lift_l_refl, ``Subst.lift_l_skip,
    ``lift_subst, ``Subst.tail_eq_lift_l, ``Subst.lift_r_tail, ``Subst.Fixes.zero,
    ``Subst.Fixes.lift, ``ClosedN.subst_eq, ``lift_subst_cons, ``lift_subst_lift,
    ``subst_inst, ``inst_lift_cons, ``Ctx.SubstEq.left, ``Ctx.SubstEq.lookup,
    ``Ctx.SubstEq.skip, ``Ctx.SubstEq.lift, ``Ctx.SubstEq.lift_at,
    ``Ctx.SubstEq.wf, ``Ctx.SubstEq.id, ``IsDefEqStrong.substEq',
    ``IsDefEqStrong.subst, ``IsDefEq.substDF, ``IsDefEq.subst,
    ``HasType.subst, ``IsDefEqU.subst, ``IsType.subst]
  for name in ownedTheorems do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "substitution axiom: {name}"
    let some proof := information.value? (allowOpaque := true) | throwError "substitution proof absent: {name}"
    if proof.hasSorry then throwError "substitution direct admission: {name}"
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "substitution inherited admission/interface: {dependency} in {name}"
    logInfo m!"{name}: {repr dependencies}"
  logInfo "strong and weak simultaneous substitution, including cross-substitution, variable lookup, binder extension, beta, and arbitrary empty-source substitutions, are proved without inherited verification/metatheory admissions"

end StrongSubstitutionTest
