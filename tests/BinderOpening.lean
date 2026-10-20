import Lean4Lean.Verify.TypeChecker.InferType
import Lean.Util.CollectAxioms

/-! Naming a native binder preserves its model binder. Exercise dependent
contexts, retained lambdas and lets, both declaration kinds, existing variables,
and projection evidence without semantic weakening or substitution. -/
namespace BinderOpeningTest
open Lean Lean4Lean

abbrev propositionId : FVarId := ⟨`proposition⟩
abbrev proofId : FVarId := ⟨`proof⟩
abbrev openedId : FVarId := ⟨`opened⟩
abbrev base : VLCtx := [
  (some (proofId, [propositionId]), .vlam (.bvar 0)),
  (some (propositionId, []), .vlam (.sort .zero))]

theorem baseWF : VLCtx.WF VEnv.empty 0 base := by
  refine ⟨⟨trivial, ?_, _, .sort trivial⟩, ?_, _, .bvar .zero⟩
  · intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars]
  · intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars, propositionId, proofId]

abbrev named (declaration : VLocalDecl) : VLCtx :=
  (some (openedId, [proofId, propositionId]), declaration) :: base

theorem namedWF (typed : VLocalDecl.WF VEnv.empty 0 base.toCtx declaration) :
    VLCtx.WF VEnv.empty 0 (named declaration) := by
  refine ⟨baseWF, ?_, typed⟩
  intro fv deps equal
  cases Option.some.inj equal
  simp [VLCtx.fvars, base, propositionId, proofId, openedId]

abbrev nested : Expr := .lam `y (.fvar propositionId)
  (.letE `alias (.fvar propositionId) (.bvar 1) (.bvar 2) false) .default
abbrev opened : Expr := .lam `y (.fvar propositionId)
  (.letE `alias (.fvar propositionId) (.fvar openedId) (.fvar openedId) false) .default

theorem lambdaTranslation :
    TrExprS VEnv.empty [] ((none, .vlam (.bvar 1)) :: base) nested
      (.lam (.bvar 2) (.bvar 1)) :=
  .lam ⟨_, .bvar (.succ (.succ .zero))⟩ (.fvar rfl)
    (.letE (.bvar (.succ .zero)) (.fvar rfl) (.bvar rfl) (.bvar rfl))

theorem openLambda : TrExprS VEnv.empty [] (named (.vlam (.bvar 1))) opened
    (.lam (.bvar 2) (.bvar 1)) := by
  have openedWF := namedWF (declaration := .vlam (.bvar 1))
    ⟨_, .bvar (.succ .zero)⟩
  simpa [nested, opened, named, Expr.instantiate1', Expr.liftLooseBVars'] using
    lambdaTranslation.inst_fvar (env := VEnv.empty) (Us := []) (a := openedId) .empty openedWF

theorem letTranslation :
    TrExprS VEnv.empty [] ((none, .vlet (.bvar 1) (.bvar 0)) :: base) nested
      (.lam (.bvar 1) (.bvar 1)) :=
  .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl)
    (.letE (.bvar (.succ .zero)) (.fvar rfl) (.bvar rfl) (.bvar rfl))

theorem openLet : TrExprS VEnv.empty [] (named (.vlet (.bvar 1) (.bvar 0))) opened
    (.lam (.bvar 1) (.bvar 1)) := by
  have openedWF := namedWF (declaration := .vlet (.bvar 1) (.bvar 0)) (.bvar .zero)
  simpa [nested, opened, named, Expr.instantiate1', Expr.liftLooseBVars'] using
    letTranslation.inst_fvar (env := VEnv.empty) (Us := []) (a := openedId) .empty openedWF

-- An ambient anonymous variable above the named base is decremented natively;
-- its model index stays one because naming preserves the model binder.
theorem ambientAnonymous :
    TrExprS VEnv.empty []
      ((some (openedId, []), .vlam (.sort .zero)) ::
        (none, .vlam (.sort .zero)) :: base) (.bvar 0) (.bvar 1) := by
  have contextWF : VLCtx.WF VEnv.empty 0
      ((some (openedId, []), .vlam (.sort .zero)) ::
        (none, .vlam (.sort .zero)) :: base) := by
    refine ⟨⟨baseWF, nofun, _, .sort trivial⟩, ?_, _, .sort trivial⟩
    intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars, base, openedId, propositionId, proofId]
  exact (TrExprS.bvar (env := VEnv.empty) (Us := [])
    (Δ := (none, .vlam (.sort .zero)) :: (none, .vlam (.sort .zero)) :: base)
    (i := 1) rfl).inst_fvar (env := VEnv.empty) (Us := []) (a := openedId) .empty contextWF

theorem openProjection
    (projection : TrProj ((.bvar 1) :: base.toCtx) structName index (.bvar 0) result) :
    TrExprS VEnv.empty [] (named (.vlam (.bvar 1)))
      (.proj structName index (.fvar openedId)) result := by
  have source : TrExprS VEnv.empty [] ((none, .vlam (.bvar 1)) :: base)
      (.proj structName index (.bvar 0)) result := .proj (.bvar rfl) projection
  exact source.inst_fvar (env := VEnv.empty) (Us := []) (a := openedId) .empty (namedWF (declaration := .vlam (.bvar 1)) ⟨_, .bvar (.succ .zero)⟩)

theorem freshRequired (declaration : VLocalDecl) :
    ¬VLCtx.WF VEnv.empty 0 ((some (proofId, []), declaration) :: base) := by
  intro wellFormed
  exact (wellFormed.2.1 _ _ rfl).1 (by simp [VLCtx.fvars, base])

theorem roundTrip :
    TrExprS VEnv.empty [] ((none, .vlam (.bvar 1)) :: base) nested
      (.lam (.bvar 2) (.bvar 1)) := by
  have openedTranslation := lambdaTranslation.inst_fvar (env := VEnv.empty) (Us := []) (a := openedId) .empty
    (namedWF (declaration := .vlam (.bvar 1)) ⟨_, .bvar (.succ .zero)⟩)
  exact openedTranslation.uninstantiate (by simp [FVarsIn, propositionId, openedId])

run_meta
  let environment ← getEnv
  let forbidden := [``TrProj.weak', ``TrProj.instN, ``TrProj.wf, ``TrProj.uniq,
    ``TrProj.defeqDFC, ``TrExprS.weakFV, ``TrExprS.weakFV', ``TrExprS.weakBV,
    ``TrExprS.inst, ``TrExprS.instN, ``TrExprS.instN_var, ``TrExprS.inst_let,
    ``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``VEnv.IsDefEqU.weakN_iff, `Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.quot_inj]
  let roots := [``TrExprS.instantiateFVar, ``TrExprS.inst_fvar,
    ``baseWF, ``namedWF, ``lambdaTranslation, ``openLambda,
    ``letTranslation, ``openLet, ``ambientAnonymous, ``openProjection,
    ``freshRequired, ``roundTrip]
  for root in roots do
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new binder-opening axiom {root}"
    let some value := info.value? (allowOpaque := true)
      | throwError "missing binder-opening proof {root}"
    if value.hasSorry then throwError "direct binder-opening admission {root}"
    let expected := if [``baseWF, ``namedWF, ``freshRequired, ``lambdaTranslation, ``letTranslation].contains root then [] else [``TrProj]
    let axioms ← collectAxioms root
    -- Lean 4.29's concrete context proofs use only propositional extensionality.
    let expectedAxioms := if [``baseWF, ``namedWF, ``freshRequired].contains root then
        [``propext]
      else [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    unless expectedAxioms.length == axioms.size && expectedAxioms.all axioms.contains do
      throwError "binder-opening axiom manifest changed for {root}: {repr axioms}"
    logInfo m!"{root}: exact axioms {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden binder-opening dependency {name} in {root}"
      if let some information := environment.find? name then
        pending := pending ++ information.type.getUsedConstants
        if let some value := information.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expected.contains name do throwError "unapproved binder-opening admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "binder-opening traversal exceeded bound"
    unless expected.length == admissions.size && expected.all admissions.contains do
      throwError "binder-opening manifest changed for {root}: {repr admissions}"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}"

  let some opening := (← getConstInfo ``TrExprS.inst_fvar).value? (allowOpaque := true)
    | throwError "missing actual binder-opening proof"
  unless opening.getUsedConstants.contains ``TrExprS.instantiateFVar do
    throwError "actual binder opening no longer consumes direct renaming"
  for consumer in [``Lean4Lean.TypeChecker.Inner.inferLambda.loop.WF,
      ``Lean4Lean.TypeChecker.Inner.inferForall.loop.WF,
      ``Lean4Lean.TypeChecker.Inner.inferLet.loop.WF] do
    let some proof := (← getConstInfo consumer).value? (allowOpaque := true)
      | throwError "missing actual binder-opening consumer {consumer}"
    if proof.hasSorry then throwError "direct binder-opening consumer admission {consumer}"
    let mut pending := proof.getUsedConstants
    let mut visited : NameSet := {}
    let mut usesOpening := false
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if name == ``TrExprS.inst_fvar then
        usesOpening := true
        break
      if visited.contains name then continue
      visited := visited.insert name
      if let some information := environment.find? name then
        if let some value := information.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
    unless usesOpening do
      throwError "actual checker consumer {consumer} no longer uses binder opening"

end BinderOpeningTest
