import Lean4Lean.Verify.InductiveSubstitutionStageBody
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveSubstitutionStageBodyTest

private def BodyReceipt (env : VEnv) (universes : List Name)
    (smaller original aligned : VLCtx) (lift : Lift)
    (originalDomain reducedDomain : VExpr) (body : Expr) (bodySemantic : VExpr)
    (domainLevel level : VLevel) : Prop :=
  ∃ reducedBody,
    VLCtx.FVLift' ((none, .vlam reducedDomain) :: smaller)
      ((none, .vlam (reducedDomain.lift' lift)) :: aligned) 1 lift 1 ∧
    VLCtx.IsDefEq env universes.length ((none, .vlam originalDomain) :: original)
      ((none, .vlam (reducedDomain.lift' lift)) :: aligned) ∧
    env.HasType universes.length smaller.toCtx reducedDomain (.sort domainLevel) ∧
    TrExprS env universes ((none, .vlam reducedDomain) :: smaller) body reducedBody ∧
    env.HasType universes.length (reducedDomain :: smaller.toCtx) reducedBody (.sort level) ∧
    env.IsDefEq universes.length (originalDomain :: original.toCtx)
      bodySemantic (reducedBody.lift' lift.cons) (.sort level)

private theorem stageBodyForwardsEveryReceipt
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {lift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
    {body : Expr} {domainLevel level : VLevel}
    (envWF : env.WF) (weakening : VLCtx.FVLift' smaller aligned 0 lift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' lift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ smaller.fvars)) :
    BodyReceipt env universes smaller original aligned lift
      originalDomain reducedDomain body bodySemantic domainLevel level :=
  translated.strengthenSubstitutionBodyIsType envWF weakening contexts domainEquality
    typed closed supported

private theorem generalizedStrengtheningForwardsBothDepths
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {binderDepth protectedDepth : Nat} {lift : Lift}
    {body : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF)
    (weakening : VLCtx.FVLift' smaller aligned binderDepth lift protectedDepth)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (translated : TrExprS env universes original body semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed body binderDepth) (supported : body.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reduced,
      TrExprS env universes smaller body reduced ∧
      env.HasType universes.length smaller.toCtx reduced (.sort level) ∧
      env.IsDefEq universes.length original.toCtx semantic
        (reduced.lift' (lift.consN protectedDepth)) (.sort level) :=
  translated.strengthenIsTypeAt envWF weakening contexts typed closed supported

private theorem zeroDepthWrapperKeepsItsOriginalInterface
    {env : VEnv} {universes : List Name} {smaller original aligned : VLCtx}
    {lift : Lift} {body : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF) (weakening : VLCtx.FVLift' smaller aligned 0 lift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (translated : TrExprS env universes original body semantic)
    (typed : env.HasType universes.length original.toCtx semantic (.sort level))
    (closed : Closed body 0) (supported : body.FVarsIn (· ∈ smaller.fvars)) :
    ∃ reduced,
      TrExprS env universes smaller body reduced ∧
      env.HasType universes.length smaller.toCtx reduced (.sort level) ∧
      env.IsDefEq universes.length original.toCtx semantic (reduced.lift' lift) (.sort level) :=
  translated.strengthenIsType envWF weakening contexts typed closed supported

private def retained : FVarId := ⟨`StageBodyRetained⟩
private def suffix : FVarId := ⟨`StageBodySuffix⟩
private def discarded : FVarId := ⟨`StageBodyDiscarded⟩
private def absent : FVarId := ⟨`StageBodyAbsent⟩
private def domain : VExpr := .sort .zero
private def domainLevel : VLevel := .succ .zero
private def base : VLCtx := [(some (retained, []), .vlam domain)]
private def smaller : VLCtx := (some (suffix, []), .vlam domain) :: base
private def aligned : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (discarded, []), .vlam domain) :: base
private def removalLift : Lift := .cons (.skip .refl)
private def nestedBody : Expr := .forallE `nested (.sort .zero) (.fvar retained) .default
private def nestedFormal : Expr := .forallE `nested (.sort .zero) (.bvar 1) .default
private def nestedLevel : VLevel := .imax (.succ .zero) .zero
private def nonliteralDomain : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) domain

private theorem selectedSuffixWeakening : VLCtx.FVLift' smaller aligned 0 removalLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (discarded, []) (.vlam domain) .refl)

private theorem alignedContextAgreement (env : VEnv) : VLCtx.IsDefEq env 0 aligned aligned := by
  apply VLCtx.IsDefEq.cons
  · apply VLCtx.IsDefEq.cons
    · apply VLCtx.IsDefEq.cons .nil
      · rintro identifier dependencies equality
        cases equality
        simp [VLCtx.fvars]
      · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
    · rintro identifier dependencies equality
      cases equality
      simp [VLCtx.fvars, base, retained, discarded]
    · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, base, retained, suffix, discarded]
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem formalBinderBodyRemainsAType (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift domain domain
      (.bvar 0) (.bvar 0) domainLevel .zero := by
  exact TrExprS.strengthenSubstitutionBodyIsType envWF selectedSuffixWeakening
    (alignedContextAgreement env) (.sortDF (by trivial) (by trivial) rfl)
    (.bvar rfl) (.bvar .zero) (by change 0 < 1; decide) (by trivial)

private theorem retainedBaseFVarBodyRemainsAType (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift domain domain
      (.fvar retained) (.bvar 3) domainLevel .zero := by
  exact TrExprS.strengthenSubstitutionBodyIsType envWF selectedSuffixWeakening
    (alignedContextAgreement env) (.sortDF (by trivial) (by trivial) rfl)
    (.fvar rfl) (.bvar (.succ (.succ (.succ .zero)))) (by trivial)
    (by simp [FVarsIn, smaller, base, VLCtx.fvars])

private theorem retainedSuffixFVarBodyRemainsAType (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift domain domain
      (.fvar suffix) (.bvar 1) domainLevel .zero := by
  exact TrExprS.strengthenSubstitutionBodyIsType envWF selectedSuffixWeakening
    (alignedContextAgreement env) (.sortDF (by trivial) (by trivial) rfl)
    (.fvar rfl) (.bvar (.succ .zero)) (by trivial)
    (by simp [FVarsIn, smaller, VLCtx.fvars])

private theorem nestedBodyProtectsItsOwnAndTheStageBinder (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift domain domain
      nestedBody (.forallE domain (.bvar 4)) domainLevel nestedLevel := by
  apply TrExprS.strengthenSubstitutionBodyIsType (universes := []) (original := aligned)
    envWF selectedSuffixWeakening
    (alignedContextAgreement env) (.sortDF (by trivial) (by trivial) rfl)
  · exact .forallE ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      ⟨.zero, .bvar (.succ (.succ (.succ (.succ .zero))))⟩ (.sort rfl) (.fvar rfl)
  · exact .forallEDF (.sortDF (by trivial) (by trivial) rfl)
      (.bvar (.succ (.succ (.succ (.succ .zero)))))
  · trivial
  · simp [nestedBody, FVarsIn, smaller, base, VLCtx.fvars, Level.hasMVar']

private theorem nestedFormalReferenceSurvivesRemoval (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift domain domain
      nestedFormal (.forallE domain (.bvar 1)) domainLevel nestedLevel := by
  apply TrExprS.strengthenSubstitutionBodyIsType (universes := []) (original := aligned)
    envWF selectedSuffixWeakening
    (alignedContextAgreement env) (.sortDF (by trivial) (by trivial) rfl)
  · exact .forallE ⟨.succ .zero, .sortDF (by trivial) (by trivial) rfl⟩
      ⟨.zero, .bvar (.succ .zero)⟩ (.sort rfl) (.bvar rfl)
  · exact .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar (.succ .zero))
  · change True ∧ 1 < 2
    decide
  · trivial

private theorem actualNonliteralDomainRequiresItsExplicitEquality (env : VEnv) (envWF : env.WF) :
    BodyReceipt env [] smaller aligned aligned removalLift nonliteralDomain domain
      (.bvar 0) (.bvar 0) domainLevel .zero := by
  have domainEquality : env.IsDefEq 0 aligned.toCtx nonliteralDomain domain (.sort domainLevel) :=
    .beta (.bvar .zero) (.sortDF (by trivial) (by trivial) rfl)
  have formalTyped : env.HasType 0 (nonliteralDomain :: aligned.toCtx) (.bvar 0) (.sort .zero) :=
    .defeqDF (domainEquality.weak envWF.ordered) (.bvar .zero)
  exact TrExprS.strengthenSubstitutionBodyIsType envWF selectedSuffixWeakening
    (alignedContextAgreement env) domainEquality (.bvar rfl) formalTyped
    (by change 0 < 1; decide) (by trivial)

private theorem twoProtectedBindersUseTheGeneralizedHelper (env : VEnv) (envWF : env.WF) :
    ∃ reduced,
      TrExprS env [] ((none, .vlam domain) :: (none, .vlam domain) :: smaller)
        (.bvar 1) reduced ∧
      env.HasType 0 (domain :: domain :: smaller.toCtx) reduced (.sort .zero) ∧
      env.IsDefEq 0 (domain :: domain :: aligned.toCtx) (.bvar 1)
        (reduced.lift' (removalLift.consN 2)) (.sort .zero) := by
  have contexts : VLCtx.IsDefEq env 0
      ((none, .vlam domain) :: (none, .vlam domain) :: aligned)
      ((none, .vlam domain) :: (none, .vlam domain) :: aligned) :=
    ((alignedContextAgreement env).cons (ofv := none) nofun
      (.vlam (.sortDF (by trivial) (by trivial) rfl))).cons nofun
      (.vlam (.sortDF (by trivial) (by trivial) rfl))
  exact TrExprS.strengthenIsTypeAt (universes := [])
    (original := (none, .vlam domain) :: (none, .vlam domain) :: aligned)
    (domain := .bvar 1) (semantic := .bvar 1) (level := .zero) envWF
    ((selectedSuffixWeakening.cons_bvar (.vlam domain)).cons_bvar (.vlam domain))
    contexts (.bvar rfl) (.bvar (.succ .zero)) (by change 1 < 2; decide) (by trivial)

private theorem anonymousLetHasNativeDepthOneButSemanticDepthZero (env : VEnv) (envWF : env.WF) :
    ∃ reduced,
      TrExprS env [] ((none, .vlet (.sort domainLevel) domain) :: smaller) (.bvar 0) reduced ∧
      env.HasType 0 smaller.toCtx reduced (.sort domainLevel) ∧
      env.IsDefEq 0 aligned.toCtx domain (reduced.lift' removalLift) (.sort domainLevel) := by
  have contexts : VLCtx.IsDefEq env 0
      ((none, .vlet (.sort domainLevel) domain) :: aligned)
      ((none, .vlet (.sort domainLevel) domain) :: aligned) :=
    (alignedContextAgreement env).cons nofun
      (.vlet (.sortDF (by trivial) (by trivial) rfl)
        (.sortDF (by trivial) (by trivial) rfl))
  exact TrExprS.strengthenIsTypeAt (universes := [])
    (original := (none, .vlet (.sort domainLevel) domain) :: aligned)
    (domain := .bvar 0) (semantic := domain) (level := domainLevel) envWF
    (selectedSuffixWeakening.cons_bvar (.vlet (.sort domainLevel) domain))
    contexts (.bvar rfl) (.sortDF (by trivial) (by trivial) rfl)
    (by change 0 < 1; decide) (by trivial)

private theorem formalBinderNeedsClosedOneRatherThanClosedZero :
    Closed (.bvar 0) 1 ∧ ¬ Closed (.bvar 0) 0 := by simp [Closed]

private theorem aSecondLooseBinderCannotUseTheStageBodyHelper : ¬ Closed (.bvar 1) 1 := by simp [Closed]

private theorem droppedAndMissingFVarsCannotSupplySmallerSupport :
    ¬ (Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) ∧
      ¬ (Expr.fvar absent).FVarsIn (· ∈ smaller.fvars) := by
  simp [FVarsIn, smaller, base, VLCtx.fvars, suffix, retained, discarded, absent]

private theorem droppedFVarIsTranslatedButStillUnsupported :
    TrExprS env [] ((none, .vlam domain) :: aligned) (.fvar discarded) (.bvar 2) ∧
      ¬ (Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) :=
  ⟨.fvar rfl, droppedAndMissingFVarsCannotSupplySmallerSupport.1⟩

private theorem nonliteralDomainIsNotItsReducedSyntax : nonliteralDomain ≠ domain := by
  intro equality
  cases equality

private theorem lookupCoordinatesIncludeSuffixAndFormalBinder :
    VLCtx.find? ((none, .vlam domain) :: smaller) (.inr retained) =
      some (.bvar 2, .sort .zero) ∧
    VLCtx.find? ((none, .vlam domain) :: aligned) (.inr retained) =
      some (.bvar 3, .sort .zero) ∧
    VLCtx.find? ((none, .vlam domain) :: smaller) (.inr suffix) =
      some (.bvar 1, .sort .zero) := ⟨rfl, rfl, rfl⟩

private theorem protectedLiftRetainsFormalAndSuffixCoordinates :
    (VExpr.bvar 0).lift' removalLift.cons = .bvar 0 ∧
    (VExpr.bvar 1).lift' removalLift.cons = .bvar 1 ∧
    (VExpr.bvar 2).lift' removalLift.cons = .bvar 3 ∧
    (VExpr.bvar 1).lift' removalLift ≠ .bvar 1 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro equality
  cases equality

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .const _ _ => [2]
  | .app function argument => 3 :: (semanticShape function ++ semanticShape argument)
  | .lam binder body => 4 :: (semanticShape binder ++ semanticShape body)
  | .forallE binder body => 5 :: (semanticShape binder ++ semanticShape body)

private def sourceClosedAt : Expr → Nat → Bool
  | .bvar position, depth => position < depth
  | .fvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => true
  | .mvar _, _ => false
  | .app function argument, depth => sourceClosedAt function depth && sourceClosedAt argument depth
  | .lam _ binder body _, depth | .forallE _ binder body _, depth =>
    sourceClosedAt binder depth && sourceClosedAt body (depth + 1)
  | .letE _ binder value body _, depth =>
    sourceClosedAt binder depth && sourceClosedAt value depth && sourceClosedAt body (depth + 1)
  | .proj _ _ body, depth | .mdata _ body, depth => sourceClosedAt body depth

private def runtimeControls : MetaM Unit := do
  let conditions := [
    (sourceClosedAt (.bvar 0) 1, "stage formal is Closed 1"),
    (!sourceClosedAt (.bvar 0) 0, "stage formal is not Closed 0"),
    (!sourceClosedAt (.bvar 1) 1, "second loose formal is not Closed 1"),
    (sourceClosedAt nestedFormal 1, "nested formal uses its increased cutoff"),
    (sourceClosedAt nestedBody 1, "nested supported fvar body is closed"),
    (smaller.fvars.contains retained, "retained base source support"),
    (smaller.fvars.contains suffix, "selected suffix source support"),
    (!smaller.fvars.contains discarded, "discarded source lacks smaller support"),
    (!smaller.fvars.contains absent, "missing source lacks smaller support"),
    (aligned.fvars.contains discarded, "discarded source exists in original context"),
    (nestedBody.fvarsList == [retained], "nested source body keeps retained identifier"),
    (semanticShape ((VExpr.bvar 0).lift' removalLift.cons) == [0, 0], "protect stage formal"),
    (semanticShape ((VExpr.bvar 1).lift' removalLift.cons) == [0, 1], "protect selected suffix"),
    (semanticShape ((VExpr.bvar 2).lift' removalLift.cons) == [0, 3], "remove below suffix"),
    (semanticShape ((VExpr.bvar 1).lift' removalLift) != [0, 1], "missing formal protection changes suffix"),
    (semanticShape ((VExpr.forallE domain (.bvar 3)).lift' removalLift.cons) ==
      semanticShape (.forallE domain (.bvar 4)), "nested body protects third binder"),
    (semanticShape ((VExpr.forallE domain (.bvar 1)).lift' removalLift.cons) ==
      semanticShape (.forallE domain (.bvar 1)), "nested formal reference retained"),
    (semanticShape ((VExpr.bvar 1).lift' (removalLift.consN 2)) == [0, 1], "two protected formals retained"),
    (semanticShape ((VExpr.bvar 3).lift' (removalLift.consN 2)) == [0, 4], "two formals and suffix cutoff"),
    (semanticShape nonliteralDomain != semanticShape domain, "actual beta domain is nonliteral"),
    (semanticShape nonliteralDomain != semanticShape (.sort (.succ .zero)), "domain level is not actual domain"),
    (VLCtx.bvars ((none, VLocalDecl.vlet (.sort domainLevel) domain) :: smaller) == 1,
      "anonymous let increases native depth"),
    ((VLCtx.toCtx ((none, VLocalDecl.vlet (.sort domainLevel) domain) :: smaller)).length ==
      smaller.toCtx.length, "anonymous let does not increase semantic depth"),
    ((VLCtx.find? ((none, VLocalDecl.vlet (.sort domainLevel) domain) :: aligned) (.inl 0)).map
      (fun (value, type) => semanticShape value ++ semanticShape type) == some [1, 1],
      "anonymous let formal translates to its value")]
  for (condition, label) in conditions do
    unless condition do throwError "stage-body runtime failed: {label}"
  logInfo m!"stage-body runtime: {conditions.length} source-support, binder-depth, semantic-cutoff, nested-body, actual-domain and anonymous-let controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "stage-body audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do throwError "stage-body unexpected axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (expected : Nat) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "stage-body audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "stage-body module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == expected do
    throwError "stage-body module declaration manifest changed: {moduleName}; expected {expected}, got {declarations}"
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditExactInheritedDependencies (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "stage-body exact inherited dependency manifest changed: {name}"
  logInfo m!"{name}: exact four inherited logical/typing axioms; no native/container/range/abstraction interfaces"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let proofControls := [``stageBodyForwardsEveryReceipt, ``generalizedStrengtheningForwardsBothDepths,
    ``zeroDepthWrapperKeepsItsOriginalInterface, ``selectedSuffixWeakening, ``alignedContextAgreement,
    ``formalBinderBodyRemainsAType, ``retainedBaseFVarBodyRemainsAType,
    ``retainedSuffixFVarBodyRemainsAType, ``nestedBodyProtectsItsOwnAndTheStageBinder,
    ``nestedFormalReferenceSurvivesRemoval, ``actualNonliteralDomainRequiresItsExplicitEquality,
    ``twoProtectedBindersUseTheGeneralizedHelper,
    ``anonymousLetHasNativeDepthOneButSemanticDepthZero,
    ``formalBinderNeedsClosedOneRatherThanClosedZero, ``aSecondLooseBinderCannotUseTheStageBodyHelper,
    ``droppedAndMissingFVarsCannotSupplySmallerSupport, ``droppedFVarIsTranslatedButStillUnsupported,
    ``nonliteralDomainIsNotItsReducedSyntax, ``lookupCoordinatesIncludeSuffixAndFormalBinder,
    ``protectedLiftRetainsFormalAndSuffixCoordinates]
  for name in proofControls do auditDeclaration name inherited
  auditDeclaration ``BodyReceipt inherited
  for name in [``retained, ``suffix, ``discarded, ``absent, ``domain, ``domainLevel,
      ``base, ``smaller, ``aligned, ``removalLift, ``nestedBody, ``nestedFormal, ``nestedLevel,
      ``nonliteralDomain, ``semanticShape, ``sourceClosedAt, ``runtimeControls, ``auditDeclaration, ``auditModule,
      ``auditExactInheritedDependencies] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveIndexDomainStrengthening 2 inherited
  auditModule `Lean4Lean.Verify.InductiveSubstitutionStageBody 2 inherited
  for name in [``TrExprS.strengthenIsTypeAt, ``TrExprS.strengthenIsType,
      ``TrExprS.strengthenSubstitutionBodyIsType] do
    auditExactInheritedDependencies name inherited
  runtimeControls
  logInfo m!"stage-body tests: {proofControls.length} proof controls; all six receipts forwarded; actual domain equality, retained formal/base/suffix, nested cutoff, two protected binders, native/semantic depth distinction, support/closure negatives"

end InductiveSubstitutionStageBodyTest
