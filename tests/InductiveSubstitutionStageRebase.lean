import Lean4Lean.Verify.InductiveSubstitutionStageRebase
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveSubstitutionStageRebaseTest

private def StageReceipt (env : VEnv) (universes : List Name)
    (smaller original aligned target : VLCtx) (removalLift insertionLift : Lift)
    (originalDomain reducedDomain : VExpr) (body : Expr) (bodySemantic : VExpr)
    (domainLevel level : VLevel) (beforeArgument afterArgument : VExpr) : Prop :=
  ∃ reducedBody,
    VLCtx.FVLift' ((none, .vlam reducedDomain) :: smaller)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) 1 removalLift 1 ∧
    VLCtx.IsDefEq env universes.length ((none, .vlam originalDomain) :: original)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) ∧
    env.HasType universes.length smaller.toCtx reducedDomain (.sort domainLevel) ∧
    TrExprS env universes ((none, .vlam reducedDomain) :: smaller) body reducedBody ∧
    env.HasType universes.length (reducedDomain :: smaller.toCtx) reducedBody (.sort level) ∧
    env.IsDefEq universes.length (originalDomain :: original.toCtx)
      bodySemantic (reducedBody.lift' removalLift.cons) (.sort level) ∧
    SemanticSubstitutionChain env universes.length smaller.toCtx level
      (reducedBody.inst beforeArgument) (reducedBody.inst afterArgument) ∧
    TrExprS env universes ((none, .vlam (reducedDomain.lift' insertionLift)) :: target)
      body (reducedBody.lift' insertionLift.cons) ∧
    env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
      (reducedBody.lift' insertionLift.cons) (.sort level) ∧
    SemanticSubstitutionChain env universes.length target.toCtx level
      ((reducedBody.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift))
      ((reducedBody.lift' insertionLift.cons).inst (afterArgument.lift' insertionLift))

private theorem stageRebaseForwardsEveryReceipt
    {env : VEnv} {universes : List Name} {smaller original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {originalDomain reducedDomain bodySemantic : VExpr}
    {body : Expr} {domainLevel level : VLevel} {beforeArgument afterArgument : VExpr}
    (envWF : env.WF) (removal : VLCtx.FVLift' smaller aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (domainEquality : env.IsDefEq universes.length original.toCtx
      originalDomain (reducedDomain.lift' removalLift) (.sort domainLevel))
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ smaller.fvars))
    (argumentEquality : env.IsDefEq universes.length smaller.toCtx beforeArgument afterArgument reducedDomain)
    (insertion : VLCtx.FVLift' smaller target 0 insertionLift 0)
    (targetWF : target.WF env universes.length) :
    StageReceipt env universes smaller original aligned target removalLift insertionLift
      originalDomain reducedDomain body bodySemantic domainLevel level beforeArgument afterArgument :=
  translated.strengthenSubstitutionStageRebased envWF removal contexts domainEquality typed closed
    supported argumentEquality insertion targetWF

private def retained : FVarId := ⟨`StageRebaseRetained⟩
private def suffix : FVarId := ⟨`StageRebaseSuffix⟩
private def discarded : FVarId := ⟨`StageRebaseDiscarded⟩
private def insertedFirst : FVarId := ⟨`StageRebaseInsertedFirst⟩
private def insertedSecond : FVarId := ⟨`StageRebaseInsertedSecond⟩
private def absent : FVarId := ⟨`StageRebaseAbsent⟩
private def domain : VExpr := .sort .zero
private def domainLevel : VLevel := .succ .zero
private def stageLevel : VLevel := .imax .zero (.imax .zero .zero)
private def base : VLCtx := [(some (retained, []), .vlam domain)]
private def smaller : VLCtx := (some (suffix, []), .vlam domain) :: base
private def aligned : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (discarded, []), .vlam domain) :: base
private def target : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (insertedFirst, []), .vlam domain) ::
    (some (insertedSecond, []), .vlam domain) :: base
private def removalLift : Lift := .cons (.skip .refl)
private def insertionLift : Lift := .cons (.skip (.skip .refl))
private def nativeBody : Expr :=
  .forallE `formalUse (.bvar 0)
    (.forallE `suffixUse (.fvar suffix) (.fvar retained) .default) .default
private def originalBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 5))
private def reducedBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 4))
private def nonliteralDomain : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) domain
private def betaArgument (position : Nat) : VExpr :=
  .app (.lam domain (.bvar 0)) (.bvar position)
private def beforeArgument : VExpr := betaArgument 1
private def afterArgument : VExpr := .bvar 1

private theorem extendDomainWF (env : VEnv) (context : VLCtx) (identifier : FVarId)
    (contextWF : context.WF env 0) (fresh : identifier ∉ context.fvars) :
    VLCtx.WF env 0 ((some (identifier, []), .vlam domain) :: context) := by
  refine ⟨contextWF, ?_, domainLevel, .sortDF (by trivial) (by trivial) rfl⟩
  rintro selected dependencies equality
  cases equality
  exact ⟨fresh, by simp⟩

private theorem baseWF (env : VEnv) : base.WF env 0 :=
  extendDomainWF env [] retained (by trivial) (by simp [VLCtx.fvars])

private theorem smallerWF (env : VEnv) : smaller.WF env 0 :=
  extendDomainWF env base suffix (baseWF env) (by simp [base, VLCtx.fvars, suffix, retained])

private theorem alignedWF (env : VEnv) : aligned.WF env 0 := by
  have middleWF := extendDomainWF env base discarded (baseWF env)
    (by simp [base, VLCtx.fvars, discarded, retained])
  exact extendDomainWF env _ suffix middleWF
    (by simp [base, VLCtx.fvars, suffix, discarded, retained])

private theorem targetWF (env : VEnv) : target.WF env 0 := by
  have secondWF := extendDomainWF env base insertedSecond (baseWF env)
    (by simp [base, VLCtx.fvars, insertedSecond, retained])
  have firstWF := extendDomainWF env _ insertedFirst secondWF
    (by simp [base, VLCtx.fvars, insertedFirst, insertedSecond, retained])
  exact extendDomainWF env _ suffix firstWF
    (by simp [base, VLCtx.fvars, suffix, insertedFirst, insertedSecond, retained])

private theorem selectedSuffixRemoval : VLCtx.FVLift' smaller aligned 0 removalLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (discarded, []) (.vlam domain) .refl)

private theorem selectedSuffixInsertion : VLCtx.FVLift' smaller target 0 insertionLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (insertedFirst, []) (.vlam domain)
      (.skip_fvar (insertedSecond, []) (.vlam domain) .refl))

private theorem actualDomainEquality (env : VEnv) :
    env.IsDefEq 0 aligned.toCtx nonliteralDomain domain (.sort domainLevel) :=
  .beta (.bvar .zero) (.sortDF (by trivial) (by trivial) rfl)

private theorem formalTypedUnderTheActualDomain (env : VEnv) (envWF : env.WF) :
    env.HasType 0 (nonliteralDomain :: aligned.toCtx) (.bvar 0) domain :=
  .defeqDF ((actualDomainEquality env).weak envWF.ordered) (.bvar .zero)

private theorem originalNestedBodyTyped (env : VEnv) (envWF : env.WF) :
    env.HasType 0 (nonliteralDomain :: aligned.toCtx) originalBody (.sort stageLevel) :=
  .forallEDF (formalTypedUnderTheActualDomain env envWF)
    (.forallEDF (.bvar (.succ (.succ .zero)))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))

private theorem originalNestedBodyTranslated (env : VEnv) (envWF : env.WF) :
    TrExprS env [] ((none, .vlam nonliteralDomain) :: aligned) nativeBody originalBody :=
  .forallE ⟨.zero, formalTypedUnderTheActualDomain env envWF⟩
    ⟨.imax .zero .zero, .forallEDF (.bvar (.succ (.succ .zero)))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))⟩
    (.bvar rfl)
    (.forallE ⟨.zero, .bvar (.succ (.succ .zero))⟩
      ⟨.zero, .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))⟩ (.fvar rfl) (.fvar rfl))

private theorem stageBodyClosedAndSupported :
    Closed nativeBody 1 ∧ nativeBody.FVarsIn (· ∈ smaller.fvars) := by
  constructor
  · change (0 < 1) ∧ True ∧ True
    decide
  · simp [nativeBody, FVarsIn, smaller, base, VLCtx.fvars]

private theorem nonliteralArgumentEquality (env : VEnv) :
    env.IsDefEq 0 smaller.toCtx beforeArgument afterArgument domain :=
  .beta (.bvar .zero) (.bvar (.succ .zero))

private theorem genuineRemovalAndDifferentInsertion (env : VEnv) (envWF : env.WF) :
    StageReceipt env [] smaller aligned aligned target removalLift insertionLift
      nonliteralDomain domain nativeBody originalBody domainLevel stageLevel
      beforeArgument afterArgument :=
  TrExprS.strengthenSubstitutionStageRebased envWF selectedSuffixRemoval
    (VLCtx.IsDefEq.refl envWF.ordered (alignedWF env)) (actualDomainEquality env)
    (originalNestedBodyTranslated env envWF) (originalNestedBodyTyped env envWF)
    stageBodyClosedAndSupported.1 stageBodyClosedAndSupported.2
    (nonliteralArgumentEquality env) selectedSuffixInsertion (targetWF env)

private theorem genuineChainsProjectTypesAndEquality (env : VEnv) (envWF : env.WF) :
    ∃ reduced : VExpr,
      env.IsDefEq 0 smaller.toCtx (reduced.inst beforeArgument)
        (reduced.inst afterArgument) (.sort stageLevel) ∧
      env.HasType 0 smaller.toCtx (reduced.inst beforeArgument) (.sort stageLevel) ∧
      env.HasType 0 smaller.toCtx (reduced.inst afterArgument) (.sort stageLevel) ∧
      env.IsDefEq 0 target.toCtx
        ((reduced.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift))
        ((reduced.lift' insertionLift.cons).inst (afterArgument.lift' insertionLift)) (.sort stageLevel) ∧
      env.HasType 0 target.toCtx
        ((reduced.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift)) (.sort stageLevel) ∧
      env.HasType 0 target.toCtx
        ((reduced.lift' insertionLift.cons).inst (afterArgument.lift' insertionLift)) (.sort stageLevel) ∧
      TrExprS env [] ((none, .vlam domain) :: target) nativeBody (reduced.lift' insertionLift.cons) ∧
      env.HasType 0 (domain :: target.toCtx) (reduced.lift' insertionLift.cons) (.sort stageLevel) := by
  obtain ⟨reduced, _, _, _, _, _, _, sourceChain, targetTranslation, targetType, targetChain⟩ :=
    genuineRemovalAndDifferentInsertion env envWF
  have sourceTypes := sourceChain.hasType envWF (smallerWF env).toCtx
  have targetTypes := targetChain.hasType envWF (targetWF env).toCtx
  exact ⟨reduced, sourceChain.isDefEq envWF (smallerWF env).toCtx,
    sourceTypes.1, sourceTypes.2, targetChain.isDefEq envWF (targetWF env).toCtx,
    targetTypes.1, targetTypes.2, targetTranslation, targetType⟩

private theorem nonliteralDomainAndArgumentAreNotTheirEndpoints :
    nonliteralDomain ≠ domain ∧ beforeArgument ≠ afterArgument := by
  constructor <;> intro equality <;> cases equality

private theorem removalAndInsertionHaveDifferentCoordinates :
    (VExpr.bvar 1).lift' removalLift = .bvar 2 ∧
    (VExpr.bvar 1).lift' insertionLift = .bvar 3 ∧
    removalLift ≠ insertionLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem protectedBodyHasDistinctFormalSuffixAndBaseCoordinates :
    reducedBody.lift' removalLift.cons = originalBody ∧
    reducedBody.lift' insertionLift.cons = .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6)) ∧
    afterArgument.lift' insertionLift = .bvar 3 := ⟨rfl, rfl, rfl⟩

private theorem bodyLiftMustProtectTheStageFormal :
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' insertionLift := by
  intro equality
  cases equality

private theorem argumentsMustNotReceiveTheBodyConsLift :
    beforeArgument.lift' insertionLift ≠ beforeArgument.lift' insertionLift.cons ∧
    afterArgument.lift' insertionLift ≠ afterArgument.lift' insertionLift.cons := by
  constructor <;> intro equality <;> cases equality

private theorem insertionMustProtectItsSelectedSuffix :
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' (Lift.skip (.skip .refl)).cons ∧
    afterArgument.lift' insertionLift ≠ afterArgument.lift' removalLift := by
  constructor <;> intro equality <;> cases equality

private theorem instantiatedEndpointsUseTheTargetContextLift :
    (reducedBody.inst beforeArgument).lift' insertionLift =
      (reducedBody.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift) ∧
    (reducedBody.inst afterArgument).lift' insertionLift =
      (reducedBody.lift' insertionLift.cons).inst (afterArgument.lift' insertionLift) := ⟨rfl, rfl⟩

private theorem droppedAndMissingFVarsCannotSupplyBodySupport :
    ¬(Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) ∧
    ¬(Expr.fvar absent).FVarsIn (· ∈ smaller.fvars) := by
  simp [FVarsIn, smaller, base, VLCtx.fvars, discarded, absent, suffix, retained]

private theorem originalTranslationDoesNotReplaceSmallerSupport (env : VEnv) :
    TrExprS env [] ((none, .vlam nonliteralDomain) :: aligned) (.fvar discarded) (.bvar 2) ∧
    ¬(Expr.fvar discarded).FVarsIn (· ∈ smaller.fvars) :=
  ⟨.fvar rfl, droppedAndMissingFVarsCannotSupplyBodySupport.1⟩

private theorem formalBinderNeedsClosedOneRatherThanClosedZero :
    Closed nativeBody 1 ∧ ¬Closed nativeBody 0 ∧ ¬Closed (.bvar 1) 1 := by
  refine ⟨stageBodyClosedAndSupported.1, ?_, ?_⟩
  · simp [nativeBody, Closed]
  · change ¬1 < 1
    decide

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
    (sourceClosedAt nativeBody 1, "nested stage body is Closed 1"),
    (!sourceClosedAt nativeBody 0, "stage formal is not Closed 0"),
    (!sourceClosedAt (.bvar 1) 1, "second loose formal is not Closed 1"),
    (nativeBody.fvarsList == [suffix, retained], "body uses retained suffix and base"),
    (smaller.fvars.contains suffix, "selected suffix remains supported"),
    (smaller.fvars.contains retained, "retained base remains supported"),
    (!smaller.fvars.contains discarded, "removed fvar lacks support"),
    (!smaller.fvars.contains absent, "absent fvar lacks support"),
    (aligned.fvars.contains discarded, "removed fvar existed in source"),
    (target.fvars.contains insertedFirst && target.fvars.contains insertedSecond, "target has two insertions"),
    (semanticShape nonliteralDomain != semanticShape domain, "actual domain is nonliteral beta syntax"),
    (semanticShape beforeArgument != semanticShape afterArgument, "stage argument is nonliteral beta syntax"),
    (semanticShape ((VExpr.bvar 0).lift' insertionLift) == [0, 0], "insertion protects selected suffix"),
    (semanticShape ((VExpr.bvar 1).lift' removalLift) == [0, 2], "removal coordinate skips one"),
    (semanticShape ((VExpr.bvar 1).lift' insertionLift) == [0, 3], "insertion coordinate skips two"),
    (semanticShape (reducedBody.lift' removalLift.cons) == semanticShape originalBody, "removal rebuilds original body"),
    (semanticShape (reducedBody.lift' insertionLift.cons) ==
      semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6))), "target protects formal and nested suffix"),
    (semanticShape (reducedBody.lift' insertionLift.cons) != semanticShape (reducedBody.lift' insertionLift),
      "missing formal cons changes nested suffix"),
    (semanticShape (beforeArgument.lift' insertionLift) == semanticShape (betaArgument 3), "beta argument lifts outside formal"),
    (semanticShape (beforeArgument.lift' insertionLift) != semanticShape (beforeArgument.lift' insertionLift.cons),
      "body cons lift is wrong for beta argument"),
    (semanticShape (afterArgument.lift' insertionLift) != semanticShape (afterArgument.lift' insertionLift.cons),
      "body cons lift is wrong for reduced argument"),
    (semanticShape (reducedBody.lift' insertionLift.cons) !=
      semanticShape (reducedBody.lift' (Lift.skip (.skip .refl)).cons), "wrong suffix cutoff changes body"),
    (semanticShape (afterArgument.lift' insertionLift) != semanticShape (afterArgument.lift' removalLift),
      "removal and insertion are not interchangeable"),
    (semanticShape ((reducedBody.inst beforeArgument).lift' insertionLift) ==
      semanticShape ((reducedBody.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift)),
      "target beta endpoint agrees with lifted source endpoint"),
    (semanticShape ((reducedBody.inst afterArgument).lift' insertionLift) ==
      semanticShape (.forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5))), "reduced endpoint coordinates are exact"),
    (semanticShape ((reducedBody.lift' insertionLift.cons).inst (beforeArgument.lift' insertionLift)) !=
      semanticShape ((reducedBody.lift' insertionLift.cons).inst (afterArgument.lift' insertionLift)),
      "target chain endpoints are not literal syntax equality")]
  for (condition, label) in conditions do
    unless condition do throwError "stage-rebase runtime failed: {label}"
  logInfo m!"stage-rebase runtime: {conditions.length} removal, distinct insertion, formal/nested/suffix coordinates, nonliteral domain/argument, support and closure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "stage-rebase audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do throwError "stage-rebase unexpected axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (expected : Nat) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "stage-rebase audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "stage-rebase module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == expected do
    throwError "stage-rebase module declaration manifest changed: {moduleName}; expected {expected}, got {declarations}"
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditExactInheritedDependencies (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "stage-rebase exact inherited dependency manifest changed: {name}"
  logInfo m!"{name}: exact four inherited logical/typing axioms; no native/container/range/abstraction interfaces"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let proofControls := [``stageRebaseForwardsEveryReceipt, ``extendDomainWF,
    ``baseWF, ``smallerWF, ``alignedWF, ``targetWF, ``selectedSuffixRemoval,
    ``selectedSuffixInsertion, ``actualDomainEquality, ``formalTypedUnderTheActualDomain,
    ``originalNestedBodyTyped, ``originalNestedBodyTranslated, ``stageBodyClosedAndSupported,
    ``nonliteralArgumentEquality, ``genuineRemovalAndDifferentInsertion,
    ``genuineChainsProjectTypesAndEquality, ``nonliteralDomainAndArgumentAreNotTheirEndpoints,
    ``removalAndInsertionHaveDifferentCoordinates, ``protectedBodyHasDistinctFormalSuffixAndBaseCoordinates,
    ``bodyLiftMustProtectTheStageFormal, ``argumentsMustNotReceiveTheBodyConsLift,
    ``insertionMustProtectItsSelectedSuffix, ``instantiatedEndpointsUseTheTargetContextLift,
    ``droppedAndMissingFVarsCannotSupplyBodySupport, ``originalTranslationDoesNotReplaceSmallerSupport,
    ``formalBinderNeedsClosedOneRatherThanClosedZero]
  for name in proofControls do auditDeclaration name inherited
  auditDeclaration ``StageReceipt inherited
  for name in [``retained, ``suffix, ``discarded, ``insertedFirst, ``insertedSecond, ``absent,
      ``domain, ``domainLevel, ``stageLevel, ``base, ``smaller, ``aligned, ``target,
      ``removalLift, ``insertionLift, ``nativeBody, ``originalBody, ``reducedBody, ``nonliteralDomain,
      ``betaArgument, ``beforeArgument, ``afterArgument, ``semanticShape, ``sourceClosedAt,
      ``runtimeControls, ``auditDeclaration, ``auditModule, ``auditExactInheritedDependencies] do
    auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveSubstitutionStageRebase 2 inherited
  auditExactInheritedDependencies ``TrExprS.strengthenSubstitutionStageRebased inherited
  runtimeControls
  logInfo m!"stage-rebase tests: {proofControls.length} proof controls; all ten receipts forwarded; concrete beta actual domain and arguments; retained formal/base/suffix under nested binders; separate removal/target coordinates; source and target chain equality/type projections; support and closure negatives"

end InductiveSubstitutionStageRebaseTest
