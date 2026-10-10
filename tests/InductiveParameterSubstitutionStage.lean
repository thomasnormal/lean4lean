import Lean4Lean.Verify.InductiveParameterSubstitutionStage
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterSubstitutionStageTest

private def StageReceipt (env : VEnv) (universes : List Name)
    (source original aligned target : VLCtx) (removalLift insertionLift : Lift)
    (identifier : FVarId) (originalArgument originalDomain : VExpr)
    (body substituted : Expr) (bodySemantic : VExpr) (level : VLevel) : Prop :=
  ∃ reducedArgument reducedDomain domainLevel reducedBody,
    source.find? (.inr identifier) = some (reducedArgument, reducedDomain) ∧
    TrExprS env universes source (.fvar identifier) reducedArgument ∧
    env.IsDefEq universes.length original.toCtx originalDomain
      (reducedDomain.lift' removalLift) (.sort domainLevel) ∧
    env.IsDefEq universes.length original.toCtx originalArgument
      (reducedArgument.lift' removalLift) originalDomain ∧
    VLCtx.FVLift' ((none, .vlam reducedDomain) :: source)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) 1 removalLift 1 ∧
    VLCtx.IsDefEq env universes.length ((none, .vlam originalDomain) :: original)
      ((none, .vlam (reducedDomain.lift' removalLift)) :: aligned) ∧
    env.HasType universes.length source.toCtx reducedDomain (.sort domainLevel) ∧
    TrExprS env universes ((none, .vlam reducedDomain) :: source) body reducedBody ∧
    env.HasType universes.length (reducedDomain :: source.toCtx) reducedBody (.sort level) ∧
    env.IsDefEq universes.length (originalDomain :: original.toCtx)
      bodySemantic (reducedBody.lift' removalLift.cons) (.sort level) ∧
    env.HasType universes.length source.toCtx reducedArgument reducedDomain ∧
    env.HasType universes.length source.toCtx (reducedBody.inst reducedArgument) (.sort level) ∧
    env.IsDefEq universes.length original.toCtx (bodySemantic.inst originalArgument)
      ((reducedBody.inst reducedArgument).lift' removalLift) (.sort level) ∧
    TrExprS env universes ((none, .vlam (reducedDomain.lift' insertionLift)) :: target)
      body (reducedBody.lift' insertionLift.cons) ∧
    env.HasType universes.length ((reducedDomain.lift' insertionLift) :: target.toCtx)
      (reducedBody.lift' insertionLift.cons) (.sort level) ∧
    env.HasType universes.length target.toCtx (reducedArgument.lift' insertionLift)
      (reducedDomain.lift' insertionLift) ∧
    env.HasType universes.length target.toCtx
      ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift)) (.sort level) ∧
    Closed substituted 0 ∧ substituted.FVarsIn (· ∈ source.fvars) ∧
    TrExprS env universes original substituted (bodySemantic.inst originalArgument) ∧
    TrExprS env universes source substituted (reducedBody.inst reducedArgument) ∧
    TrExprS env universes target (.fvar identifier) (reducedArgument.lift' insertionLift) ∧
    TrExprS env universes target substituted
      ((reducedBody.lift' insertionLift.cons).inst (reducedArgument.lift' insertionLift))

private theorem coreForwardsEveryReceipt
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalDomain : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalDomain))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ source.fvars)) :
    StageReceipt env universes source original aligned target removalLift insertionLift identifier
      originalArgument originalDomain body (body.instantiate1' (.fvar identifier)) bodySemantic level :=
  receipt.instantiateStageIsTypeRebasedCore envWF removal contexts insertion targetWF position identifier
    selected originalLookup translated typed closed supported

private theorem nativeForwardsEveryReceipt
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalDomain : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalDomain))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes ((none, .vlam originalDomain) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalDomain :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ source.fvars)) :
    StageReceipt env universes source original aligned target removalLift insertionLift identifier
      originalArgument originalDomain body (body.instantiate1 (.fvar identifier)) bodySemantic level :=
  receipt.instantiateStageIsTypeRebased envWF removal contexts insertion targetWF position identifier
    selected originalLookup translated typed closed supported

private def retained : FVarId := ⟨`ParameterStageRetained⟩
private def suffix : FVarId := ⟨`ParameterStageSuffix⟩
private def discarded : FVarId := ⟨`ParameterStageDiscarded⟩
private def insertedFirst : FVarId := ⟨`ParameterStageInsertedFirst⟩
private def insertedSecond : FVarId := ⟨`ParameterStageInsertedSecond⟩
private def absent : FVarId := ⟨`ParameterStageAbsent⟩
private def domain : VExpr := .sort .zero
private def domainLevel : VLevel := .succ .zero
private def stageLevel : VLevel := .imax .zero (.imax .zero .zero)
private def betaDomain : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) domain
private def base : VLCtx := [(some (retained, []), .vlam domain)]
private def originalBase : VLCtx := [(some (retained, []), .vlam betaDomain)]
private def source : VLCtx := (some (suffix, []), .vlam domain) :: base
private def aligned : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (discarded, []), .vlam domain) :: base
private def original : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (discarded, []), .vlam domain) :: originalBase
private def target : VLCtx :=
  (some (suffix, []), .vlam domain) :: (some (insertedFirst, []), .vlam domain) ::
    (some (insertedSecond, []), .vlam domain) :: base
private def removalLift : Lift := .cons (.skip .refl)
private def insertionLift : Lift := .cons (.skip (.skip .refl))
private def identifiers : List FVarId := [suffix, retained]
private def nativeBody : Expr :=
  .forallE `formalUse (.bvar 0)
    (.forallE `suffixUse (.fvar suffix) (.fvar retained) .default) .default
private def originalBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 5))
private def reducedBody : VExpr := .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 4))
private def substituted : Expr := nativeBody.instantiate1' (.fvar retained)

private theorem betaDomainEquality (env : VEnv) (context : List VExpr) :
    env.IsDefEq 0 context betaDomain domain (.sort domainLevel) :=
  .beta (.bvar .zero) (.sortDF (by trivial) (by trivial) rfl)

private theorem extendDomainWF (env : VEnv) (context : VLCtx) (identifier : FVarId)
    (contextWF : context.WF env 0) (fresh : identifier ∉ context.fvars) :
    VLCtx.WF env 0 ((some (identifier, []), .vlam domain) :: context) := by
  refine ⟨contextWF, ?_, domainLevel, .sortDF (by trivial) (by trivial) rfl⟩
  rintro selected dependencies equality
  cases equality
  exact ⟨fresh, by simp⟩

private theorem baseWF (env : VEnv) : base.WF env 0 :=
  extendDomainWF env [] retained (by trivial) (by simp [VLCtx.fvars])

private theorem sourceWF (env : VEnv) : source.WF env 0 :=
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

private theorem extendDomainAgreement {env : VEnv} {first second : VLCtx}
    (contexts : VLCtx.IsDefEq env 0 first second) (identifier : FVarId)
    (fresh : identifier ∉ first.fvars) :
    VLCtx.IsDefEq env 0 ((some (identifier, []), .vlam domain) :: first)
      ((some (identifier, []), .vlam domain) :: second) := by
  apply VLCtx.IsDefEq.cons contexts
  · rintro selected dependencies equality
    cases equality
    exact ⟨fresh, by simp⟩
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem originalAndAlignedContextsAgree (env : VEnv) :
    VLCtx.IsDefEq env 0 original aligned := by
  have bases : VLCtx.IsDefEq env 0 originalBase base := by
    apply VLCtx.IsDefEq.cons .nil
    · rintro selected dependencies equality
      cases equality
      simp [VLCtx.fvars]
    · exact .vlam (betaDomainEquality env [])
  have middles := extendDomainAgreement bases discarded
    (by simp [originalBase, VLCtx.fvars, discarded, retained])
  exact extendDomainAgreement middles suffix
    (by simp [originalBase, VLCtx.fvars, suffix, discarded, retained])

private theorem selectedSuffixRemoval : VLCtx.FVLift' source aligned 0 removalLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (discarded, []) (.vlam domain) .refl)

private theorem selectedSuffixInsertion : VLCtx.FVLift' source target 0 insertionLift 0 :=
  .cons_fvar (suffix, []) (.vlam domain) (by simp)
    (.skip_fvar (insertedFirst, []) (.vlam domain)
      (.skip_fvar (insertedSecond, []) (.vlam domain) .refl))

private theorem actualPrefixReceipt (env : VEnv) (envWF : env.WF) :
    RetainedFVarPrefixAgreement env [] source original aligned removalLift identifiers := by
  have transported := selectedSuffixRemoval.retainedPrefix (universes := []) (identifiers := identifiers)
    envWF (sourceWF env) (alignedWF env)
    (by intro identifier member; simpa [identifiers, source, base, VLCtx.fvars] using member)
  exact transported.agreesWithOriginal envWF (originalAndAlignedContextsAgree env)

private theorem selectedOriginalLookup : original.find? (.inr retained) = some (.bvar 2, betaDomain) := rfl

private theorem selectedSourceLookup : source.find? (.inr retained) = some (.bvar 1, domain) := rfl

private theorem originalNestedBodyTyped (env : VEnv) :
    env.HasType 0 (betaDomain :: original.toCtx) originalBody (.sort stageLevel) :=
  .forallEDF (.defeqDF (betaDomainEquality env _) (.bvar .zero))
    (.forallEDF (.bvar (.succ (.succ .zero)))
      (.defeqDF (betaDomainEquality env _) (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))))

private theorem originalNestedBodyTranslated (env : VEnv) :
    TrExprS env [] ((none, .vlam betaDomain) :: original) nativeBody originalBody :=
  .forallE ⟨.zero, .defeqDF (betaDomainEquality env _) (.bvar .zero)⟩
    ⟨.imax .zero .zero, .forallEDF (.bvar (.succ (.succ .zero)))
      (.defeqDF (betaDomainEquality env _) (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))⟩
    (.bvar rfl)
    (.forallE ⟨.zero, .bvar (.succ (.succ .zero))⟩
      ⟨.zero, .defeqDF (betaDomainEquality env _) (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))⟩
      (.fvar rfl) (.fvar rfl))

private theorem stageBodyClosedAndSupported :
    Closed nativeBody 1 ∧ nativeBody.FVarsIn (· ∈ source.fvars) := by
  constructor
  · change (0 < 1) ∧ True ∧ True
    decide
  · simp [nativeBody, FVarsIn, source, base, VLCtx.fvars]

private theorem genuineSelectedCore (env : VEnv) (envWF : env.WF) :
    StageReceipt env [] source original aligned target removalLift insertionLift retained (.bvar 2)
      betaDomain nativeBody substituted originalBody stageLevel :=
  (actualPrefixReceipt env envWF).instantiateStageIsTypeRebasedCore envWF selectedSuffixRemoval
    (originalAndAlignedContextsAgree env) selectedSuffixInsertion (targetWF env) 1 retained
    rfl selectedOriginalLookup (originalNestedBodyTranslated env) (originalNestedBodyTyped env)
    stageBodyClosedAndSupported.1 stageBodyClosedAndSupported.2

private theorem genuineSelectedNative (env : VEnv) (envWF : env.WF) :
    StageReceipt env [] source original aligned target removalLift insertionLift retained (.bvar 2)
      betaDomain nativeBody (nativeBody.instantiate1 (.fvar retained)) originalBody stageLevel :=
  (actualPrefixReceipt env envWF).instantiateStageIsTypeRebased envWF selectedSuffixRemoval
    (originalAndAlignedContextsAgree env) selectedSuffixInsertion (targetWF env) 1 retained
    rfl selectedOriginalLookup (originalNestedBodyTranslated env) (originalNestedBodyTyped env)
    stageBodyClosedAndSupported.1 stageBodyClosedAndSupported.2

private theorem selectedStageProjectsAllThreeSubstitutedTranslations (env : VEnv) (envWF : env.WF) :
    ∃ reduced : VExpr,
      Closed substituted 0 ∧ substituted.FVarsIn (· ∈ source.fvars) ∧
      TrExprS env [] original substituted (originalBody.inst (.bvar 2)) ∧
      TrExprS env [] source substituted (reduced.inst (.bvar 1)) ∧
      TrExprS env [] target (.fvar retained) ((VExpr.bvar 1).lift' insertionLift) ∧
      TrExprS env [] target substituted
        ((reduced.lift' insertionLift.cons).inst ((VExpr.bvar 1).lift' insertionLift)) ∧
      env.IsDefEq 0 original.toCtx (originalBody.inst (.bvar 2))
        ((reduced.inst (.bvar 1)).lift' removalLift) (.sort stageLevel) ∧
      env.HasType 0 source.toCtx (reduced.inst (.bvar 1)) (.sort stageLevel) ∧
      env.HasType 0 target.toCtx
        ((reduced.lift' insertionLift.cons).inst ((VExpr.bvar 1).lift' insertionLift)) (.sort stageLevel) := by
  obtain ⟨argument, reducedDomain, _, reduced, lookup, _, _, _, _, _, _, _, _, _, _, reducedType,
    endpointEquality, _, _, _, targetType, closed, supported, originalTranslation,
    sourceTranslation, argumentTranslation, targetTranslation⟩ := genuineSelectedCore env envWF
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lookup.symm.trans selectedSourceLookup))
  exact ⟨reduced, closed, supported, originalTranslation, sourceTranslation, argumentTranslation,
    targetTranslation, endpointEquality, reducedType, targetType⟩

private theorem selectedPositionAndLookupBoundaries :
    identifiers[1]? = some retained ∧ identifiers[0]? = some suffix ∧ identifiers[2]? = none ∧
    original.find? (.inr absent) = none ∧ source.find? (.inr discarded) = none ∧
    original.find? (.inr retained) ≠ some (.bvar 1, betaDomain) ∧
    original.find? (.inr retained) ≠ some (.bvar 2, domain) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem actualOriginalDomainIsNotTheAlignedDeclaredDomain :
    betaDomain ≠ domain ∧ original ≠ aligned ∧
    (VExpr.bvar 1).lift' removalLift = .bvar 2 := by
  refine ⟨?_, ?_, rfl⟩ <;> intro equality <;> cases equality

private theorem substitutedNativeBodyUsesTheSelectedParameter :
    substituted = .forallE `formalUse (.fvar retained)
      (.forallE `suffixUse (.fvar suffix) (.fvar retained) .default) .default ∧
    Closed substituted 0 ∧ substituted.FVarsIn (· ∈ source.fvars) := by
  refine ⟨rfl, ?_, ?_⟩
  · change True ∧ True ∧ True
    trivial
  · simp [substituted, nativeBody, Expr.instantiate1', FVarsIn, source, base, VLCtx.fvars]

private theorem bodyFormalAndContextLiftsRemainIndependent :
    reducedBody.lift' removalLift.cons = originalBody ∧
    reducedBody.lift' insertionLift.cons = .forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6)) ∧
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' insertionLift ∧
    (VExpr.bvar 1).lift' insertionLift ≠ (VExpr.bvar 1).lift' insertionLift.cons := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem instantiatedEndpointsUseTheIndependentTargetLift :
    (reducedBody.inst (.bvar 1)).lift' insertionLift =
      (reducedBody.lift' insertionLift.cons).inst ((VExpr.bvar 1).lift' insertionLift) ∧
    (reducedBody.inst (.bvar 1)).lift' insertionLift = .forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5)) ∧
    (reducedBody.inst (.bvar 1)).lift' insertionLift ≠ (reducedBody.inst (.bvar 1)).lift' removalLift := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem targetInsertionProtectsTheSelectedSuffix :
    (VExpr.bvar 0).lift' insertionLift = .bvar 0 ∧
    reducedBody.lift' insertionLift.cons ≠ reducedBody.lift' (Lift.skip (.skip .refl)).cons := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private theorem droppedAndMissingFreeVarsCannotSupplyBodySupport :
    ¬(Expr.fvar discarded).FVarsIn (· ∈ source.fvars) ∧
    ¬(Expr.fvar absent).FVarsIn (· ∈ source.fvars) := by
  simp [FVarsIn, source, base, VLCtx.fvars, discarded, absent, suffix, retained]

private theorem originalTranslationDoesNotReplaceSourceSupport (env : VEnv) :
    TrExprS env [] ((none, .vlam betaDomain) :: original) (.fvar discarded) (.bvar 2) ∧
    ¬(Expr.fvar discarded).FVarsIn (· ∈ source.fvars) :=
  ⟨.fvar rfl, droppedAndMissingFreeVarsCannotSupplyBodySupport.1⟩

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
    (identifiers[1]? == some retained, "selected position chooses retained base parameter"),
    (identifiers[0]? == some suffix, "different position chooses suffix"),
    (identifiers[2]? == none, "missing position does not select a parameter"),
    (!source.fvars.contains discarded && !source.fvars.contains absent, "removed and missing declarations lack support"),
    (original.fvars.contains discarded, "removed declaration existed originally"),
    (target.fvars.contains insertedFirst && target.fvars.contains insertedSecond, "target has two independent insertions"),
    (source.toCtx.length == 2 && original.toCtx.length == 3 && target.toCtx.length == 4, "source original target context widths differ"),
    (semanticShape betaDomain != semanticShape domain, "original lookup uses a nonliteral beta domain"),
    (sourceClosedAt nativeBody 1 && !sourceClosedAt nativeBody 0, "formal body requires Closed 1"),
    (!sourceClosedAt (.bvar 1) 1, "extra loose formal is excluded"),
    (sourceClosedAt substituted 0, "selected substitution closes the formal"),
    (substituted.fvarsList.contains retained && substituted.fvarsList.contains suffix, "substituted body uses retained parameter and suffix"),
    (!substituted.fvarsList.contains discarded, "substitution does not acquire removed support"),
    (nativeBody.instantiate1 (.fvar retained) == substituted, "native substitution agrees with structural substitution"),
    (semanticShape ((VExpr.bvar 1).lift' removalLift) == [0, 2], "source selected parameter lifts to original base"),
    (semanticShape ((VExpr.bvar 1).lift' insertionLift) == [0, 3], "source selected parameter lifts to independent target base"),
    (semanticShape ((VExpr.bvar 0).lift' insertionLift) == [0, 0], "target insertion protects suffix"),
    (semanticShape (reducedBody.lift' removalLift.cons) == semanticShape originalBody, "body removal protects stage formal"),
    (semanticShape (reducedBody.lift' insertionLift.cons) ==
      semanticShape (.forallE (.bvar 0) (.forallE (.bvar 2) (.bvar 6))), "target body formal suffix and base coordinates are exact"),
    (semanticShape (reducedBody.lift' insertionLift.cons) != semanticShape (reducedBody.lift' insertionLift), "target body needs the cons lift"),
    (semanticShape ((VExpr.bvar 1).lift' insertionLift) != semanticShape ((VExpr.bvar 1).lift' insertionLift.cons), "selected domain and argument need plain context lift"),
    (semanticShape ((reducedBody.inst (.bvar 1)).lift' insertionLift) ==
      semanticShape ((reducedBody.lift' insertionLift.cons).inst ((VExpr.bvar 1).lift' insertionLift)), "target endpoint commutes with selected instantiation"),
    (semanticShape ((reducedBody.inst (.bvar 1)).lift' insertionLift) ==
      semanticShape (.forallE (.bvar 3) (.forallE (.bvar 1) (.bvar 5))), "target endpoint coordinates are exact"),
    (semanticShape ((reducedBody.inst (.bvar 1)).lift' insertionLift) !=
      semanticShape ((reducedBody.inst (.bvar 1)).lift' removalLift), "target insertion does not reuse removal coordinates")]
  for (condition, label) in conditions do
    unless condition do throwError "selected-stage runtime failed: {label}"
  logInfo m!"selected-stage runtime: {conditions.length} position/lookup, nonliteral actual domain, independent removal/insertion, protected formal/suffix/base, native/core substitution, support and closure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "selected-stage audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do throwError "selected-stage unexpected axiom {axiomName} in {name}"

private def auditModule (moduleName : Name) (expected : Nat) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "selected-stage audited module absent: {moduleName}"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "selected-stage module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  unless declarations == expected do
    throwError "selected-stage module declaration manifest changed: {moduleName}; expected {expected}, got {declarations}"
  logInfo m!"{moduleName}: {declarations} declarations including private/generated helpers audited"

private def auditExactDependencies (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == allowed.length && allowed.all axioms.contains do
    throwError "selected-stage exact dependency manifest changed: {name}"
  logInfo m!"{name}: exact {allowed.length} inherited dependencies"

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let native := inherited ++ [``Expr.instantiate1_eq]
  let coreControls := [``coreForwardsEveryReceipt, ``betaDomainEquality, ``extendDomainWF, ``baseWF,
    ``sourceWF, ``alignedWF, ``targetWF, ``extendDomainAgreement, ``originalAndAlignedContextsAgree,
    ``selectedSuffixRemoval, ``selectedSuffixInsertion, ``actualPrefixReceipt, ``selectedOriginalLookup,
    ``selectedSourceLookup, ``originalNestedBodyTyped, ``originalNestedBodyTranslated,
    ``stageBodyClosedAndSupported, ``genuineSelectedCore, ``selectedStageProjectsAllThreeSubstitutedTranslations,
    ``selectedPositionAndLookupBoundaries, ``actualOriginalDomainIsNotTheAlignedDeclaredDomain,
    ``substitutedNativeBodyUsesTheSelectedParameter, ``bodyFormalAndContextLiftsRemainIndependent,
    ``instantiatedEndpointsUseTheIndependentTargetLift, ``targetInsertionProtectsTheSelectedSuffix,
    ``droppedAndMissingFreeVarsCannotSupplyBodySupport, ``originalTranslationDoesNotReplaceSourceSupport,
    ``formalBinderNeedsClosedOneRatherThanClosedZero]
  for name in coreControls do auditDeclaration name inherited
  for name in [``nativeForwardsEveryReceipt, ``genuineSelectedNative] do auditDeclaration name native
  auditDeclaration ``StageReceipt inherited
  for name in [``retained, ``suffix, ``discarded, ``insertedFirst, ``insertedSecond, ``absent, ``domain,
      ``domainLevel, ``stageLevel, ``betaDomain, ``base, ``originalBase, ``source, ``aligned, ``original,
      ``target, ``removalLift, ``insertionLift, ``identifiers, ``nativeBody, ``originalBody, ``reducedBody,
      ``substituted, ``semanticShape, ``sourceClosedAt, ``runtimeControls, ``auditDeclaration,
      ``auditModule, ``auditExactDependencies] do auditDeclaration name logical
  auditModule `Lean4Lean.Verify.InductiveParameterSubstitutionStage 2 native
  auditExactDependencies ``RetainedFVarPrefixAgreement.instantiateStageIsTypeRebasedCore inherited
  auditExactDependencies ``RetainedFVarPrefixAgreement.instantiateStageIsTypeRebased native
  runtimeControls
  logInfo m!"selected-stage tests: {coreControls.length + 2} proof controls; both APIs forward all twenty-three receipts; genuine selected prefix with beta-valued original declared domain; original/reduced/target substituted translations and endpoint typing; exact selected lookup, context, closure, support and plain-versus-cons lift boundaries"

end InductiveParameterSubstitutionStageTest
