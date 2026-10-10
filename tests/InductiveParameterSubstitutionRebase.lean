import Lean4Lean.Verify.InductiveParameterSubstitutionRebase
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterSubstitutionRebaseTest

private theorem coreProjectsThreeSortCorrectAgreements
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ source.fvars)) :
    ∃ (reducedArgument reducedArgumentType reducedSemantic : VExpr),
      source.find? (.inr identifier) = some (reducedArgument, reducedArgumentType) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (bodySemantic.inst (reducedArgument.lift' removalLift)) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst originalArgument) (reducedSemantic.lift' removalLift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        (bodySemantic.inst (reducedArgument.lift' removalLift)) (reducedSemantic.lift' removalLift) (.sort level) := by
  obtain ⟨argument, argumentType, semantic, lookup, _, _, _, _, _, _, substitutionEquality,
    _, _, rebaseEquality, alternateEquality, _, _⟩ :=
    receipt.instantiateIsTypeRebasedCore envWF removal contexts insertion targetWF position identifier
      selected originalLookup translated typed closed supported
  exact ⟨argument, argumentType, semantic, lookup, substitutionEquality, rebaseEquality, alternateEquality⟩

private theorem nativeProjectsClosureSupportAndTargetTyping
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift identifiers)
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    (position : Nat) (identifier : FVarId) (selected : identifiers[position]? = some identifier)
    {originalArgument originalArgumentType : VExpr}
    (originalLookup : original.find? (.inr identifier) = some (originalArgument, originalArgumentType))
    {body : Expr} {bodySemantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes ((none, .vlam originalArgumentType) :: original) body bodySemantic)
    (typed : env.HasType universes.length (originalArgumentType :: original.toCtx) bodySemantic (.sort level))
    (closed : Closed body 1) (supported : body.FVarsIn (· ∈ source.fvars)) :
    Closed (body.instantiate1 (.fvar identifier)) 0 ∧
      (body.instantiate1 (.fvar identifier)).FVarsIn (· ∈ source.fvars) ∧
      ∃ (reducedSemantic : VExpr),
        TrExprS env universes target (body.instantiate1 (.fvar identifier)) (reducedSemantic.lift' insertionLift) ∧
        env.HasType universes.length target.toCtx (reducedSemantic.lift' insertionLift) (.sort level) := by
  obtain ⟨_, _, semantic, _, _, _, resultClosed, resultSupported, _, _, _, _, _, _, _,
    targetTranslation, targetTyping⟩ :=
    receipt.instantiateIsTypeRebased envWF removal contexts insertion targetWF position identifier
      selected originalLookup translated typed closed supported
  exact ⟨resultClosed, resultSupported, semantic, targetTranslation, targetTyping⟩

private def carrier : FVarId := ⟨`ParameterSubstitutionRebaseCarrier⟩
private def aliasIdentifier : FVarId := ⟨`ParameterSubstitutionRebaseAlias⟩
private def insertedOne : FVarId := ⟨`ParameterSubstitutionRebaseInsertedOne⟩
private def insertedTwo : FVarId := ⟨`ParameterSubstitutionRebaseInsertedTwo⟩
private def insertedThree : FVarId := ⟨`ParameterSubstitutionRebaseInsertedThree⟩
private def selectedIdentifier : FVarId := ⟨`ParameterSubstitutionRebaseSelected⟩
private def absentIdentifier : FVarId := ⟨`ParameterSubstitutionRebaseAbsent⟩
private def parameterType : VExpr := .sort (.succ .zero)
private def betaValue : VExpr := .app (.lam parameterType (.bvar 0)) (.bvar 0)

private def sourceContext : VLCtx :=
  [(some (aliasIdentifier, [carrier]), .vlet parameterType (.bvar 0)),
    (some (carrier, []), .vlam parameterType)]

private def originalContext : VLCtx :=
  [(some (aliasIdentifier, [carrier]), .vlet parameterType betaValue),
    (some (carrier, []), .vlam parameterType)]

private def insertLambda (identifier : FVarId) (context : VLCtx) : VLCtx :=
  (some (identifier, []), .vlam (.sort .zero)) :: context

private def insertThree (context : VLCtx) : VLCtx :=
  insertLambda insertedThree (insertLambda insertedTwo (insertLambda insertedOne context))

private theorem contextsAgreeByNonLiteralBeta (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes originalContext sourceContext := by
  apply VLCtx.IsDefEq.cons
  · apply VLCtx.IsDefEq.cons .nil
    · rintro identifier dependencies equality
      cases equality
      simp [VLCtx.fvars]
    · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, carrier, aliasIdentifier]
  · exact .vlet (.beta (.bvar .zero) (.bvar .zero)) (.sortDF (by trivial) (by trivial) rfl)

private theorem insertionPreservesContextAgreement
    {env : VEnv} {universes : Nat} {original aligned : VLCtx}
    (contexts : VLCtx.IsDefEq env universes original aligned)
    (identifier : FVarId) (fresh : identifier ∉ original.fvars) :
    VLCtx.IsDefEq env universes (insertLambda identifier original) (insertLambda identifier aligned) := by
  apply VLCtx.IsDefEq.cons contexts
  · rintro selected dependencies equality
    cases equality
    exact ⟨fresh, by simp⟩
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem oneInsertedContextsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertLambda insertedOne originalContext)
      (insertLambda insertedOne sourceContext) :=
  insertionPreservesContextAgreement (contextsAgreeByNonLiteralBeta env universes) insertedOne (by decide)

private theorem threeInsertedContextsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertThree originalContext) (insertThree sourceContext) := by
  apply insertionPreservesContextAgreement
  · apply insertionPreservesContextAgreement
    · exact oneInsertedContextsAgree env universes
    · decide
  · decide

private theorem oneInsertedWeakening :
    VLCtx.FVLift' sourceContext (insertLambda insertedOne sourceContext) 0 (.skip .refl) 0 :=
  .skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl

private theorem threeInsertedWeakening :
    VLCtx.FVLift' sourceContext (insertThree sourceContext) 0 (.skipN .refl 3) 0 :=
  .skip_fvar (insertedThree, []) (.vlam (.sort .zero))
    (.skip_fvar (insertedTwo, []) (.vlam (.sort .zero))
      (.skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl))

private def forallBody : Expr :=
  .forallE `outer (.bvar 0) (.forallE `inner (.bvar 1) (.bvar 2) .default) .default

private def forallSemantic : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))
private def forallLevel : VLevel := .imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))

private theorem forallBodyTyped (env : VEnv) (universes : Nat) (context : List VExpr) :
    env.HasType universes (parameterType :: context) forallSemantic (.sort forallLevel) :=
  VEnv.HasType.forallE (.bvar .zero)
    (VEnv.HasType.forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero))))

private theorem forallBodyTranslated (env : VEnv) (universes : List Name) (context : VLCtx) :
    TrExprS env universes ((none, .vlam parameterType) :: context) forallBody forallSemantic := by
  apply TrExprS.forallE
  · exact ⟨.succ .zero, .bvar .zero⟩
  · exact ⟨.imax (.succ .zero) (.succ .zero),
      VEnv.HasType.forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))⟩
  · exact .bvar rfl
  · apply TrExprS.forallE
    · exact ⟨.succ .zero, .bvar (.succ .zero)⟩
    · exact ⟨.succ .zero, .bvar (.succ (.succ .zero))⟩
    · exact .bvar rfl
    · exact .bvar rfl

private theorem forallBodyClosed : Closed forallBody 1 := by simp [forallBody, Closed]

private theorem forallBodySupported (source : VLCtx) : forallBody.FVarsIn (· ∈ source.fvars) := by
  simp [forallBody, FVarsIn]

private def RebasedOutcome (env : VEnv) (universes : List Name) (source original target : VLCtx)
    (removalLift insertionLift : Lift) (originalArgument reducedArgument : VExpr) : Prop :=
  Closed (forallBody.instantiate1' (.fvar aliasIdentifier)) 0 ∧
    (forallBody.instantiate1' (.fvar aliasIdentifier)).FVarsIn (· ∈ source.fvars) ∧
    ∃ reducedSemantic,
      TrExprS env universes source (forallBody.instantiate1' (.fvar aliasIdentifier)) reducedSemantic ∧
      env.HasType universes.length source.toCtx reducedSemantic (.sort forallLevel) ∧
      env.IsDefEq universes.length original.toCtx
        (forallSemantic.inst originalArgument) (forallSemantic.inst (reducedArgument.lift' removalLift)) (.sort forallLevel) ∧
      env.IsDefEq universes.length original.toCtx
        (forallSemantic.inst originalArgument) (reducedSemantic.lift' removalLift) (.sort forallLevel) ∧
      env.IsDefEq universes.length original.toCtx
        (forallSemantic.inst (reducedArgument.lift' removalLift)) (reducedSemantic.lift' removalLift) (.sort forallLevel) ∧
      TrExprS env universes target (forallBody.instantiate1' (.fvar aliasIdentifier)) (reducedSemantic.lift' insertionLift) ∧
      env.HasType universes.length target.toCtx (reducedSemantic.lift' insertionLift) (.sort forallLevel)

private theorem agreementRebasesTheForallBody
    {env : VEnv} {universes : List Name} {source original aligned target : VLCtx}
    {removalLift insertionLift : Lift}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned removalLift [carrier, aliasIdentifier])
    (envWF : env.WF) (removal : VLCtx.FVLift' source aligned 0 removalLift 0)
    (contexts : VLCtx.IsDefEq env universes.length original aligned)
    (insertion : VLCtx.FVLift' source target 0 insertionLift 0)
    (targetWF : target.WF env universes.length)
    {originalArgument reducedArgument : VExpr}
    (originalLookup : original.find? (.inr aliasIdentifier) = some (originalArgument, parameterType))
    (sourceLookup : source.find? (.inr aliasIdentifier) = some (reducedArgument, parameterType)) :
    RebasedOutcome env universes source original target removalLift insertionLift originalArgument reducedArgument := by
  obtain ⟨argument, argumentType, semantic, lookup, _, _, closed, supported, _, _, substitutionEquality,
    sourceTranslation, sourceTyping, rebaseEquality, alternateEquality, targetTranslation, targetTyping⟩ :=
    receipt.instantiateIsTypeRebasedCore envWF removal contexts insertion targetWF 1 aliasIdentifier
      rfl originalLookup (forallBodyTranslated env universes original)
      (forallBodyTyped env universes.length original.toCtx) forallBodyClosed (forallBodySupported source)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lookup.symm.trans sourceLookup))
  exact ⟨closed, supported, semantic, sourceTranslation, sourceTyping, substitutionEquality,
    rebaseEquality, alternateEquality, targetTranslation, targetTyping⟩

private theorem oneRemovedThreeInsertedRebasesNonLiteralBeta
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RebasedOutcome env universes sourceContext (insertLambda insertedOne originalContext)
      (insertThree sourceContext) (.skip .refl) (.skipN .refl 3)
      (betaValue.lift' (.skip .refl)) (.bvar 0) := by
  have contexts := oneInsertedContextsAgree env universes.length
  have sourceWF := ((contextsAgreeByNonLiteralBeta env universes.length).symm envWF.ordered).wf
  have alignedWF := (contexts.symm envWF.ordered).wf
  have targetWF := ((threeInsertedContextsAgree env universes.length).symm envWF.ordered).wf
  have receipt := (oneInsertedWeakening.retainedPrefix envWF sourceWF alignedWF
    (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simpa [sourceContext, VLCtx.fvars, or_comm] using member)).agreesWithOriginal envWF contexts
  exact agreementRebasesTheForallBody receipt envWF oneInsertedWeakening contexts
    threeInsertedWeakening targetWF rfl rfl

private def selectedSource : VLCtx := insertLambda selectedIdentifier sourceContext
private def selectedOriginal : VLCtx := insertLambda selectedIdentifier (insertLambda insertedOne originalContext)
private def selectedAligned : VLCtx := insertLambda selectedIdentifier (insertLambda insertedOne sourceContext)
private def selectedTarget : VLCtx := insertLambda selectedIdentifier (insertThree sourceContext)

private theorem selectedEndpointsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes selectedOriginal selectedAligned :=
  insertionPreservesContextAgreement (oneInsertedContextsAgree env universes) selectedIdentifier (by decide)

private theorem selectedTargetContextsAgree (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertLambda selectedIdentifier (insertThree originalContext)) selectedTarget :=
  insertionPreservesContextAgreement (threeInsertedContextsAgree env universes) selectedIdentifier (by decide)

private theorem selectedRemoval :
    VLCtx.FVLift' selectedSource selectedAligned 0 (.consN (.skip .refl) 1) 0 :=
  .cons_fvar (selectedIdentifier, []) (.vlam (.sort .zero)) (by simp) oneInsertedWeakening

private theorem selectedInsertion :
    VLCtx.FVLift' selectedSource selectedTarget 0 (.consN (.skipN .refl 3) 1) 0 :=
  .cons_fvar (selectedIdentifier, []) (.vlam (.sort .zero)) (by simp) threeInsertedWeakening

private theorem selectedEndpointRebaseUsesDistinctConsNCutoffs
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RebasedOutcome env universes selectedSource selectedOriginal selectedTarget
      (.consN (.skip .refl) 1) (.consN (.skipN .refl 3) 1)
      (betaValue.lift' (.skipN .refl 2)) (.bvar 1) := by
  have contexts := selectedEndpointsAgree env universes.length
  have alignedWF := (contexts.symm envWF.ordered).wf
  have sourceWF := selectedRemoval.wf envWF alignedWF
  have targetWF := ((selectedTargetContextsAgree env universes.length).symm envWF.ordered).wf
  have receipt := (selectedRemoval.retainedPrefix envWF sourceWF alignedWF
    (identifiers := [carrier, aliasIdentifier])
    (by intro identifier member; simp [selectedSource, insertLambda, sourceContext, VLCtx.fvars] at member ⊢
        grind)).agreesWithOriginal envWF contexts
  exact agreementRebasesTheForallBody receipt envWF selectedRemoval contexts selectedInsertion targetWF rfl rfl

private theorem nativeCoreSubstitutionPreservesBothForallBinders :
    forallBody.instantiate1' (.fvar aliasIdentifier) =
      .forallE `outer (.fvar aliasIdentifier) (.forallE `inner (.fvar aliasIdentifier) (.fvar aliasIdentifier) .default) .default := rfl

private theorem substitutedSemanticRaisesItsArgumentUnderBothBinders :
    forallSemantic.inst (.bvar 2) = .forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4)) := rfl

private theorem originalBetaIsNotItsReducedArgument : betaValue ≠ .bvar 0 := by
  intro equality
  cases equality

private theorem omittedParameterCannotProvideAgreement
    {env : VEnv} {universes : List Name} {original aligned : VLCtx} {lift : Lift} :
    ¬ RetainedFVarPrefixAgreement env universes [] original aligned lift [aliasIdentifier] := by
  intro receipt
  have member : aliasIdentifier ∈ VLCtx.fvars [] := receipt.transported.sourceRetained (by simp)
  simp at member

private theorem unsupportedBodyFailsItsPremise :
    ¬ (Expr.app forallBody (.fvar absentIdentifier)).FVarsIn (· ∈ sourceContext.fvars) := by
  simp [forallBody, FVarsIn, sourceContext, VLCtx.fvars, absentIdentifier, carrier, aliasIdentifier]

private theorem unclosedBodyFailsItsPremise : ¬ Closed (Expr.bvar 1) 1 := by simp [Closed]

private theorem wrongRequestedPositionCannotSelectTheParameter :
    [carrier, aliasIdentifier][0]? ≠ some aliasIdentifier ∧
      [carrier, aliasIdentifier][2]? = none := by simp [carrier, aliasIdentifier]

private theorem droppedOriginalContextCannotProvideAgreement
    {env : VEnv} {universes : List Name} {aligned : VLCtx} {lift : Lift} :
    ¬ RetainedFVarPrefixAgreement env universes sourceContext [] aligned lift [aliasIdentifier] := by
  intro receipt
  have member : aliasIdentifier ∈ VLCtx.fvars [] := receipt.originalRetained (by simp)
  simp at member

private def semanticShape : VExpr → List Nat
  | .bvar position => [0, position]
  | .sort _ => [1]
  | .const _ _ => [2]
  | .app function argument => [3] ++ semanticShape function ++ semanticShape argument
  | .lam type body => [4] ++ semanticShape type ++ semanticShape body
  | .forallE type body => [5] ++ semanticShape type ++ semanticShape body

private def runtimeRebases : MetaM Unit := do
  let expectedNative := Expr.forallE `outer (.fvar aliasIdentifier)
    (.forallE `inner (.fvar aliasIdentifier) (.fvar aliasIdentifier) .default) .default
  let mut checks := 0
  for (source, original, aligned, target, removalLift, insertionLift, reducedPosition, oldPosition, newPosition) in
      [(sourceContext, insertLambda insertedOne originalContext,
        insertLambda insertedOne sourceContext, insertThree sourceContext,
        Lift.skip .refl, Lift.skipN .refl 3, 0, 1, 3),
       (selectedSource, selectedOriginal, selectedAligned, selectedTarget,
        Lift.consN (.skip .refl) 1, Lift.consN (.skipN .refl 3) 1, 1, 2, 4)] do
    let some (sourceArgument, _) := source.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution-rebase source argument absent"
    let some (originalArgument, _) := original.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution-rebase original argument absent"
    let some (alignedArgument, _) := aligned.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution-rebase aligned argument absent"
    let some (targetArgument, _) := target.find? (.inr aliasIdentifier)
      | throwError "parameter-substitution-rebase target argument absent"
    let removedArgument := sourceArgument.lift' removalLift
    let insertedArgument := sourceArgument.lift' insertionLift
    let removedSemantic := (forallSemantic.inst sourceArgument).lift' removalLift
    let insertedSemantic := (forallSemantic.inst sourceArgument).lift' insertionLift
    let conditions := [
      (semanticShape sourceArgument == [0, reducedPosition], "source position"),
      (semanticShape alignedArgument == [0, oldPosition], "aligned position"),
      (semanticShape targetArgument == [0, newPosition], "target position"),
      (semanticShape removedArgument == semanticShape alignedArgument, "removal lookup"),
      (semanticShape insertedArgument == semanticShape targetArgument, "insertion lookup"),
      (semanticShape originalArgument != semanticShape removedArgument, "nonliteral beta"),
      (semanticShape removedArgument != semanticShape insertedArgument, "distinct lifts"),
      (forallBody.instantiate1' (.fvar aliasIdentifier) == expectedNative, "core nested substitution"),
      (forallBody.instantiate1 (.fvar aliasIdentifier) == expectedNative, "native nested substitution"),
      (semanticShape removedSemantic == semanticShape (forallSemantic.inst removedArgument), "removal under binders"),
      (semanticShape insertedSemantic == semanticShape (forallSemantic.inst insertedArgument), "insertion under binders"),
      (semanticShape removedSemantic == semanticShape (.forallE (.bvar oldPosition)
        (.forallE (.bvar (oldPosition + 1)) (.bvar (oldPosition + 2)))), "removed nested positions"),
      (semanticShape insertedSemantic == semanticShape (.forallE (.bvar newPosition)
        (.forallE (.bvar (newPosition + 1)) (.bvar (newPosition + 2)))), "inserted nested positions"),
      (semanticShape (forallSemantic.inst originalArgument) == semanticShape
        (.forallE originalArgument (.forallE originalArgument.lift (originalArgument.liftN 2))), "original beta shifts")]
    for (condition, label) in conditions do
      unless condition do throwError "parameter-substitution-rebase runtime failed: {label}"
    checks := checks + conditions.length
  logInfo m!"parameter-substitution-rebase runtime: {checks} lookup/substitution/shift checks; distinct one/three lifts and selected consN cutoff"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-substitution-rebase declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "parameter-substitution-rebase unexpected axiom {axiomName} in {name}"

private def auditModule (coreAllowed nativeAllowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterSubstitutionRebase
    | throwError "parameter-substitution-rebase module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-substitution-rebase module-owned axiom {name}"
      let allowed := if name == ``RetainedFVarPrefixAgreement.instantiateIsTypeRebased then nativeAllowed else coreAllowed
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"parameter-substitution-rebase module: {declarations} declarations audited; core excludes native/container/range/abstraction interfaces"

private def rejectedNativeInterface (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.instantiate1_eq (logical ++ [``sorryAx])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "parameter-substitution-rebase core audit accepted native instantiation"
  match exception with
  | .error _ message =>
    let expected := m!"parameter-substitution-rebase unexpected axiom {``Expr.instantiate1_eq} in {``Expr.instantiate1_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let nativeAllowed := inherited ++ [``Expr.instantiate1_eq]
  let inheritedControls := [``coreProjectsThreeSortCorrectAgreements, ``forallBodyTranslated,
    ``agreementRebasesTheForallBody, ``oneRemovedThreeInsertedRebasesNonLiteralBeta,
    ``selectedEndpointRebaseUsesDistinctConsNCutoffs,
    ``omittedParameterCannotProvideAgreement, ``droppedOriginalContextCannotProvideAgreement]
  let logicalControls := [``contextsAgreeByNonLiteralBeta, ``insertionPreservesContextAgreement,
    ``oneInsertedContextsAgree, ``threeInsertedContextsAgree, ``oneInsertedWeakening,
    ``threeInsertedWeakening, ``forallBodyTyped, ``forallBodyClosed, ``forallBodySupported,
    ``selectedEndpointsAgree, ``selectedTargetContextsAgree, ``selectedRemoval, ``selectedInsertion,
    ``nativeCoreSubstitutionPreservesBothForallBinders, ``substitutedSemanticRaisesItsArgumentUnderBothBinders,
    ``originalBetaIsNotItsReducedArgument, ``unsupportedBodyFailsItsPremise,
    ``unclosedBodyFailsItsPremise, ``wrongRequestedPositionCannotSelectTheParameter]
  for name in inheritedControls do auditDeclaration name inherited
  for name in logicalControls do auditDeclaration name logical
  auditDeclaration ``nativeProjectsClosureSupportAndTargetTyping nativeAllowed
  auditDeclaration ``Closed.instantiate1_offset logical
  auditModule inherited nativeAllowed
  rejectedNativeInterface logical
  runtimeRebases
  logInfo m!"parameter-substitution-rebase tests: {inheritedControls.length + logicalControls.length + 1} proof controls; sort-correct substitution/rebase/alternate agreement; nonliteral beta type parameter; nested forall; distinct one/three lifts; selected consN cutoff; omitted/dropped/unsupported/unclosed/wrong-position negatives; structural closure provenance audited"

end InductiveParameterSubstitutionRebaseTest
