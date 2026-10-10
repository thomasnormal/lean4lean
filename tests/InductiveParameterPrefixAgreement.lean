import Lean4Lean.Verify.InductiveParameterPrefixAgreement
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterPrefixAgreementTest

private theorem transportedPrefixAgreesWithItsOriginalTypedContext
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefix env universes source aligned lift identifiers)
    (envWF : env.WF) (contexts : VLCtx.IsDefEq env universes.length original aligned) :
    RetainedFVarPrefixAgreement env universes source original aligned lift identifiers :=
  receipt.agreesWithOriginal envWF contexts

private theorem originalLookupProjectsTypedValueAndSortCorrectTypeAgreement
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier) :
    ∃ semantic type originalSemantic originalType level,
      source.find? (.inr identifier) = some (semantic, type) ∧
      TrExprS env universes source (.fvar identifier) semantic ∧
      env.HasType universes.length source.toCtx semantic type ∧
      original.find? (.inr identifier) = some (originalSemantic, originalType) ∧
      TrExprS env universes original (.fvar identifier) originalSemantic ∧
      env.HasType universes.length original.toCtx originalSemantic originalType ∧
      env.IsDefEq universes.length original.toCtx originalType (type.lift' lift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        originalSemantic (semantic.lift' lift) originalType :=
  receipt.lookups position identifier selected

private theorem agreementRetainsTheDistinctAlignedTransportReceipt
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefixAgreement env universes source original aligned lift identifiers) :
    RetainedFVarPrefix env universes source aligned lift identifiers :=
  receipt.transported

private theorem missingOriginalParameterCannotSupplyAgreement
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (missing : identifier ∉ original.fvars) :
    ¬ RetainedFVarPrefixAgreement env universes source original aligned lift [identifier] := by
  intro receipt
  exact missing (receipt.originalRetained (by simp))

private theorem missingAlignedParameterCannotSupplyAgreement
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (missing : identifier ∉ aligned.fvars) :
    ¬ RetainedFVarPrefixAgreement env universes source original aligned lift [identifier] := by
  intro receipt
  exact missing (receipt.transported.targetRetained (by simp))

private theorem duplicatePositionsRemainSeparateLookupRequests
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (receipt : RetainedFVarPrefix env universes source aligned lift [identifier, identifier])
    (envWF : env.WF) (contexts : VLCtx.IsDefEq env universes.length original aligned) :
    RetainedFVarPrefixAgreement env universes source original aligned lift [identifier, identifier] :=
  receipt.agreesWithOriginal envWF contexts

private def carrier : FVarId := ⟨`PrefixAgreementCarrier⟩
private def element : FVarId := ⟨`PrefixAgreementElement⟩
private def aliasIdentifier : FVarId := ⟨`PrefixAgreementAlias⟩
private def insertedOne : FVarId := ⟨`PrefixAgreementInsertedOne⟩
private def insertedTwo : FVarId := ⟨`PrefixAgreementInsertedTwo⟩
private def insertedThree : FVarId := ⟨`PrefixAgreementInsertedThree⟩

private def betaValue : VExpr :=
  .app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)

private def sourceContext : VLCtx :=
  [(some (aliasIdentifier, [carrier, element]), .vlet (.bvar 1) (.bvar 0)),
    (some (element, [carrier]), .vlam (.bvar 0)),
    (some (carrier, []), .vlam (.sort (.succ .zero)))]

private def originalContext : VLCtx :=
  [(some (aliasIdentifier, [carrier, element]), .vlet (.bvar 1) betaValue),
    (some (element, [carrier]), .vlam (.bvar 0)),
    (some (carrier, []), .vlam (.sort (.succ .zero)))]

private def insertLambda (identifier : FVarId) (context : VLCtx) : VLCtx :=
  (some (identifier, []), .vlam (.sort .zero)) :: context

private def insertThreeLambdas (context : VLCtx) : VLCtx :=
  insertLambda insertedThree (insertLambda insertedTwo (insertLambda insertedOne context))

private theorem mixedLambdaLetContextsAgreeByBetaRatherThanLiteralEquality
    (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes originalContext sourceContext := by
  apply VLCtx.IsDefEq.cons
  · apply VLCtx.IsDefEq.cons
    · apply VLCtx.IsDefEq.cons
      · exact .nil
      · rintro identifier dependencies equality
        cases equality
        simp [VLCtx.fvars]
      · exact .vlam (.sortDF (by trivial) (by trivial) rfl)
    · rintro identifier dependencies equality
      cases equality
      simp [VLCtx.fvars, carrier, element]
    · exact .vlam (.bvar .zero)
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars, carrier, element, aliasIdentifier]
  · exact .vlet (.beta (.bvar .zero) (.bvar .zero)) (.bvar (.succ .zero))

private theorem insertingTheSameFreshLambdaPreservesTypedContextAgreement
    {env : VEnv} {universes : Nat} {original aligned : VLCtx}
    (contexts : VLCtx.IsDefEq env universes original aligned)
    (identifier : FVarId) (fresh : identifier ∉ original.fvars) :
    VLCtx.IsDefEq env universes (insertLambda identifier original) (insertLambda identifier aligned) := by
  apply VLCtx.IsDefEq.cons contexts
  · rintro selected dependencies equality
    cases equality
    exact ⟨fresh, by simp⟩
  · exact .vlam (.sortDF (by trivial) (by trivial) rfl)

private theorem oneInsertedLambdaPreservesTheNonLiteralAgreement
    (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertLambda insertedOne originalContext)
      (insertLambda insertedOne sourceContext) :=
  insertingTheSameFreshLambdaPreservesTypedContextAgreement
    (mixedLambdaLetContextsAgreeByBetaRatherThanLiteralEquality env universes) insertedOne (by decide)

private theorem threeInsertedLambdasPreserveTheNonLiteralAgreement
    (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes (insertThreeLambdas originalContext)
      (insertThreeLambdas sourceContext) := by
  apply insertingTheSameFreshLambdaPreservesTypedContextAgreement
  · apply insertingTheSameFreshLambdaPreservesTypedContextAgreement
    · exact oneInsertedLambdaPreservesTheNonLiteralAgreement env universes
    · decide
  · decide

private theorem oneInsertedLambdaWeakensTheRetainedBase :
    VLCtx.FVLift' sourceContext (insertLambda insertedOne sourceContext) 0 (.skip .refl) 0 :=
  .skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl

private theorem threeInsertedLambdasWeakenTheRetainedBase :
    VLCtx.FVLift' sourceContext (insertThreeLambdas sourceContext) 0 (.skipN .refl 3) 0 :=
  .skip_fvar (insertedThree, []) (.vlam (.sort .zero))
    (.skip_fvar (insertedTwo, []) (.vlam (.sort .zero))
      (.skip_fvar (insertedOne, []) (.vlam (.sort .zero)) .refl))

private theorem orderedDuplicatePrefixRetainsItsRequestedPositions :
    [carrier, element, carrier, aliasIdentifier] ⊆ sourceContext.fvars ∧
      [carrier, element, carrier, aliasIdentifier][0]? = some carrier ∧
      [carrier, element, carrier, aliasIdentifier][1]? = some element ∧
      [carrier, element, carrier, aliasIdentifier][2]? = some carrier ∧
      [carrier, element, carrier, aliasIdentifier][3]? = some aliasIdentifier := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro identifier member
  simp [sourceContext, VLCtx.fvars] at member ⊢
  grind

private theorem concreteOneBinderAgreementTypesEveryRetainedParameter
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RetainedFVarPrefixAgreement env universes sourceContext
      (insertLambda insertedOne originalContext) (insertLambda insertedOne sourceContext)
      (.skip .refl) [carrier, element, carrier, aliasIdentifier] := by
  have originalContexts := mixedLambdaLetContextsAgreeByBetaRatherThanLiteralEquality env universes.length
  have insertedContexts := oneInsertedLambdaPreservesTheNonLiteralAgreement env universes.length
  have sourceWF := (originalContexts.symm envWF.ordered).wf
  have alignedWF := (insertedContexts.symm envWF.ordered).wf
  exact (oneInsertedLambdaWeakensTheRetainedBase.retainedPrefix envWF sourceWF alignedWF
    orderedDuplicatePrefixRetainsItsRequestedPositions.1).agreesWithOriginal envWF insertedContexts

private theorem concreteThreeBinderAgreementTypesEveryRetainedParameter
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RetainedFVarPrefixAgreement env universes sourceContext
      (insertThreeLambdas originalContext) (insertThreeLambdas sourceContext)
      (.skipN .refl 3) [carrier, element, carrier, aliasIdentifier] := by
  have originalContexts := mixedLambdaLetContextsAgreeByBetaRatherThanLiteralEquality env universes.length
  have insertedContexts := threeInsertedLambdasPreserveTheNonLiteralAgreement env universes.length
  have sourceWF := (originalContexts.symm envWF.ordered).wf
  have alignedWF := (insertedContexts.symm envWF.ordered).wf
  exact (threeInsertedLambdasWeakenTheRetainedBase.retainedPrefix envWF sourceWF alignedWF
    orderedDuplicatePrefixRetainsItsRequestedPositions.1).agreesWithOriginal envWF insertedContexts

private theorem originalLetLookupIsNotItsAlignedSemanticExpression :
    originalContext.find? (.inr aliasIdentifier) = some (betaValue, .bvar 1) ∧
      sourceContext.find? (.inr aliasIdentifier) = some (.bvar 0, .bvar 1) ∧
      betaValue ≠ .bvar 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem oneBinderOriginalLookupIsNotTheLiftedSourceValue :
    (insertLambda insertedOne originalContext).find? (.inr aliasIdentifier) =
      some (betaValue.lift' (.skip .refl), .bvar 2) ∧
      betaValue.lift' (.skip .refl) ≠ (VExpr.bvar 0).lift' (.skip .refl) := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private theorem threeBinderOriginalLookupIsNotTheLiftedSourceValue :
    (insertThreeLambdas originalContext).find? (.inr aliasIdentifier) =
      some (betaValue.lift' (.skipN .refl 3), .bvar 4) ∧
      betaValue.lift' (.skipN .refl 3) ≠ (VExpr.bvar 0).lift' (.skipN .refl 3) := by
  refine ⟨rfl, ?_⟩
  intro equality
  cases equality

private theorem removingTheOriginalContextLosesTheParameter :
    VLCtx.find? [] (.inr aliasIdentifier) = none ∧
      aliasIdentifier ∉ VLCtx.fvars [] := ⟨rfl, by simp⟩

private def originalUniverse : VLevel := .max (.succ .zero) .zero

private def originalUniverseContext : VLCtx :=
  [(some (carrier, []), .vlam (.sort originalUniverse))]

private def alignedUniverseContext : VLCtx :=
  [(some (carrier, []), .vlam (.sort (.succ .zero)))]

private theorem equivalentUniversesSupplyNonLiteralTypedContextAgreement
    (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes originalUniverseContext alignedUniverseContext := by
  apply VLCtx.IsDefEq.cons .nil
  · rintro identifier dependencies equality
    cases equality
    simp [VLCtx.fvars]
  · apply VLocalDecl.IsDefEq.vlam
    apply VEnv.IsDefEq.sortDF (by trivial) (by trivial)
    simp [VLevel.equiv_def, VLevel.eval, originalUniverse]

private theorem equivalentUniverseLookupTypesAreNotLiteralExpressions :
    originalUniverseContext.find? (.inr carrier) = some (.bvar 0, .sort originalUniverse) ∧
      alignedUniverseContext.find? (.inr carrier) = some (.bvar 0, .sort (.succ .zero)) ∧
      (VExpr.sort originalUniverse) ≠ .sort (.succ .zero) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  cases equality

private theorem equivalentUniversesProduceSortCorrectRetainedTypeAgreement
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RetainedFVarPrefixAgreement env universes alignedUniverseContext originalUniverseContext
      alignedUniverseContext .refl [carrier] := by
  have contexts := equivalentUniversesSupplyNonLiteralTypedContextAgreement env universes.length
  have alignedWF := (contexts.symm envWF.ordered).wf
  have retained : [carrier] ⊆ alignedUniverseContext.fvars := by simp [alignedUniverseContext]
  exact ((VLCtx.FVLift'.refl (Δ := alignedUniverseContext)).retainedPrefix envWF alignedWF
    alignedWF retained).agreesWithOriginal envWF contexts

private def selectedIdentifier : FVarId := ⟨`PrefixAgreementSelected⟩

private def selectedSource : VLCtx :=
  (some (selectedIdentifier, [carrier]), .vlam (.bvar 1)) :: sourceContext

private def selectedOriginal : VLCtx :=
  (some (selectedIdentifier, [carrier]), .vlam (.bvar 2)) :: insertLambda insertedOne originalContext

private def selectedAligned : VLCtx :=
  (some (selectedIdentifier, [carrier]), .vlam (.bvar 2)) :: insertLambda insertedOne sourceContext

private theorem selectedEndpointsAgreeAboveTheInsertedBetaContext
    (env : VEnv) (universes : Nat) :
    VLCtx.IsDefEq env universes selectedOriginal selectedAligned := by
  apply VLCtx.IsDefEq.cons (oneInsertedLambdaPreservesTheNonLiteralAgreement env universes)
  · rintro identifier dependencies equality
    cases equality
    simp [insertLambda, originalContext, VLCtx.fvars, selectedIdentifier, carrier,
      element, aliasIdentifier, insertedOne]
  · exact .vlam (.bvar (.succ (.succ .zero)))

private theorem selectedEndpointWeakeningRetainsTheEarlierBinderCutoff :
    VLCtx.FVLift' selectedSource selectedAligned 0 (.consN (.skip .refl) 1) 0 :=
  .cons_fvar (selectedIdentifier, [carrier]) (.vlam (.bvar 1))
    (by simp [sourceContext, VLCtx.fvars]) oneInsertedLambdaWeakensTheRetainedBase

private theorem selectedEndpointAgreementTypesItsOrderedRetainedPrefix
    {env : VEnv} {universes : List Name} (envWF : env.WF) :
    RetainedFVarPrefixAgreement env universes selectedSource selectedOriginal selectedAligned
      (.consN (.skip .refl) 1) [carrier, element, carrier, aliasIdentifier] := by
  have contexts := selectedEndpointsAgreeAboveTheInsertedBetaContext env universes.length
  have alignedWF := (contexts.symm envWF.ordered).wf
  have weakening := selectedEndpointWeakeningRetainsTheEarlierBinderCutoff
  have sourceWF := weakening.wf envWF alignedWF
  have retained : [carrier, element, carrier, aliasIdentifier] ⊆ selectedSource.fvars := by
    intro identifier member
    exact List.mem_cons_of_mem selectedIdentifier
      (orderedDuplicatePrefixRetainsItsRequestedPositions.1 member)
  exact (weakening.retainedPrefix envWF sourceWF alignedWF retained).agreesWithOriginal envWF contexts

private theorem selectedEndpointLiftIsNotIdentityOrCutoffZero :
    (VExpr.bvar 0).lift' (.consN (.skip .refl) 1) = .bvar 0 ∧
      (VExpr.bvar 1).lift' (.consN (.skip .refl) 1) = .bvar 2 ∧
      (VExpr.bvar 0).lift' (.consN (.skip .refl) 1) ≠ (VExpr.bvar 0).lift' (.skip .refl) ∧
      (VExpr.bvar 1).lift' (.consN (.skip .refl) 1) ≠ (VExpr.bvar 1) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private def variablePositions : VExpr → List Nat
  | .bvar position => [position]
  | .sort _ | .const _ _ => []
  | .app function argument | .lam function argument | .forallE function argument =>
      variablePositions function ++ variablePositions argument

private def checkLookup (context : VLCtx) (identifier : FVarId)
    (semanticPositions typePositions : List Nat) : MetaM Unit := do
  let some (semantic, type) := context.find? (.inr identifier)
    | throwError "parameter-agreement retained lookup absent: {identifier.name}"
  unless variablePositions semantic == semanticPositions && variablePositions type == typePositions do
    throwError "parameter-agreement semantic/type positions changed: {identifier.name}"

private def runtimeFixtures : MetaM Unit := do
  for (inserted, original, aligned) in
      [(0, originalContext, sourceContext),
        (1, insertLambda insertedOne originalContext, insertLambda insertedOne sourceContext),
        (3, insertThreeLambdas originalContext, insertThreeLambdas sourceContext)] do
    for context in [original, aligned] do
      checkLookup context carrier [inserted + 1] []
      checkLookup context element [inserted] [inserted + 1]
      unless context.toCtx.length == sourceContext.toCtx.length + inserted do
        throwError "parameter-agreement counted a retained vlet as a semantic binder"
    checkLookup original aliasIdentifier [inserted + 1, 0, inserted] [inserted + 1]
    checkLookup aligned aliasIdentifier [inserted] [inserted + 1]
    unless original.fvars == aligned.fvars do
      throwError "parameter-agreement original/aligned identifier correspondence changed"
  checkLookup selectedSource carrier [2] []
  checkLookup selectedSource element [1] [2]
  checkLookup selectedSource aliasIdentifier [1] [2]
  checkLookup selectedSource selectedIdentifier [0] [2]
  for context in [selectedOriginal, selectedAligned] do
    checkLookup context carrier [3] []
    checkLookup context element [2] [3]
    checkLookup context selectedIdentifier [0] [3]
  checkLookup selectedOriginal aliasIdentifier [3, 0, 2] [3]
  checkLookup selectedAligned aliasIdentifier [2] [3]
  logInfo "parameter-agreement runtime: 30 exact lookup checks; dependent lambda/let base; zero, one, three inserted binders; nonliteral original beta values; selected endpoint consN cutoff preserves its own bound variable"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-agreement audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "parameter-agreement unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterPrefixAgreement
    | throwError "parameter-agreement module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-agreement new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"parameter-agreement bridge: {declarations} declarations including private/generated helpers audited"

private def auditFoundations (logical : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some lookupModule := environment.getModuleIdx? `Lean4Lean.Verify.Typing.Lemmas
    | throwError "parameter-agreement lookup foundations module absent"
  for name in [``VLCtx.IsDefEq.find?_uniq, ``VLCtx.IsDefEq.wf, ``VLCtx.IsDefEq.fvars,
      ``VLCtx.WF.find?_wf] do
    unless environment.getModuleIdxFor? name == some lookupModule do
      throwError "parameter-agreement inherited lookup foundation provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  for (name, moduleName) in
      [(``VEnv.IsDefEq.isType, `Lean4Lean.Theory.Typing.Lemmas),
        (``VEnv.IsDefEqU.of_l, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "parameter-agreement typed equality foundation module absent: {moduleName}"
    unless environment.getModuleIdxFor? name == some moduleIndex do
      throwError "parameter-agreement typed equality foundation provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  let some translationModule := environment.getModuleIdx? `Lean4Lean.Verify.Typing.Expr
    | throwError "parameter-agreement inherited translation foundations module absent"
  unless environment.getModuleIdxFor? ``TrProj == some translationModule &&
      (← collectAxioms ``TrProj).contains ``sorryAx do
    throwError "parameter-agreement inherited translation admission provenance changed"
  auditDeclaration ``TrProj (logical ++ [``sorryAx])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "parameter-agreement forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"parameter-agreement unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  for name in [``transportedPrefixAgreesWithItsOriginalTypedContext,
      ``originalLookupProjectsTypedValueAndSortCorrectTypeAgreement,
      ``agreementRetainsTheDistinctAlignedTransportReceipt,
      ``missingOriginalParameterCannotSupplyAgreement, ``missingAlignedParameterCannotSupplyAgreement,
      ``duplicatePositionsRemainSeparateLookupRequests,
      ``concreteOneBinderAgreementTypesEveryRetainedParameter,
      ``concreteThreeBinderAgreementTypesEveryRetainedParameter,
      ``equivalentUniversesProduceSortCorrectRetainedTypeAgreement,
      ``selectedEndpointAgreementTypesItsOrderedRetainedPrefix] do
    auditDeclaration name inherited
  for name in [``carrier, ``element, ``aliasIdentifier, ``insertedOne, ``insertedTwo, ``insertedThree,
      ``betaValue, ``sourceContext, ``originalContext, ``insertLambda, ``insertThreeLambdas,
      ``mixedLambdaLetContextsAgreeByBetaRatherThanLiteralEquality,
      ``insertingTheSameFreshLambdaPreservesTypedContextAgreement,
      ``oneInsertedLambdaPreservesTheNonLiteralAgreement,
      ``threeInsertedLambdasPreserveTheNonLiteralAgreement,
      ``oneInsertedLambdaWeakensTheRetainedBase, ``threeInsertedLambdasWeakenTheRetainedBase,
      ``orderedDuplicatePrefixRetainsItsRequestedPositions,
      ``originalLetLookupIsNotItsAlignedSemanticExpression,
      ``oneBinderOriginalLookupIsNotTheLiftedSourceValue,
      ``threeBinderOriginalLookupIsNotTheLiftedSourceValue,
      ``removingTheOriginalContextLosesTheParameter,
      ``originalUniverse, ``originalUniverseContext, ``alignedUniverseContext,
      ``equivalentUniversesSupplyNonLiteralTypedContextAgreement,
      ``equivalentUniverseLookupTypesAreNotLiteralExpressions,
      ``selectedIdentifier, ``selectedSource, ``selectedOriginal, ``selectedAligned,
      ``selectedEndpointsAgreeAboveTheInsertedBetaContext,
      ``selectedEndpointWeakeningRetainsTheEarlierBinderCutoff,
      ``selectedEndpointLiftIsNotIdentityOrCutoffZero, ``variablePositions, ``checkLookup,
      ``runtimeFixtures, ``auditDeclaration, ``auditModule, ``auditFoundations,
      ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule inherited
  auditFoundations logical
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures
  logInfo "parameter-prefix agreement: typed original/aligned correspondence at each supplied list position; sort-correct type agreement and value agreement in the original context; beta-redex values and equivalent nonliteral universe types; ordered duplicate positions; missing originals rejected; no literal context/value equality claim"

end InductiveParameterPrefixAgreementTest
