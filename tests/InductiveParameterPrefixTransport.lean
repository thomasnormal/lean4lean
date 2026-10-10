import Lean4Lean.Verify.InductiveParameterPrefixTransport
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveParameterPrefixTransportTest

private theorem retainedPrefixHasPositionwiseTypedLookupReceipts
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (weakening : VLCtx.FVLift' source target 0 lift 0)
    (envWF : env.WF) (sourceWF : source.WF env universes.length)
    (targetWF : target.WF env universes.length) (retained : identifiers ⊆ source.fvars) :
    RetainedFVarPrefix env universes source target lift identifiers :=
  weakening.retainedPrefix envWF sourceWF targetWF retained

private theorem retainedPrefixLookupProjectsBothTypedTranslations
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefix env universes source target lift identifiers)
    (position : Nat) (identifier : FVarId)
    (selected : identifiers[position]? = some identifier) :
    ∃ semantic type,
      source.find? (.inr identifier) = some (semantic, type) ∧
      TrExprS env universes source (.fvar identifier) semantic ∧
      env.HasType universes.length source.toCtx semantic type ∧
      target.find? (.inr identifier) = some (semantic.lift' lift, type.lift' lift) ∧
      TrExprS env universes target (.fvar identifier) (semantic.lift' lift) ∧
      env.HasType universes.length target.toCtx (semantic.lift' lift) (type.lift' lift) :=
  receipt.lookups position identifier selected

private theorem retainedPrefixKeepsDuplicatePositionsWithoutClaimingDistinctness
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (weakening : VLCtx.FVLift' source target 0 lift 0)
    (envWF : env.WF) (sourceWF : source.WF env universes.length)
    (targetWF : target.WF env universes.length) (retained : identifier ∈ source.fvars) :
    RetainedFVarPrefix env universes source target lift [identifier, identifier] := by
  apply weakening.retainedPrefix envWF sourceWF targetWF
  intro selected member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  exact member ▸ retained

private theorem duplicatePrefixPositionsSelectTheSameIdentifier (identifier : FVarId) :
    [identifier, identifier][0]? = some identifier ∧
      [identifier, identifier][1]? = some identifier := ⟨rfl, rfl⟩

private theorem removedSourceParameterCannotSupplyRetainedPrefix
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (missing : identifier ∉ source.fvars) :
    ¬ RetainedFVarPrefix env universes source target lift [identifier] := by
  intro receipt
  exact missing (receipt.sourceRetained (by simp))

private theorem absentTargetParameterCannotSupplyRetainedPrefix
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifier : FVarId}
    (missing : identifier ∉ target.fvars) :
    ¬ RetainedFVarPrefix env universes source target lift [identifier] := by
  intro receipt
  exact missing (receipt.targetRetained (by simp))

private def collidingContext (identifier : FVarId) : VLCtx :=
  [(some (identifier, []), .vlam (.sort .zero)),
    (some (identifier, []), .vlam (.sort .zero))]

private theorem largerParameterCollisionCannotSupplyWellFormedness
    (env : VEnv) (universes : Nat) (identifier : FVarId) :
    ¬ (collidingContext identifier).WF env universes := by
  intro wellFormed
  have fresh := (wellFormed.2.1 identifier [] rfl).1
  apply fresh
  simp [VLCtx.fvars]

private theorem collisionStillAdmitsOnlyAStructuralWeakening (identifier : FVarId) :
    VLCtx.FVLift' [(some (identifier, []), .vlam (.sort .zero))]
      (collidingContext identifier) 0 (.skip .refl) 0 :=
  .skip_fvar (identifier, []) (.vlam (.sort .zero)) .refl

private def carrier : FVarId := ⟨`PrefixTransportCarrier⟩
private def element : FVarId := ⟨`PrefixTransportElement⟩
private def aliasIdentifier : FVarId := ⟨`PrefixTransportAlias⟩

private def sourceContext : VLCtx :=
  [(some (aliasIdentifier, [carrier, element]), .vlet (.bvar 1) (.bvar 0)),
    (some (element, [carrier]), .vlam (.bvar 0)),
    (some (carrier, []), .vlam (.sort (.succ .zero)))]

private def insertLambdas : Nat → VLCtx → VLCtx
  | 0, context => context
  | count + 1, context =>
    (some (⟨Name.num `PrefixTransportInserted count⟩, []), .vlam (.sort .zero)) ::
      insertLambdas count context

private def insertLet (context : VLCtx) : VLCtx :=
  (some (⟨`PrefixTransportInsertedLet⟩, []), .vlet (.sort (.succ .zero)) (.sort .zero)) :: context

private theorem insertedLambdasProduceTheExpectedWeakening (inserted : Nat) :
    VLCtx.FVLift' sourceContext (insertLambdas inserted sourceContext)
      0 (.skipN .refl inserted) 0 := by
  induction inserted with
  | zero => exact .refl
  | succ count previous =>
    exact .skip_fvar (⟨Name.num `PrefixTransportInserted count⟩, [])
      (.vlam (.sort .zero)) previous

private theorem insertedVletProducesIdentitySemanticWeakening (context : VLCtx) :
    VLCtx.FVLift' context (insertLet context) 0 .refl 0 :=
  .skip_fvar (⟨`PrefixTransportInsertedLet⟩, []) (.vlet (.sort (.succ .zero)) (.sort .zero)) .refl

private def selectedIdentifier : FVarId := ⟨`PrefixTransportSelected⟩

private def selectedContext : VLCtx :=
  (some (selectedIdentifier, [carrier]), .vlam (.bvar 1)) :: sourceContext

private def selectedTarget (inserted : Nat) : VLCtx :=
  (some (selectedIdentifier, [carrier]), .vlam ((VExpr.bvar 1).lift' (.skipN .refl inserted))) ::
    insertLambdas inserted sourceContext

private theorem selectedEndpointWeakeningRetainsTheEarlierBinderCutoff (inserted : Nat) :
    VLCtx.FVLift' selectedContext (selectedTarget inserted)
      0 (.consN (.skipN .refl inserted) 1) 0 := by
  apply VLCtx.FVLift'.cons_fvar (selectedIdentifier, [carrier]) (.vlam (.bvar 1))
  · intro identifier member
    simp only [List.mem_singleton] at member
    subst identifier
    simp [sourceContext, VLCtx.fvars]
  · exact insertedLambdasProduceTheExpectedWeakening inserted

private theorem selectedEndpointOneBinderLookupLiftsOnlyBaseReferences :
    (selectedTarget 1).find? (.inr selectedIdentifier) = some (.bvar 0, .bvar 3) ∧
      (selectedTarget 1).find? (.inr carrier) = some (.bvar 3, .sort (.succ .zero)) ∧
      (selectedTarget 1).find? (.inr aliasIdentifier) = some (.bvar 2, .bvar 3) :=
  ⟨rfl, rfl, rfl⟩

private theorem selectedEndpointThreeBinderLookupLiftsOnlyBaseReferences :
    (selectedTarget 3).find? (.inr selectedIdentifier) = some (.bvar 0, .bvar 5) ∧
      (selectedTarget 3).find? (.inr carrier) = some (.bvar 5, .sort (.succ .zero)) ∧
      (selectedTarget 3).find? (.inr aliasIdentifier) = some (.bvar 4, .bvar 5) :=
  ⟨rfl, rfl, rfl⟩

private theorem selectedEndpointLiftIsNeitherIdentityNorCutoffZero :
    (VExpr.app (.bvar 0) (.bvar 1)).lift' (.consN (.skipN .refl 3) 1) =
        .app (.bvar 0) (.bvar 4) ∧
      (VExpr.app (.bvar 0) (.bvar 1)).lift' (.consN (.skipN .refl 3) 1) ≠
        .app (.bvar 0) (.bvar 1) ∧
      (VExpr.app (.bvar 0) (.bvar 1)).lift' (.consN (.skipN .refl 3) 1) ≠
        (VExpr.app (.bvar 0) (.bvar 1)).lift' (.skipN .refl 3) := by
  refine ⟨rfl, ?_, ?_⟩ <;> intro equality <;> cases equality

private theorem omittedParameterLookupIsAbsent :
    (VLCtx.find? [] (.inr carrier)) = none := rfl

private theorem wrongPrefixPositionsCannotSelectTheRequestedParameter :
    [carrier, element, aliasIdentifier][3]? = none ∧
      [carrier, element, aliasIdentifier][0]? ≠ some element := by
  refine ⟨rfl, ?_⟩
  intro equality
  have names := congrArg FVarId.name (Option.some.inj equality)
  simp [carrier, element] at names

private theorem dependentVlamLookupLiftsItsDomainInItsOwnContext :
    sourceContext.find? (.inr element) = some (.bvar 0, .bvar 1) := rfl

private theorem dependentVletLookupAddsNoSemanticDepth :
    sourceContext.find? (.inr aliasIdentifier) = some (.bvar 0, .bvar 1) ∧
      sourceContext.find? (.inr carrier) = some (.bvar 1, .sort (.succ .zero)) := ⟨rfl, rfl⟩

private theorem insertingAVletKeepsParameterLookupsUnshifted :
    (insertLet sourceContext).find? (.inr carrier) = some (.bvar 1, .sort (.succ .zero)) ∧
      (insertLet sourceContext).find? (.inr element) = some (.bvar 0, .bvar 1) ∧
      (insertLet sourceContext).find? (.inr aliasIdentifier) = some (.bvar 0, .bvar 1) :=
  ⟨rfl, rfl, rfl⟩

private theorem insertingOneBinderGenuinelyLiftsDependentParameters :
    (insertLambdas 1 sourceContext).find? (.inr carrier) = some (.bvar 2, .sort (.succ .zero)) ∧
      (insertLambdas 1 sourceContext).find? (.inr element) = some (.bvar 1, .bvar 2) ∧
      (insertLambdas 1 sourceContext).find? (.inr aliasIdentifier) = some (.bvar 1, .bvar 2) :=
  ⟨rfl, rfl, rfl⟩

private theorem insertingThreeBindersGenuinelyLiftsDependentParameters :
    (insertLambdas 3 sourceContext).find? (.inr carrier) = some (.bvar 4, .sort (.succ .zero)) ∧
      (insertLambdas 3 sourceContext).find? (.inr element) = some (.bvar 3, .bvar 4) ∧
      (insertLambdas 3 sourceContext).find? (.inr aliasIdentifier) = some (.bvar 3, .bvar 4) :=
  ⟨rfl, rfl, rfl⟩

private theorem liftedParameterIsNotTheOldSemanticExpression :
    (VExpr.bvar 0).lift' (.skip .refl) ≠ .bvar 0 ∧
      (VExpr.bvar 1).lift' (.skipN .refl 3) ≠ .bvar 1 := by
  constructor <;> intro equality <;> cases equality

private theorem retainedSourceSupportsItsRequestedDuplicatePrefix :
    [carrier, element, carrier, aliasIdentifier] ⊆ sourceContext.fvars := by
  intro identifier member
  simp [sourceContext, VLCtx.fvars] at member ⊢
  grind

private def variablePositions : VExpr → List Nat
  | .bvar position => [position]
  | .sort _ | .const _ _ => []
  | .app function argument | .lam function argument | .forallE function argument =>
      variablePositions function ++ variablePositions argument

private def checkLookup (context : VLCtx) (identifier : FVarId)
    (semanticPositions typePositions : List Nat) : MetaM Unit := do
  let some (semantic, type) := context.find? (.inr identifier)
    | throwError "parameter-prefix retained lookup absent: {identifier.name}"
  unless variablePositions semantic == semanticPositions && variablePositions type == typePositions do
    throwError "parameter-prefix semantic/type lift changed: {identifier.name}"

private def runtimeFixtures : MetaM Unit := do
  for inserted in [0, 1, 3] do
    let target := insertLambdas inserted sourceContext
    for context in [target, insertLet target] do
      checkLookup context carrier [inserted + 1] []
      checkLookup context element [inserted] [inserted + 1]
      checkLookup context aliasIdentifier [inserted] [inserted + 1]
      unless context.toCtx.length == sourceContext.toCtx.length + inserted do
        throwError "parameter-prefix counted a vlet as a semantic binder"
    unless (insertLet target).fvars.contains carrier && target.fvars.contains aliasIdentifier do
      throwError "parameter-prefix insertion removed a retained identifier"
    let endpoint := selectedTarget inserted
    checkLookup endpoint selectedIdentifier [0] [inserted + 2]
    checkLookup endpoint carrier [inserted + 2] []
    checkLookup endpoint element [inserted + 1] [inserted + 2]
    checkLookup endpoint aliasIdentifier [inserted + 1] [inserted + 2]
  logInfo "parameter-prefix runtime: 30 exact retained/selected lookup position checks; dependent vlam/vlet parameters; zero, one, three inserted binders; extra vlet adds no semantic depth; selected endpoint cutoff protects its own bound variable"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "parameter-prefix audited declaration absent: {name}"
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "parameter-prefix unexpected or forbidden axiom {axiomName} in {name}"

private def auditModule (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveParameterPrefixTransport
    | throwError "parameter-prefix bridge module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "parameter-prefix new module-owned axiom {name}"
      auditDeclaration name allowed
      declarations := declarations + 1
  logInfo m!"parameter-prefix bridge: {declarations} declarations including private/generated helpers audited"

private def auditFoundations (logical : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.Typing.Lemmas
    | throwError "parameter-prefix lookup foundations module absent"
  for name in [``VLCtx.FVLift'.find?, ``VLCtx.WF.find?_wf] do
    unless environment.getModuleIdxFor? name == some moduleIndex do
      throwError "parameter-prefix inherited lookup foundation provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
  let some translationModule := environment.getModuleIdx? `Lean4Lean.Verify.Typing.Expr
    | throwError "parameter-prefix inherited translation foundations module absent"
  unless environment.getModuleIdxFor? ``TrProj == some translationModule &&
      (← collectAxioms ``TrProj).contains ``sorryAx do
    throwError "parameter-prefix inherited translation admission provenance changed"
  auditDeclaration ``TrProj (logical ++ [``sorryAx])

private def forbiddenRangeStillFailsWhenWhitelisted (logical : List Name) : MetaM Unit := do
  let failure ← try
    auditDeclaration ``Expr.looseBVarRange_eq (logical ++ [``Expr.looseBVarRange_eq])
    pure none
  catch exception => pure (some exception)
  let some exception := failure | throwError "parameter-prefix forbidden range audit unexpectedly succeeded"
  match exception with
  | .error _ message =>
    let expected := m!"parameter-prefix unexpected or forbidden axiom {``Expr.looseBVarRange_eq} in {``Expr.looseBVarRange_eq}"
    unless (← message.toString) == (← expected.toString) do throw exception
  | .internal .. => throw exception

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  for name in [``retainedPrefixHasPositionwiseTypedLookupReceipts,
      ``retainedPrefixLookupProjectsBothTypedTranslations,
      ``retainedPrefixKeepsDuplicatePositionsWithoutClaimingDistinctness,
      ``removedSourceParameterCannotSupplyRetainedPrefix,
      ``absentTargetParameterCannotSupplyRetainedPrefix] do
    auditDeclaration name inherited
  for name in [``duplicatePrefixPositionsSelectTheSameIdentifier,
      ``collidingContext,
      ``largerParameterCollisionCannotSupplyWellFormedness,
      ``collisionStillAdmitsOnlyAStructuralWeakening, ``carrier, ``element, ``aliasIdentifier,
      ``sourceContext, ``insertLambdas, ``insertLet,
      ``insertedLambdasProduceTheExpectedWeakening,
      ``insertedVletProducesIdentitySemanticWeakening, ``selectedIdentifier,
      ``selectedContext, ``selectedTarget,
      ``selectedEndpointWeakeningRetainsTheEarlierBinderCutoff,
      ``selectedEndpointOneBinderLookupLiftsOnlyBaseReferences,
      ``selectedEndpointThreeBinderLookupLiftsOnlyBaseReferences,
      ``selectedEndpointLiftIsNeitherIdentityNorCutoffZero,
      ``omittedParameterLookupIsAbsent,
      ``wrongPrefixPositionsCannotSelectTheRequestedParameter,
      ``dependentVlamLookupLiftsItsDomainInItsOwnContext,
      ``dependentVletLookupAddsNoSemanticDepth,
      ``insertingAVletKeepsParameterLookupsUnshifted,
      ``insertingOneBinderGenuinelyLiftsDependentParameters,
      ``insertingThreeBindersGenuinelyLiftsDependentParameters,
      ``liftedParameterIsNotTheOldSemanticExpression,
      ``retainedSourceSupportsItsRequestedDuplicatePrefix, ``variablePositions, ``checkLookup,
      ``runtimeFixtures, ``auditDeclaration, ``auditModule, ``auditFoundations,
      ``forbiddenRangeStillFailsWhenWhitelisted] do
    auditDeclaration name logical
  auditModule inherited
  auditFoundations logical
  forbiddenRangeStillFailsWhenWhitelisted logical
  runtimeFixtures
  logInfo "parameter-prefix transport: supplied retained IDs receive positionwise translation/typehood after weakening; duplicate positions do not imply header validity; dropped source parameters and target collisions are rejected; no accepted header or collision discharge claim"

end InductiveParameterPrefixTransportTest
