import Lean4Lean.Verify.TypeChecker.WHNF
import Lean.Util.CollectAxioms

namespace QuotientEliminatorInversionTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

section
variable {environment : VEnv} {locals : List VExpr} {universes : Nat}
  {levels : List VLevel} {domain relation target function respect major resultType : VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (registered : environment.constants ``Quot.lift = some quotLiftConst)
  (typed : environment.HasType universes locals
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
      domain) relation) target) function) respect) major) resultType)

example : ∃ sourceUniverse targetUniverse,
    levels = [sourceUniverse, targetUniverse] ∧
    sourceUniverse.WF universes ∧ targetUniverse.WF universes ∧
    environment.HasType universes locals domain (.sort sourceUniverse) ∧
    environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))) ∧
    environment.HasType universes locals target (.sort targetUniverse) ∧
    environment.HasType universes locals function (.forallE domain target.lift) ∧
    environment.HasType universes locals respect
      (.forallE domain (.forallE domain.lift
        (.forallE (.app (.app (relation.liftN 2) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const ``Eq [targetUniverse]) (target.liftN 3))
            (.app (function.liftN 3) (.bvar 2))) (.app (function.liftN 3) (.bvar 1)))))) ∧
    environment.HasType universes locals major
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) ∧
    environment.IsDefEqU universes locals resultType target :=
  VEnv.quotLift_inv environmentWF localsWF registered typed

example (wrongArity : levels.length ≠ 2) : False := by
  obtain ⟨sourceUniverse, targetUniverse, rfl, _⟩ :=
    VEnv.quotLift_inv environmentWF localsWF registered typed
  exact wrongArity rfl

end

section
variable {environment : VEnv} {locals : List VExpr} {universes : Nat}
  {levels : List VLevel} {domain relation motive minor major resultType : VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (registered : environment.constants ``Quot.ind = some quotIndConst)
  (typed : environment.HasType universes locals
    (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
      domain) relation) motive) minor) major) resultType)

example : ∃ sourceUniverse, levels = [sourceUniverse] ∧ sourceUniverse.WF universes ∧
    environment.HasType universes locals domain (.sort sourceUniverse) ∧
    environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))) ∧
    environment.HasType universes locals motive
      (.forallE (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.sort .zero)) ∧
    environment.HasType universes locals minor
      (.forallE domain (.app motive.lift
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain.lift)
          relation.lift) (.bvar 0)))) ∧
    environment.HasType universes locals major
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) ∧
    environment.IsDefEqU universes locals resultType (.app motive major) :=
  VEnv.quotInd_inv environmentWF localsWF registered typed

example (wrongArity : levels.length ≠ 1) : False := by
  obtain ⟨sourceUniverse, rfl, _⟩ := VEnv.quotInd_inv environmentWF localsWF registered typed
  exact wrongArity rfl

end

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse targetUniverse : VLevel} {domain relation target function respect value : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (liftRegistered : environment.constants ``Quot.lift = some quotLiftConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (targetUniverseWF : targetUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (targetTyped : environment.HasType universes locals target (.sort targetUniverse))
    (functionTyped : environment.HasType universes locals function (.forallE domain target.lift))
    (respectTyped : environment.HasType universes locals respect
      (.forallE domain (.forallE domain.lift
        (.forallE (.app (.app (relation.liftN 2) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const ``Eq [targetUniverse]) (target.liftN 3))
            (.app (function.liftN 3) (.bvar 2))) (.app (function.liftN 3) (.bvar 1)))))))
    (valueTyped : environment.HasType universes locals value domain) :
    environment.HasType universes locals
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  have reduction := VEnv.quotLift_beta environmentWF localsWF registered
    sourceUniverseWF targetUniverseWF domainTyped relationTyped targetTyped
    functionTyped respectTyped valueTyped
  obtain ⟨recoveredSource, recoveredTarget, levelsEqual, _, _, _, _, _, _, _, majorTyped, _⟩ :=
    VEnv.quotLift_inv environmentWF localsWF liftRegistered reduction.hasType.1
  cases levelsEqual
  exact majorTyped

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse : VLevel} {domain relation motive minor value : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (constructorRegistered : environment.constants ``Quot.mk = some quotMkConst)
    (inductionRegistered : environment.constants ``Quot.ind = some quotIndConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (motiveTyped : environment.HasType universes locals motive
      (.forallE (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.sort .zero)))
    (minorTyped : environment.HasType universes locals minor
      (.forallE domain (.app motive.lift
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain.lift)
          relation.lift) (.bvar 0)))))
    (valueTyped : environment.HasType universes locals value domain) :
    environment.HasType universes locals
      (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  have reduction := VEnv.quotInd_beta constructorRegistered inductionRegistered sourceUniverseWF
    domainTyped relationTyped motiveTyped minorTyped valueTyped
  obtain ⟨recoveredSource, levelsEqual, _, _, _, _, _, majorTyped, _⟩ :=
    VEnv.quotInd_inv environmentWF localsWF inductionRegistered reduction.hasType.1
  cases levelsEqual
  exact majorTyped

section
variable {context : VContext} {levels : List Level}
  {domain relation target function respect major : Expr} {semantic : VExpr}
  (initialized : context.env.quotInit = true)
  (translated : context.TrExprS
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
      domain) relation) target) function) respect) major) semantic)

example : ∃ majorSemantic domainSemantic relationSemantic sourceUniverse,
    context.TrExprS major majorSemantic ∧
    context.HasType majorSemantic
      (.app (.app (.const ``Quot [sourceUniverse]) domainSemantic) relationSemantic) := by
  obtain ⟨sourceUniverse, _, domainSemantic, relationSemantic, _, _, _, majorSemantic,
    _, _, _, _, _, _, _, _, _, majorTranslated, _, _, _, _, _, majorTyped⟩ :=
      context.quotLiftArguments initialized translated
  exact ⟨majorSemantic, domainSemantic, relationSemantic, sourceUniverse, majorTranslated, majorTyped⟩

example (wrongArity : levels.length ≠ 2) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, levelsTranslated, _⟩ :=
    context.quotLiftArguments initialized translated
  have arity := (List.mapM_eq_some.mp levelsTranslated).length_eq
  exact wrongArity (by simpa using arity)

example {state : VState} :
    RecM.WF context state (Inner.whnf major) fun normalized _ =>
      normalized.isAppOfArity ``Quot.mk 3 = true →
        ∃ payloadDomain payload, context.TrExprS normalized.appArg! payload ∧
          context.HasType payload payloadDomain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, majorTranslated, _⟩ :=
    context.quotLiftArguments initialized translated
  refine (Inner.whnf.WF majorTranslated).mono ?_
  intro normalized _ _ receipt shape
  obtain ⟨_, _, normalizedTranslated, _⟩ := receipt
  exact context.quotMkPayload initialized normalizedTranslated shape

end

section
variable {context : VContext} {levels : List Level}
  {domain relation motive minor major : Expr} {semantic : VExpr}
  (initialized : context.env.quotInit = true)
  (translated : context.TrExprS
    (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
      domain) relation) motive) minor) major) semantic)

example : ∃ majorSemantic domainSemantic relationSemantic sourceUniverse,
    context.TrExprS major majorSemantic ∧
    context.HasType majorSemantic
      (.app (.app (.const ``Quot [sourceUniverse]) domainSemantic) relationSemantic) := by
  obtain ⟨sourceUniverse, domainSemantic, relationSemantic, _, _, majorSemantic,
    _, _, _, _, _, _, _, majorTranslated, _, _, _, _, majorTyped⟩ :=
      context.quotIndArguments initialized translated
  exact ⟨majorSemantic, domainSemantic, relationSemantic, sourceUniverse, majorTranslated, majorTyped⟩

example (wrongArity : levels.length ≠ 1) : False := by
  obtain ⟨_, _, _, _, _, _, _, levelsTranslated, _⟩ :=
    context.quotIndArguments initialized translated
  have arity := (List.mapM_eq_some.mp levelsTranslated).length_eq
  exact wrongArity (by simpa using arity)

example {state : VState} :
    RecM.WF context state (Inner.whnf major) fun normalized _ =>
      normalized.isAppOfArity ``Quot.mk 3 = true →
        ∃ payloadDomain payload, context.TrExprS normalized.appArg! payload ∧
          context.HasType payload payloadDomain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, majorTranslated, _⟩ :=
    context.quotIndArguments initialized translated
  refine (Inner.whnf.WF majorTranslated).mono ?_
  intro normalized _ _ receipt shape
  obtain ⟨_, _, normalizedTranslated, _⟩ := receipt
  exact context.quotMkPayload initialized normalizedTranslated shape

end

run_meta
  let environment ← getEnv
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let registrationBaseline ← collectAxioms ``VContext.quotientDefEq
  let localContextBaseline ← collectAxioms ``VContext.Δwf
  for name in #[``VEnv.quotLift_inv, ``VEnv.quotInd_inv,
      ``VContext.quotLiftArguments, ``VContext.quotIndArguments] do
    let some information := environment.find? name
      | throwError "quotient eliminator inversion absent: {name}"
    if information matches .axiomInfo _ then throwError "quotient eliminator inversion axiom: {name}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "quotient eliminator inversion proof absent: {name}"
    if proof.hasSorry then throwError "direct quotient eliminator inversion admission: {name}"
    let dependencies ← collectAxioms name
    let nativeBridge := name == ``VContext.quotLiftArguments || name == ``VContext.quotIndArguments
    for dependency in dependencies do
      unless baseline.contains dependency || (nativeBridge &&
          (registrationBaseline.contains dependency || localContextBaseline.contains dependency)) do
        throwError "unexpected quotient eliminator inversion dependency: {dependency} in {name}"
    logInfo m!"{name}: {repr dependencies}"
  for name in #[``VEnv.quotMk_hasType, ``VEnv.quotInd_beta] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "quotient constructor/induction acquired a metatheory admission: {dependency} in {name}"
  logInfo m!"both quotient eliminators derive universe arity and every argument typing from the typed application; native major translations compose with verified WHNF and constructor payload extraction; exact respect/minor types and dependent result conversion are checked; automatic parameter alignment and full native quotient soundness are audited separately"

end QuotientEliminatorInversionTest
