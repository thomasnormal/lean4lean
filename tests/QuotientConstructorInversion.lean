import Lean4Lean.Verify.TypeChecker.WHNF
import Lean.Util.CollectAxioms

namespace QuotientConstructorInversionTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

section
variable {environment : VEnv} {locals : List VExpr} {universes : Nat}
  {levels : List VLevel} {domain relation value resultType : VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (registered : environment.constants ``Quot.mk = some quotMkConst)
  (typed : environment.HasType universes locals
    (.app (.app (.app (.const ``Quot.mk levels) domain) relation) value) resultType)

example : ∃ sourceUniverse, levels = [sourceUniverse] ∧ sourceUniverse.WF universes ∧
    environment.HasType universes locals domain (.sort sourceUniverse) ∧
    environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))) ∧
    environment.HasType universes locals value domain ∧
    environment.IsDefEqU universes locals resultType
      (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) :=
  VEnv.quotMk_inv environmentWF localsWF registered typed

example (wrongArity : levels.length ≠ 1) : False := by
  obtain ⟨sourceUniverse, rfl, _⟩ := VEnv.quotMk_inv environmentWF localsWF registered typed
  exact wrongArity rfl

end

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {sourceUniverse : VLevel} {domain relation value : VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.constants ``Quot.mk = some quotMkConst)
    (sourceUniverseWF : sourceUniverse.WF universes)
    (domainTyped : environment.HasType universes locals domain (.sort sourceUniverse))
    (relationTyped : environment.HasType universes locals relation
      (.forallE domain (.forallE domain.lift (.sort .zero))))
    (valueTyped : environment.HasType universes locals value domain) :
    ∃ recoveredUniverse, [sourceUniverse] = [recoveredUniverse] ∧
      recoveredUniverse.WF universes ∧
      environment.HasType universes locals value domain := by
  obtain ⟨recoveredUniverse, levelsEqual, recoveredWF, _, _, recoveredValue, _⟩ :=
    VEnv.quotMk_inv environmentWF localsWF registered
      (VEnv.quotMk_hasType registered sourceUniverseWF domainTyped relationTyped valueTyped)
  exact ⟨recoveredUniverse, levelsEqual, recoveredWF, recoveredValue⟩

example {context : VContext} {levels : List Level} {domain relation value : Expr}
    {semantic : VExpr} (initialized : context.env.quotInit = true)
    (translated : context.TrExprS
      (.app (.app (.app (.const ``Quot.mk levels) domain) relation) value) semantic) :
    ∃ sourceUniverse domainSemantic relationSemantic valueSemantic,
      semantic = .app (.app (.app (.const ``Quot.mk [sourceUniverse]) domainSemantic)
        relationSemantic) valueSemantic ∧
      levels.mapM (VLevel.ofLevel context.lparams) = some [sourceUniverse] ∧
      sourceUniverse.WF context.lparams.length ∧
      context.TrExprS domain domainSemantic ∧ context.TrExprS relation relationSemantic ∧
      context.TrExprS value valueSemantic ∧
      context.HasType domainSemantic (.sort sourceUniverse) ∧
      context.HasType relationSemantic
        (.forallE domainSemantic (.forallE domainSemantic.lift (.sort .zero))) ∧
      context.HasType valueSemantic domainSemantic :=
  VContext.quotMkArguments initialized translated

example {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (initialized : context.env.quotInit = true)
    (translated : context.TrExprS expression semantic) :
    RecM.WF context state (Inner.whnf expression) fun normalized _ =>
      normalized.isAppOfArity ``Quot.mk 3 = true →
        ∃ domain value, context.TrExprS normalized.appArg! value ∧
          context.HasType value domain := by
  refine (Inner.whnf.WF translated).mono ?_
  intro normalized _ _ receipt shape
  obtain ⟨_, _, normalizedTranslated, _⟩ := receipt
  exact context.quotMkPayload initialized normalizedTranslated shape

example {context : VContext} {levels : List Level} {domain relation value : Expr}
    {semantic : VExpr} (initialized : context.env.quotInit = true)
    (translated : context.TrExprS
      (.app (.app (.app (.const ``Quot.mk levels) domain) relation) value) semantic)
    (wrongArity : levels.length ≠ 1) : False := by
  obtain ⟨_, _, _, _, _, levelsTranslated, _⟩ :=
    context.quotMkArguments initialized translated
  have arity := (List.mapM_eq_some.mp levelsTranslated).length_eq
  exact wrongArity (by simpa using arity)

run_meta
  let environment ← getEnv
  let some semanticModule := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotReduction
    | throwError "quotient semantic module absent"
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let registrationBaseline ← collectAxioms ``VContext.quotientDefEq
  let localContextBaseline ← collectAxioms ``VContext.Δwf
  let mut audited := 0
  for (name, information) in environment.constants do
    if name == ``VEnv.quotMk_inv || name == ``VContext.quotMkArguments ||
        name == ``VContext.quotMkPayload ||
        (name.toString.endsWith ".applicationArgumentTyped" &&
          environment.getModuleIdxFor? name == some semanticModule) then
      if information matches .axiomInfo _ then throwError "quotient inversion axiom: {name}"
      let some proof := information.value? (allowOpaque := true) | throwError "quotient inversion proof absent: {name}"
      if proof.hasSorry then throwError "direct quotient inversion admission: {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency || registrationBaseline.contains dependency ||
            localContextBaseline.contains dependency do
          throwError "unexpected quotient inversion dependency: {dependency} in {name}"
      logInfo m!"{name}: {repr dependencies}"
      audited := audited + 1
  unless audited == 4 do throwError "expected four quotient inversion proofs, found {audited}"
  logInfo m!"quotient constructor inversion derives universe arity, domain/relation/payload typing, and result-type conversion; native translation retains each original argument; existing unique-typing and registration dependencies remain explicit"

end QuotientConstructorInversionTest
