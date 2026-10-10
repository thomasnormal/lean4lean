import Lean4Lean.Verify.StagedApplications
import Lean4Lean.Verify.Primitive
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.TypeChecker
open private Lean.Kernel.Environment.add from Lean.Environment

namespace StagedApplicationsTest

private def leafMethods : Methods := {
  isDefEqCore := fun _ _ => throw .deepRecursion
  whnfCore := fun _ _ _ => throw .deepRecursion
  whnf := fun expression => pure expression
  inferType := fun expression _ =>
    match expression with
    | .const name [] => fun reader state =>
      (fun result => (result, state)) <$> Inner.inferConstant reader name [] true
    | .sort level => pure (.sort level.succ)
    | _ => throw .deepRecursion }

private theorem leafContracts (context : RestrictedContext safety env venv) (valid : State → Prop) :
    context.ApplicationMethods leafMethods valid where
  whnf translated := by
    intro initial initialValid returned success
    cases success
    exact ⟨initialValid, .rfl, translated.trExpr context.checker.wf context.scope_wf⟩
  inferType {expression semantic} translated := by
    cases expression <;> try (solve | intro initial initialValid returned success; cases success)
    case sort level =>
      cases translated with
      | sort levelTr =>
        intro initial initialValid returned success
        cases success
        exact ⟨initialValid, _, context.inferSort levelTr⟩
    case const name levels =>
      cases levels with
      | cons level levels => intro initial initialValid returned success; cases success
      | nil =>
        intro initial initialValid returned success
        change ((fun result => (result, initial)) <$>
          Inner.inferConstant context.toContext name [] true) = .ok returned at success
        cases headSuccess : Inner.inferConstant context.toContext name [] true with
        | error exception => simp only [headSuccess, Functor.map, Except.map] at success; cases success
        | ok result =>
          simp only [headSuccess, Functor.map, Except.map] at success
          cases success
          obtain ⟨model, type, below, modelTr, typeTr, typed⟩ :=
            context.inferConstant (by simp) (fun _ => ⟨_, translated⟩) result headSuccess
          have equal := modelTr.uniq context.checker.wf (.refl context.checker.wf context.scope_wf) translated
          exact ⟨initialValid, type, below, translated, typeTr,
            typed.defeqU_l context.checker.wf context.scope_wf equal⟩

private theorem leafApplication (context : RestrictedContext safety env venv)
    (valid : State → Prop)
    (translated : TrExprS venv context.lparams context.scope expression semantic) :
    context.RunWF leafMethods valid (Inner.inferApp expression) fun result =>
      ∃ type, TrTyping venv context.lparams context.scope expression result semantic type :=
  context.inferApp (leafContracts context valid) translated

private def betaMethods : Methods := {
  leafMethods with whnf := fun expression => pure expression.cheapBetaReduce }

private theorem betaContracts (context : RestrictedContext safety env venv) (valid : State → Prop) :
    context.ApplicationMethods betaMethods valid where
  whnf translated := by
    intro initial initialValid returned success
    cases success
    exact ⟨initialValid, .cheapBetaReduce (context.noBV ▸ translated.closed),
      (translated.trExpr context.checker.wf context.scope_wf).cheapBetaReduce
        context.checker.wf context.scope_wf context.noBV⟩
  inferType translated := (leafContracts context valid).inferType translated

private theorem betaApplication (context : RestrictedContext safety env venv)
    (valid : State → Prop)
    (translated : TrExprS venv context.lparams context.scope expression semantic) :
    context.RunWF betaMethods valid (Inner.inferApp expression) fun result =>
      ∃ type, TrTyping venv context.lparams context.scope expression result semantic type :=
  context.inferApp (betaContracts context valid) translated

private def countingMethods : Methods := {
  leafMethods with whnf := fun expression => do
    modify fun state => { state with ngen := state.ngen.next }
    pure expression.cheapBetaReduce }

private theorem countingContracts (context : RestrictedContext safety env venv) (namePrefix : Name) :
    context.ApplicationMethods countingMethods (fun state => state.ngen.namePrefix = namePrefix) where
  whnf translated := by
    intro initial initialValid returned success
    cases success
    exact ⟨initialValid, .cheapBetaReduce (context.noBV ▸ translated.closed),
      (translated.trExpr context.checker.wf context.scope_wf).cheapBetaReduce
        context.checker.wf context.scope_wf context.noBV⟩
  inferType translated := (leafContracts context _).inferType translated

private theorem countingApplication (context : RestrictedContext safety env venv) (namePrefix : Name)
    (translated : TrExprS venv context.lparams context.scope expression semantic) :
    context.RunWF countingMethods (fun state => state.ngen.namePrefix = namePrefix)
      (Inner.inferApp expression) fun result =>
        ∃ type, TrTyping venv context.lparams context.scope expression result semantic type :=
  context.inferApp (countingContracts context namePrefix) translated

private theorem natSuccessorApplication (context : RestrictedContext safety env venv)
    (valid : State → Prop) (natPresent : venv.contains ``Nat) (value : Nat) :
    context.RunWF leafMethods valid
      (Inner.inferApp (.app (.const ``Nat.succ []) (.lit (.natVal value)))) fun result =>
        ∃ type, TrTyping venv context.lparams context.scope
          (.app (.const ``Nat.succ []) (.lit (.natVal value))) result
          (.app .natSucc (.natLit value)) type := by
  have successor : venv.HasType context.lparams.length context.scope.toCtx
      .natSucc (.forallE .nat .nat) := context.hasPrimitives.natSucc_type natPresent
  have literal : venv.HasType context.lparams.length context.scope.toCtx (.natLit value) .nat :=
    context.hasPrimitives.natLit_type natPresent value
  exact leafApplication context valid (.app successor literal
    (TrExprS.natSucc context.hasPrimitives natPresent).1
    (TrExprS.natLit context.hasPrimitives natPresent value).1)

private theorem acceptedApplication (context : RestrictedContext safety env venv)
    (contracts : context.ApplicationMethods methods valid)
    (translated : TrExprS venv context.lparams context.scope expression semantic)
    (initialValid : valid initial)
    (accepted : Inner.inferApp expression methods context.toContext initial = .ok (result, final)) :
    valid final ∧ ∃ type, TrTyping venv context.lparams context.scope expression result semantic type :=
  context.inferApp contracts translated initial initialValid (result, final) accepted

private def natType (binder : Name) (annotation : BinderInfo) : InductiveType := {
  name := ``Nat, type := .sort (.succ .zero),
  ctors := [⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ, .forallE binder (.const ``Nat []) (.const ``Nat []) annotation⟩] }

private def natStage (native : Kernel.Environment) (binder : Name) (annotation : BinderInfo) :=
  let types := #[natType binder annotation]
  AddInductive.checkInductiveTypes 0 types (fun stats => do
    AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0 types 0 false) do
      AddInductive.checkConstructors types stats false
      AddInductive.declareConstructors stats types false)
    { env := native, lparams := [], safety := .safe, allowPrimitive := true }

private theorem stagedSuccessor {native : Kernel.Environment} {semantic : VEnv}
    (checker : CheckerEnv safety native semantic) (primitives : semantic.HasPrimitives)
    (safePrimitives : NativePrimitiveSafety native) (binder : Name) (annotation : BinderInfo)
    (valid : State → Prop) (value : Nat) :
    (natStage native binder annotation).WF fun result =>
      ∃ final, ∃ context : RestrictedContext safety result final,
        context.lparams = [] ∧ context.scope = [] ∧
        context.RunWF leafMethods valid
          (Inner.inferApp (.app (.const ``Nat.succ []) (.lit (.natVal value)))) fun inferred =>
            ∃ type, TrTyping final context.lparams context.scope
              (.app (.const ``Nat.succ []) (.lit (.natVal value))) inferred
              (.app .natSucc (.natLit value)) type := by
  have recognized := (Lean4Lean.Environment.checkPrimitiveInductive.eq_true_iff
    native [] 0 [natType binder annotation] false).mpr (.nat binder annotation)
  refine (AddInductive.checkInductiveTypes.refinesPrimitiveInterfaces
    { env := native, lparams := [], safety := .safe, allowPrimitive := true }
    0 [natType binder annotation] 0 false checker primitives safePrimitives recognized).mono ?_
  intro result ⟨decl, headers, constructors, shape, addedHeaders, _, translated,
    addedCtors, finalChecker, finalPrimitives, finalSafe⟩
  have same : decl = natInductDecl := by
    rcases shape with rfl | same
    · have names : (``Nat : Name) = ``Bool := (List.forall₂_cons.mp translated.2.2).1.1
      exact ((by decide : (``Nat : Name) ≠ ``Bool) names).elim
    · exact same
  subst decl
  have headerNat := VEnv.addInductHeaders.constants addedHeaders
    (header := natInductDecl.types[0]) (by simp [natInductDecl])
  have finalNat : constructors.contains ``Nat :=
    ⟨_, (VEnv.addConstructorHeaders.le addedCtors).constants headerNat⟩
  let context := RestrictedContext.emptyScope finalChecker finalPrimitives finalSafe []
  exact ⟨constructors, context, rfl, rfl, natSuccessorApplication context valid finalNat value⟩

private def nativeBase : Kernel.Environment :=
  let env := Kernel.Environment.empty `StagedApplications
  let env := env.add (.axiomInfo {
    name := `Carrier, levelParams := [], type := .sort (.succ .zero), isUnsafe := false })
  let env := env.add (.axiomInfo {
    name := `value, levelParams := [], type := .const `Carrier [], isUnsafe := false })
  let env := env.add (.axiomInfo {
    name := `binary, levelParams := [],
    type := .forallE `first (.const `Carrier [])
      (.forallE `second (.const `Carrier []) (.const `Carrier []) .default) .default,
    isUnsafe := false })
  let env := env.add (.axiomInfo {
    name := `dependent, levelParams := [],
    type := .forallE `type (.sort (.succ .zero))
      (.forallE `value (.bvar 0) (.bvar 1) .default) .implicit,
    isUnsafe := false })
  let env := env.add (.defnInfo {
    name := `ArrowAlias, levelParams := [], type := .sort (.succ .zero),
    value := .forallE `value (.const `Carrier []) (.const `Carrier []) .default,
    hints := .abbrev, safety := .safe })
  let env := env.add (.axiomInfo {
    name := `wrapped, levelParams := [],
    type := .forallE `first (.const `Carrier []) (.const `ArrowAlias []) .default,
    isUnsafe := false })
  let env := env.add (.axiomInfo {
    name := `betaWrapped, levelParams := [],
    type := .forallE `first (.const `Carrier [])
      (.app (.lam `unused (.sort (.succ .zero))
        (.forallE `value (.const `Carrier []) (.const `Carrier []) .default) .default)
        (.const `Carrier [])) .default,
    isUnsafe := false })
  env.add (.axiomInfo {
    name := `polymorphic, levelParams := [`u],
    type := .forallE `type (.sort (.param `u)) (.sort (.param `u)) .default,
    isUnsafe := false })

private def nativeMethods : Methods := {
  leafMethods with
  whnf := TypeChecker.whnf
  inferType := fun expression _ => TypeChecker.inferType expression }

run_meta
  let carrier := Expr.const `Carrier []
  let value := Expr.const `value []
  let reader : Context := { env := nativeBase }
  let initial : State := { ngen := { namePrefix := `ApplicationControl, idx := 17 } }
  let controls := [
    (Expr.const `binary [], (nativeBase.find? `binary).get!.type),
    (.app (.const `binary []) value, .forallE `second carrier carrier .default),
    (.app (.app (.const `binary []) value) value, carrier),
    (.app (.const `dependent []) carrier, .forallE `value carrier carrier .default),
    (.app (.app (.const `dependent []) carrier) value, carrier),
    (.app (.const `polymorphic [.succ .zero]) carrier, .sort (.succ .zero))]
  let mut accepted := 0
  let mut rejected := 0
  for (methods, allowPolymorphic) in [(leafMethods, false), (betaMethods, false), (nativeMethods, true)] do
    for (expression, expected) in controls do
      if expression.getAppFn.constName! == `polymorphic && !allowPolymorphic then
        pure ()
      else
        let .ok (result, final) := Inner.inferApp expression methods reader initial
          | throwError "application control failed: {expression}"
        unless result == expected do throwError "wrong application type: {expression}"
        unless final.ngen.namePrefix == initial.ngen.namePrefix && final.ngen.idx == initial.ngen.idx do
          throwError "application control changed the name generator"
        accepted := accepted + 1
  let wrapped := .app (.app (.const `wrapped []) value) value
  let .ok (result, _) := Inner.inferApp wrapped nativeMethods reader initial
    | throwError "normalized telescope-tail control failed"
  unless result == carrier do throwError "normalized telescope-tail control returned the wrong type"
  if (Inner.inferApp wrapped leafMethods reader initial).isOk then
    throwError "identity normalization unexpectedly unfolded a telescope tail"
  rejected := rejected + 1
  let betaWrapped := Expr.app (.app (.const `betaWrapped []) value) value
  for methods in [betaMethods, nativeMethods] do
    let .ok (result, _) := Inner.inferApp betaWrapped methods reader initial
      | throwError "beta-normalized telescope-tail control failed"
    unless result == carrier do throwError "beta-normalized telescope-tail control returned the wrong type"
  if (Inner.inferApp betaWrapped leafMethods reader initial).isOk then
    throwError "identity normalization unexpectedly beta-reduced a telescope tail"
  rejected := rejected + 1
  let .ok (countedType, countedFinal) := Inner.inferApp betaWrapped countingMethods reader initial
    | throwError "state-changing normalization control failed"
  unless countedType == carrier && countedFinal.ngen.namePrefix == initial.ngen.namePrefix &&
      countedFinal.ngen.idx == initial.ngen.idx + 1 do
    throwError "state-changing normalization did not retain its invariant and actual effect"
  for expression in [
      .app (.const `missing []) value,
      .app (.const `binary [.zero]) value,
      .app (.app (.app (.const `binary []) value) value) value] do
    for methods in [leafMethods, betaMethods, nativeMethods] do
      if (Inner.inferApp expression methods reader initial).isOk then
        throwError "application accepted missing head, invalid universes, or excessive arguments"
      rejected := rejected + 1
  let .ok staged := natStage (Kernel.Environment.empty `ApplicationNatStage) `value .implicit
    | throwError "canonical Nat staging control failed"
  for value in [0, 1, 37] do
    for methods in [leafMethods, betaMethods, nativeMethods] do
      let expression := Expr.app (.const ``Nat.succ []) (.lit (.natVal value))
      let .ok (result, _) := Inner.inferApp expression methods { reader with env := staged } initial
        | throwError "staged Nat successor application failed"
      unless result == .const ``Nat [] do throwError "wrong staged Nat successor application type"
  logInfo m!"{accepted} leaf/beta/full-method application controls, three normalized telescope tails, and {rejected} rejection controls"
  logInfo "nine canonical Nat staged-successor controls"
  logInfo "one state-changing normalization control"

private def audit (name : Name) (expected : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == expected.length && axioms.all expected.contains do
    throwError "{name}: unexpected dependencies: {repr axioms}"
  logInfo m!"{name}: axioms = {repr axioms}"

run_meta
  let logical := [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  let application := logical ++ [``Lean.Expr.instantiateRevRange_eq,
    ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq]
  let leaves := logical ++ [``Lean.Level.hasParam_eq, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.Expr.replace_eq, ``Lean.Expr.hasLevelParam_eq, ``Lean.Level.hasMVar_eq,
    ``Lean.Level.instLawfulBEqLevel]
  for name in [``RestrictedContext.RunWF.pure, ``RestrictedContext.RunWF.throw,
      ``RestrictedContext.RunWF.bind, ``RestrictedContext.RunWF.mono,
      ``RestrictedContext.ensureForall] do
    audit name logical
  for name in [``RestrictedContext.inferAppLoop, ``RestrictedContext.inferApp, ``acceptedApplication] do
    audit name application
  audit ``leafContracts leaves
  for name in [``leafApplication, ``natSuccessorApplication] do
    audit name (leaves ++ [``Lean.Expr.instantiateRevRange_eq,
      ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq])
  audit ``stagedSuccessor (leaves ++ [``Lean.Expr.instantiateRevRange_eq,
    ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq, ``Lean.Expr.eqv_eq, ``Lean.Syntax.structEq_eq])
  let beta := leaves ++ [``Lean.Expr.mkAppRangeAux.eq_def, ``Lean.Expr.looseBVarRange_eq]
  audit ``betaContracts beta
  audit ``betaApplication (beta ++ [``Lean.Expr.instantiateRevRange_eq,
    ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq])
  audit ``countingContracts beta
  audit ``countingApplication (beta ++ [``Lean.Expr.instantiateRevRange_eq,
    ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq])

end StagedApplicationsTest
