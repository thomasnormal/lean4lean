import Lean4Lean.Theory.Typing.QuotPatternSoundness
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean.Util.CollectAxioms

namespace QuotientPatternSoundnessTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {environment : VEnv} (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.HasObjects [.defeq quotDefEq, .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst, .const ``Quot.mk quotMkConst, .const ``Quot quotConst] :=
  environmentWF.quotientObjects registered

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {expression resultType : VExpr} {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (registered : environment.defeqs quotDefEq)
    (matched : quotLiftPattern.Matches expression levels values)
    (typed : environment.HasType universes locals expression resultType)
    (checked : quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values) :
    environment.IsDefEq universes locals expression
      (quotLiftPatternResult.apply levels values) resultType :=
  quotLiftPattern.sound environmentWF localsWF registered matched typed checked

section
variable {environment : VEnv} {locals : List VExpr} {universes : Nat}
  {levels constructorLevels : List VLevel}
  {domain relation target function respect constructorDomain constructorRelation value resultType : VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (registered : environment.defeqs quotDefEq)
  (typed : environment.HasType universes locals
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
      domain) relation) target) function) respect)
        (.app (.app (.app (.const ``Quot.mk constructorLevels)
          constructorDomain) constructorRelation) value)) resultType)
  (domainEqual : environment.IsDefEqU universes locals constructorDomain domain)
  (relationEqual : environment.IsDefEqU universes locals constructorRelation relation)

example : environment.IsDefEq universes locals
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
      domain) relation) target) function) respect)
        (.app (.app (.app (.const ``Quot.mk constructorLevels)
          constructorDomain) constructorRelation) value))
    (.app function value) resultType :=
  VEnv.quotLift_beta_of_checkedParameters environmentWF localsWF registered typed
    domainEqual relationEqual

example : environment.IsDefEq universes locals
    (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
      domain) relation) target) function) respect)
        (.app (.app (.app (.const ``Quot.mk constructorLevels)
          constructorDomain) constructorRelation) value))
    (.app function value) resultType := by
  have liftMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := levels)
    |>.var (a' := domain) |>.var (a' := relation) |>.var (a' := target)
    |>.var (a' := function) |>.var (a' := respect)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := constructorLevels)
    |>.var (a' := constructorDomain) |>.var (a' := constructorRelation) |>.var (a' := value)
  exact quotLiftPattern.sound environmentWF localsWF registered (liftMatched.app constructorMatched)
    typed ⟨domainEqual.symm, relationEqual.symm, trivial⟩

end

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (domainMismatch : ¬environment.IsDefEqU universes locals
      (values (.inl (some (some (some (some none))))))
      (values (.inr (some (some none))))) :
    ¬quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values := by
  intro checked
  exact domainMismatch checked.1

example {environment : VEnv} {locals : List VExpr} {universes : Nat}
    {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (relationMismatch : ¬environment.IsDefEqU universes locals
      (values (.inl (some (some (some none)))))
      (values (.inr (some none)))) :
    ¬quotLiftPatternCheck.OK (environment.IsDefEqU universes locals) levels values := by
  intro checked
  exact relationMismatch checked.2.1

example {context : VContext} {native : Expr} {semantic : VExpr}
    {levels : List VLevel} {values : quotLiftPattern.Path → VExpr}
    (initialized : context.env.quotInit = true)
    (translated : context.TrExprS native semantic)
    (matched : quotLiftPattern.Matches semantic levels values)
    (checked : quotLiftPatternCheck.OK (context.IsDefEqU) levels values) :
    context.IsDefEqU semantic (quotLiftPatternResult.apply levels values) := by
  obtain ⟨resultType, typed⟩ := translated.wf context.Ewf context.Δwf
  exact (quotLiftPattern.sound context.Ewf context.Δwf
    (context.trenv.quotientObjects initialized).1 matched typed checked).toU

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotPatternSoundness
    | throwError "quotient pattern soundness module absent"
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let mut audited := 0
  let mut pending := #[]
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned quotient pattern axiom: {name}"
      let some proof := information.value? | throwError "owned quotient pattern proof absent: {name}"
      if proof.hasSorry then throwError "owned quotient pattern direct admission: {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency do
          throwError "unexpected quotient pattern dependency: {dependency} in {name}"
      logInfo m!"{name}: {repr dependencies}"
      pending := pending.push name
      audited := audited + 1
  unless audited >= 3 do throwError "expected all quotient pattern soundness proofs, found {audited}"
  let primitiveDependencies ← collectAxioms ``VEnv.WF.quotientObjects
  for dependency in primitiveDependencies do
    unless #[``propext, ``Quot.sound].contains dependency do
      throwError "quotient equation origin proof acquired an admission/interface: {dependency}"
  let forbidden := #[``VEnv.Params, ``VEnv.Params.pat_wf, ``VEnv.NormalEq.parRed,
    ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser]
  let mut visited : NameSet := {}
  for _ in [:100000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "quotient pattern soundness uses its confluence consumer: {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? then
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "quotient pattern dependency traversal exceeded its bound"
  logInfo m!"the concrete quotient pattern preserves arbitrary supplied result types using its actual domain/relation checks; all argument typings, universe arities/equivalence and payload transport are derived; quotient equation registration recovers primitive signatures from the WF declaration history without admissions; no Params instance or confluence theorem is assumed"

end QuotientPatternSoundnessTest
