import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace NativeQuotientReductionTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

section
variable {context : VContext} {state : VState}
  (translated : context.TrExprS expression semantic)

example (initialized : context.env.quotInit = true) :
    RecM.WF context state (quotReduceRec expression Inner.whnf) fun outcome _ =>
      ∀ reduced, outcome = some reduced →
        context.FVarsBelow expression reduced ∧ context.TrExpr reduced semantic :=
  Inner.quotReduceRec.WF initialized translated

example : RecM.WF context state (Inner.reduceRecursor expression) fun outcome _ =>
    ∀ reduced, outcome = some reduced →
      context.FVarsBelow expression reduced ∧ context.TrExpr reduced semantic :=
  Inner.reduceRecursor.WF translated

example (initialized : context.env.quotInit = true) (depth : Nat) :
    M.WF context state
      (quotReduceRec expression Inner.whnf (Methods.withFuel depth))
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow expression reduced ∧ context.TrExpr reduced semantic) :=
  Inner.quotReduceRec.WF initialized translated _ Methods.withFuel.WF

example (depth : Nat) :
    M.WF context state
      (Inner.reduceRecursor expression (Methods.withFuel depth))
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow expression reduced ∧ context.TrExpr reduced semantic) :=
  Inner.reduceRecursor.WF translated _ Methods.withFuel.WF

example : (RecM.run (Inner.reduceRecursor expression)).WF context state
    (fun outcome _ => ∀ reduced, outcome = some reduced →
      context.FVarsBelow expression reduced ∧ context.TrExpr reduced semantic) :=
  (Inner.reduceRecursor.WF translated).run

example (notInitialized : context.env.quotInit = false) :
    RecM.WF context state (Inner.reduceRecursor expression)
      (fun outcome _ => outcome = none) :=
  Inner.reduceRecursor.none_of_translation notInitialized translated

end

example {context : VContext} {state : VState}
    (initialized : context.env.quotInit = true)
    (translated : context.TrExprS
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift levels)
        domain) relation) target) function) respect) major) semantic)
    (majorTranslated : context.TrExprS major majorSemantic) :
    RecM.WF context state (Inner.whnf major) fun normalized _ =>
      normalized.isAppOfArity ``Quot.mk 3 = true →
        context.TrExpr (.app function normalized.appArg!) semantic := by
  refine (Inner.whnf.WF majorTranslated).mono ?_
  intro normalized _ _ receipt shape
  exact context.quotLiftReduction initialized translated majorTranslated receipt.2 shape

example {context : VContext} {state : VState}
    (initialized : context.env.quotInit = true)
    (translated : context.TrExprS
      (.app (.app (.app (.app (.app (.const ``Quot.ind levels)
        domain) relation) motive) minor) major) semantic)
    (majorTranslated : context.TrExprS major majorSemantic) :
    RecM.WF context state (Inner.whnf major) fun normalized _ =>
      normalized.isAppOfArity ``Quot.mk 3 = true →
        context.TrExpr (.app minor normalized.appArg!) semantic := by
  refine (Inner.whnf.WF majorTranslated).mono ?_
  intro normalized _ _ receipt shape
  exact context.quotIndReduction initialized translated majorTranslated receipt.2 shape

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.WHNF
    | throwError "native quotient proof module absent"
  let roots := #[``VContext.quotLiftReduction, ``VContext.quotIndReduction,
    ``Inner.quotReduceRec.trExpr, ``Inner.quotReduceRec.WF, ``Inner.reduceRecursor.WF]
  let privateSegments := #["quotLiftArgumentShape", "quotIndArgumentShape", "quotReapplyTranslation",
    "quotLiftArrayReduction", "quotIndArrayReduction"]
  let mut baseline : NameSet := {}
  for name in #[``VEnv.IsDefEq.church_rosser, ``VContext.quotMkPayload,
      ``VContext.quotientDefEq, ``VContext.Δwf, ``Inner.quotReduceRec.fvarsBelow,
      ``Inner.inductiveReduceRec.none_of_translation] do
    for dependency in ← collectAxioms name do baseline := baseline.insert dependency
  let mut audited : NameSet := {}
  let mut pending := roots
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name != some moduleIndex then continue
    let owned := roots.any (·.isPrefixOf name) ||
      (name.toString.splitOn ".").any (privateSegments.contains ·)
    unless owned do continue
    if information matches .axiomInfo _ then throwError "owned native quotient axiom: {name}"
    let some proof := information.value? (allowOpaque := true) | throwError "native quotient proof/value absent: {name}"
    if proof.hasSorry then throwError "direct native quotient admission: {name}"
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected native quotient dependency: {dependency} in {name}"
    audited := audited.insert name
    pending := pending.push name
    logInfo m!"{name}: {repr dependencies}"
  unless audited.size >= 10 do throwError "native quotient proof audit incomplete: {audited.size}"
  for name in roots do
    unless audited.contains name do throwError "native quotient public proof not audited: {name}"
  for name in #[``VEnv.quotMk_hasType, ``VEnv.quotInd_beta] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "constructor/induction beta trust boundary changed: {dependency} in {name}"
  let forbidden := #[``Inner.whnfCore'.WF, ``Inner.whnf'.WF, ``Methods.withFuel.WF, ``RecM.WF.run]
  let mut scheduled : NameSet := {}
  for name in pending do scheduled := scheduled.insert name
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "circular native quotient/normalizer proof: {name}"
    if let some information := environment.find? name then
      let mut dependencies := information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then dependencies := dependencies ++ proof.getUsedConstants
      for dependency in dependencies do
        unless scheduled.contains dependency do
          scheduled := scheduled.insert dependency
          pending := pending.push dependency
  unless pending.isEmpty do throwError "native quotient dependency traversal exceeded its bound"
  for name in #[``VEnv.quotLift_beta_of_normalizedMajor, ``VEnv.quotInd_beta_of_normalizedMajor,
      ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEq.church_rosser, ``VEnv.NormalEq.parRed,
      ``TrExpr.rebuild_mkAppList, ``Inner.inductiveReduceRec.none_of_translation] do
    unless visited.contains name do throwError "expected native quotient semantic dependency absent: {name}"
  logInfo m!"{audited.size} native quotient proof values have no direct admission or new interface axiom; actual callback normalization, payload translation, parameter inference and trailing applications establish quotReduceRec.WF and the unchanged reduceRecursor.WF contract at arbitrary fuel; the constructor-free inductive rejection and inherited typing/confluence admissions remain explicit"

end NativeQuotientReductionTest
