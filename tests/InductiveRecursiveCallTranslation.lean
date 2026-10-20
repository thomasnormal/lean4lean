import Lean4Lean.Verify.InductiveRecursiveCallTranslation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.NativeInductive (hasExplicitConst)

namespace InductiveRecursiveCallTranslationTest

private theorem dependentArgumentsComeFromActualLocals
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (envWF : env.WF) (modelWF : model.WF env universes)
    (carrier element : FVarId) (level : Level)
    (carrierLookup : model.lctx.find? carrier =
      some (.cdecl carrierIndex carrier `actualCarrier (.sort level) .implicit .default))
    (elementLookup : model.lctx.find? element =
      some (.cdecl elementIndex element `actualElement (.fvar carrier) .default .default)) :
    NativeTelescopeArguments env universes model
      (.forallE `signatureCarrier (.sort level)
        (.forallE `signatureElement (.bvar 0) (.bvar 1) .default) .implicit)
      [.fvar carrier, .fvar element] (.fvar carrier) := by
  refine NativeTelescopeArguments.cdeclCons envWF modelWF carrierLookup ?_
  change NativeTelescopeArguments env universes model
    (.forallE `signatureElement (.fvar carrier) (.fvar carrier) .default)
    [.fvar element] (.fvar carrier)
  refine NativeTelescopeArguments.cdeclCons envWF modelWF elementLookup ?_
  exact .nil

private theorem dependentApplicationDerivesTheResultType
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (envWF : env.WF) (modelWF : model.WF env universes)
    (carrier element : FVarId) (level : Level)
    (carrierLookup : model.lctx.find? carrier =
      some (.cdecl carrierIndex carrier `actualCarrier (.sort level) .implicit .default))
    (elementLookup : model.lctx.find? element =
      some (.cdecl elementIndex element `actualElement (.fvar carrier) .default .default))
    (sourceTranslated : TrExprS env universes model.vlctx
      (.forallE `signatureCarrier (.sort level)
        (.forallE `signatureElement (.bvar 0) (.bvar 1) .default) .implicit) sourceSemantic)
    (headTranslated : TrExprS env universes model.vlctx head headSemantic)
    (headTyped : env.HasType universes.length model.vlctx.toCtx headSemantic sourceSemantic) :
    ∃ value resultType,
      TrExprS env universes model.vlctx (.app (.app head (.fvar carrier)) (.fvar element)) value ∧
      TrExprS env universes model.vlctx (.fvar carrier) resultType ∧
      env.HasType universes.length model.vlctx.toCtx value resultType :=
  (dependentArgumentsComeFromActualLocals envWF modelWF carrier element level
    carrierLookup elementLookup).application envWF modelWF sourceTranslated headTranslated headTyped

private theorem sortCannotConsumeAnExtraArgument
    (env : VEnv) (universes : List Name) (model : MLCtx) (level : Level)
    (argument : Expr) (arguments : List Expr) (terminal : Expr) :
    ¬ NativeTelescopeArguments env universes model (.sort level) (argument :: arguments) terminal := by
  intro arguments
  cases arguments

private theorem changedIndicesAreSubstitutedUnderTheMajorBinder (index : FVarId) :
    (Expr.forallE `major (.app (.const `Indexed []) (.bvar 0))
      (.app (.app (.fvar ⟨`motive⟩) (.bvar 1)) (.bvar 0)) .default).instantiate1' (.fvar index) =
    .forallE `major (.app (.const `Indexed []) (.fvar index))
      (.app (.app (.fvar ⟨`motive⟩) (.fvar index)) (.bvar 0)) .default := rfl

private theorem insertedSignatureUsesTheCallersUniverseAndLocalContext
    {before after : VEnv} {models : List VConstVal} {safety : DefinitionSafety}
    {info : RecursorVal} {constant : VConstVal} {model : MLCtx}
    (signature : TrConstVal safety before (.recInfo info) constant)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some after)
    (envWF : after.WF) (modelWF : model.WF after [`caller])
    (arity : info.levelParams.length = 1) :
    Nonempty (RecursorConstantInput after [`caller] model.vlctx info.name [.param `caller]
      (info.type.instantiateLevelParams info.levelParams [.param `caller])) :=
  recursorInputAfterInsertion signature member inserted envWF modelWF
    (semanticLevels := [.param 0]) rfl arity.symm

private def checkRecursiveValue (name : Name) (fuel : Nat) (value : Expr) : M Nat := do
  let fuel + 1 := fuel | throw (.other "recursive call: value opening fuel exhausted")
  let _ ← (monadLift (TypeChecker.checkType value) : M Expr)
  match value with
  | .lam binderName domain body binder =>
    withLocalDecl binderName binder domain fun fresh => do
      let count ← checkRecursiveValue name fuel (body.instantiate1 fresh)
      return count + 1
  | _ =>
    let .const called levels := value.getAppFn
      | throw (.other "recursive call: value did not end in a constant application")
    unless called == name do throw (.other "recursive call: wrong called signature")
    let arguments := value.getAppArgs
    unless arguments.size == 6 do
      throw (.other "recursive call: parameter/motive/minor/index/major argument count changed")
    let major := arguments.back!
    let index := arguments[arguments.size - 2]!
    unless index.isFVar && major.isApp && major.appArg! == index do
      throw (.other "recursive call: major must be the recursive field applied to its actual index")
    let partialCall := mkAppN value.getAppFn arguments.pop
    let prefixType ← (monadLift (TypeChecker.checkType partialCall) : M Expr)
    let prefixType ← (monadLift (TypeChecker.whnf prefixType) : M Expr)
    let .forallE _ majorDomain resultBody _ := prefixType
      | throw (.other "recursive call: partial signature has no major binder")
    let majorType ← (monadLift (TypeChecker.checkType major) : M Expr)
    unless (← (monadLift (TypeChecker.isDefEq majorType majorDomain) : M Bool)) do
      throw (.other "recursive call: field type and instantiated major domain differ")
    let inferred ← (monadLift (TypeChecker.checkType value) : M Expr)
    unless (← (monadLift (TypeChecker.isDefEq inferred (resultBody.instantiate1 major)) : M Bool)) do
      throw (.other "recursive call: inferred result differs from substituted signature body")
    let reader ← read
    for malformed in [
        mkAppN value.getAppFn (arguments.set! (arguments.size - 1) (.const ``Nat.zero [])),
        mkAppN value.getAppFn (arguments.set! (arguments.size - 2) (.sort (.succ .zero))),
        value.app (.const ``Nat.zero []),
        mkAppN (.const called (levels ++ [.zero])) arguments] do
      if ((monadLift (TypeChecker.checkType malformed) : M Expr) reader).isOk then
        throw (.other "recursive call: ill-typed major, index, extra argument or universe was accepted")
    return 0
termination_by fuel

private def checkOpenedRule (name : Name) (fuel : Nat) (rhs : Expr) : M (Nat × Nat) := do
  let fuel + 1 := fuel | throw (.other "recursive call: RHS opening fuel exhausted")
  match rhs with
  | .lam binderName domain body binder =>
    withLocalDecl binderName binder domain fun fresh =>
      checkOpenedRule name fuel (body.instantiate1 fresh)
  | _ =>
    let mut count := 0
    let mut lambdas := 0
    for value in rhs.getAppArgs do
      if hasExplicitConst name value then
        lambdas := lambdas + (← checkRecursiveValue name 100 value)
        count := count + 1
    return (count, lambdas)
termination_by fuel

private def runtimeFixtures : MetaM Unit := do
  let head := Expr.const `RecursiveCallIndexed []
  let natural := Expr.const ``Nat []
  let zero := Expr.const ``Nat.zero []
  let sortType := Expr.sort (.succ .zero)
  let type : InductiveType := {
    name := `RecursiveCallIndexed
    type := .forallE `carrier sortType (.forallE `ordinal natural sortType .default) .implicit
    ctors := [
      { name := `RecursiveCallIndexed.leaf
        type := .forallE `carrier sortType (mkAppN head #[.bvar 0, zero]) .implicit },
      { name := `RecursiveCallIndexed.branch
        type := .forallE `carrier sortType
          (.forallE `children
            (.forallE `ordinal natural (mkAppN head #[.bvar 1, .bvar 0]) .default)
            (mkAppN head #[.bvar 1, zero]) .default) .implicit }] }
  let host ← getEnv
  unless (host.addDeclCore 0 (.inductDecl [] 1 [type] false) none).isOk do
    throwError "recursive call: native kernel rejected the higher-order indexed fixture"
  let reader : Context := {
    env := host.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let .ok registered := run 1 [type] 0 reader
    | throwError "recursive call: fresh parameterized indexed higher-order family failed"
  let some (.recInfo info) := registered.find? `RecursiveCallIndexed.rec
    | throwError "recursive call: fresh recursor absent"
  let mut count := 0
  let mut lambdas := 0
  for rule in info.rules do
    let current := { reader with env := registered, lparams := info.levelParams }
    let .ok _ := (monadLift (TypeChecker.checkType rule.rhs) : M Expr) current
      | throwError "recursive call: complete native RHS failed to typecheck"
    let .ok (calls, closed) := checkOpenedRule info.name 100 rule.rhs current
      | throwError "recursive call: actual call/value application controls failed"
    count := count + calls
    lambdas := lambdas + closed
  unless count == 1 && lambdas == 1 do
    throwError "recursive call: expected one higher-order recursive value with one closing lambda"
  logInfo "recursive call runtime: parameter, motive, two minors, changed index and applied major checked; actual dependent higher-order recursive value closes one lambda; result substitution agrees; four malformed calls rejected"

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "recursive call: dependency manifest changed for {name}: {repr actual}"

private def auditModule : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let projection := logical ++ [``sorryAx]
  let contextInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let levelInterfaces := [``Expr.hasLevelParam_eq, ``Expr.replace_eq, ``Level.hasMVar_eq,
    ``Level.hasParam_eq, ``Level.instLawfulBEqLevel]
  let bindingInterfaces := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let structural := projection ++ contextInterfaces
  let signature := structural ++ levelInterfaces
  let closure := structural ++ bindingInterfaces
  let allowed := signature ++ bindingInterfaces
  for (name, expected) in [
      (``TrProj, [``sorryAx]), (``TrExprS.uniq, projection),
      (``TrExpr.weakFV, projection), (``TrExprS.instL, projection ++ levelInterfaces),
      (``TypeChecker.MLCtx.WF.mkLambda_trS, projection),
      (``RecursorConstantInput.ofTranslation, signature),
      (``NativeTelescopeArguments.translated, structural),
      (``NativeTelescopeArguments.application, structural),
      (``recursorInputAfterInsertion, signature),
      (``UArgModelEndpoint.recursiveCallAfterInsertion, signature),
      (``IndexMLCtxExtension.typedValueAbstraction, closure),
      (``UArgModelEndpoint.typedValueAbstraction, closure),
      (``UArgModelEndpoint.recursiveValueAfterInsertion, allowed)] do
    exactAxioms name expected
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRecursiveCallTranslation
    | throwError "recursive call: missing audited module"
  let mut pending := #[]
  let mut count := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "recursive call: new module axiom {name}"
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then throwError "recursive call: direct admission in {name}"
      let actual ← collectAxioms name
      for dependency in actual do
        unless allowed.contains dependency do
          throwError "recursive call: unexpected dependency {dependency} in {name}"
      pending := pending.push name
      count := count + 1
  unless count > 0 do throwError "recursive call: empty module audit"
  for name in [``dependentArgumentsComeFromActualLocals, ``dependentApplicationDerivesTheResultType,
      ``sortCannotConsumeAnExtraArgument, ``changedIndicesAreSubstitutedUnderTheMajorBinder,
      ``insertedSignatureUsesTheCallersUniverseAndLocalContext,
      ``RecursorConstantInput.ofTranslation] do
    pending := pending.push name
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do
      throwError "recursive call: missing forbidden dependency audit root {name}"
  let mut visited : NameSet := {}
  let mut admitted := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "recursive call: forbidden dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then admitted := admitted.push name
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "recursive call: dependency traversal bound exceeded"
  let expectedAdmissions := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq,
    ``TrProj.wf, ``TrProj.instL, ``TrProj.defeqDFC]
  unless admitted.size == expectedAdmissions.length && expectedAdmissions.all admitted.contains do
    throwError "recursive call: reached admission roots changed: {repr admitted}"
  let mut rejected := false
  try
    exactAxioms ``NativeTelescopeArguments.translated logical
  catch exception =>
    let actual ← exception.toMessageData.toString
    unless actual.startsWith "recursive call: dependency manifest changed" do throw exception
    rejected := true
  unless rejected do throwError "recursive call: logical-only negative audit was silently accepted"
  for name in [``checkRecursiveValue, ``checkOpenedRule, ``runtimeFixtures] do
    let actual ← collectAxioms name
    for dependency in actual do
      unless logical.contains dependency do
        throwError "recursive call: fixture unexpectedly depends on {dependency}"
  logInfo m!"recursive call: all {count} module-owned declarations audited; exact inherited projection/context/universe/closing manifests pinned; known-false strengthening/confluence roots excluded; logical-only negative audit rejected"

run_meta
  auditModule
  runtimeFixtures

end InductiveRecursiveCallTranslationTest
