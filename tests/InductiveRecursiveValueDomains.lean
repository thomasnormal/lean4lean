import Lean4Lean.Verify.InductiveRecursiveValueDomains
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.NativeInductive (hasExplicitConst)

namespace InductiveRecursiveValueDomainsTest

private theorem changedIndexAfterSharedDeclaration
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (envWF : env.WF) (modelWF : model.WF env universes)
    (carrier actualIndex : FVarId) (level : Level)
    (carrierLookup : model.lctx.find? carrier =
      some (.cdecl carrierPosition carrier `carrier (.sort level) .implicit .default))
    (indexLookup : model.lctx.find? actualIndex =
      some (.cdecl indexPosition actualIndex `changedIndex (.fvar carrier) .default .default)) :
    NativeTelescopeArguments env universes model
      (model.lctx.mkForall #[.fvar carrier]
        (.forallE `formalIndex (.fvar carrier)
          (.forallE `major (.app (.const `Family []) (.bvar 0))
            (.app (.app (.fvar ⟨`motive⟩) (.bvar 1)) (.bvar 0)) .default) .default))
      [.fvar carrier, .fvar actualIndex]
      (.forallE `major (.app (.const `Family []) (.fvar actualIndex))
        (.app (.app (.fvar ⟨`motive⟩) (.fvar actualIndex)) (.bvar 0)) .default) := by
  apply NativeTelescopeArguments.selectedPrefix envWF modelWF [carrier] (by simp)
    (fun identifier member => by
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, _, _, _, carrierLookup⟩) rfl
  exact NativeTelescopeArguments.cdeclCons envWF modelWF indexLookup .nil

private theorem rawMetadataTranslationRecovered
    (signature : TrConstVal safety before
      (.recInfo (declareRecursors.metadataVal stats types elimination infos universes
        full false false parent rules)) constant) :
    TrExprS before (getRecLevelParams elimination universes) []
      (recursorRawType stats infos parent full) constant.type := by
  have translated := signature.1.2.2
  exact translated.of_inferImplicit 1000 false

private theorem inferImplicitRoundTrip
    (translated : TrExprS env universes virtual expression semantic)
    (count : Nat) (range : Bool) :
    TrExprS env universes virtual expression semantic :=
  (translated.inferImplicit count range).of_inferImplicit count range

/-- Reconstruct the IH type from the actual called recursor's motive, indices
and applied recursive field, closing exactly the lambda binders in its value. -/
private def expectedIH (fuel : Nat) (value : Expr) (variant : Nat := 0) : M Expr := do
  let fuel + 1 := fuel | throw (.other "recursive domains: IH opening exhausted fuel")
  match value with
  | .lam name domain body binder =>
    withLocalDecl name binder domain fun fresh => do
      let result ← expectedIH fuel (body.instantiate1 fresh) variant
      return (← getLCtx).mkForall #[fresh] result
  | _ =>
    let .const name levels := value.getAppFn
      | throw (.other "recursive domains: missing recursive head")
    let some (.recInfo info) := (← read).env.find? name
      | throw (.other "recursive domains: called recursor metadata missing")
    unless levels == info.levelParams.map Level.param do
      throw (.other "recursive domains: generated call levels differ from declared parameters")
    let values := value.getAppArgs
    unless values.size == info.numParams + info.numMotives + info.numMinors + info.numIndices + 1 do
      throw (.other "recursive domains: recursive call arity differs from metadata")
    let some (.inductInfo parentInfo) := (← read).env.find? info.getMajorInduct
      | throw (.other "recursive domains: called parent metadata missing")
    let some parent := parentInfo.all.idxOf? parentInfo.name
      | throw (.other "recursive domains: called parent absent from mutual block")
    let parent := if variant == 1 then (parent + 1) % info.numMotives else parent
    let motive := values[info.numParams + parent]!
    let indices := values.extract (info.numParams + info.numMotives + info.numMinors)
      (values.size - 1)
    let indices := if variant == 2 then indices.set! 0 (.const ``Nat.zero []) else indices
    return (mkAppN motive indices).app values.back!
termination_by fuel

private def checkRule (recursors : List Name) (fuel : Nat) (rhs : Expr) : M Nat := do
  let fuel + 1 := fuel | throw (.other "recursive domains: rule opening exhausted fuel")
  match rhs with
  | .lam name domain body binder =>
    withLocalDecl name binder domain fun fresh => checkRule recursors fuel (body.instantiate1 fresh)
  | _ =>
    let head := rhs.getAppFn
    let mut current ← (monadLift (TypeChecker.checkType head) : M Expr)
    let mut checked := 0
    for argument in rhs.getAppArgs do
      let .forallE _ domain body _ ← (monadLift (TypeChecker.whnf current) : M Expr)
        | throw (.other "recursive domains: minor argument has no domain")
      let actual ← (monadLift (TypeChecker.checkType argument) : M Expr)
      unless (← (monadLift (TypeChecker.isDefEq actual domain) : M Bool)) do
        throw (.other "recursive domains: actual minor argument type mismatch")
      if recursors.any (fun name => hasExplicitConst name argument) then
        let expected ← expectedIH 100 argument
        unless (← (monadLift (TypeChecker.isDefEq expected domain) : M Bool)) do
          throw (.other "recursive domains: recursive value does not match the minor IH domain")
        unless (← (monadLift (TypeChecker.isDefEq actual expected) : M Bool)) do
          throw (.other "recursive domains: recursive value has a different reconstructed IH type")
        if (← (monadLift (TypeChecker.isDefEq actual (.const ``Nat [])) : M Bool)) then
          throw (.other "recursive domains: unrelated Nat domain accepted")
        let context ← read
        let wrongIndex ← expectedIH 100 argument 2
        if ((monadLift (TypeChecker.checkType wrongIndex) : M Expr) context).isOk then
          throw (.other "recursive domains: changed-index mismatch accepted in IH type")
        if recursors.length > 1 then
          let wrongMotive ← expectedIH 100 argument 1
          if ((monadLift (TypeChecker.checkType wrongMotive) : M Expr) context).isOk then
            throw (.other "recursive domains: other-parent motive accepted in IH type")
        if ((monadLift (TypeChecker.checkType (argument.app (.sort .zero))) : M Expr) context).isOk then
          throw (.other "recursive domains: malformed higher-order IH argument accepted")
        checked := checked + 1
      current := body.instantiate1 argument
    return checked
termination_by fuel

private def indexedFamily (name other : Name) (parameter : Bool) : InductiveType := Id.run do
  let natural := Expr.const ``Nat []
  let sortType := Expr.sort (.succ .zero)
  let result (parent : Name) (carrier index : Expr) :=
    if parameter then mkAppN (.const parent []) #[carrier, index] else .app (.const parent []) index
  let parameterize (body : Expr) :=
    if parameter then Expr.forallE `carrier sortType body .implicit else body
  return {
    name
    type := parameterize (.forallE `index natural sortType .default)
    ctors := [
      { name := name ++ `leaf
        type := parameterize (result name (.bvar 0) (.const ``Nat.zero [])) },
      { name := name ++ `branch
        type := parameterize (.forallE `children
          (.forallE `changedIndex natural (result other (.bvar 1) (.bvar 0)) .default)
          (result name (.bvar 1) (.const ``Nat.zero [])) .default) }] }

private def runtimeFixtures : MetaM Unit := do
  let host ← getEnv
  let single := indexedFamily `DomainIndexed `DomainIndexed true
  let left := indexedFamily `DomainLeft `DomainRight false
  let right := indexedFamily `DomainRight `DomainLeft false
  let mut total : Nat := 0
  for (parameters, types, expected) in [(1, [single], 1), (0, [left, right], 2)] do
    unless (host.addDeclCore 0 (.inductDecl [] parameters types false) none).isOk do
      throwError "recursive domains: native kernel rejected a fixture"
    let context : Context := {
      env := host.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
    let .ok registered := run parameters types 0 context
      | throwError "recursive domains: checked inductive frontend rejected a fixture"
    let recursors := types.map (fun type => mkRecName type.name)
    let mut count : Nat := 0
    for name in recursors do
      let some (.recInfo info) := registered.find? name
        | throwError "recursive domains: actual recursor absent"
      for rule in info.rules do
        let .ok checked := checkRule recursors 100 rule.rhs
            { context with env := registered, lparams := info.levelParams }
          | throwError "recursive domains: minor/IH argument alignment failed"
        count := count + checked
    unless count == expected do throwError "recursive domains: recursive value coverage changed"
    total := total + count
  logInfo m!"recursive domains: {total} actual higher-order recursive values match reconstructed IH domains and instantiated minor domains; parameterized indexed and mutual indexed families; unrelated domains, changed-index mismatches, other-parent motives and malformed higher-order arguments rejected"

#print axioms TrExprS.of_inferImplicit
#print axioms NativeTelescopeArguments.selectedPrefix
#print axioms recursorRawInputAfterInsertion
#print axioms UArgModelEndpoint.recursiveValueInIHDomain
#print axioms RecursorIHOpening.acceptsValue
#print axioms changedIndexAfterSharedDeclaration
#print axioms rawMetadataTranslationRecovered
#print axioms recursorRawOriginalInputAfterInsertion
#print axioms recursorRawType_sharedPrefix
#print axioms UArgModelEndpoint.recursiveValueInGeneratedIHDomain
#print axioms declaredRecursor_callLevels

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "recursive domains: dependency manifest changed for {name}: {repr actual}"

private def audit : MetaM Unit := do
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
      (``TrExprS.of_inferImplicit, projection),
      (``rawMetadataTranslationRecovered, projection), (``inferImplicitRoundTrip, projection),
      (``changedIndexAfterSharedDeclaration, closure),
      (``NativeTelescopeArguments.selectedPrefix, closure),
      (``UArgModelEndpoint.recursiveCallFromInput, structural),
      (``UArgModelEndpoint.recursiveValueFromInput, closure),
      (``recursorRawInputAfterInsertion, signature),
      (``recursorRawOriginalInputAfterInsertion, structural),
      (``recursorRawType_sharedPrefix, logical ++ bindingInterfaces),
      (``declaredRecursor_callLevels, logical),
      (``UArgModelEndpoint.recursiveValueInIHDomain, allowed),
      (``UArgModelEndpoint.recursiveValueInGeneratedIHDomain, closure),
      (``RecursorIHOpening.acceptsValue, structural)] do
    exactAxioms name expected
  let mut pending := #[``changedIndexAfterSharedDeclaration, ``rawMetadataTranslationRecovered,
    ``inferImplicitRoundTrip]
  let mut count : Nat := 0
  for moduleName in #[`Lean4Lean.Verify.InductiveRecursiveValueDomains,
      `Lean4Lean.Verify.InductiveRecursiveCallTranslation,
      `Lean4Lean.Verify.InductiveRecursorImplicitTranslation] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "recursive domains: audited module absent {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "recursive domains: owned axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "recursive domains: direct admission {name}"
        let actual ← collectAxioms name
        for dependency in actual do
          unless allowed.contains dependency do
            throwError "recursive domains: unexpected dependency {dependency} in {name}"
        pending := pending.push name
        count := count + 1
  unless count > 0 do throwError "recursive domains: empty owned-module audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do
      throwError "recursive domains: missing forbidden audit root {name}"
  let mut visited : NameSet := {}
  let mut admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "recursive domains: forbidden dependency {name}"
    let some information := environment.find? name
      | throwError "recursive domains: dependency absent {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then admissions := admissions.push name
      pending := pending ++ proof.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        throwError "recursive domains: missing proof body {name}"
      | _ => pure ()
  unless pending.isEmpty do throwError "recursive domains: dependency traversal exceeded bound"
  let expectedAdmissions := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq,
    ``TrProj.wf, ``TrProj.instL, ``TrProj.defeqDFC]
  unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
    throwError "recursive domains: inherited admission roots changed {repr admissions}"
  for name in [``UArgModelEndpoint.recursiveValueInIHDomain,
      ``UArgModelEndpoint.recursiveValueInGeneratedIHDomain] do
    let mut rejected := false
    try
      exactAxioms name logical
    catch exception =>
      let message ← exception.toMessageData.toString
      unless message.startsWith "recursive domains: dependency manifest changed" do throw exception
      rejected := true
    unless rejected do throwError "recursive domains: logical-only audit accepted inherited admissions"
  for name in [``expectedIH, ``checkRule, ``indexedFamily, ``runtimeFixtures] do
    let actual ← collectAxioms name
    for dependency in actual do
      unless logical.contains dependency do
        throwError "recursive domains: runtime fixture unexpectedly depends on {dependency}"
  logInfo m!"recursive domains: {count} owned declarations checked; exact raw-signature/shared-prefix/IH-value/peeled-domain manifests pinned; seven inherited projection admission roots reached; known-false strengthening/confluence roots excluded; logical-only negative audit rejected"

run_meta
  audit
  runtimeFixtures

end InductiveRecursiveValueDomainsTest
