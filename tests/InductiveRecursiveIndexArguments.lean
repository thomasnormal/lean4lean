import Lean4Lean.Verify.InductiveRecursiveIndexArguments
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.TypeChecker (MLCtx)
open Lean4Lean.NativeInductive (hasExplicitConst)

namespace InductiveRecursiveIndexArgumentsTest

private def source (carrier predicate : FVarId) : Expr :=
  .forallE `index (.fvar carrier)
    (.forallE `witness (.app (.fvar predicate) (.bvar 0)) (.sort .zero) .implicit) .default

private def target (carrier predicate : FVarId) : Expr :=
  .forallE `changed (.fvar carrier)
    (.forallE `evidence (.app (.fvar predicate) (.bvar 0))
      (.forallE `major (mkAppN (.const `Family []) #[.bvar 1, .bvar 0])
        (.app (.const `Result []) (.bvar 0)) .default) .instImplicit) .strictImplicit

private theorem dependentDomains (carrier predicate index witness : FVarId) :
    NativeTelescopeDomains (source carrier predicate) (target carrier predicate)
      [.fvar index, .fvar witness] (.sort .zero)
      (.forallE `major (mkAppN (.const `Family []) #[.fvar index, .fvar witness])
        (.app (.const `Result []) (.bvar 0)) .default) := by
  exact .cons (.cons .nil)

/-- Both dependent indices are recovered from the complete family translation;
there are no individual index translations or typings among the premises. -/
private theorem dependentArguments
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (envWF : env.WF) (modelWF : model.WF env universes)
    (carrier predicate index witness : FVarId)
    (signature : TrExprS env universes model.vlctx (source carrier predicate) signatureSemantic)
    (head : TrExprS env universes model.vlctx function functionSemantic)
    (typed : env.HasType universes.length model.vlctx.toCtx functionSemantic signatureSemantic)
    (terminal : TrExprS env universes model.vlctx
      (function.mkAppList [.fvar index, .fvar witness]) terminalSemantic) :
    NativeTelescopeArguments env universes model (target carrier predicate)
      [.fvar index, .fvar witness]
      (.forallE `major (mkAppN (.const `Family []) #[.fvar index, .fvar witness])
        (.app (.const `Result []) (.bvar 0)) .default) :=
  ((dependentDomains carrier predicate index witness).argumentsFromApplication envWF modelWF
    signature head typed terminal).2

private theorem nonPiRejected (argument nativeTarget : Expr) :
    ¬ NativeTelescopeDomains (.sort .zero) nativeTarget [argument] sourceEnd targetEnd := by
  intro domains
  cases domains

private theorem mismatchedDomainRejected :
    ¬ NativeTelescopeDomains
      (.forallE `left (.sort .zero) (.sort .zero) .default)
      (.forallE `right (.sort (.succ .zero)) (.sort .zero) .implicit)
      [argument] sourceEnd targetEnd := by
  intro domains
  cases domains

private theorem outOfRangeParameterPrefix (terminal : Expr)
    (bound : terminal.getAppArgs.size ≤ stats.params.size) :
    familyIndexPrefix stats terminal = terminal := by
  unfold familyIndexPrefix
  rw [List.take_of_length_le (by simpa using bound), Expr.getAppArgs_eq, List.toList_toArray]
  exact Expr.mkAppList_getAppArgsList terminal

/-- Reconstruct the IH type from the actual called recursor's motive, indices
and applied recursive field, closing exactly the lambda binders in its value. -/
private def expectedIH (fuel : Nat) (value : Expr) (variant : Nat := 0) : M Expr := do
  let fuel + 1 := fuel | throw (.other "recursive indices: IH opening exhausted fuel")
  match value with
  | .lam name domain body binder =>
    withLocalDecl name binder domain fun fresh => do
      let result ← expectedIH fuel (body.instantiate1 fresh) variant
      return (← getLCtx).mkForall #[fresh] result
  | _ =>
    let .const name levels := value.getAppFn
      | throw (.other "recursive indices: missing recursive head")
    let some (.recInfo info) := (← read).env.find? name
      | throw (.other "recursive indices: called recursor metadata missing")
    unless levels == info.levelParams.map Level.param do
      throw (.other "recursive indices: generated call levels differ from declared parameters")
    let values := value.getAppArgs
    unless values.size == info.numParams + info.numMotives + info.numMinors + info.numIndices + 1 do
      throw (.other "recursive indices: recursive call arity differs from metadata")
    let some (.inductInfo parentInfo) := (← read).env.find? info.getMajorInduct
      | throw (.other "recursive indices: called parent metadata missing")
    let some parent := parentInfo.all.idxOf? parentInfo.name
      | throw (.other "recursive indices: called parent absent from mutual block")
    let parent := if variant == 1 then (parent + 1) % info.numMotives else parent
    let motive := values[info.numParams + parent]!
    let indices := values.extract (info.numParams + info.numMotives + info.numMinors)
      (values.size - 1)
    let majorType ← (monadLift (TypeChecker.checkType values.back!) : M Expr)
    let indexCounts ← parentInfo.all.toArray.mapM fun name => do
      let some (.inductInfo family) := (← read).env.find? name
        | throw (.other "recursive indices: missing family metadata")
      pure family.numIndices
    let stats : InductiveStats := { (default : InductiveStats) with
      params := values.extract 0 info.numParams, nindices := indexCounts
      indConsts := parentInfo.all.toArray.map (fun name => .const name []) }
    unless (isValidIndApp? stats majorType) == parentInfo.all.idxOf? parentInfo.name do
      throw (.other "recursive indices: actual terminal failed checked family recognition")
    unless (getIIndices stats majorType).2 == indices do
      throw (.other "recursive indices: actual field terminal changed indices differ from call")
    let familyPrefix := familyIndexPrefix stats majorType
    unless familyPrefix.mkAppList indices.toList == majorType do
      throw (.other "recursive indices: actual family prefix did not reconstruct terminal")
    let mut indexType ← (monadLift (TypeChecker.checkType familyPrefix) : M Expr)
    for index in indices do
      let .forallE _ domain body _ ← (monadLift (TypeChecker.whnf indexType) : M Expr)
        | throw (.other "recursive indices: partial family exhausted index telescope")
      let actual ← (monadLift (TypeChecker.checkType index) : M Expr)
      unless (← (monadLift (TypeChecker.isDefEq actual domain) : M Bool)) do
        throw (.other "recursive indices: actual index disagrees with partial family domain")
      indexType := body.instantiate1 index
    let indices := if variant == 2 then indices.set! 0 (.const ``Nat.zero []) else indices
    let indices := if variant == 3 then
      indices.set! (indices.size - 1) (.const ``Nat.succ []) else indices
    return (mkAppN motive indices).app values.back!
termination_by fuel

private def checkRule (recursors : List Name) (fuel : Nat) (rhs : Expr) : M Nat := do
  let fuel + 1 := fuel | throw (.other "recursive indices: rule opening exhausted fuel")
  match rhs with
  | .lam name domain body binder =>
    withLocalDecl name binder domain fun fresh => checkRule recursors fuel (body.instantiate1 fresh)
  | _ =>
    let head := rhs.getAppFn
    let mut current ← (monadLift (TypeChecker.checkType head) : M Expr)
    let mut checked := 0
    for argument in rhs.getAppArgs do
      let .forallE _ domain body _ ← (monadLift (TypeChecker.whnf current) : M Expr)
        | throw (.other "recursive indices: minor argument has no domain")
      let actual ← (monadLift (TypeChecker.checkType argument) : M Expr)
      unless (← (monadLift (TypeChecker.isDefEq actual domain) : M Bool)) do
        throw (.other "recursive indices: actual minor argument type mismatch")
      if recursors.any (fun name => hasExplicitConst name argument) then
        let expected ← expectedIH 100 argument
        unless (← (monadLift (TypeChecker.isDefEq expected domain) : M Bool)) do
          throw (.other "recursive indices: recursive value does not match the minor IH domain")
        unless (← (monadLift (TypeChecker.isDefEq actual expected) : M Bool)) do
          throw (.other "recursive indices: recursive value has a different reconstructed IH type")
        if (← (monadLift (TypeChecker.isDefEq actual (.const ``Nat [])) : M Bool)) then
          throw (.other "recursive indices: unrelated Nat domain accepted")
        let context ← read
        let wrongIndex ← expectedIH 100 argument 2
        if ((monadLift (TypeChecker.checkType wrongIndex) : M Expr) context).isOk then
          throw (.other "recursive indices: changed-index mismatch accepted in IH type")
        let wrongDependent ← expectedIH 100 argument 3
        if ((monadLift (TypeChecker.checkType wrongDependent) : M Expr) context).isOk then
          throw (.other "recursive indices: malformed final dependent index accepted")
        if recursors.length > 1 then
          let wrongMotive ← expectedIH 100 argument 1
          if ((monadLift (TypeChecker.checkType wrongMotive) : M Expr) context).isOk then
            throw (.other "recursive indices: other-parent motive accepted in IH type")
        if ((monadLift (TypeChecker.checkType (argument.app (.const ``Nat.succ []))) : M Expr) context).isOk then
          throw (.other "recursive indices: malformed higher-order IH argument accepted")
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

/-- The second index's domain changes after substitution of the first. -/
private def dependentFamily : InductiveType := Id.run do
  let sortType := Expr.sort (.succ .zero)
  let result (carrier point : Expr) := mkAppN (.const `DependentIndices []) #[carrier, point]
  let base := result (.const ``Nat []) (.const ``Nat.zero [])
  return {
    name := `DependentIndices
    type := .forallE `carrier sortType
      (.forallE `point (.bvar 0) (.sort (.succ (.succ .zero))) .default) .implicit
    ctors := [
      { name := `DependentIndices.leaf, type := base },
      { name := `DependentIndices.branch
        type := .forallE `children
          (.forallE `carrier sortType
            (.forallE `point (.bvar 0) (result (.bvar 1) (.bvar 0)) .default) .implicit)
          base .default }] }

private def runtimeFixtures : MetaM Unit := do
  let host ← getEnv
  let single := indexedFamily `DomainIndexed `DomainIndexed true
  let left := indexedFamily `DomainLeft `DomainRight false
  let right := indexedFamily `DomainRight `DomainLeft false
  let mut total : Nat := 0
  for (parameters, types, expected) in [(1, [single], 1), (0, [left, right], 2), (0, [dependentFamily], 1)] do
    unless (host.addDeclCore 0 0 (.inductDecl [] parameters types false) none).isOk do
      throwError "recursive indices: native kernel rejected fixture {types.map (·.name)}"
    let context : Context := {
      env := host.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
    let .ok registered := run parameters types 0 context
      | throwError "recursive indices: checked inductive frontend rejected a fixture"
    let recursors := types.map (fun type => mkRecName type.name)
    let mut count : Nat := 0
    for name in recursors do
      let some (.recInfo info) := registered.find? name
        | throwError "recursive indices: actual recursor absent"
      for rule in info.rules do
        match checkRule recursors 100 rule.rhs
            { context with env := registered, lparams := info.levelParams } with
        | .ok checked => count := count + checked
        | .error (.other message) => throwError "{name}: {message}"
        | .error _ => throwError "{name}: recursive indices: minor/IH argument alignment failed"
    unless count == expected do throwError "recursive indices: recursive value coverage changed"
    total := total + count
  logInfo m!"recursive indices: {total} actual higher-order recursive values match reconstructed IH domains and instantiated minor domains; parameterized indexed, mutual indexed and dependent-index families; actual family prefix/index-domain reconstruction; unrelated domains, changed-index mismatches, other-parent motives and malformed higher-order arguments rejected"


#print axioms NativeTelescopeDomains.argumentsFromStack
#print axioms NativeTelescopeDomains.argumentsFromApplication
#print axioms familyIndexPrefix_apply
#print axioms UArgModelEndpoint.indexArguments
#print axioms UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromFamily
#print axioms dependentDomains
#print axioms dependentArguments
#print axioms nonPiRejected
#print axioms mismatchedDomainRejected
#print axioms outOfRangeParameterPrefix

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "recursive indices: dependency manifest changed for {name}: {repr actual}"

private def audit : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let projection := logical ++ [``sorryAx]
  let contextInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let bindingInterfaces := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let structural := projection ++ contextInterfaces
  let closure := structural ++ bindingInterfaces
  let allowed := closure
  for (name, expected) in [
      (``NativeTelescopeDomains.argumentsFromStack, structural),
      (``NativeTelescopeDomains.argumentsFromApplication, structural),
      (``familyIndexPrefix_apply, logical),
      (``UArgModelEndpoint.indexArguments, structural),
      (``UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromFamily, closure),
      (``dependentDomains, []), (``dependentArguments, structural),
      (``nonPiRejected, []), (``mismatchedDomainRejected, []),
      (``outOfRangeParameterPrefix, logical)] do
    exactAxioms name expected
  let mut pending := #[``dependentDomains, ``dependentArguments, ``nonPiRejected,
    ``mismatchedDomainRejected, ``outOfRangeParameterPrefix]
  let mut count : Nat := 0
  for moduleName in #[`Lean4Lean.Verify.InductiveRecursiveIndexArguments] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "recursive indices: audited module absent {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "recursive indices: owned axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "recursive indices: direct admission {name}"
        let actual ← collectAxioms name
        for dependency in actual do
          unless allowed.contains dependency do
            throwError "recursive indices: unexpected dependency {dependency} in {name}"
        pending := pending.push name
        count := count + 1
  unless count > 0 do throwError "recursive indices: empty owned-module audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do
      throwError "recursive indices: missing forbidden audit root {name}"
  let mut visited : NameSet := {}
  let mut admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "recursive indices: forbidden dependency {name}"
    let some information := environment.find? name
      | throwError "recursive indices: dependency absent {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then admissions := admissions.push name
      pending := pending ++ proof.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        throwError "recursive indices: missing proof body {name}"
      | _ => pure ()
  unless pending.isEmpty do throwError "recursive indices: dependency traversal exceeded bound"
  let expectedAdmissions := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq,
    ``TrProj.wf, ``TrProj.instL]
  unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
    throwError "recursive indices: inherited admission roots changed {repr admissions}"
  for name in [``UArgModelEndpoint.indexArguments,
      ``UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromFamily] do
    let mut rejected := false
    try
      exactAxioms name logical
    catch exception =>
      let message ← exception.toMessageData.toString
      unless message.startsWith "recursive indices: dependency manifest changed" do throw exception
      rejected := true
    unless rejected do throwError "recursive indices: logical-only audit accepted inherited admissions"
  for name in [``expectedIH, ``checkRule, ``indexedFamily, ``dependentFamily, ``runtimeFixtures] do
    let actual ← collectAxioms name
    for dependency in actual do
      unless logical.contains dependency do
        throwError "recursive indices: runtime fixture unexpectedly depends on {dependency}"
  logInfo m!"recursive indices: {count} owned declarations checked; exact 7-axiom argument and 11-axiom generated-IH-value manifests pinned; six inherited projection admission roots reached; known-false strengthening/confluence roots excluded; logical-only negative audits rejected"

run_meta
  audit
  runtimeFixtures

end InductiveRecursiveIndexArgumentsTest
