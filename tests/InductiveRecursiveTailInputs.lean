import Lean4Lean.Verify.InductiveRecursiveTailInputs
import Lean.Util.CollectAxioms

namespace InductiveRecursiveTailInputsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

/-- Simultaneous index substitution preserves references to the other selected
identifier. Sequential free-variable rewriting would collapse this swap. -/
private theorem zeroSelectedTail (body : Expr) :
    body.instantiateSelected [] [] = body := by
  simp [Expr.instantiateSelected, Expr.abstractFVars_nil]

private def parameter (binder : BinderInfo) : Expr :=
  .lam `input (.const ``Nat []) (.bvar 0) binder

private theorem annotatedPrefixesAreDistinct : parameter .implicit ≠ parameter .default := by
  intro equality
  cases equality

private def parameterVariation : MetaM Unit := do
  let host ← getEnv
  let natural := Expr.const ``Nat []
  let type : InductiveType := {
    name := `TailAnnotationFamily
    type := .forallE `function (.forallE `x natural natural .default)
      (.forallE `index natural (.sort (.succ .zero)) .default) .default
    ctors := [] }
  unless (host.addDeclCore 0 0 (.inductDecl [] 1 [type] false) none).isOk do
    throwError "native kernel rejected annotated-prefix family"
  let reader : Context := { env := host.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let .ok registered := run 1 [type] 0 reader | throwError "family registration failed"
  let original := { reader with env := registered }
  let some (.recInfo recInfo) := registered.find? (mkRecName type.name)
    | throwError "generated recursor metadata absent"
  let mut count := 0
  for storedBinder in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for actualBinder in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
      let stats : InductiveStats := { (default : InductiveStats) with
        indConsts := #[.const type.name []], params := #[parameter storedBinder], nindices := #[1] }
      let changed := #[Expr.const ``Nat.zero []]
      let terminal := mkAppN (.const type.name []) #[parameter actualBinder, changed[0]!]
      unless isValidIndAppIdx stats terminal 0 do throwError "accepted prefix annotation variation rejected"
      let storedFamily := mkAppN (mkAppN stats.indConsts[0]! stats.params) changed
      let motiveId : FVarId := ⟨`TailMotive⟩
      let body := Expr.app ((mkAppN (.fvar motiveId) changed).liftLooseBVars 0 1) (.bvar 0)
      let storedTail := Expr.forallE `major storedFamily body .default
      let actualTail := Expr.forallE `major terminal body .default
      unless storedTail == actualTail do throwError "canonical tail comparison lost accepted annotation variation"
      let major : FVarId := ⟨`TailMajor⟩
      let current := { original with lctx := original.lctx.mkLocalDecl major `major terminal .default }
      let motive := Expr.lam `index natural
        (.lam `major (mkAppN (.const type.name []) #[parameter storedBinder, .bvar 0])
          (.const ``True []) .default) .default
      let levels := recInfo.levelParams.map (fun _ => Level.zero)
      let value := (mkAppN (.const recInfo.name levels)
        #[parameter storedBinder, motive, changed[0]!]).app (.fvar major)
      let .ok result := (monadLift (TypeChecker.checkType value) : M Expr) current
        | throwError "actual generated recursive call rejected accepted prefix variation"
      unless ((monadLift (TypeChecker.isDefEq result (.const ``True [])) : M Bool) current).toOption == some true do
        throwError "actual generated call failed expected motive result"
      unless ((monadLift (TypeChecker.isDefEq result (.const ``False [])) : M Bool) current).toOption == some false do
        throwError "wrong motive result unexpectedly aligned"
      let wrong := (mkAppN (.const recInfo.name levels)
        #[parameter storedBinder, motive, .sort .zero]).app (.fvar major)
      if ((monadLift (TypeChecker.checkType wrong) : M Expr) current).isOk then
        throwError "malformed changed index accepted"
      count := count + 1
  logInfo m!"canonical tail: {count} actual generated calls preserve parameter binder variation; exact expected motive result; wrong-result and malformed-index controls rejected"

private def exactAxioms (name : Name) (expected : List Name) : MetaM Unit := do
  let actual ← collectAxioms name
  unless actual.size == expected.length && expected.all actual.contains do
    throwError "canonical tail: manifest changed for {name}: {repr actual}"

private def audit : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let nativeBinding := logical ++ [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let structural := logical ++ [``sorryAx, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let selected := structural ++ [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  let nativeEquality := [``Expr.eqv_eq, ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq]
  let call := structural ++ [``Expr.eqv_eq, ``Level.instLawfulBEqLevel]
  let value := selected ++ [``Expr.eqv_eq, ``Level.instLawfulBEqLevel]
  let allowed := selected ++ nativeEquality
  for (name, expected) in [
      (``Expr.instantiateMany_append_last, logical),
      (``NativeTelescopeArguments.terminalOfTail, logical ++ [``sorryAx]),
      (``mkForall_selected_tail, nativeBinding), (``recursorMajorTail_substitution, nativeBinding),
      (``NativeTelescopeArguments.terminalOfSelected, nativeBinding ++ [``sorryAx]),
      (``isValidIndAppIdx.familyIndexApplicationMatches, logical ++ nativeEquality),
      (``canonicalRecursorTail_matchesFieldTerminal, logical ++ nativeEquality),
      (``UArgModelEndpoint.canonicalIndexArgumentsFromSelectedTrace, selected),
      (``UArgModelEndpoint.recursiveCallFromInputOfEqvTail, call),
      (``UArgModelEndpoint.recursiveValueFromInputOfEqvTail, value),
      (``UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromCanonicalTail, allowed)] do
    exactAxioms name expected
  let mut pending := #[``zeroSelectedTail, ``annotatedPrefixesAreDistinct]
  let mut count := 0
  for moduleName in #[`Lean4Lean.Verify.InductiveIndexTailSubstitution,
      `Lean4Lean.Verify.InductiveRecursorTailAlignment, `Lean4Lean.Verify.InductiveRecursiveTailInputs] do
    let some moduleIndex := environment.getModuleIdx? moduleName | throwError "audited module absent"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned axiom {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "owned direct admission {name}"
        for dependency in (← collectAxioms name) do
          unless allowed.contains dependency do throwError "unexpected interface {dependency} in {name}"
        pending := pending.push name
        count := count + 1
  unless count > 0 do throwError "empty owned audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do throwError "forbidden audit root absent {name}"
  let mut visited : NameSet := {}
  let mut admissions := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden dependency {name}"
    let some information := environment.find? name | throwError "dependency absent {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then admissions := admissions.push name
      pending := pending ++ proof.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => throwError "missing proof body {name}"
      | _ => pure ()
  unless pending.isEmpty do throwError "dependency traversal exceeded bound"
  let expected := [``TrProj, ``TrProj.instN, ``TrProj.weak', ``TrProj.uniq, ``TrProj.wf, ``TrProj.instL]
  unless admissions.size == expected.length && expected.all admissions.contains do
    throwError "inherited direct roots changed {repr admissions}"
  for name in [``UArgModelEndpoint.canonicalIndexArgumentsFromSelectedTrace,
      ``UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromCanonicalTail] do
    let mut rejected := false
    try exactAxioms name logical
    catch exception =>
      let message ← exception.toMessageData.toString
      unless message.startsWith "canonical tail: manifest changed" do throw exception
      rejected := true
    unless rejected do throwError "logical-only negative audit accepted inherited admissions"
  for name in [``zeroSelectedTail, ``annotatedPrefixesAreDistinct] do
    for dependency in (← collectAxioms name) do
      unless logical.contains dependency do throwError "fixture helper depends on semantic interface {dependency}"
  logInfo m!"canonical tail: {count} owned declarations; exact 11/14-axiom selected-index/IH-value manifests; six inherited projection roots; full proof/opaque traversal excludes known-false strengthening/confluence; logical-only negative audits rejected"

run_meta
  audit
  parameterVariation

end InductiveRecursiveTailInputsTest
