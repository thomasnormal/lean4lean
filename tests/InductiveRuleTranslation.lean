import Lean4Lean.Verify.InductiveRuleTranslation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.NativeInductive

namespace InductiveRuleTranslationTest

private def nativeSuccessorRuleRhs : Expr :=
  let head := Expr.const `RuleStageNat []
  let motiveDomain := Expr.forallE `t head (.sort (.param `u)) .default
  let zeroDomain := Expr.app (.bvar 0) (.const `RuleStageNat.zero [])
  let stepDomain := Expr.forallE `n head
    (.forallE `n_ih (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const `RuleStageNat.succ []) (.bvar 1))) .default) .default
  let recursiveCall := Expr.mkAppList (.const `RuleStageNat.rec [.param `u])
    [.bvar 3, .bvar 2, .bvar 1, .bvar 0]
  .lam `motive motiveDomain (.lam `zero zeroDomain (.lam `succ stepDomain
    (.lam `n head (.app (.app (.bvar 1) (.bvar 0)) recursiveCall) .default) .default)
    .default) .default

private theorem actualRecursiveBodyContainsTheNewRecursor :
    hasExplicitConst `RuleStageNat.rec nativeSuccessorRuleRhs = true := by decide

private theorem recursiveBodyCannotTranslateBeforeItsRecursor
    (before : VEnv) (absent : before.constants `RuleStageNat.rec = none) :
    ¬ ∃ semantic, TrExprS before [`u] [] nativeSuccessorRuleRhs semantic :=
  noTranslation_of_absentExplicitConst absent actualRecursiveBodyContainsTheNewRecursor

private theorem mutualHeadRequiresTheWholeBatch
    (before middle after : VEnv) (earlier later : VConstVal)
    (first : before.addConstructorHeaders [earlier] = some middle)
    (batch : before.addConstructorHeaders [earlier, later] = some after)
    (distinct : earlier.name ≠ later.name) (arity : later.uvars = 1) :
    (¬ ∃ semantic, TrExprS middle [`u] [] (.const later.name [.param `u]) semantic) ∧
      TrExprS after [`u] [] (.const later.name [.param `u]) (.const later.name [.param 0]) := by
  have beforeFresh := VEnv.addConstructorHeaders.fresh batch (by simp : later ∈ [earlier, later])
  have middleFresh : middle.constants later.name = none := by
    rw [VEnv.addConstructorHeaders.otherConstants first (by simpa using distinct)]
    exact beforeFresh
  refine ⟨noTranslation_of_absentExplicitConst middleFresh ?_, ?_⟩
  · simp [hasExplicitConst]
  · exact .const (VEnv.addConstructorHeaders.constants batch (by simp)) rfl arity.symm

private theorem insertedHeadStillRequiresTheRightUniverseArity
    (env : VEnv) (model : VConstVal)
    (lookup : env.constants model.name = some model.toVConstant) (arity : model.uvars = 1) :
    ¬ ∃ semantic, TrExprS env [`u] [] (.const model.name []) semantic := by
  rintro ⟨semantic, translated⟩
  cases translated with
  | const actual _ length =>
    have same := Option.some.inj (actual.symm.trans lookup)
    cases same
    simp [arity] at length

private theorem recursiveRuleReceiptUsesTheResultEnvironment
    {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry called : RecursorEntry} (member : entry ∈ evidence.recursors)
    (calledMember : called ∈ evidence.recursors) {rule : RecursorRule}
    (ruleMember : rule ∈ entry.info.rules)
    (recursiveCall : hasExplicitConst called.info.name rule.rhs = true) :
    (∃ semantic, TrExprS result entry.info.levelParams [] rule.rhs semantic) ∧
      ¬ ∃ semantic,
        TrExprS evidence.constructorEnv entry.info.levelParams [] rule.rhs semantic :=
  evidence.recursiveRuleTranslationStages member calledMember ruleMember recursiveCall

private theorem headTranslationDoesNotRequireRuleReceiptsAndUsesTheCallersUniverses
    {safety : DefinitionSafety} {before after : VEnv} {models : List VConstVal}
    {info : RecursorVal} {model : VConstVal}
    (signature : TrConstVal safety before (.recInfo info) model)
    (member : model ∈ models) (inserted : before.addConstructorHeaders models = some after)
    (arity : info.levelParams.length = 1) :
    TrExprS after [`callersUniverse] [] (.const info.name [.param `callersUniverse])
      (.const info.name [.param 0]) :=
  recursorHeadAfterInsertion signature member inserted [`callersUniverse]
    [.param `callersUniverse] [.param 0] rfl arity.symm []

private def constructorPrefix (types : List InductiveType) : AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes 0 types.toArray fun stats => do
    AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0 types.toArray 0 false) do
      AddInductive.checkConstructors types.toArray stats false
      AddInductive.declareConstructors stats types.toArray false

private def checkRuntimeRuleStages (reader : AddInductive.Context)
    (types : List InductiveType) (registered : Kernel.Environment) : MetaM Unit := do
  let .ok constructors := constructorPrefix types reader
    | throwError "rule staging: constructor prefix failed"
  for parent in types do
    let some (.recInfo info) := registered.find? (mkRecName parent.name)
      | throwError "rule staging: recursor absent during full RHS check"
    unless (constructors.find? info.name).isNone do
      throwError "rule staging: recursor was already present at the constructor stage"
    for rule in info.rules do
      let check := (monadLift (TypeChecker.checkType rule.rhs) : AddInductive.M Expr)
      let .ok _ := check { reader with env := registered, lparams := info.levelParams }
        | throwError "rule staging: full generated RHS failed to typecheck after registration"
      let early := check { reader with env := constructors, lparams := info.levelParams }
      if types.any (fun parent => hasExplicitConst (mkRecName parent.name) rule.rhs) then
        let .error (.unknownConstant _ called) := early
          | throwError "rule staging: recursive RHS did not fail on its unavailable recursor"
        unless types.any (fun parent => called == mkRecName parent.name) do
          throwError "rule staging: early failure named an unrelated missing constant"
      else
        let .ok _ := early
          | throwError "rule staging: nonrecursive RHS should typecheck at constructor stage"

private def runtimeFixtures : MetaM Unit := do
  let name := `RuleStageNat
  let head := Expr.const name []
  let type : InductiveType := {
    name, type := .sort (.succ .zero), ctors := [
      { name := `RuleStageNat.zero, type := head },
      { name := `RuleStageNat.succ, type := .forallE `n head head .default }] }
  let ctx : AddInductive.Context := {
    env := (← getEnv).toKernelEnv
    lparams := []
    safety := .safe
    allowPrimitive := false }
  let .ok result := AddInductive.run 0 [type] 0 ctx
    | throwError "rule staging: native fresh recursive inductive failed"
  let some (.recInfo info) := result.find? (mkRecName name)
    | throwError "rule staging: native recursor missing"
  unless info.levelParams == [`u] do throwError "rule staging: wrong elimination universes"
  let [base, step] := info.rules | throwError "rule staging: wrong native rule count"
  unless step.ctor == `RuleStageNat.succ && step.rhs == nativeSuccessorRuleRhs do
    throwError "rule staging: native generated recursive RHS differs from the formal control"
  unless !hasExplicitConst info.name base.rhs && hasExplicitConst info.name step.rhs do
    throwError "rule staging: recursive/base occurrence controls failed"
  unless (ctx.env.find? info.name).isNone && (result.find? info.name).isSome do
    throwError "rule staging: recursor must be fresh before registration and present afterwards"
  checkRuntimeRuleStages ctx [type] result
  let left := Expr.const `RuleStageEven []
  let right := Expr.const `RuleStageOdd []
  let types : List InductiveType := [
    { name := `RuleStageEven, type := .sort (.succ .zero), ctors := [
      { name := `RuleStageEven.base, type := left },
      { name := `RuleStageEven.next, type := .forallE `other right left .default }] },
    { name := `RuleStageOdd, type := .sort (.succ .zero), ctors := [
      { name := `RuleStageOdd.next, type := .forallE `other left right .default }] }]
  let .ok mutualResult := AddInductive.run 0 types 0 ctx
    | throwError "rule staging: native fresh mutual inductive failed"
  let some (.recInfo even) := mutualResult.find? `RuleStageEven.rec
    | throwError "rule staging: first mutual recursor missing"
  let some (.recInfo odd) := mutualResult.find? `RuleStageOdd.rec
    | throwError "rule staging: later mutual recursor missing"
  let [_, step] := even.rules | throwError "rule staging: first mutual rule count"
  let [otherStep] := odd.rules | throwError "rule staging: later mutual rule count"
  unless hasExplicitConst odd.name step.rhs && hasExplicitConst even.name otherStep.rhs do
    throwError "rule staging: actual mutual rules must call the other recursor"
  checkRuntimeRuleStages ctx types mutualResult
  logInfo "rule staging runtime: actual fresh successor RHS equals the formal obstruction; five complete single/mutual RHSs typecheck after registration; three recursive RHSs fail on their fresh recursor at constructor stage, while two base RHSs typecheck there; both mutual call directions checked, including a call to a later recursor"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let some _ := (← getEnv).find? name | throwError "rule staging: missing audited declaration {name}"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "rule staging: unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

#print axioms actualRecursiveBodyContainsTheNewRecursor
#print axioms recursiveBodyCannotTranslateBeforeItsRecursor
#print axioms mutualHeadRequiresTheWholeBatch
#print axioms insertedHeadStillRequiresTheRightUniverseArity
#print axioms recursiveRuleReceiptUsesTheResultEnvironment
#print axioms headTranslationDoesNotRequireRuleReceiptsAndUsesTheCallersUniverses
#print axioms RegistrationEvidence.recursorHeadTranslation
#print axioms RegistrationEntry.RuleSemantics.mono

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  for name in [``nativeSuccessorRuleRhs, ``actualRecursiveBodyContainsTheNewRecursor,
      ``constructorPrefix, ``checkRuntimeRuleStages, ``runtimeFixtures, ``auditDeclaration] do
    auditDeclaration name logical
  for name in [
      ``recursiveBodyCannotTranslateBeforeItsRecursor, ``mutualHeadRequiresTheWholeBatch,
      ``insertedHeadStillRequiresTheRightUniverseArity,
      ``recursiveRuleReceiptUsesTheResultEnvironment,
      ``headTranslationDoesNotRequireRuleReceiptsAndUsesTheCallersUniverses,
      ``RegistrationEntry.RuleSemantics.mono, ``RegistrationEvidence.orderedRuleSemantics] do
    auditDeclaration name inherited
  let environment ← getEnv
  let some projectionModule := environment.getModuleIdx? `Lean4Lean.Verify.Typing.Expr
    | throwError "rule staging: missing projection foundation module"
  unless environment.getModuleIdxFor? ``TrProj == some projectionModule do
    throwError "rule staging: projection foundation provenance changed"
  for (name, expected) in [( ``TrProj, [``sorryAx]), (``TrExprS.rec, inherited),
      (``TrExprS.const, []), (``TrExprS.mono, inherited)] do
    let actual ← collectAxioms name
    unless actual.size == expected.length && expected.all actual.contains do
      throwError "rule staging: inherited foundation dependency set changed for {name}"
  let mut rejected := false
  try
    auditDeclaration ``TrExprS.rec logical
  catch exception =>
    let actual ← exception.toMessageData.toString
    let expected ← (m!"rule staging: unexpected axiom {``sorryAx} in {``TrExprS.rec}").toString
    unless actual == expected do
      throw exception
    rejected := true
  unless rejected do throwError "rule staging: logical-only projection audit was silently accepted"
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveRuleTranslation
    | throwError "rule staging: missing audited module"
  let mut count := 0
  let mut pending := #[]
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "rule staging: new module axiom {name}"
      if let some proof := information.value? (allowOpaque := true) then
        if proof.hasSorry then throwError "rule staging: direct admission in {name}"
      auditDeclaration name inherited
      pending := pending.push name
      count := count + 1
  unless count > 0 do throwError "rule staging: empty module audit"
  let forbidden := [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser, ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  for name in forbidden do
    unless (environment.find? name).isSome do
      throwError "rule staging: missing forbidden dependency audit root {name}"
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "rule staging: forbidden dependency {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "rule staging: dependency traversal bound exceeded"
  runtimeFixtures
  logInfo "rule staging: all new module declarations and private helpers exclude direct admissions, new axioms, native interface axioms and known-false strengthening/confluence dependencies; inherited projection dependency sets pinned, with a negative logical-only audit control"

end InductiveRuleTranslationTest
