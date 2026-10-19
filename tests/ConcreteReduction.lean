import Lean4Lean.Theory.Typing.ConcreteReduction
import Lean.Util.CollectAxioms

namespace ConcreteReductionTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.VEnv

section
variable {environment : VEnv} (environmentWF : environment.WF)

example {equation : VDefEq} (registered : environment.defeqs equation) :
    equation = quotDefEq ∨ ∃ definition : VDefVal, equation = definition.toDefEq :=
  environmentWF.rewriteMetadata.classify registered

example {definition : VDefVal} (registered : environment.defeqs definition.toDefEq) :
    environment.constants definition.name = some definition.toVConstant :=
  environmentWF.rewriteMetadata.lookup registered

example {first second : VDefVal} (firstRegistered : environment.defeqs first.toDefEq)
    (secondRegistered : environment.defeqs second.toDefEq) (sameName : first.name = second.name) :
    first = second :=
  environmentWF.rewriteMetadata.unique firstRegistered secondRegistered sameName

example {definition : VDefVal} (registered : environment.defeqs definition.toDefEq)
    (initialized : environment.defeqs quotDefEq) {name : Name}
    (primitive : name ∈ [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]) :
    definition.name ≠ name :=
  environmentWF.rewriteMetadata.quotientNames registered initialized name primitive

example {definition : VDefVal} (registered : environment.defeqs definition.toDefEq)
    (initialized : environment.defeqs quotDefEq) (masksConstructor : definition.name = ``Quot.mk) :
    False :=
  environmentWF.rewriteMetadata.quotientNames registered initialized _ (by simp) masksConstructor

example {definition : VDefVal} (registered : environment.defeqs definition.toDefEq)
    (initialized : environment.defeqs quotDefEq) (masksType : definition.name = ``Quot) : False :=
  environmentWF.rewriteMetadata.quotientNames registered initialized _ (by simp) masksType

end

example (rule : RewriteRule .empty pattern result) : False := by
  cases rule with
  | delta _ registered => cases registered
  | quot registered => cases registered

section
variable {environment : VEnv} {locals : List VExpr} {universes : Nat}
  {pattern : Pattern} {result : pattern.RHS × pattern.Check}
  {expression resultType : VExpr} {levels : List VLevel} {values : pattern.Path → VExpr}
  (environmentWF : environment.WF)
  (localsWF : OnCtx locals (environment.IsType universes))
  (rule : RewriteRule environment pattern result)
  (matched : pattern.Matches expression levels values)
  (typed : environment.HasType universes locals expression resultType)
  (checked : result.2.OK (environment.IsDefEqU universes locals) levels values)

example : ∃ simple : SimplePattern, pattern = simple.toPattern := rule.simple

example : environment.IsDefEqU universes locals expression (result.1.apply levels values) :=
  RewriteRule.sound environmentWF localsWF rule matched typed checked

example : environment.IsDefEqU universes locals expression (result.1.apply levels values) :=
  (environmentWF.reductionParams universes).pat_wf localsWF rule matched typed checked

example : @ParRed (environmentWF.reductionParams universes) locals expression
    (result.1.apply levels values) := by
  letI := environmentWF.reductionParams universes
  exact (Pattern.Equation.rule rule matched checked).parRed

example : environment.IsDefEq universes locals expression (result.1.apply levels values) resultType := by
  letI := environmentWF.reductionParams universes
  have reduced := (Pattern.Equation.rule rule matched checked).parRed
  exact reduced.defeq localsWF typed

end

example {environment : VEnv} {universes : Nat} {locals : List VExpr}
    {equation : VDefEq} {levels : List VLevel}
    (environmentWF : environment.WF) (registered : environment.defeqs equation)
    (arity : levels.length = equation.uvars) :
    Pattern.Equation (RewriteRule environment) (environment.IsDefEqU universes) locals
      (equation.lhs.instL levels) (equation.rhs.instL levels) :=
  RewriteRule.equation environmentWF registered arity

example {environment : VEnv} {universes : Nat} {locals : List VExpr}
    {equation : VDefEq} {levels : List VLevel}
    (environmentWF : environment.WF) (registered : environment.defeqs equation)
    (levelsWF : ∀ level ∈ levels, level.WF universes) (arity : levels.length = equation.uvars) :
    @ParRed (environmentWF.reductionParams universes) locals
      (equation.lhs.instL levels) (equation.rhs.instL levels) := by
  letI := environmentWF.reductionParams universes
  exact (Params.extra_pat registered levelsWF arity).parRed

example {environment : VEnv} {universes : Nat} {locals : List VExpr}
    {first second resultType : VExpr} (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (equal : environment.IsDefEq universes locals first second resultType) :
    @CRDefEq (environmentWF.reductionParams universes) locals first second := by
  letI := environmentWF.reductionParams universes
  exact equal.church_rosser localsWF

example {environment : VEnv} (environmentWF : environment.WF)
    (first : RewriteRule environment firstPattern firstResult)
    (second : RewriteRule environment secondPattern secondResult)
    (subpattern : Subpattern shared firstPattern)
    (intersection : secondPattern.inter shared = some overlap) :
    firstPattern = secondPattern ∧ secondPattern = shared ∧ HEq firstResult secondResult :=
  RewriteRule.unique environmentWF first second subpattern intersection

example {environment : VEnv}
    (first : RewriteRule environment firstPattern firstResult)
    (second : RewriteRule environment secondPattern secondResult)
    (firstSubpattern : Subpattern (.app firstFunction firstArgument) firstPattern)
    (secondSubpattern : Subpattern (.app secondFunction secondArgument) secondPattern)
    (functionSubpattern : Subpattern left firstFunction)
    (argumentSubpattern : Subpattern right secondArgument) :
    left.inter right = none :=
  RewriteRule.majorArgumentDisjoint first second firstSubpattern secondSubpattern
    functionSubpattern argumentSubpattern

run_meta
  let environment ← getEnv
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let mut owned := 0
  let mut pending := #[]
  for moduleName in #[`Lean4Lean.Theory.Typing.RewriteRules,
      `Lean4Lean.Theory.Typing.ConcreteReduction] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "concrete reduction module absent: {moduleName}"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "owned concrete reduction axiom: {name}"
        if let some proof := information.value? (allowOpaque := true) then
          if proof.hasSorry then throwError "owned concrete reduction direct admission: {name}"
          let dependencies ← collectAxioms name
          for dependency in dependencies do
            unless baseline.contains dependency do
              throwError "unexpected concrete reduction dependency: {dependency} in {name}"
          pending := pending.push name
          owned := owned + 1
        else
          match information with
          | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure ()
          | _ => throwError "concrete reduction proof/value absent: {name}"
  unless owned >= 20 do throwError "concrete reduction proof audit incomplete: {owned}"
  for name in #[``VEnv.WF.rewriteMetadata, ``VEnv.RewriteRule.simple, ``VEnv.RewriteRule.unique,
      ``VEnv.RewriteRule.equation, ``VEnv.RewriteRule.noNestedApplication,
      ``VEnv.RewriteRule.majorHeadDisjoint, ``VEnv.RewriteRule.majorArgumentDisjoint] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "metadata/non-overlap acquired an admission/interface: {dependency} in {name}"
    logInfo m!"{name}: {repr dependencies}"
  let modelDependencies ← collectAxioms ``VEnv.WF.reductionParams
  logInfo m!"concrete model: {repr modelDependencies}"
  let forbidden := #[``VEnv.Params.pat_wf, ``VEnv.NormalEq.parRed,
    ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser]
  let mut visited : NameSet := {}
  for _ in [:100000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "concrete model depends on its reduction/confluence consumer: {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "concrete reduction dependency traversal exceeded its bound"
  logInfo m!"every WF environment supplies a concrete definition/quotient Params model; equation coverage, unique definition origins, primitive-name protection and all non-overlap obligations are derived from the declaration history; actual parallel reduction and the unchanged confluence theorem instantiate the model; metadata is admission-free, rule soundness retains existing unique-typing dependencies, and the generic confluence admission remains explicit"

end ConcreteReductionTest
