import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace QuotientReductionAlignmentTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

section
variable {context : VContext} {sourceUniverse constructorUniverse targetUniverse : VLevel}
  {domain relation value constructorDomain constructorRelation constructorValue : VExpr}
  (initialized : context.env.quotInit = true)
  (sourceUniverseWF : sourceUniverse.WF context.lparams.length)
  (constructorUniverseWF : constructorUniverse.WF context.lparams.length)
  (universeEqual : sourceUniverse ≈ constructorUniverse)
  (domainTyped : context.HasType domain (.sort sourceUniverse))
  (relationTyped : context.HasType relation (.forallE domain (.forallE domain.lift (.sort .zero))))
  (valueTyped : context.HasType value domain)
  (domainEqual : context.IsDefEqU constructorDomain domain)
  (relationEqual : context.IsDefEqU constructorRelation relation)
  (valueEqual : context.IsDefEqU constructorValue value)

private def constructorSemantic (sourceLevel : VLevel) (domain relation value : VExpr) : VExpr :=
  .app (.app (.app (.const ``Quot.mk [sourceLevel]) domain) relation) value

example : context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
    (constructorSemantic constructorUniverse constructorDomain constructorRelation constructorValue)
    (constructorSemantic sourceUniverse domain relation value)
    (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) :=
  VEnv.quotMk_congr context.Ewf context.Δwf (context.trenv.quotientObjects initialized).2.2.2.1
    sourceUniverseWF constructorUniverseWF universeEqual domainTyped relationTyped valueTyped
    domainEqual relationEqual valueEqual

example {target function respect : VExpr}
    (targetUniverseWF : targetUniverse.WF context.lparams.length)
    (targetTyped : context.HasType target (.sort targetUniverse))
    (functionTyped : context.HasType function (.forallE domain target.lift))
    (respectTyped : context.HasType respect
      (.forallE domain (.forallE domain.lift
        (.forallE (.app (.app (relation.liftN 2) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const ``Eq [targetUniverse]) (target.liftN 3))
            (.app (function.liftN 3) (.bvar 2))) (.app (function.liftN 3) (.bvar 1))))))) :
    context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
      (.app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
        domain) relation) target) function) respect)
        (constructorSemantic constructorUniverse constructorDomain constructorRelation constructorValue))
      (.app function value) target := by
  have objects := context.trenv.quotientObjects initialized
  have constructorEqual := VEnv.quotMk_congr context.Ewf context.Δwf objects.2.2.2.1
    sourceUniverseWF constructorUniverseWF universeEqual domainTyped relationTyped valueTyped
    domainEqual relationEqual valueEqual
  exact VEnv.quotLift_beta_of_majorEq context.Ewf context.Δwf objects.1
    sourceUniverseWF targetUniverseWF domainTyped relationTyped targetTyped functionTyped
    respectTyped valueTyped constructorEqual.toU

example {motive minor : VExpr}
    (motiveTyped : context.HasType motive
      (.forallE (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.sort .zero)))
    (minorTyped : context.HasType minor
      (.forallE domain (.app motive.lift
        (constructorSemantic sourceUniverse domain.lift relation.lift (.bvar 0))))) :
    context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
      (.app (.app (.app (.app (.app (.const ``Quot.ind [sourceUniverse]) domain) relation) motive) minor)
        (constructorSemantic constructorUniverse constructorDomain constructorRelation constructorValue))
      (.app minor value)
      (.app motive
        (constructorSemantic constructorUniverse constructorDomain constructorRelation constructorValue)) := by
  have objects := context.trenv.quotientObjects initialized
  have constructorEqual := VEnv.quotMk_congr context.Ewf context.Δwf objects.2.2.2.1
    sourceUniverseWF constructorUniverseWF universeEqual domainTyped relationTyped valueTyped
    domainEqual relationEqual valueEqual
  exact VEnv.quotInd_beta_of_majorEq context.Ewf context.Δwf objects.2.2.2.1 objects.2.1
    sourceUniverseWF domainTyped relationTyped motiveTyped minorTyped valueTyped constructorEqual.toU

example : context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
    (constructorSemantic (.max sourceUniverse sourceUniverse) domain relation value)
    (constructorSemantic sourceUniverse domain relation value)
    (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) := by
  exact VEnv.quotMk_congr context.Ewf context.Δwf (context.trenv.quotientObjects initialized).2.2.2.1
    sourceUniverseWF ⟨sourceUniverseWF, sourceUniverseWF⟩ VLevel.max_self.symm
    domainTyped relationTyped valueTyped domainTyped.toU relationTyped.toU valueTyped.toU

end

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotReductionAlignment
    | throwError "quotient alignment module absent"
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned quotient alignment axiom: {name}"
      let some proof := information.value? (allowOpaque := true) | throwError "owned quotient alignment proof absent: {name}"
      if proof.hasSorry then throwError "owned quotient alignment admission: {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency do
          throwError "unexpected quotient alignment dependency: {dependency} in {name}"
      logInfo m!"{name}: {repr dependencies}"
      owned := owned + 1
  logInfo m!"{owned} exhaustive owned quotient alignment declarations have no direct admission or axiom; existing unique-typing baseline is explicit: {repr baseline}; constructor levels/parameters/payloads may differ by conversion, and induction transports to the original dependent motive; automatic parameter inference and native worker soundness are audited separately"

end QuotientReductionAlignmentTest
