import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace QuotientReductionSemanticsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

section
variable {context : VContext} {sourceUniverse targetUniverse : VLevel}
  {domain relation target function respect value : VExpr}
  (initialized : context.env.quotInit = true)
  (sourceUniverseWF : sourceUniverse.WF context.lparams.length)
  (targetUniverseWF : targetUniverse.WF context.lparams.length)
  (domainTyped : context.HasType domain (.sort sourceUniverse))
  (relationTyped : context.HasType relation (.forallE domain (.forallE domain.lift (.sort .zero))))
  (targetTyped : context.HasType target (.sort targetUniverse))
  (functionTyped : context.HasType function (.forallE domain target.lift))
  (respectTyped : context.HasType respect
    (.forallE domain (.forallE domain.lift
      (.forallE (.app (.app (relation.liftN 2) (.bvar 1)) (.bvar 0))
        (.app (.app (.app (.const ``Eq [targetUniverse]) (target.liftN 3))
          (.app (function.liftN 3) (.bvar 2))) (.app (function.liftN 3) (.bvar 1)))))))
  (valueTyped : context.HasType value domain)

private def liftSemantic (sourceUniverse targetUniverse : VLevel)
    (domain relation target function respect value : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Quot.lift [sourceUniverse, targetUniverse])
    domain) relation) target) function) respect)
    (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)

example : context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
    (liftSemantic sourceUniverse targetUniverse domain relation target function respect value)
    (.app function value) target :=
  VEnv.quotLift_beta context.Ewf context.Δwf (context.trenv.quotientObjects initialized).1
    sourceUniverseWF targetUniverseWF domainTyped relationTyped targetTyped functionTyped
    respectTyped valueTyped

example {original reduced : Expr} {arguments : List Expr} {result : VExpr}
    (originalTranslated : context.TrExprS original
      (liftSemantic sourceUniverse targetUniverse domain relation target function respect value))
    (reducedTranslated : context.TrExprS reduced (.app function value))
    (appliedTranslated : context.TrExprS (original.mkAppList arguments) result) :
    context.TrExpr (reduced.mkAppList arguments) result := by
  have equality := VEnv.quotLift_beta context.Ewf context.Δwf
    (context.trenv.quotientObjects initialized).1 sourceUniverseWF targetUniverseWF
    domainTyped relationTyped targetTyped functionTyped respectTyped valueTyped
  have reducedRelation : context.TrExpr reduced
      (liftSemantic sourceUniverse targetUniverse domain relation target function respect value) :=
    ⟨_, reducedTranslated, equality.symm.toU⟩
  exact reducedRelation.rebuild_mkAppList context.Ewf context.Δwf
    originalTranslated appliedTranslated

example {motive minor : VExpr}
    (motiveTyped : context.HasType motive
      (.forallE (.app (.app (.const ``Quot [sourceUniverse]) domain) relation) (.sort .zero)))
    (minorTyped : context.HasType minor
      (.forallE domain (.app motive.lift
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain.lift) relation.lift) (.bvar 0))))) :
    context.venv.IsDefEq context.lparams.length context.vlctx.toCtx
      (.app (.app (.app (.app (.app (.const ``Quot.ind [sourceUniverse]) domain) relation) motive) minor)
        (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value))
      (.app minor value)
      (.app motive (.app (.app (.app (.const ``Quot.mk [sourceUniverse]) domain) relation) value)) := by
  have objects := context.trenv.quotientObjects initialized
  exact VEnv.quotInd_beta objects.2.2.2.1 objects.2.1 sourceUniverseWF
    domainTyped relationTyped motiveTyped minorTyped valueTyped

end

private def liftControl : Nat :=
  Quot.lift (fun value : Nat => value)
    (by intro first second related; exact related)
    (Quot.mk (fun first second : Nat => first = second) 5)

private def functionControl : Nat → Nat :=
  Quot.lift (fun value : Nat => fun argument : Nat => value + argument)
    (by intro first second related; cases related; rfl)
    (Quot.mk (fun first second : Nat => first = second) 5)

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let localId : FVarId := ⟨`quotientSemanticLocal⟩
  let letId : FVarId := ⟨`quotientSemanticLet⟩
  let localValue := Expr.fvar localId
  let mut controls := 0
  for declarationName in [``liftControl, ``functionControl] do
    let some (.defnInfo information) := environment.find? declarationName
      | throwError "quotient semantic control declaration absent: {declarationName}"
    let source := information.value
    let arguments := source.getAppArgs
    let majorPosition := 5
    let major := arguments[majorPosition]!
    unless major.isAppOfArity ``Quot.mk 3 do
      throwError "quotient semantic control lost its constructor: {declarationName}"
    let openMajor := Expr.app major.appFn! localValue
    let locals := ({} : LocalContext).mkLocalDecl localId `value natural .default
      |>.mkLetDecl letId `major (mkAppN (.const ``Quot [.succ .zero]) #[
        natural, major.getAppArgs[1]!]) openMajor
    let wrapped : List (Expr × Expr) := [
      (major, major.appArg!), (.mdata {} major, major.appArg!),
      (.app (.lam `ignored natural major .default) (.lit (.natVal 9)), major.appArg!),
      (.letE `ignored natural (.lit (.natVal 9)) major false, major.appArg!),
      (openMajor, localValue), (.fvar letId, localValue)]
    for safety in [DefinitionSafety.safe, .unsafe] do
      for eager in [false, true] do
        for depth in [32, 128] do
          let methods := Methods.withFuel depth
          let context : Context := {
            env := environment, lctx := locals, safety, eagerReduce := eager,
            fuel := { recDepth := depth, whnf := depth, whnfEager := depth } }
          for cheapRec in [false, true] do
            for cheapProj in [false, true] do
              let mut state : State := {}
              for _ in [:2] do
                for (wrappedMajor, payload) in wrapped do
                  let canonical := mkAppN source.getAppFn (arguments.set! majorPosition wrappedMajor)
                    let trailing : List (List Expr) := if declarationName == ``functionControl then
                    [[], [.lit (.natVal 7)]] else [[]]
                  for extraArguments in trailing do
                    let expression := canonical.mkAppList extraArguments
                    let expected := (Expr.app arguments[3]! payload).mkAppList extraArguments
                    let .ok (outcome, nextState) := quotReduceRec expression
                        (fun argument => Inner.whnf argument methods) context state
                      | throwError "actual quotient semantic helper rejected: {declarationName}"
                    unless outcome == some expected do
                      throwError "actual quotient semantic helper lost its payload/spine: {declarationName}"
                    let .ok (dispatched, finalState) := Inner.reduceRecursor expression
                        cheapRec cheapProj methods context nextState
                      | throwError "actual quotient semantic dispatch rejected: {declarationName}"
                    unless dispatched == some expected do
                      throwError "actual quotient semantic dispatch differs from the helper: {declarationName}"
                    state := finalState
                    controls := controls + 1
          let guardContext : Context := { env := environment, lctx := locals }
          let underApplied := mkAppN source.getAppFn (arguments.extract 0 majorPosition)
          let .ok (missing, _) := quotReduceRec underApplied
              (fun argument => Inner.whnf argument (Methods.withFuel 128)) guardContext {}
            | throwError "under-applied quotient semantic control rejected"
          unless missing.isNone do throwError "under-applied quotient semantic control reduced"
          let malformed := mkAppN source.getAppFn (arguments.set! majorPosition natural)
          let .ok (wrongHead, _) := quotReduceRec malformed
              (fun argument => Inner.whnf argument (Methods.withFuel 128)) guardContext {}
            | throwError "malformed quotient major control rejected"
          unless wrongHead.isNone do throwError "malformed quotient major control reduced"
    let context : Context := { env := environment, lctx := locals }
    unless !(quotReduceRec source (fun argument => Inner.whnf argument (Methods.withFuel 0))
        context {}).isOk do
      throwError "zero-depth quotient normalization unexpectedly accepted"
  logInfo m!"{controls} actual cold/warm quotient lift helper/dispatch pairs preserve constructor payloads and trailing applications; function-valued lift, metadata/beta/let majors and open/local-let payloads, both safeties/eager modes, depths 32/128 and all cheap flags; saturation, malformed-major and zero-depth guards pass; induction is covered by the typed proof above because native reduction erases its proposition result"

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Theory.Typing.QuotReduction
    | throwError "quotient semantic module absent"
  let baseline ← collectAxioms ``VEnv.IsDefEqU.of_r
  let mut owned := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "owned quotient semantic axiom: {name}"
      let some proof := information.value? | throwError "owned quotient semantic proof absent: {name}"
      if proof.hasSorry then throwError "owned quotient semantic admission: {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless baseline.contains dependency do
          throwError "unexpected quotient semantic dependency: {dependency} in {name}"
      logInfo m!"{name}: {repr dependencies}"
      owned := owned + 1
  for theoremName in #[``VEnv.quotMk_hasType, ``VEnv.quotInd_beta] do
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "quotient constructor/induction acquired a metatheory admission: {dependency}"
  logInfo m!"{owned} exhaustive owned quotient semantic declarations have no direct admission or axiom; lift explicitly inherits the existing unique-typing baseline {repr baseline}; constructor/induction exclude inherited admissions and choice; canonical parameter alignment is not full quotReduceRec.WF"
  nativeControls

end QuotientReductionSemanticsTest
