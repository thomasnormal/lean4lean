import Lean4Lean.Verify.TypeChecker.ScopedMethods
import Lean.Util.CollectAxioms

namespace ProjectionReductionSemanticsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapProj).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS (.proj name index source) semantic) :
    (Inner.reduceProj index source cheapProj).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow (.proj name index source) reduced ∧ context.TrExpr reduced semantic) :=
  Inner.reduceProj.WF translated

example {context : VContext} {state : VState} {methods : Methods}
    (valid : methods.WF) (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapProj methods).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated methods valid

example {context : VContext} {state : VState} (depth : Nat)
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapProj (Methods.withFuel depth)).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated _ Methods.withFuel.WF

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment)
    (translated : (VContext.mk' wellFormed safety levels fuel).TrExprS source semantic) :
    (M.run environment safety {} levels fuel
      (RecM.run (Inner.reduceProj index source cheapProj))).WF (fun outcome => outcome = none) :=
  M.WF.run wellFormed (Inner.reduceProj.none_of_translation translated).run

example {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProjCore index source).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProjCore.none_of_translation translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS (.proj name index source) semantic) :
    (Inner.reduceProjCore index source).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow (.proj name index source) reduced ∧ context.TrExpr reduced semantic) :=
  Inner.reduceProjCore.WF translated

example {context : VContext} {state : VState} {methods : Methods}
    (valid : methods.WF) (translated : context.TrExprS source semantic) :
    (Inner.reduceProjCore index source methods).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProjCore.none_of_translation translated methods valid

example {context : VContext} {state : VState} (depth : Nat)
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProjCore index source (Methods.withFuel depth)).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProjCore.none_of_translation translated _ Methods.withFuel.WF

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment)
    (translated : (VContext.mk' wellFormed safety levels fuel).TrExprS source semantic) :
    (M.run environment safety {} levels fuel
      (RecM.run (Inner.reduceProjCore index source))).WF (fun outcome => outcome = none) :=
  M.WF.run wellFormed (Inner.reduceProjCore.none_of_translation translated).run

private def nativeControls : MetaM Unit := do
  let environment := (← getEnv).toKernelEnv
  let natural := Expr.const ``Nat []
  let literal := Expr.lit (.natVal 7)
  let localId : FVarId := ⟨`projectionReductionLocal⟩
  let letId : FVarId := ⟨`projectionReductionLet⟩
  let localHead := Expr.fvar localId
  let locals := ({} : LocalContext).mkLocalDecl localId `value natural .default
    |>.mkLetDecl letId `alias natural (.mdata {} literal)
  let identity := Expr.lam `argument natural (.bvar 0) .default
  let negatives : List Expr := [
    natural, literal, localHead, .fvar letId, .sort .zero, .mdata {} literal,
    .app identity literal, .letE `value natural literal (.bvar 0) false]
  let pair := mkAppN (.const ``Prod.mk [.zero, .zero]) #[natural, natural, literal, localHead]
  let mut noneCount : Nat := 0
  let mut constructorCount : Nat := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for eager in [false, true] do
      for depth in [32, 128] do
        let methods := Methods.withFuel depth
        let context : Context := {
          env := environment, lctx := locals, safety, eagerReduce := eager,
          fuel := { recDepth := depth, whnf := depth, whnfEager := depth } }
        for core in [false, true] do
          for cheapProj in [false, true] do
            let mut negativeState : State := {}
            for _ in [:2] do
              for source in negatives do
                for index in [0, 11, 9999] do
                  let action := if core then Inner.reduceProjCore index source
                    else Inner.reduceProj index source cheapProj
                  let .ok (outcome, finalState) := action methods context negativeState
                    | throwError "projection rejection worker failed: core={core}, {repr source}"
                  unless outcome.isNone do
                    throwError "projection rejection worker returned a value: core={core}, {repr source}"
                  negativeState := finalState
                  noneCount := noneCount + 1
            let mut positiveState : State := {}
            for _ in [:2] do
              for (index, expected) in [(0, literal), (1, localHead)] do
                let action := if core then Inner.reduceProjCore index pair
                  else Inner.reduceProj index pair cheapProj
                let .ok (outcome, finalState) := action methods context positiveState
                  | throwError "native constructor projection control rejected: core={core}"
                unless outcome == some expected do
                  throwError "native constructor projection control lost its expected field: core={core}"
                positiveState := finalState
                constructorCount := constructorCount + 1
            let source := Expr.const ``Prod.mk [.zero, .zero]
            let action := if core then Inner.reduceProjCore 0 source
              else Inner.reduceProj 0 source cheapProj
            let .ok (underApplied, _) := action methods context {}
              | throwError "under-applied native constructor projection rejected"
            unless underApplied.isNone do
              throwError "under-applied native constructor projection returned a field"
  let context : Context := { env := environment, lctx := locals }
  let zero := Methods.withFuel 0
  for cheapProj in [false, true] do
    unless !(Inner.reduceProj 0 literal cheapProj zero context {}).isOk do
      throwError "zero-depth projection callback unexpectedly accepted"
  let .ok (some rawField, _) := Inner.reduceProjCore 0 pair zero context {}
    | throwError "raw constructor projection unexpectedly called a zero-depth callback"
  unless rawField == literal do throwError "raw constructor projection lost its field"
  unless !(Inner.reduceProjCore 0 (.lit (.strVal "A")) zero context {}).isOk do
    throwError "raw string projection unexpectedly bypassed its zero-depth callback"
  let poisonedSource := Expr.app identity literal
  let poisoned : State := {
    whnfCoreCache := ({} : ExprMap Expr).insert poisonedSource pair,
    whnfCache := ({} : ExprMap Expr).insert poisonedSource pair }
  for cheapProj in [false, true] do
    let .ok (outcome, _) := Inner.reduceProj 0 poisonedSource cheapProj
        (Methods.withFuel 128) context poisoned
      | throwError "poisoned projection-cache premise control rejected"
    unless outcome == some literal do
      throwError "poisoned projection-cache premise control disappeared"
  let stringMethods := Methods.withFuel 1024
  let stringContext : Context := {
    context with fuel := { recDepth := 1024, whnf := 1024, whnfEager := 1024 } }
  let characterList := mkAppN (.const ``List.cons [.zero]) #[
    .const ``Char [], .app (.const ``Char.ofNat []) (.lit (.natVal 65)),
    .app (.const ``List.nil [.zero]) (.const ``Char [])]
  let expectedEncoding := Expr.app (.const ``List.utf8Encode []) characterList
  let .ok (some characters, stringState) := Inner.reduceProj 0 (.lit (.strVal "A"))
      false stringMethods stringContext {}
    | throwError "native string projection expansion control rejected"
  unless characters == expectedEncoding do
    throwError "native string projection helper lost its encoded field: {repr characters}"
  let .ok (normalizedCharacters, _) := Inner.whnf characters stringMethods stringContext stringState
    | throwError "native string projection field normalization rejected"
  unless normalizedCharacters.getAppFn == .const ``ByteArray.mk [] do
    throwError "native string projection field normalization lost its byte-array head"
  let .ok (rawStringField, _) := Inner.reduceProjCore 0 (.lit (.strVal "A"))
      stringMethods stringContext {}
    | throwError "raw string projection expansion rejected"
  unless rawStringField == some expectedEncoding do
    throwError "raw string projection expansion lost its encoded field"
  let .ok (rawPoisoned, _) := Inner.reduceProjCore 0 poisonedSource
      (Methods.withFuel 128) context poisoned
    | throwError "raw projection cache-premise control rejected"
  unless rawPoisoned.isNone do throwError "raw projection read an unrelated normalization cache"
  logInfo m!"{noneCount} actual cold/warm raw-core/normalized projection rejection controls and {constructorCount} native constructor-field successes pass; both safeties/eager modes, callback depths 32/128, both cheap flags, varied indices, metadata/beta/local-let heads and under-application covered; zero-depth callbacks distinguish raw constructor lookup from normalization/string expansion; native constructor/string successes remain outside the current TrEnv fragment, and poisoned caches remain excluded by the original state premise"

run_meta
  let environment ← getEnv
  let smallRoots := [``Inner.reduceProjCore.none_of_translation, ``Inner.reduceProjCore.WF,
    ``Inner.reduceProj.none_of_translation, ``Inner.reduceProj.WF]
  let smallAxioms := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let comparisonAxioms := smallAxioms ++ [``Lean.PersistentArray.toList'_push]
  let loopAxioms := comparisonAxioms ++ [``Lean4Lean.ptrEqConstantInfo_eq,
    ``Lean4Lean.ptrEqExpr_eq, ``Lean.Expr.eqv_eq, ``Lean.Expr.instantiateRev_eq,
    ``Lean.Expr.instantiate_eq, ``Lean.Expr.looseBVarRange_eq, ``Lean.Expr.mkAppData_eq,
    ``Lean.Expr.mkData_eq, ``Lean.Expr.replace_eq, ``Lean.Level.hasMVar_eq,
    ``Lean.Level.hasParam_eq, ``Lean.Level.instLawfulBEqLevel,
    ``Lean.Level.isExplicitSubsumedAux_eq, ``Lean.Level.normalize_eq,
    ``Lean.Syntax.structEq_eq, ``Std.TreeMap.all_eq_all_toList,
    (Name.mkNum `_private.Lean4Lean.Verify.Expr 0).str "Lean" |>.str "Expr"
      |>.str "mkData_flags" |>.str "_native" |>.str "bv_decide" |>.str "ax_1_12",
    `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7]
  let methodAxioms := loopAxioms ++ [``Lean.Expr.abstractRange_eq, ``Lean.Expr.abstract_eq,
    ``Lean.Expr.hasLooseBVar_eq, ``Lean.Expr.instantiate1_eq, ``Lean.Expr.instantiateRange_eq,
    ``Lean.Expr.instantiateRevRange_eq, ``Lean.Expr.lowerLooseBVars_eq]
  let comparisonAdmissions := [``VEnv.IsDefEqU.sort_inv,
    ``VEnv.IsDefEqU.forallE_inv_stratified, ``TrProj, ``TrProj.uniq]
  let loopAdmissions := comparisonAdmissions ++ [``TrProj.defeqDFC, ``TrProj.wf,
    ``TrProj.weak', ``VEnv.IsDefEqU.weakN_iff, ``TrProj.weak'_inv, ``TrProj.instL]
  let methodAdmissions := loopAdmissions ++ [``TrProj.instN, `Lean4Lean.VEnv.NormalEq.parRed]
  let smallForbidden := [``TrProj.uniq, ``TrProj.wf, ``TrProj.weak', ``TrProj.instN,
    ``TrProj.weak'_inv, ``VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.quot_inj]
  let roots := smallRoots ++ [``Inner.lazyDeltaProjReduction.finish.WF,
    ``Inner.lazyDeltaProjReduction.loop.WF, ``Inner.isDefEqCore'.WF,
    ``Methods.withFuel.WF, ``Methods.withFuel.scopeWF]
  for root in roots do
    let information ← getConstInfo root
    if information matches .axiomInfo _ then throwError "projection theorem is an axiom: {root}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "projection proof missing: {root}"
    if proof.hasSorry then throwError "projection theorem has a direct admission: {root}"
    let small := smallRoots.contains root
    let expected := if small then [``TrProj]
      else if root == ``Inner.lazyDeltaProjReduction.finish.WF then comparisonAdmissions
      else if [``Inner.lazyDeltaProjReduction.loop.WF, ``Inner.isDefEqCore'.WF].contains root then
        loopAdmissions else methodAdmissions
    let axioms ← collectAxioms root
    let expectedAxioms := if small then smallAxioms
      else if root == ``Inner.lazyDeltaProjReduction.finish.WF then comparisonAxioms
      else if [``Inner.lazyDeltaProjReduction.loop.WF, ``Inner.isDefEqCore'.WF].contains root then
        loopAxioms else methodAxioms
    unless expectedAxioms.length == axioms.size && expectedAxioms.all axioms.contains do
      throwError "projection axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if small && smallForbidden.contains name then
        throwError "forbidden projection dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expected.contains name do throwError "unapproved admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "projection audit traversal exceeded bound"
    unless expected.length == admissions.size && expected.all admissions.contains do
      throwError "projection admission manifest changed for {root}: {repr admissions}"
    if small then
      unless visited.contains ``Inner.reduceProjCore.none_of_translation do
        throwError "projection proof bypassed the core theorem: {root}"
    else
      unless visited.contains ``Inner.reduceProjCore.WF do
        throwError "actual comparison/method consumer bypassed the repaired core contract: {root}"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}; axioms {repr axioms}"
  nativeControls

end ProjectionReductionSemanticsTest
