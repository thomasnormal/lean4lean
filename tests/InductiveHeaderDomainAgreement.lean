import Lean4Lean.Verify.InductiveHeaderDomainAgreement
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive Lean4Lean.ElimNestedInductive
open Lean4Lean.TypeChecker (MLCtx)

namespace InductiveHeaderDomainAgreementTest

private def sourceType : FVarId := ⟨`HeaderSourceType⟩
private def sourceValue : FVarId := ⟨`HeaderSourceValue⟩
private def targetType : FVarId := ⟨`HeaderTargetType⟩
private def targetValue : FVarId := ⟨`HeaderTargetValue⟩
private def betaDomain : Expr := .app (.lam `type (.sort (.succ .zero)) (.bvar 0) .default) (.sort .zero)
private def betaSemantic : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
private def sourceFirst : MLCtx := .vlam sourceType `type (.sort .zero) (.sort .zero) .default .nil
private def source : MLCtx := .vlam sourceValue `value (.fvar sourceType) (.bvar 0) .default sourceFirst
private def targetFirst : MLCtx := .vlam targetType `type betaDomain betaSemantic .default .nil
private def target : MLCtx := .vlam targetValue `value (.fvar targetType) (.bvar 0) .default targetFirst
private def sourceIdentifiers : List FVarId := [sourceType, sourceValue]
private def targetIdentifiers : List FVarId := [targetType, targetValue]

private theorem environmentWF : VEnv.empty.WF := ⟨[], .empty⟩

private theorem sortTyping (context : List VExpr) (level : VLevel) (valid : level.WF 0) :
    VEnv.empty.HasType 0 context (.sort level) (.sort (.succ level)) := .sortDF valid valid rfl

private theorem betaTranslation : TrExprS VEnv.empty [] [] betaDomain betaSemantic :=
  .app (.lam (sortTyping [] (.succ .zero) (by trivial)) (.bvar .zero))
    (sortTyping [] .zero (by trivial))
    (.lam ⟨_, sortTyping [] (.succ .zero) (by trivial)⟩ (.sort rfl) (.bvar rfl)) (.sort rfl)

private theorem betaEquality : VEnv.empty.IsDefEq 0 [] betaSemantic (.sort .zero) (.sort (.succ .zero)) :=
  .beta (.bvar .zero) (sortTyping [] .zero (by trivial))

private theorem sourceWellFormed : source.WF VEnv.empty [] := by
  have first : sourceFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      .sort rfl, _, sortTyping [] .zero (by trivial)⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [sourceFirst, sourceType, sourceValue]),
    .fvar rfl, _, .bvar .zero⟩

private theorem targetWellFormed : target.WF VEnv.empty [] := by
  have first : targetFirst.WF VEnv.empty [] :=
    ⟨trivial, (TrLCtx.nil (env := VEnv.empty) (Us := [])).find?_eq_none.mpr (by simp),
      betaTranslation, _, betaEquality.hasType.1⟩
  have converted : VEnv.empty.HasType 0 targetFirst.vlctx.toCtx (.bvar 0) (.sort .zero) := by
    have equality := betaEquality.weak environmentWF.ordered (B := betaSemantic)
    simpa [betaSemantic, VExpr.lift, VExpr.liftN] using VEnv.IsDefEq.defeqDF equality (VEnv.IsDefEq.bvar Lookup.zero)
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [targetFirst, targetType, targetValue]),
    .fvar rfl, _, converted⟩

private theorem sourcePrefix : ParameterPrefix .nil source sourceIdentifiers := .snoc (.snoc .nil)
private theorem targetPrefix : ParameterPrefix .nil target targetIdentifiers := .snoc (.snoc .nil)

private def checker : TypeChecker.VContext :=
  { TypeChecker.VContext.mk' (VEnvs.WF.empty `HeaderDomainFixture) .safe [] {} with
    lctx := source.lctx, mlctx := source, mlctx_wf := sourceWellFormed, lctx_eq := rfl }

private theorem namesReserved : ∀ identifier ∈ checker.vlctx.fvars,
    ({} : TypeChecker.VState).ngen.Reserves identifier := by
  intro identifier member position equality
  change identifier ∈ [sourceValue, sourceType] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  obtain rfl | rfl := member <;> cases equality

private theorem initialWellFormed : ({} : TypeChecker.VState).WF checker where
  trctx := sourceWellFormed.tr
  ngen_wf := namesReserved
  ectx := ⟨checker.vlctx, .refl, checker.Δwf, .refl, .empty, namesReserved⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

private def reader : AddInductive.Context :=
  { env := Kernel.Environment.empty `HeaderDomainFixture, lctx := source.lctx, lparams := [], safety := .safe,
    allowPrimitive := false }

private def stats : InductiveStats :=
  { levels := [], resultLevel := .zero, indConsts := #[.const `AlreadyCheckedHeader []],
    params := (sourceIdentifiers.map Expr.fvar).toArray, isNotZero := false }

private def targetBody : Expr := .forallE `value (.fvar sourceType) (.sort .zero) .default
private def targetTelescope : Expr :=
  .forallE `type betaDomain (.forallE `value (.bvar 0) (.sort .zero) .default) .default

private theorem firstStoredType : getType stats.params[0]! reader = .ok (.sort .zero) := by
  change Except.ok (source.lctx.get! sourceType).type = (.ok (.sort .zero) : Except Kernel.Exception Expr)
  simp only [LocalContext.get!, sourceWellFormed.find?_eq]
  simp [MLCtx.decls, source, sourceFirst, sourceType, sourceValue, List.find?, LocalDecl.fvarId, LocalDecl.type]

private theorem secondStoredType : getType stats.params[1]! reader = .ok (.fvar sourceType) := by
  change Except.ok (source.lctx.get! sourceValue).type = (.ok (.fvar sourceType) : Except Kernel.Exception Expr)
  simp only [LocalContext.get!, sourceWellFormed.find?_eq]
  simp [MLCtx.decls, source, sourceFirst, sourceType, sourceValue, LocalDecl.fvarId, LocalDecl.type]

private theorem firstReceipt : ReducedParameterDomainReceipt VEnv.empty [] reader betaDomain
    (.sort .zero) [] (.sort .zero) betaSemantic :=
  ⟨checker, [], .skipN .refl 2, .succ .zero, rfl, rfl, rfl, rfl, sourcePrefix.insertion,
    .sort rfl, betaTranslation, sortTyping [] .zero (by trivial), initialWellFormed⟩

private theorem secondReceipt : ReducedParameterDomainReceipt VEnv.empty [] reader (.fvar sourceType)
    (.fvar sourceType) sourceFirst.vlctx.toCtx (.bvar 0) (.bvar 0) :=
  ⟨checker, sourceFirst.vlctx, .skipN .refl 1, .zero, rfl, rfl, rfl, rfl,
    .skip_fvar _ _ .refl, .fvar rfl, .fvar rfl, .bvar .zero, initialWellFormed⟩

private theorem unequalDomains : source.vlctx.toCtx ≠ target.vlctx.toCtx := by
  simp [source, target, sourceFirst, targetFirst, betaSemantic, VLCtx.toCtx]

private theorem nativeTrace
    (firstAccepted : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool)
      reader = .ok true)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (firstNormalized : (monadLift (TypeChecker.whnf
      ((.forallE `value (.bvar 0) (.sort .zero) .default : Expr).instantiate1 (.fvar sourceType)))
      : AddInductive.M Expr) reader = .ok targetBody)
    (secondNormalized : (monadLift (TypeChecker.whnf
      ((.sort .zero : Expr).instantiate1 (.fvar sourceValue))) : AddInductive.M Expr)
      reader = .ok (.sort .zero)) :
    CheckedHeaderTrace 2 stats targetTelescope 0 0 reader (.sort .zero) stats 0 reader :=
  .reusedParameter (by decide) (by decide) firstStoredType firstAccepted firstNormalized
    (.reusedParameter (by decide) (by decide) secondStoredType secondAccepted secondNormalized
      (.stop (by intro name domain body binder equality; cases equality) rfl))

private theorem acceptedDomainsAggregate
    (firstAccepted : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool)
      reader = .ok true)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (firstNormalized : (monadLift (TypeChecker.whnf
      ((.forallE `value (.bvar 0) (.sort .zero) .default : Expr).instantiate1 (.fvar sourceType)))
      : AddInductive.M Expr) reader = .ok targetBody)
    (secondNormalized : (monadLift (TypeChecker.whnf
      ((.sort .zero : Expr).instantiate1 (.fvar sourceValue))) : AddInductive.M Expr)
      reader = .ok (.sort .zero)) :
    CheckedHeaderDomainReceipts VEnv.empty [] 2
      (nativeTrace firstAccepted secondAccepted firstNormalized secondNormalized)
      [] [] source.vlctx.toCtx target.vlctx.toCtx :=
  .reusedParameter (by decide) (by decide) firstStoredType firstAccepted firstNormalized firstReceipt
    (.reusedParameter (name := `value) (binder := .default) (body := .sort .zero)
      (by decide) (by decide) secondStoredType secondAccepted secondNormalized secondReceipt
      (.stop (by intro name domain body binder equality; cases equality) rfl))

private theorem aggregateProducesEquivalence
    {trace : CheckedHeaderTrace 2 stats targetTelescope 0 0 reader (.sort .zero) stats 0 reader}
    (model : CheckedHeaderDomainReceipts VEnv.empty [] 2 trace [] []
      source.vlctx.toCtx target.vlctx.toCtx) :
    VEnv.empty.IsDefEqCtx 0 [] source.vlctx.toCtx target.vlctx.toCtx ∧
      source.vlctx.toCtx.length = 2 ∧ target.vlctx.toCtx.length = 2 :=
  ⟨model.agreement .zero, by simpa using model.growth.1, by simpa using model.growth.2⟩

private theorem zeroPrefixKeepsBase (base : List VExpr) :
    ∃ trace : CheckedHeaderTrace 0 stats (.sort .zero) 0 0 reader (.sort .zero) stats 0 reader,
      CheckedHeaderDomainReceipts VEnv.empty [] 0 trace base base base base :=
  ⟨.stop (by intro name domain body binder equality; cases equality) rfl,
    .stop (by intro name domain body binder equality; cases equality) rfl⟩

private theorem firstStepStrengthens
    (accepted : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool)
      reader = .ok true) :
    ∃ level, VEnv.empty.IsDefEq 0 [] (.sort .zero) betaSemantic (.sort level) :=
  firstReceipt.accepted accepted

private theorem secondStepStrengthens
    (accepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true) :
    ∃ level, VEnv.empty.IsDefEq 0 sourceFirst.vlctx.toCtx (.bvar 0) (.bvar 0) (.sort level) :=
  secondReceipt.accepted accepted

private theorem indexRetainsDomainContexts (baseSource baseTarget : List VExpr)
    (normalized : (monadLift (TypeChecker.whnf
      ((.sort .zero : Expr).instantiate1 (.fvar ⟨reader.ngen.curr⟩))) : AddInductive.M Expr)
      (recursorIndexContext reader `index .default (.sort .zero)) = .ok (.sort .zero)) :
    ∃ trace : CheckedHeaderTrace 2 stats (.forallE `index (.sort .zero) (.sort .zero) .default)
      2 0 reader (.sort .zero) stats 1 (recursorIndexContext reader `index .default (.sort .zero)),
      CheckedHeaderDomainReceipts VEnv.empty [] 2 trace baseSource baseTarget baseSource baseTarget :=
  ⟨.index (by decide) normalized (.stop (by intro name domain body binder equality; cases equality) rfl),
    .index (by decide) normalized (.stop (by intro name domain body binder equality; cases equality) rfl)⟩

private def family : Expr := .lam `argument (.fvar sourceType) (.fvar sourceType) .default

private theorem aggregateRebindsNonSort
    {trace : CheckedHeaderTrace 2 stats targetTelescope 0 0 reader (.sort .zero) stats 0 reader}
    (model : CheckedHeaderDomainReceipts VEnv.empty [] 2 trace [] []
      source.vlctx.toCtx target.vlctx.toCtx)
    (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (replaceParams (targetIdentifiers.map Expr.fvar).toArray family
      (sourceIdentifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        Closed returned.1 0 ∧
        ∃ semantic, TrExprS VEnv.empty [] target.vlctx returned.1 semantic ∧
          VEnv.empty.HasType 0 target.vlctx.toCtx semantic (.forallE (.bvar 1) (.sort .zero)) := by
  have translated : TrExprS VEnv.empty [] source.vlctx family (.lam (.bvar 1) (.bvar 2)) :=
    .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl) (.fvar rfl)
  have typed : VEnv.empty.HasType 0 source.vlctx.toCtx (.lam (.bvar 1) (.bvar 2))
      (.forallE (.bvar 1) (.sort .zero)) :=
    .lam (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))
  exact (model.rebindPrefix environmentWF sourceWellFormed targetWellFormed
    sourcePrefix targetPrefix translated typed nativeEnv state).mono
      fun _ ⟨_, _, closed, _, _, semantic, translated, typed⟩ => ⟨closed, semantic, translated, typed⟩

private def runtimeControls : MetaM Unit := do
  let mut checks := 0
  for fuel in [4, 32] do
    let actualReader := { reader with fuel := { inductiveFuel := fuel, recDepth := 256 } }
    let .ok (terminal, finished, count) := checkInductiveTypes.loopInd.loop 2 stats targetTelescope 0 0 fuel
        (fun terminal finished count => pure (terminal, finished, count)) actualReader
      | throwError "actual reused-header loop rejected equivalent dependent domains"
    unless terminal == .sort .zero && count == 0 && finished.params == stats.params do
      throwError "actual reused-header loop changed its endpoint or parameter identities"
    checks := checks + 3
    let .ok true := (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool) actualReader
      | throwError "first actual checker call rejected nonliteral domains"
    let .ok true := (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
        actualReader | throwError "second actual checker call rejected dependent domains"
    let .ok firstNormalized := (monadLift (TypeChecker.whnf
        ((.forallE `value (.bvar 0) (.sort .zero) .default : Expr).instantiate1 (.fvar sourceType)))
        : AddInductive.M Expr) actualReader | throwError "actual first normalization failed"
    let .ok secondNormalized := (monadLift (TypeChecker.whnf
        ((.sort .zero : Expr).instantiate1 (.fvar sourceValue))) : AddInductive.M Expr) actualReader
      | throwError "actual second normalization failed"
    unless firstNormalized == targetBody && secondNormalized == .sort .zero do
      throwError "actual normalization receipts do not match the proof fixture"
    checks := checks + 4
    let incompatible := Expr.forallE `type (.sort (.succ .zero))
      (.forallE `value (.bvar 0) (.sort .zero) .default) .default
    match checkInductiveTypes.loopInd.loop 2 stats incompatible 0 0 fuel (fun _ _ _ => pure ()) actualReader with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "actual reused-header loop accepted incompatible domains"
  let indexed := Expr.forallE `index (.sort .zero) (.sort .zero) .default
  let .ok count := checkInductiveTypes.loopInd.loop 2 stats indexed 2 0 2
      (fun _ _ count => pure count) reader | throwError "actual retained-prefix index loop failed"
  unless count == 1 do throwError "index counted as another checked parameter"
  checks := checks + 2
  match checkInductiveTypes.loopInd.loop 2 stats targetTelescope 0 0 2 (fun _ _ _ => pure ()) reader with
  | .error .deepRecursion => checks := checks + 1
  | _ => throwError "insufficient header fuel did not reject"
  unless sourceIdentifiers.toArray != targetIdentifiers.toArray &&
      (source.lctx.get! sourceType).type != (target.lctx.get! targetType).type do
    throwError "independent nonliteral contexts accidentally coincide"
  checks := checks + 1
  let initial : ElimNestedInductive.State := { newTypes := #[], lvls := [] }
  let .ok (rebound, final) := replaceParams (targetIdentifiers.map Expr.fvar).toArray family
      (sourceIdentifiers.map Expr.fvar).toArray reader.env initial
    | throwError "actual aggregate boundary replacement failed"
  unless rebound == .lam `argument (.fvar targetType) (.fvar targetType) .default &&
      !rebound.hasLooseBVars && final.ngen.idx == initial.ngen.idx &&
      final.ngen.namePrefix == initial.ngen.namePrefix do
    throwError "actual aggregate boundary replacement changed syntax, scope or state"
  checks := checks + 3
  let .ok sourceFamilyType := (monadLift (TypeChecker.checkType family) : AddInductive.M Expr) reader
    | throwError "actual source family failed full type checking"
  let targetReader := { reader with lctx := target.lctx }
  let .ok targetFamilyType := (monadLift (TypeChecker.checkType rebound) : AddInductive.M Expr) targetReader
    | throwError "actual rebound family failed full type checking"
  unless sourceFamilyType.isForall && targetFamilyType.isForall do
    throwError "actual family typing lost the non-sort result"
  let .ok true := (monadLift (TypeChecker.isDefEq targetFamilyType
      (.forallE `argument (.fvar targetType) (.sort .zero) .default)) : AddInductive.M Bool) targetReader
    | throwError "actual target family type not equivalent to the proved result type"
  checks := checks + 4
  unless checks == 27 do throwError "header domain agreement runtime manifest changed: {checks}"
  logInfo m!"header domain agreement runtime: {checks} dependent, nonliteral, reused-header, index, fuel, state and negative controls"

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "unexpected header-domain dependency {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} dependencies = {repr dependencies}"

private def auditExact (name : Name) (expected : List Name) : MetaM Unit := do
  audit name expected
  let dependencies ← collectAxioms name
  unless dependencies.size == expected.length do
    throwError "header-domain exact dependency manifest changed for {name}: {dependencies.size}"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let receipts := inherited ++ [``PersistentHashMap.WF.find?_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.toList'_insert, ``PersistentHashMap.findAux_isSome, ``Expr.eqv_eq,
    ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq]
  let checker := receipts ++ [``Lean4Lean.ptrEqExpr_eq, ``Expr.looseBVarRange_eq,
    ``Expr.instantiateRev_eq, ``Expr.instantiate_eq, ``Expr.replace_eq, ``Level.hasParam_eq,
    ``Expr.hasLevelParam_eq, ``Level.hasMVar_eq, ``Lean4Lean.ptrEqConstantInfo_eq,
    ``Expr.instantiateRange_eq, ``Expr.instantiate1_eq, `Lean.Expr.mkAppRangeAux.eq_def,
    ``Expr.abstractRange_eq, ``Expr.abstract_eq, ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq,
    ``Expr.instantiateRevRange_eq]
  let allowed := checker
  for name in [``ReducedParameterDomainReceipt.accepted, ``CheckedHeaderDomainReceipts.agreement,
      ``CheckedHeaderDomainReceipts.growth, ``checkInductiveTypes.loopInd.loop.scopedDomainAgreement,
      ``CheckedHeaderDomainReceipts.rebindPrefix, ``firstReceipt, ``secondReceipt,
      ``acceptedDomainsAggregate, ``aggregateProducesEquivalence, ``firstStepStrengthens,
      ``secondStepStrengthens, ``aggregateRebindsNonSort] do audit name allowed
  audit ``unequalDomains logical
  for name in [``zeroPrefixKeepsBase, ``indexRetainsDomainContexts,
      ``CheckedHeaderDomainReceipts.growth] do audit name allowed
  for name in [``TypeChecker.isDefEq.WF, ``ReducedParameterDomainReceipt.accepted,
      ``CheckedHeaderDomainReceipts.agreement, ``checkInductiveTypes.loopInd.loop.scopedDomainAgreement,
      ``CheckedHeaderDomainReceipts.rebindPrefix, ``aggregateProducesEquivalence,
      ``firstStepStrengthens, ``secondStepStrengthens, ``aggregateRebindsNonSort] do auditExact name checker
  for name in [``firstReceipt, ``secondReceipt, ``acceptedDomainsAggregate] do auditExact name receipts
  for name in [``CheckedHeaderDomainReceipts.growth, ``zeroPrefixKeepsBase,
      ``indexRetainsDomainContexts] do auditExact name inherited
  auditExact ``unequalDomains [``propext]
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveHeaderDomainAgreement
    | throwError "header-domain module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new header-domain axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected header-domain module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveHeaderDomainAgreementTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected header-domain fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"header domain agreement exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 22 do throwError "header-domain module manifest changed: {moduleCount}"
  unless fixtureCount == 69 do throwError "header-domain fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveHeaderDomainAgreementTest
