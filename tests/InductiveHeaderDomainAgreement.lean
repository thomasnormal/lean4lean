import Lean4Lean.Verify.InductiveConstructorPrefixReceipts
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

namespace InductiveConstructorDomainTraceTest
open InductiveHeaderDomainAgreementTest

inductive DependentProbe (proposition : Prop) (value : proposition) : Prop where
  | intro : DependentProbe proposition value

private def constructorTerminal : Expr :=
  mkApp2 stats.indConsts[0]! (.fvar sourceType) (.fvar sourceValue)

private def constructorType : Expr :=
  .forallE `type betaDomain
    (.forallE `value (.bvar 0) (mkApp2 stats.indConsts[0]! (.bvar 1) (.bvar 0)) .default) .default

private theorem secondNativeTrace (isUnsafe : Bool)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (valid : isValidIndAppIdx stats constructorTerminal 0 = true) :
    AcceptedConstructorTrace stats isUnsafe 0 reader 1
      (.forallE `value (.fvar sourceType) (mkApp2 stats.indConsts[0]! (.fvar sourceType) (.bvar 0)) .default)
      reader 2 constructorTerminal := by
  refine .parameter (parameter := .fvar sourceValue) (by rfl) secondStoredType secondAccepted ?_
  simp only [Expr.instantiate1_eq]
  exact .terminal (by rfl) valid

private theorem acceptedTrace
    (isUnsafe : Bool)
    (firstAccepted : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool)
      reader = .ok true)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (valid : isValidIndAppIdx stats constructorTerminal 0 = true) :
    AcceptedConstructorTrace stats isUnsafe 0 reader 0 constructorType reader 2 constructorTerminal := by
  refine .parameter (parameter := .fvar sourceType) (by rfl) firstStoredType firstAccepted ?_
  simp only [Expr.instantiate1_eq]
  exact secondNativeTrace isUnsafe secondAccepted valid

private theorem acceptedReceiptModel
    (isUnsafe : Bool)
    (firstAccepted : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool)
      reader = .ok true)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (valid : isValidIndAppIdx stats constructorTerminal 0 = true) :
    CheckedConstructorDomainReceipts VEnv.empty [] (acceptedTrace isUnsafe firstAccepted secondAccepted valid)
      [] [] source.vlctx.toCtx target.vlctx.toCtx := by
  refine .parameter (parameter := .fvar sourceType)
    (trace := by
      simp only [Expr.instantiate1_eq]
      exact secondNativeTrace isUnsafe secondAccepted valid)
    (by rfl) firstStoredType firstAccepted firstReceipt ?_
  simp only [Expr.instantiate1_eq]
  refine .parameter (stats := stats) (index := 1) (parameter := .fvar sourceValue)
    (name := `value) (binder := .default)
    (body := mkApp2 stats.indConsts[0]! (.fvar sourceType) (.bvar 0))
    (trace := by
      simp only [Expr.instantiate1_eq]
      exact .terminal (by rfl) valid)
    (by rfl) secondStoredType secondAccepted secondReceipt ?_
  simp only [Expr.instantiate1_eq]
  exact .terminal (source := source.vlctx.toCtx) (target := target.vlctx.toCtx) (by rfl) valid

private theorem aggregatedDomains
    {isUnsafe : Bool}
    {trace : AcceptedConstructorTrace stats isUnsafe 0 reader 0 constructorType reader 2 constructorTerminal}
    (model : CheckedConstructorDomainReceipts VEnv.empty [] trace [] []
      source.vlctx.toCtx target.vlctx.toCtx) :
    VEnv.empty.IsDefEqCtx 0 [] source.vlctx.toCtx target.vlctx.toCtx ∧
      source.vlctx.toCtx.length = 2 ∧ target.vlctx.toCtx.length = 2 :=
  ⟨model.agreement .zero, by simpa [stats] using model.completeGrowth (by decide) |>.1,
    by simpa [stats] using model.completeGrowth (by decide) |>.2⟩

private theorem rawTerminalKeepsZeroChecks (isUnsafe : Bool) (baseSource baseTarget : List VExpr)
    (valid : isValidIndAppIdx stats constructorTerminal 0 = true) :
    ∃ trace : AcceptedConstructorTrace stats isUnsafe 0 reader 0 constructorTerminal reader 0 constructorTerminal,
      CheckedConstructorDomainReceipts VEnv.empty [] trace baseSource baseTarget baseSource baseTarget :=
  ⟨.terminal (by rfl) valid, .terminal (by rfl) valid⟩

private theorem partialPrefixRetainsBase (isUnsafe : Bool)
    (secondAccepted : (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool)
      reader = .ok true)
    (valid : isValidIndAppIdx stats constructorTerminal 0 = true) :
    ∃ trace : AcceptedConstructorTrace stats isUnsafe 0 reader 1
      (.forallE `value (.fvar sourceType) (mkApp2 stats.indConsts[0]! (.fvar sourceType) (.bvar 0)) .default)
      reader 2 constructorTerminal,
      CheckedConstructorDomainReceipts VEnv.empty [] trace sourceFirst.vlctx.toCtx targetFirst.vlctx.toCtx
        source.vlctx.toCtx target.vlctx.toCtx := by
  refine ⟨secondNativeTrace isUnsafe secondAccepted valid, ?_⟩
  refine .parameter (stats := stats) (index := 1) (parameter := .fvar sourceValue)
    (trace := by
      simp only [Expr.instantiate1_eq]
      exact .terminal (by rfl) valid)
    (by rfl) secondStoredType secondAccepted secondReceipt ?_
  simp only [Expr.instantiate1_eq]
  exact .terminal (source := source.vlctx.toCtx) (target := target.vlctx.toCtx) (by rfl) valid

private theorem fieldRetainsCompletePrefix (isUnsafe : Bool) (baseSource baseTarget : List VExpr)
    (checked : (monadLift (TypeChecker.ensureType (.sort .zero)) : AddInductive.M Expr)
      reader = .ok (.sort (.succ .zero)))
    (positive : isUnsafe = false → PositivityTrace stats PositivityWHNF reader (.sort .zero))
    (valid : isValidIndAppIdx stats (constructorTerminal.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) 0 = true) :
    ∃ trace : AcceptedConstructorTrace stats isUnsafe 0 reader 2
      (.forallE `field (.sort .zero) constructorTerminal .default)
      (reader.withPositivityArg `field (.sort .zero) .default) 3
      (constructorTerminal.instantiate1 (.fvar ⟨reader.ngen.curr⟩)),
      CheckedConstructorDomainReceipts VEnv.empty [] trace baseSource baseTarget baseSource baseTarget := by
  have notForall : (constructorTerminal.instantiate1 (.fvar ⟨reader.ngen.curr⟩)).isForall = false := by
    simp only [Expr.instantiate1_eq, constructorTerminal, mkApp2, Expr.instantiate1', Expr.isForall]
  exact ⟨.field (by rfl) checked (by decide) positive (.terminal notForall valid),
    .field (by rfl) checked (by decide) positive (.terminal notForall valid)⟩

private theorem aggregateRebindsFamily
    {isUnsafe : Bool}
    {trace : AcceptedConstructorTrace stats isUnsafe 0 reader 0 constructorType reader 2 constructorTerminal}
    (model : CheckedConstructorDomainReceipts VEnv.empty [] trace [] []
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

private theorem batchRetainsSourceCheck (types : Array InductiveType) (statistics : InductiveStats)
    (isUnsafe : Bool) (ambient : AddInductive.Context)
    (accepted : checkConstructors types statistics isUnsafe ambient = .ok ())
    (parent : Nat) (bound : parent < types.size) (constructor : Constructor)
    (member : constructor ∈ types[parent].ctors) :
    ∃ sourceType finalReader finalIndex terminal,
      (monadLift (TypeChecker.checkType constructor.type) : AddInductive.M Expr) ambient = .ok sourceType ∧
      AcceptedConstructorTrace statistics isUnsafe parent ambient 0 constructor.type finalReader finalIndex terminal :=
  by
    obtain ⟨sourceType, finalReader, finalIndex, terminal, _, sourceChecked, trace⟩ :=
      checkConstructors.acceptedTraces types statistics isUnsafe ambient () accepted parent bound constructor member
    exact ⟨sourceType, finalReader, finalIndex, terminal, sourceChecked, trace⟩

private def runtimeConstructorType (head : Expr) (field : Option Expr := none) : Expr :=
  let result := mkApp2 head (.bvar 1) (.bvar 0)
  let body := match field with
    | none => result
    | some domain => .forallE `field domain (mkApp2 head (.bvar 2) (.bvar 1)) .default
  .forallE `type betaDomain (.forallE `value (.bvar 0) body .default) .default

private def runtimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let head := Expr.const ``DependentProbe []
  let statistics := { stats with indConsts := #[head], nindices := #[0] }
  let ambient := { reader with env := nativeEnv, fuel := { inductiveFuel := 32, recDepth := 256 } }
  let positive := runtimeConstructorType head (some (.sort .zero))
  let negativeDomain := Expr.forallE `argument (mkApp2 head (.bvar 1) (.bvar 0)) (.const ``False []) .default
  let negative := runtimeConstructorType head (some negativeDomain)
  let mut checks := 0
  for isUnsafe in [false, true] do
    for fuel in [4, 32] do
      for type in [runtimeConstructorType head, positive] do
        let .ok () := checkConstructors.loop statistics isUnsafe 0 `AcceptedConstructor type 0 fuel ambient
          | throwError "actual constructor loop rejected nonliteral dependent parameter domains"
        checks := checks + 1
    let constructor : Constructor := { name := `AcceptedConstructor, type := runtimeConstructorType head }
    let fieldConstructor : Constructor := { name := `AcceptedFieldConstructor, type := positive }
    let types : Array InductiveType :=
      #[{
        name := ``DependentProbe
        type := .forallE `type (.sort .zero) (.forallE `value (.bvar 0) (.sort .zero) .default) .default,
        ctors := [constructor, fieldConstructor] }]
    let .ok () := checkConstructors types statistics isUnsafe ambient
      | throwError "actual checked constructor batch rejected matching dependent domains"
    checks := checks + 1
    let duplicate := #[{ types[0]! with ctors := [constructor, constructor] }]
    match checkConstructors duplicate statistics isUnsafe ambient with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "actual constructor batch accepted duplicate names"
    let openResult := mkApp2 head (.fvar sourceType) (.fvar sourceValue)
    let .ok () := checkConstructors.loop statistics isUnsafe 0 `OpenLoop openResult 0 1 ambient
      | throwError "raw terminal control unexpectedly required prior parameter checks"
    checks := checks + 1
    let openSource := #[{ types[0]! with ctors := [{ name := `RejectedOpenSource, type := openResult }] }]
    match checkConstructors openSource statistics isUnsafe ambient with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "outer constructor source guard accepted the open raw-loop control"
    let partialType := Expr.forallE `value (.fvar sourceType) (mkApp2 head (.fvar sourceType) (.bvar 0)) .default
    let .ok () := checkConstructors.loop statistics isUnsafe 0 `PartialLoop partialType 1 2 ambient
      | throwError "retained-base partial parameter check failed"
    checks := checks + 1
    for fuel in [0, 1, 2] do
      match checkConstructors.loop statistics isUnsafe 0 `FuelControl (runtimeConstructorType head) 0 fuel ambient with
      | .error .deepRecursion => checks := checks + 1
      | _ => throwError "constructor parameter fuel control changed"
    let incompatible := Expr.forallE `type (.sort (.succ .zero))
      (.forallE `value (.bvar 0) (mkApp2 head (.bvar 1) (.bvar 0)) .default) .default
    match checkConstructors.loop statistics isUnsafe 0 `Mismatch incompatible 0 32 ambient with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "constructor loop accepted incompatible parameter universes"
    match checkConstructors.loop statistics isUnsafe 0 `Negative negative 0 32 ambient with
    | .ok () =>
      unless isUnsafe do throwError "safe constructor loop skipped negative positivity"
      checks := checks + 1
    | .error _ =>
      if isUnsafe then throwError "unsafe constructor loop unexpectedly enforced positivity"
      checks := checks + 1
  let .ok stored := getType statistics.params[0]! ambient | throwError "actual stored-domain lookup failed"
  let .ok true := (monadLift (TypeChecker.isDefEq betaDomain stored) : AddInductive.M Bool) ambient
    | throwError "actual retained first-domain checker result was not true"
  let .ok dependent := getType statistics.params[1]! ambient | throwError "actual dependent-domain lookup failed"
  let .ok true := (monadLift (TypeChecker.isDefEq (.fvar sourceType) dependent) : AddInductive.M Bool) ambient
    | throwError "actual retained dependent-domain checker result was not true"
  unless stored == .sort .zero && dependent == .fvar sourceType && stored != betaDomain do
    throwError "native retained lookup/check pairs collapsed or changed"
  checks := checks + 5
  unless checks == 33 do throwError "constructor-domain runtime manifest changed: {checks}"
  logInfo m!"constructor domain trace runtime: {checks} dependent, nonliteral, safe/unsafe, fields, batch, retained-base, truncated-loop, fuel and negative controls"

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
  for name in [``AcceptedConstructorTrace.index_le, ``AcceptedConstructorTrace.safe,
      ``checkConstructors.loop.acceptedTrace,
      ``InductiveStats.AcceptedConstructorTraces.safe, ``checkConstructors.acceptedTraces,
      ``batchRetainsSourceCheck] do audit name logical
  audit ``AcceptedConstructorTrace.scope
    (logical ++ [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
      ``PersistentHashMap.WF.toList'_insert])
  for name in [``CheckedConstructorDomainReceipts.agreement, ``CheckedConstructorDomainReceipts.growth,
      ``CheckedConstructorDomainReceipts.completeGrowth, ``CheckedConstructorDomainReceipts.rebindPrefix,
      ``checkConstructors.domainAgreement,
      ``acceptedTrace, ``acceptedReceiptModel, ``aggregatedDomains, ``rawTerminalKeepsZeroChecks,
      ``partialPrefixRetainsBase, ``fieldRetainsCompletePrefix, ``aggregateRebindsFamily] do audit name checker
  for name in [``AcceptedConstructorTrace.index_le, ``AcceptedConstructorTrace.safe,
      ``checkConstructors.loop.acceptedTrace, ``InductiveStats.AcceptedConstructorTraces.safe,
      ``checkConstructors.acceptedTraces, ``batchRetainsSourceCheck] do auditExact name logical
  auditExact ``AcceptedConstructorTrace.scope
    (logical ++ [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
      ``PersistentHashMap.WF.toList'_insert])
  for name in [``CheckedConstructorDomainReceipts.agreement, ``CheckedConstructorDomainReceipts.rebindPrefix,
      ``checkConstructors.domainAgreement, ``aggregatedDomains, ``aggregateRebindsFamily] do auditExact name checker
  for name in [``CheckedConstructorDomainReceipts.growth, ``CheckedConstructorDomainReceipts.completeGrowth,
      ``rawTerminalKeepsZeroChecks] do auditExact name inherited
  auditExact ``acceptedTrace
    (inherited ++ [``PersistentHashMap.WF.find?_eq, ``PersistentArray.toList'_push,
      ``PersistentHashMap.WF.toList'_insert, ``Expr.instantiate1_eq])
  for name in [``acceptedReceiptModel, ``partialPrefixRetainsBase] do
    auditExact name (receipts ++ [``Expr.instantiate1_eq])
  auditExact ``fieldRetainsCompletePrefix (inherited ++ [``Expr.instantiate1_eq])
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorDomainTrace
    | throwError "constructor-domain module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new constructor-domain axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless checker.contains dependency do throwError "unexpected constructor-domain module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveConstructorDomainTraceTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless checker.contains dependency do throwError "unexpected constructor-domain fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"constructor domain trace exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 51 do throwError "constructor-domain module manifest changed: {moduleCount}"
  unless fixtureCount == 26 do throwError "constructor-domain fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveConstructorDomainTraceTest

namespace InductiveConstructorDomainReceiptTest
open InductiveHeaderDomainAgreementTest
open InductiveConstructorDomainTraceTest

private theorem canonicalFirstDomain :
    ∃ smaller nativeDomain semanticDomain insertion,
      ParameterPrefix .nil smaller [] ∧ smaller.WF VEnv.empty [] ∧
      VLCtx.FVLift' smaller.vlctx source.vlctx 0 insertion 0 ∧
      TrExprS VEnv.empty [] smaller.vlctx nativeDomain semanticDomain ∧
      VEnv.empty.IsType 0 smaller.vlctx.toCtx semanticDomain ∧
      ∃ declaration, source.lctx.find? sourceType = some declaration ∧ declaration.type = nativeDomain := by
  simpa using sourcePrefix.selectedDomain sourceWellFormed (index := 0) (identifier := sourceType) (by rfl)

private theorem canonicalDependentDomain :
    ∃ smaller nativeDomain semanticDomain insertion,
      ParameterPrefix .nil smaller [sourceType] ∧ smaller.WF VEnv.empty [] ∧
      VLCtx.FVLift' smaller.vlctx source.vlctx 0 insertion 0 ∧
      TrExprS VEnv.empty [] smaller.vlctx nativeDomain semanticDomain ∧
      VEnv.empty.IsType 0 smaller.vlctx.toCtx semanticDomain ∧
      ∃ declaration, source.lctx.find? sourceValue = some declaration ∧ declaration.type = nativeDomain := by
  simpa [sourceIdentifiers] using
    sourcePrefix.selectedDomain sourceWellFormed (index := 1) (identifier := sourceValue) (by rfl)

private theorem firstReceiptFromCheckedSource {result : Expr}
    (accepted : (monadLift (TypeChecker.checkType targetTelescope) : AddInductive.M Expr) reader = .ok result) :
    ∃ storedSemantic candidateSemantic,
      ReducedParameterDomainReceipt VEnv.empty [] reader betaDomain (.sort .zero)
        [] storedSemantic candidateSemantic := by
  obtain ⟨smaller, storedSemantic, candidateSemantic, history, receipt⟩ :=
    ReducedParameterDomainReceipt.ofCheckedForall checker reader rfl initialWellFormed sourcePrefix
      (index := 0) (identifier := sourceType) (by rfl) firstStoredType
      (by simp [FVarsIn, betaDomain, Level.hasMVar'])
      (by simp [FVarsIn, sourceIdentifiers, betaDomain, Level.hasMVar']) accepted
  have sameContext : smaller = .nil := by simpa using history.drop
  subst smaller
  exact ⟨storedSemantic, candidateSemantic, receipt⟩

private theorem dependentReceiptFromCheckedSource {result : Expr}
    (accepted : (monadLift (TypeChecker.checkType targetBody) : AddInductive.M Expr) reader = .ok result) :
    ∃ smaller storedSemantic candidateSemantic,
      ParameterPrefix .nil smaller [sourceType] ∧
      ReducedParameterDomainReceipt VEnv.empty [] reader (.fvar sourceType) (.fvar sourceType)
        smaller.vlctx.toCtx storedSemantic candidateSemantic := by
  simpa [sourceIdentifiers] using
    ReducedParameterDomainReceipt.ofCheckedForall checker reader rfl initialWellFormed sourcePrefix
      (index := 1) (identifier := sourceValue) (by rfl) secondStoredType
      (by simp [FVarsIn, checker, source, sourceFirst, Level.hasMVar'])
      (by simp [FVarsIn, sourceIdentifiers]) accepted

private theorem checkedSourceProducesEquality {result : Expr}
    (checked : (monadLift (TypeChecker.checkType targetTelescope) : AddInductive.M Expr) reader = .ok result)
    (equal : (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool) reader = .ok true) :
    ∃ storedSemantic candidateSemantic level,
      VEnv.empty.IsDefEq 0 [] storedSemantic candidateSemantic (.sort level) := by
  obtain ⟨storedSemantic, candidateSemantic, receipt⟩ := firstReceiptFromCheckedSource checked
  obtain ⟨level, equality⟩ := receipt.accepted equal
  exact ⟨storedSemantic, candidateSemantic, level, equality⟩

private theorem retainedBaseReceiptFromCheckedSource {result : Expr}
    (accepted : (monadLift (TypeChecker.checkType targetBody) : AddInductive.M Expr) reader = .ok result) :
    ∃ storedSemantic candidateSemantic,
      ReducedParameterDomainReceipt VEnv.empty [] reader (.fvar sourceType) (.fvar sourceType)
        sourceFirst.vlctx.toCtx storedSemantic candidateSemantic := by
  have parameters : ParameterPrefix sourceFirst source [sourceValue] := .snoc .nil
  obtain ⟨smaller, storedSemantic, candidateSemantic, history, receipt⟩ :=
    ReducedParameterDomainReceipt.ofCheckedForall checker reader rfl initialWellFormed parameters
      (index := 0) (identifier := sourceValue) (by rfl) secondStoredType
      (by simp [FVarsIn, checker, source, sourceFirst, Level.hasMVar'])
      (by simp [FVarsIn, sourceFirst]) accepted
  have sameContext : smaller = sourceFirst := by simpa using history.drop
  subst smaller
  exact ⟨storedSemantic, candidateSemantic, receipt⟩

private theorem emptyPrefixRejectsCandidateDependency :
    ¬ ∃ semantic, TrExprS VEnv.empty [] [] (.fvar sourceType) semantic := by
  rintro ⟨semantic, translated⟩
  have supported := translated.fvarsIn
  simp [FVarsIn] at supported

private theorem actualTraceProducesFirstReceipt {result : Expr}
    (sourceGuard : reader.env.checkNoMVarNoFVar `Constructor constructorType = .ok ())
    (sourceChecked : (monadLift (TypeChecker.checkType constructorType) : AddInductive.M Expr) reader = .ok result)
    {isUnsafe : Bool} {finalReader : AddInductive.Context} {finalIndex : Nat} {terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe 0 reader 0 constructorType finalReader finalIndex terminal) :
    ∃ stored storedSemantic candidateSemantic,
      getType (.fvar sourceType) reader = .ok stored ∧
      (monadLift (TypeChecker.isDefEq betaDomain stored) : AddInductive.M Bool) reader = .ok true ∧
      ReducedParameterDomainReceipt VEnv.empty [] reader betaDomain stored [] storedSemantic candidateSemantic ∧
      ∃ level, VEnv.empty.IsDefEq 0 [] storedSemantic candidateSemantic (.sort level) :=
  trace.firstDomainAgreement checker reader rfl initialWellFormed sourcePrefix rfl (by rfl) sourceGuard sourceChecked

private def runtimeControls : MetaM Unit := do
  let mut checks := 0
  for type in [targetTelescope, targetBody] do
    let .ok result := (monadLift (TypeChecker.checkType type) : AddInductive.M Expr) reader
      | throwError "accepted source-check receipt control failed"
    unless result.isSort do throwError "source-check receipt control did not infer a sort"
    checks := checks + 1
  for position in [0, 1] do
    let identifier := sourceIdentifiers[position]!
    let .ok stored := getType (.fvar identifier) reader
      | throwError "canonical selected-domain lookup failed"
    let expected := if position == 0 then Expr.sort .zero else Expr.fvar sourceType
    unless stored == expected do throwError "canonical lookup selected the wrong parameter domain"
    checks := checks + 1
  let .ok true := (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool) reader
    | throwError "checked nonliteral candidate domain failed equality"
  checks := checks + 1
  for type in [Expr.forallE `bad (.bvar 0) (.sort .zero) .default,
      Expr.forallE `bad (.fvar sourceValue) (.sort .zero) .default] do
    match (monadLift (TypeChecker.checkType type) : AddInductive.M Expr) reader with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "source-check receipt accepted an ill-typed candidate domain"
  let nativeEnv := (← getEnv).toKernelEnv
  let head := Expr.const ``DependentProbe []
  let statistics := { stats with indConsts := #[head], nindices := #[0] }
  let ambient := { reader with env := nativeEnv, fuel := { inductiveFuel := 32, recDepth := 256 } }
  let constructor : Constructor := { name := `CheckedFirstDomain, type := runtimeConstructorType head }
  let types : Array InductiveType :=
    #[{ name := ``DependentProbe, type := targetTelescope, ctors := [constructor] }]
  for isUnsafe in [false, true] do
    let .ok () := checkConstructors types statistics isUnsafe ambient
      | throwError "accepted whole-batch first-domain receipt control failed"
    let .ok () := ambient.env.checkNoMVarNoFVar constructor.name constructor.type
      | throwError "retained accepted-batch source guard failed"
    let .ok _ := (monadLift (TypeChecker.checkType constructor.type) : AddInductive.M Expr) ambient
      | throwError "retained accepted-batch source check failed"
    checks := checks + 3
  unless checks == 13 do throwError "constructor first-domain runtime manifest changed: {checks}"
  logInfo m!"constructor first-domain runtime: {checks} source-check, dependent-prefix, safe/unsafe batch and negative controls"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let canonical := inherited ++ [``PersistentHashMap.WF.find?_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.toList'_insert]
  let checker := canonical ++ [``PersistentHashMap.findAux_isSome, ``Expr.eqv_eq,
    ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq, ``Lean4Lean.ptrEqExpr_eq, ``Expr.looseBVarRange_eq,
    ``Expr.instantiateRev_eq, ``Expr.instantiate_eq, ``Expr.replace_eq, ``Level.hasParam_eq,
    ``Expr.hasLevelParam_eq, ``Level.hasMVar_eq, ``Lean4Lean.ptrEqConstantInfo_eq, ``Expr.instantiateRange_eq,
    ``Expr.instantiate1_eq, `Lean.Expr.mkAppRangeAux.eq_def, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``Expr.instantiateRevRange_eq]
  let allowed := checker ++ [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq]
  for name in [``ParameterPrefix.selectedDomain, ``acceptedSourceTranslation,
      ``ReducedParameterDomainReceipt.ofCheckedForall, ``AcceptedConstructorTrace.firstDomainAgreement,
      ``checkConstructors.firstDomainAgreement, ``canonicalFirstDomain, ``canonicalDependentDomain,
      ``firstReceiptFromCheckedSource, ``dependentReceiptFromCheckedSource,
      ``checkedSourceProducesEquality, ``retainedBaseReceiptFromCheckedSource,
      ``emptyPrefixRejectsCandidateDependency, ``actualTraceProducesFirstReceipt] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unexpected constructor first-domain dependency {dependency} in {name}"
    logInfo m!"{name}: {dependencies.size} dependencies = {repr dependencies}"
  for name in [``ParameterPrefix.selectedDomain, ``canonicalFirstDomain, ``canonicalDependentDomain] do
    auditExact name canonical
  for name in [``TypeChecker.checkType.WF, ``TypeChecker.isDefEq.WF, ``acceptedSourceTranslation,
      ``ReducedParameterDomainReceipt.ofCheckedForall, ``firstReceiptFromCheckedSource,
      ``dependentReceiptFromCheckedSource, ``checkedSourceProducesEquality,
      ``retainedBaseReceiptFromCheckedSource] do auditExact name checker
  for name in [``AcceptedConstructorTrace.firstDomainAgreement, ``checkConstructors.firstDomainAgreement,
      ``actualTraceProducesFirstReceipt] do auditExact name allowed
  auditExact ``emptyPrefixRejectsCandidateDependency inherited
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorDomainReceipts
    | throwError "constructor-domain receipt module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new constructor-domain receipt axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected constructor-domain receipt module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveConstructorDomainReceiptTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected constructor-domain receipt fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"constructor first-domain exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 14 do throwError "constructor-domain receipt module manifest changed: {moduleCount}"
  unless fixtureCount == 10 do throwError "constructor-domain receipt fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveConstructorDomainReceiptTest

namespace InductiveConstructorPrefixReceiptTest
open InductiveHeaderDomainAgreementTest

private def family : AxiomVal :=
  { name := `ReceiptFamily, levelParams := [], isUnsafe := false,
    type := .forallE `type (.sort .zero) (.forallE `value (.bvar 0) (.sort .zero) .default) .default }

private def constructorType (field : Bool := false) : Expr :=
  let head := Expr.const family.name []
  let result := if field then
      Expr.forallE `field (.sort .zero) (mkApp2 head (.bvar 2) (.bvar 1)) .default
    else mkApp2 head (.bvar 1) (.bvar 0)
  .forallE `type betaDomain (.forallE `value (.bvar 0) result .default) .default

private def constructors : Array InductiveType :=
  #[{
    name := family.name
    type := family.type
    ctors := [{ name := `ReceiptConstructor, type := constructorType },
      { name := `ReceiptFieldConstructor, type := constructorType true }] }]

private def statistics : InductiveStats :=
  { stats with indConsts := #[.const family.name []], nindices := #[0] }

private theorem sourceWFFor (env : VEnv) : source.WF env [] := by
  have first : sourceFirst.WF env [] :=
    ⟨trivial, (TrLCtx.nil (env := env) (Us := [])).find?_eq_none.mpr (by simp),
      .sort rfl, _, .sortDF (by trivial) (by trivial) rfl⟩
  exact ⟨first, first.tr.find?_eq_none.mpr (by simp [sourceFirst, sourceType, sourceValue]),
    .fvar rfl, _, .bvar .zero⟩

private def fixtureChecker {nativeEnv : Kernel.Environment} {environments : VEnvs}
    (nativeWF : environments.WF nativeEnv) : TypeChecker.VContext :=
  { TypeChecker.VContext.mk' nativeWF .safe [] {} with
    lctx := source.lctx, mlctx := source, mlctx_wf := sourceWFFor _, lctx_eq := rfl }

private theorem fixtureInitialWF {nativeEnv : Kernel.Environment} {environments : VEnvs}
    (nativeWF : environments.WF nativeEnv) : ({} : TypeChecker.VState).WF (fixtureChecker nativeWF) := by
  let checker := fixtureChecker nativeWF
  have reserved : ∀ identifier ∈ checker.vlctx.fvars,
      ({} : TypeChecker.VState).ngen.Reserves identifier := by
    intro identifier member position equality
    change identifier ∈ [sourceValue, sourceType] at member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    obtain rfl | rfl := member <;> cases equality
  exact {
    trctx := checker.mlctx_wf.tr
    ngen_wf := reserved
    ectx := ⟨checker.vlctx, .refl, checker.Δwf, .refl, .empty, reserved⟩
    inferTypeI_wf := .empty
    inferTypeC_wf := .empty
    whnfCore_wf := .empty
    whnf_wf := .empty
    unfold_wf := fun _ => by simp }

private theorem registeredFamilyBatchProducesReceipts
    {nativeEnv : Kernel.Environment}
    (registered : Lean4Lean.addAxiom (Kernel.Environment.empty `PrefixReceiptFixture) family true {} = .ok nativeEnv)
    (isUnsafe : Bool)
    (accepted : checkConstructors constructors statistics isUnsafe { reader with env := nativeEnv } = .ok ()) :
    ∃ environments : VEnvs, ∃ _nativeWF : environments.WF nativeEnv,
      ∀ constructor ∈ constructors[0]!.ctors,
        ∃ finalReader finalIndex terminal finalTarget,
          ∃ trace : AcceptedConstructorTrace statistics isUnsafe 0 { reader with env := nativeEnv }
            0 constructor.type finalReader finalIndex terminal,
          CheckedConstructorDomainReceipts (environments.venv .safe) [] trace
            [] [] source.vlctx.toCtx finalTarget ∧
          (environments.venv .safe).IsDefEqCtx 0 [] source.vlctx.toCtx finalTarget ∧ finalTarget.length = 2 := by
  obtain ⟨environments, nativeWF, _⟩ := addAxiom.WF (VEnvs.WF.empty `PrefixReceiptFixture) family {}
    nativeEnv registered
  refine ⟨environments, nativeWF, ?_⟩
  intro constructor member
  let checker := fixtureChecker nativeWF
  have receipts := checkConstructors.domainReceipts constructors statistics isUnsafe checker
    { reader with env := nativeEnv } rfl (fixtureInitialWF nativeWF) sourcePrefix rfl () accepted
    0 (by decide) constructor member
  simpa [statistics, stats, sourceIdentifiers] using receipts

private theorem canonicalOpeningChangesDependentDomain
    (equal : VEnv.empty.IsDefEq 0 [] (.sort .zero) betaSemantic (.sort (.succ .zero))) :
    ∃ opened, TrExprS VEnv.empty [] sourceFirst.vlctx
      ((Expr.forallE `value (.bvar 0) (.sort .zero) .default).instantiate1 (.fvar sourceType)) opened := by
  have raw : TrExprS VEnv.empty [] [(none, .vlam betaSemantic)]
      (.forallE `value (.bvar 0) (.sort .zero) .default) (.forallE (.bvar 0) (.sort .zero)) :=
    .forallE ⟨_, by
      have equality := betaEquality.weak environmentWF.ordered (B := betaSemantic)
      simpa [betaSemantic, VExpr.lift, VExpr.liftN] using
        VEnv.IsDefEq.defeqDF equality (VEnv.IsDefEq.bvar Lookup.zero)⟩
      ⟨_, sortTyping _ .zero (by trivial)⟩ (.bvar rfl) (.sort rfl)
  exact TrExprS.openCanonicalParameter environmentWF sourceWellFormed.1 raw equal

private theorem completeParametersRequireSourceAbsence
    {statistics : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {ambient finalReader : AddInductive.Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace statistics isUnsafe parent ambient index type finalReader finalIndex terminal)
    (fvars : statistics.ParamsAreFVars) (distinct : statistics.params.toList.Nodup)
    (absent : statistics.RemainingParamsAbsent index type) : statistics.params.size ≤ finalIndex :=
  trace.completeParameters fvars distinct absent

private def runtimeControls : MetaM Unit := do
  let .ok nativeEnv := Lean4Lean.addAxiom (Kernel.Environment.empty `PrefixReceiptFixture) family true {}
    | throwError "verified family registration control failed"
  let ambient := { reader with env := nativeEnv }
  let mut checks := 1
  for isUnsafe in [false, true] do
    let .ok () := checkConstructors constructors statistics isUnsafe ambient
      | throwError "complete dependent constructor-prefix batch failed"
    checks := checks + 1
    for constructor in constructors[0]!.ctors do
      let .ok () := ambient.env.checkNoMVarNoFVar constructor.name constructor.type
        | throwError "complete-prefix source guard failed"
      let .ok _ := (monadLift (TypeChecker.checkType constructor.type) : AddInductive.M Expr) ambient
        | throwError "complete-prefix source check failed"
      let .ok () := checkConstructors.loop statistics isUnsafe 0 constructor.name constructor.type 0 32 ambient
        | throwError "complete-prefix native loop failed"
      checks := checks + 3
    let partialType := Expr.forallE `value (.fvar sourceType)
      (mkApp2 (.const family.name []) (.fvar sourceType) (.bvar 0)) .default
    let .ok () := checkConstructors.loop statistics isUnsafe 0 `Partial partialType 1 2 ambient
      | throwError "dependent partial-loop control failed"
    checks := checks + 1
    let openResult := mkApp2 (.const family.name []) (.fvar sourceType) (.fvar sourceValue)
    let .ok () := checkConstructors.loop statistics isUnsafe 0 `RawTerminal openResult 0 1 ambient
      | throwError "raw zero-check terminal boundary failed"
    match ambient.env.checkNoMVarNoFVar `RawTerminal openResult with
    | .error _ => checks := checks + 2
    | .ok _ => throwError "full source guard accepted the zero-check raw terminal"
    let bad := Expr.forallE `type (.sort (.succ .zero))
      (.forallE `value (.bvar 0) (mkApp2 (.const family.name []) (.bvar 1) (.bvar 0)) .default) .default
    match checkConstructors.loop statistics isUnsafe 0 `Mismatch bad 0 32 ambient with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "complete-prefix loop accepted incompatible first domains"
  let .ok true := (monadLift (TypeChecker.isDefEq betaDomain (.sort .zero)) : AddInductive.M Bool) ambient
    | throwError "nonliteral canonical opening equality failed"
  let .ok true := (monadLift (TypeChecker.isDefEq (.fvar sourceType) (.fvar sourceType)) : AddInductive.M Bool) ambient
    | throwError "dependent second checkpoint equality failed"
  checks := checks + 2
  unless checks == 25 do throwError "constructor prefix-receipt runtime manifest changed: {checks}"
  logInfo m!"constructor prefix-receipt runtime: {checks} registered-family, dependent, safe/unsafe, field, partial, truncated and negative controls"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let canonical := inherited ++ [``PersistentHashMap.WF.find?_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.toList'_insert]
  let checker := canonical ++ [``PersistentHashMap.findAux_isSome, ``Expr.eqv_eq,
    ``Level.instLawfulBEqLevel, ``Syntax.structEq_eq, ``Lean4Lean.ptrEqExpr_eq, ``Expr.looseBVarRange_eq,
    ``Expr.instantiateRev_eq, ``Expr.instantiate_eq, ``Expr.replace_eq, ``Level.hasParam_eq,
    ``Expr.hasLevelParam_eq, ``Level.hasMVar_eq, ``Lean4Lean.ptrEqConstantInfo_eq, ``Expr.instantiateRange_eq,
    ``Expr.instantiate1_eq, `Lean.Expr.mkAppRangeAux.eq_def, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq, ``Expr.instantiateRevRange_eq]
  let allowed := checker ++ [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq]
  for name in [``ParameterPrefix.baseWF, ``ParameterPrefix.uncons, ``ParameterPrefix.retainsLookup,
      ``ParameterPrefix.contextAgreement,
      ``AcceptedConstructorTrace.receiptsAfterParameters, ``TrExprS.openCanonicalParameter,
      ``AcceptedConstructorTrace.completeParameters, ``AcceptedConstructorTrace.domainReceipts,
      ``AcceptedConstructorTrace.domainReceiptsAtParameterModel,
      ``checkConstructors.domainReceipts, ``checkConstructors.domainReceiptsAtParameterModel,
      ``registeredFamilyBatchProducesReceipts,
      ``canonicalOpeningChangesDependentDomain, ``completeParametersRequireSourceAbsence] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unexpected constructor prefix-receipt dependency {dependency} in {name}"
    logInfo m!"{name}: {dependencies.size} dependencies = {repr dependencies}"
  auditExact ``ParameterPrefix.uncons [``propext]
  auditExact ``ParameterPrefix.contextAgreement inherited
  for name in [``ParameterPrefix.baseWF, ``AcceptedConstructorTrace.receiptsAfterParameters] do
    auditExact name inherited
  auditExact ``ParameterPrefix.retainsLookup canonical
  for name in [``TrExprS.openCanonicalParameter, ``canonicalOpeningChangesDependentDomain] do
    auditExact name (canonical ++ [``Expr.instantiate1_eq])
  for name in [``AcceptedConstructorTrace.completeParameters, ``completeParametersRequireSourceAbsence] do
    auditExact name (logical ++ [``Expr.eqv_eq, ``Expr.instantiate1_eq])
  auditExact ``AcceptedConstructorTrace.domainReceipts checker
  auditExact ``AcceptedConstructorTrace.domainReceiptsAtParameterModel checker
  for name in [``checkConstructors.domainReceipts, ``checkConstructors.domainReceiptsAtParameterModel,
      ``registeredFamilyBatchProducesReceipts] do
    auditExact name allowed
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveConstructorPrefixReceipts
    | throwError "constructor prefix-receipt module absent"
  let mut moduleCount := 0
  let mut fixtureCount := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then throwError "new constructor prefix-receipt axiom {name}"
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected constructor prefix-receipt module dependency {dependency} in {name}"
      moduleCount := moduleCount + 1
    if name.toString.contains "InductiveConstructorPrefixReceiptTest" then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unexpected constructor prefix-receipt fixture dependency {dependency} in {name}"
      fixtureCount := fixtureCount + 1
  logInfo m!"constructor prefix-receipt exhaustive audit: {moduleCount} module and {fixtureCount} fixture declarations"
  unless moduleCount == 29 do throwError "constructor prefix-receipt module manifest changed: {moduleCount}"
  unless fixtureCount == 17 do throwError "constructor prefix-receipt fixture manifest changed: {fixtureCount}"
  runtimeControls

end InductiveConstructorPrefixReceiptTest
