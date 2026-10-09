import Lean4Lean.Verify.InductiveIndexTraceTranslation
import Lean4Lean.Verify.InductiveIndexTraceTranslationFacts
import Lean4Lean.Verify.InductiveIndexTraceTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexTraceTranslationTest

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def binary (name : Name) (carrier payload : Expr) : Expr :=
  .app (.app (.const name [.zero]) carrier) payload

private def equalityDomain (carrier left right : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier left right

private def dependentTwo : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``outParam (.bvar 0)) (.sort (.succ .zero)) .implicit) .default

private def dependentThree : Expr := .forallE `carrier (.sort (.succ .zero))
  (.forallE `element (unary ``semiOutParam (.bvar 0))
    (.forallE `witness (binary ``optParam (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
      (mkApp2 (.const ``Eq.refl [.succ .zero]) (.bvar 1) (.bvar 0)))
      (.sort (.succ .zero)) .instImplicit) .implicit) .default

private theorem dependentTwoIsSortTelescope : SortTelescope dependentTwo :=
  .forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero)))

private theorem dependentThreeIsSortTelescope : SortTelescope dependentThree :=
  .forallE _ _ _ (.forallE _ _ _ (.forallE _ _ _ (.sort (.succ .zero))))

private theorem plainHeadUniformAtAnySemanticLevel (universes : List Name) (level : VLevel) :
    UniformAnnotationUniverse universes (.sort (.succ .zero)) level := by trivial

private theorem firstIndexAnnotationUsesItsLiteralUniverse :
    UniformAnnotationUniverse [] (unary ``outParam (.bvar 0)) (.succ .zero) := by
  simp [unary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem laterWitnessAnnotationUsesItsOwnLiteralUniverse :
    UniformAnnotationUniverse []
      (binary ``optParam (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) (.bvar 0)) .zero := by
  simp [binary, equalityDomain, UniformAnnotationUniverse, VLevel.ofLevel, mkApp3]

private theorem noOneGlobalLiteralUniverseForDistinctAnnotations (level : VLevel) :
    ¬ (UniformAnnotationUniverse [] (unary ``outParam (.bvar 0)) level ∧
      UniformAnnotationUniverse []
        (binary ``optParam (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) (.bvar 0)) level) := by
  simp [unary, binary, equalityDomain, UniformAnnotationUniverse, VLevel.ofLevel, mkApp3]
  rintro rfl impossible
  cases impossible

private theorem parameterBoundExcludesReusedParameterStep {stats : InductiveStats} {index : Nat}
    (bound : stats.params.size ≤ index) : ¬ index < stats.params.size := by omega

private theorem parameterBoundIsNotImpliedByPositiveIndex :
    1 > 0 ∧ ¬ 3 ≤ 1 := by decide

private theorem normalizationUsesExactRecordedResult {env : VEnv} {universes : List Name}
    {virtualContext : VLCtx} {ctx : Context} {body normalized : Expr} {value : Expr} {semantic : VExpr}
    (telescope : SortTelescope body)
    (actual : ((monadLift (TypeChecker.whnf (body.instantiate1 value)) : M Expr) ctx) = .ok normalized)
    (translated : TrExpr env universes virtualContext (body.instantiate1 value) semantic) :
    ∃ normalizedSemantic, TrExprS env universes virtualContext normalized normalizedSemantic ∧
      env.IsDefEqU universes.length virtualContext.toCtx normalizedSemantic semantic :=
  telescope.normalizedTranslation actual translated

private theorem normalizationCannotChooseAnArbitraryReplacement {ctx : Context} {body normalized replacement : Expr}
    {value : Expr} (telescope : SortTelescope body)
    (actual : ((monadLift (TypeChecker.whnf (body.instantiate1 value)) : M Expr) ctx) = .ok normalized)
    (different : replacement ≠ body.instantiate1 value) : replacement ≠ normalized := by
  have same := (telescope.instantiate1 value).whnf ctx normalized actual
  rw [same]
  exact different

private theorem actualSortTraceDischargesOnlyItsNormalizationEdges {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (telescope : SortTelescope source) : IndexTraceNormalizationSupport env universes trace :=
  trace.normalizationSupport_ofSortTelescope telescope

private theorem unrecognizedActualDomainHasLocalSupport (env : VEnv) (universes : List Name)
    (reader : Context) (name : Name) (levels : List Level) :
    IndexAnnotationSupport env universes reader (.const name levels) := by
  intro virtual semantic _ _ typed
  obtain ⟨level, typed⟩ := typed
  exact ⟨level, typed, True.intro⟩

private theorem actualTraceTranslationNeedsNoAssumedSpines {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context} {virtual : VLCtx} {semantic : VExpr}
    (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (annotations : IndexTraceAnnotationSupport env universes trace)
    (normalizations : IndexTraceNormalizationSupport env universes trace) :
    ∃ finalVirtual finalSemantic,
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic :=
  trace.translated envWF constants definitions indexOnly correspondence reserved translated annotations normalizations

private theorem actualTraceTerminalCorrespondenceIsDerived {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic) :
    TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic :=
  history.finalTranslation

private theorem sameHistoryContainsExactNativeAllocations {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ steps : List BinderStep, finalIndex = index ∧
      TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal finalSemantic ∧
      finalIndices.toList = indices.toList ++ steps.map BinderStep.value ∧
      (∀ step ∈ steps, step.role = .index) ∧
      BinderIndexAllocations finalReader reader.lctx.decls.size steps := by
  obtain ⟨steps, values, roles, allocated⟩ := history.allocations reserved
  obtain ⟨correspondence, translated⟩ := history.finalTranslation
  exact ⟨steps, history.indexUnchanged, correspondence, translated, values, roles, allocated⟩

private theorem existingIndexPrefixIsPreservedBySameHistory {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices finalReader}
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ suffix : List Expr, finalIndices.toList = indices.toList ++ suffix := by
  obtain ⟨steps, values, _, _⟩ := history.allocations reserved
  exact ⟨steps.map BinderStep.value, values⟩

private theorem stopHistoryAddsNoNativeOrVirtualContext {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {source : Expr} {index : Nat} {indices : Array Expr}
    {reader : Context} {virtual : VLCtx} {semantic : VExpr}
    (notForall : ∀ name domain body bi, source ≠ .forallE name domain body bi)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (translated : TrExprS env universes virtual source semantic) :
    TranslatedRecursorIndexTrace env universes
      (.stop (stats := stats) (index := index) (indices := indices) (ctx := reader) notForall)
      virtual semantic virtual semantic :=
  .stop notForall correspondence translated

private def capture (stats : InductiveStats) (type : Expr) (index : Nat) (prefixIndices : Array Expr)
    (fuel : Nat) : M (Array Expr × Context) :=
  mkRecInfos.loopArgs1 stats type index prefixIndices fuel fun indices => do
    return (indices, ← read)

private theorem captureCarriesActualRuntimeTrace (stats : InductiveStats) (type : Expr) (index : Nat)
    (prefixIndices : Array Expr) (fuel : Nat) (ctx : Context) (contextWF : ctx.lctx.WF)
    (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (capture stats type index prefixIndices fuel ctx).WF fun result =>
      ∃ terminal finalIndex, RecursorIndexTrace stats type index prefixIndices ctx
        terminal finalIndex result.1 result.2 ∧ ctx.RecursorScopeFrame result.2 := by
  refine mkRecInfos.loopArgs1.scopedTrace stats type index prefixIndices fuel
    (fun finalIndices current => .ok (finalIndices, current)) ctx
    (fun result => ∃ terminal finalIndex, RecursorIndexTrace stats type index prefixIndices ctx
      terminal finalIndex result.1 result.2 ∧ ctx.RecursorScopeFrame result.2) contextWF reserved ?_
  intro terminal finalIndex finalIndices current trace frame result success
  obtain rfl := Except.ok.inj success
  exact ⟨terminal, finalIndex, trace, frame⟩

private theorem getterCarriesActualSemanticHistory {env : VEnv} {universes : List Name}
    {virtual : VLCtx} {semantic : VExpr} (stats : InductiveStats) (source : Expr)
    (index : Nat) (indices : Array Expr) (fuel : Nat) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic)
    (supports : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices current),
      IndexTraceAnnotationSupport env universes trace ∧ IndexTraceNormalizationSupport env universes trace) :
    (capture stats source index indices fuel reader).WF fun result =>
      ∃ terminal finalVirtual finalSemantic,
      ∃ trace : RecursorIndexTrace stats source index indices reader terminal index result.1 result.2,
        TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic ∧
        TrLCtx env universes result.2.lctx finalVirtual ∧
        TrExprS env universes finalVirtual terminal finalSemantic ∧ reader.RecursorScopeFrame result.2 :=
  mkRecInfos.loopArgs1.getTranslatedTrace stats source index indices fuel reader envWF constants definitions
    indexOnly correspondence reserved translated supports

private theorem plainTelescopeCpsNeedsNoNormalizationAssumption {ResultType : Type}
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {semantic : VExpr}
    (stats : InductiveStats) (source : Expr) (index : Nat) (indices : Array Expr)
    (fuel : Nat) (next : Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual source semantic) (telescope : SortTelescope source)
    (annotations : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices current),
      IndexTraceAnnotationSupport env universes trace)
    (nextWF : ∀ terminal finalIndex finalIndices current
      (trace : RecursorIndexTrace stats source index indices reader terminal finalIndex finalIndices current),
      ∀ finalVirtual finalSemantic,
      TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic →
      TrLCtx env universes current.lctx finalVirtual → TrExprS env universes finalVirtual terminal finalSemantic →
      reader.RecursorScopeFrame current → (next finalIndices current).WF post) :
    (mkRecInfos.loopArgs1 stats source index indices fuel next reader).WF post :=
  mkRecInfos.loopArgs1.translatedTrace_ofSortTelescope stats source index indices fuel next reader post
    envWF constants definitions indexOnly correspondence reserved translated telescope annotations nextWF

private def plainInner : Expr := .forallE `plainSecond (.const ``Nat [])
  (.sort (.succ .zero)) .default

private def plainTwo : Expr := .forallE `plainFirst (.const ``Nat []) plainInner .default

private theorem plainInnerTelescope : SortTelescope plainInner :=
  .forallE _ _ _ (.sort (.succ .zero))

private theorem plainTwoTelescope : SortTelescope plainTwo :=
  .forallE _ _ _ plainInnerTelescope

private theorem plainInnerActualAnnotationSupport {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats plainInner index indices reader terminal finalIndex finalIndices finalReader)
    (bound : stats.params.size ≤ index) : IndexTraceAnnotationSupport env universes trace := by
  cases trace with
  | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
  | parameter parameter _ _ => exact False.elim (Nat.not_lt_of_ge bound parameter)
  | index notParameter normalization tail =>
    have stable := ((SortTelescope.sort (.succ .zero)).instantiate1 (.fvar ⟨reader.ngen.curr⟩)).whnf
      (recursorIndexContext reader `plainSecond .default (.const ``Nat [])) _ normalization
    simp only [Expr.instantiate1_eq, Expr.instantiate1'] at stable
    cases stable
    cases tail with
    | stop notForall =>
      exact .index notParameter normalization (.stop notForall)
        (unrecognizedActualDomainHasLocalSupport _ _ _ ``Nat []) (.stop notForall)

private theorem plainTwoActualAnnotationSupport {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {reader finalReader : Context}
    (trace : RecursorIndexTrace stats plainTwo index indices reader terminal finalIndex finalIndices finalReader)
    (bound : stats.params.size ≤ index) : IndexTraceAnnotationSupport env universes trace := by
  cases trace with
  | stop notForall => exact False.elim (notForall _ _ _ _ rfl)
  | parameter parameter _ _ => exact False.elim (Nat.not_lt_of_ge bound parameter)
  | index notParameter normalization tail =>
    have stable := (plainInnerTelescope.instantiate1 (.fvar ⟨reader.ngen.curr⟩)).whnf
      (recursorIndexContext reader `plainFirst .default (.const ``Nat [])) _ normalization
    simp only [Expr.instantiate1_eq, plainInner, Expr.instantiate1'] at stable
    cases stable
    exact .index notParameter normalization tail
      (unrecognizedActualDomainHasLocalSupport _ _ _ ``Nat []) (plainInnerActualAnnotationSupport tail bound)

private theorem plainNatTyped {env : VEnv} (context : List VExpr)
    (lookup : env.constants ``Nat = some { uvars := 0, type := .sort (.succ .zero) }) :
    env.HasType 0 context (.const ``Nat []) (.sort (.succ .zero)) := by
  simpa only [VExpr.instL] using VEnv.HasType.const (env := env) (U := 0) (Γ := context)
    (ci := { uvars := 0, type := .sort (.succ .zero) }) lookup (ls := []) (by simp) rfl

private theorem plainTwoActualSourceTranslation {env : VEnv} (virtual : VLCtx)
    (lookup : env.constants ``Nat = some { uvars := 0, type := .sort (.succ .zero) }) :
    TrExprS env [] virtual plainTwo
      (.forallE (.const ``Nat []) (.forallE (.const ``Nat []) (.sort (.succ .zero)))) := by
  apply TrExprS.forallE ⟨.succ .zero, plainNatTyped _ lookup⟩
    ⟨.imax (.succ .zero) (.succ (.succ .zero)),
      (plainNatTyped _ lookup).forallE (VEnv.HasType.sort (by trivial))⟩
  · exact .const lookup rfl rfl
  · exact .forallE ⟨.succ .zero, plainNatTyped _ lookup⟩
      ⟨.succ (.succ .zero), VEnv.HasType.sort (by trivial)⟩ (.const lookup rfl rfl) (.sort rfl)

private theorem concreteTwoIndexSemanticGetter {env : VEnv} {virtual : VLCtx}
    (stats : InductiveStats) (index : Nat) (prefixIndices : Array Expr) (fuel : Nat) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (indexOnly : stats.params.size ≤ index)
    (correspondence : TrLCtx env [] reader.lctx virtual) (reserved : ContextReserved reader.lctx reader.ngen)
    (lookup : env.constants ``Nat = some { uvars := 0, type := .sort (.succ .zero) }) :
    (capture stats plainTwo index prefixIndices fuel reader).WF fun result =>
      ∃ terminal finalVirtual finalSemantic,
      ∃ trace : RecursorIndexTrace stats plainTwo index prefixIndices reader terminal index result.1 result.2,
        TranslatedRecursorIndexTrace env [] trace virtual
          (.forallE (.const ``Nat []) (.forallE (.const ``Nat []) (.sort (.succ .zero))))
          finalVirtual finalSemantic ∧ TrLCtx env [] result.2.lctx finalVirtual ∧
        TrExprS env [] finalVirtual terminal finalSemantic ∧ reader.RecursorScopeFrame result.2 := by
  refine mkRecInfos.loopArgs1.getTranslatedTrace stats plainTwo index prefixIndices fuel reader
    envWF constants definitions indexOnly correspondence reserved (plainTwoActualSourceTranslation virtual lookup) ?_
  intro terminal finalIndex finalIndices current trace
  exact ⟨plainTwoActualAnnotationSupport trace indexOnly,
    trace.normalizationSupport_ofSortTelescope plainTwoTelescope⟩

private def statsFor (params : Array Expr) : InductiveStats where
  params := params
  levels := []
  resultLevel := .succ .zero
  indConsts := #[]
  isNotZero := true

private def checkStoredSuffix (original current : Context) (type : Expr) (values : Array Expr)
    (prefixSize : Nat) : MetaM Unit := do
  let mut opened := type
  let mut generator := original.ngen
  for offset in [:values.size - prefixSize] do
    let .forallE name domain body binderInfo := opened
      | throwError "index-trace runtime suffix exhausted source telescope early"
    let value := values[prefixSize + offset]!
    unless value == Expr.fvar ⟨generator.curr⟩ do
      throwError "index-trace runtime suffix fresh-ID order changed"
    let some declaration := current.lctx.find? value.fvarId!
      | throwError "index-trace runtime suffix actual native lookup missing"
    unless declaration.toExpr == value && declaration.type == peelTypeAnnotations domain &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == original.lctx.decls.size + offset do
      throwError "index-trace runtime suffix native allocation/type/name/bi/position changed"
    unless declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "index-trace runtime suffix exact peeled dependencies changed"
    opened := body.instantiate1 value
    generator := generator.next
  unless opened == Expr.sort (.succ .zero) && current.ngen.curr == generator.curr do
    throwError "index-trace runtime suffix terminal/final native generator changed"

private def checkSuffix (ctx : Context) (type : Expr) (count : Nat) (params prefixIndices : Array Expr)
    (index : Nat) : MetaM Unit := do
  let .ok (indices, current) := capture (statsFor params) type index prefixIndices 16 ctx
    | throwError "index-trace actual loopArgs1 callback failed"
  unless indices.size == prefixIndices.size + count && current.lctx.decls.size == ctx.lctx.decls.size + count do
    throwError "index-trace runtime suffix allocation count changed"
  for position in [:prefixIndices.size] do
    unless indices[position]! == prefixIndices[position]! do
      throwError "index-trace runtime replaced an existing index prefix"
  checkStoredSuffix ctx current type indices prefixIndices.size
  for position in [:ctx.lctx.decls.size] do
    if let some prior := ctx.lctx.getAt? position then
      let some retained := current.lctx.find? prior.fvarId
        | throwError "index-trace runtime removed a prior native local"
      unless retained.toExpr == prior.toExpr && retained.type == prior.type &&
          retained.value? == prior.value? && retained.index == prior.index do
        throwError "index-trace runtime changed a prior native local"

private def parameterReuseControl (ctx : Context) (carrier : Expr) : MetaM Unit := do
  let .ok (indices, current) := capture (statsFor #[carrier]) dependentTwo 0 #[] 16 ctx
    | throwError "index-trace parameter-reuse omission control failed"
  unless indices.size == 1 && current.lctx.decls.size == ctx.lctx.decls.size + 1 do
    throwError "index-trace parameter-bound omission no longer exercises parameter reuse"
  let some declaration := current.lctx.find? indices[0]!.fvarId!
    | throwError "index-trace reused-parameter control native index missing"
  unless declaration.type == carrier do
    throwError "index-trace reused-parameter control no longer opens the source with the old parameter"

private def runtimeFixtures (ctx : Context) : MetaM Unit := do
  let oldCarrier : FVarId := ⟨`TraceTranslationCarrier⟩
  let oldElement : FVarId := ⟨`TraceTranslationElement⟩
  let seeded := { ctx with
    ngen := { namePrefix := `TraceTranslationSeed, idx := 23 }
    lctx := ctx.lctx.mkLocalDecl oldCarrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl oldElement `oldElement (.fvar oldCarrier) .default
      |>.mkLetDecl ⟨`TraceTranslationOldLet⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  let oldType := Expr.fvar oldCarrier
  let oldValue := Expr.fvar oldElement
  for params in [#[], #[oldType], #[oldType, oldValue, oldType]] do
    for prefixIndices in [#[], #[oldValue], #[oldType, oldValue]] do
      for index in [params.size, params.size + 4] do
        checkSuffix seeded dependentTwo 2 params prefixIndices index
        checkSuffix seeded dependentThree 3 params prefixIndices index
  parameterReuseControl seeded oldType
  logInfo "index-trace runtime: 36 actual suffix callbacks; 90 dependent allocations; preserved prefixes; one parameter-reuse control"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-trace unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-trace audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "index-trace module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let environment ← getEnv
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrExprS.defeqDFC', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas)] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? moduleName do
      throwError "index-trace inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "index-trace inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    logInfo m!"pinned inherited trace foundation: {name} from {moduleName}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "index-trace native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name ==
        environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "index-trace native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

#print axioms RecursorIndexTrace.translated
#print axioms RecursorIndexTrace.normalizationSupport_ofSortTelescope
#print axioms TranslatedRecursorIndexTrace.allocations
#print axioms mkRecInfos.loopArgs1.getTranslatedTrace
#print axioms concreteTwoIndexSemanticGetter
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := inherited ++ nativeInterfaces
  for theoremName in [``dependentTwoIsSortTelescope, ``dependentThreeIsSortTelescope,
      ``plainHeadUniformAtAnySemanticLevel, ``firstIndexAnnotationUsesItsLiteralUniverse,
      ``laterWitnessAnnotationUsesItsOwnLiteralUniverse, ``noOneGlobalLiteralUniverseForDistinctAnnotations,
      ``parameterBoundExcludesReusedParameterStep, ``parameterBoundIsNotImpliedByPositiveIndex,
      ``plainInnerTelescope, ``plainTwoTelescope, ``plainNatTyped] do
    auditDeclaration theoremName logical
  for functionName in [``capture, ``checkStoredSuffix, ``checkSuffix, ``parameterReuseControl,
      ``runtimeFixtures] do
    auditDeclaration functionName logical
  for theoremName in [``normalizationUsesExactRecordedResult,
      ``normalizationCannotChooseAnArbitraryReplacement, ``actualSortTraceDischargesOnlyItsNormalizationEdges,
      ``unrecognizedActualDomainHasLocalSupport, ``actualTraceTranslationNeedsNoAssumedSpines,
      ``actualTraceTerminalCorrespondenceIsDerived, ``sameHistoryContainsExactNativeAllocations,
      ``existingIndexPrefixIsPreservedBySameHistory, ``stopHistoryAddsNoNativeOrVirtualContext,
      ``captureCarriesActualRuntimeTrace, ``getterCarriesActualSemanticHistory,
      ``plainTelescopeCpsNeedsNoNormalizationAssumption, ``plainInnerActualAnnotationSupport,
      ``plainTwoActualAnnotationSupport, ``plainTwoActualSourceTranslation,
      ``concreteTwoIndexSemanticGetter] do
    auditDeclaration theoremName native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  for moduleName in [`Lean4Lean.Verify.InductiveIndexTraceTranslation,
      `Lean4Lean.Verify.InductiveIndexTraceTranslationFacts, `Lean4Lean.Verify.InductiveIndexTraceTranslationCPS] do
    auditModule moduleName native
  auditFoundations nativeInterfaces
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures ctx
  logInfo "index-trace translation: 27 proof controls; clean old core; same-history terminal/allocation/CPS audits"

end InductiveIndexTraceTranslationTest
