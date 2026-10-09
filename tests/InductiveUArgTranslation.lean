import Lean4Lean.Verify.InductiveCtorFieldTranslationCPS
import Lean4Lean.Verify.InductiveBinderTyping
import Lean4Lean.Verify.InductiveUArgTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveUArgTranslationTest

abbrev ArgumentHeaderAlias := Nat → Nat
abbrev ArgumentDomainAlias := Nat

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def optionalDomain (carrier value : Expr) : Expr :=
  .app (.app (.const ``optParam [.succ .zero]) carrier) value

private def equalityDomain (carrier left right : Expr) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) carrier) left) right

private theorem annotationPeelingDoesNotNormalizeAnAlias :
    peelTypeAnnotations (.const ``ArgumentDomainAlias []) = .const ``ArgumentDomainAlias [] := rfl

private theorem metadataFieldBarrierKeepsItsActualNativeDomain (metadata : MData) (domain : Expr) :
    peelTypeAnnotations (.mdata metadata domain) = .mdata metadata domain := rfl

private theorem discardedOptionalDefaultIsNotAStoredDependency (carrier value : FVarId) :
    (optionalDomain (.fvar carrier) (.fvar value)).fvarsList = [carrier, value] ∧
      (peelTypeAnnotations (optionalDomain (.fvar carrier) (.fvar value))).fvarsList = [carrier] := by
  constructor
  · rfl
  · simp [optionalDomain, peelTypeAnnotations]
    rfl

private theorem retainedParentLocalCannotUseIdentityArgumentWeakening :
    (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 = .forallE (.sort .zero) (.bvar 2) ∧
      (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 ≠ .forallE (.sort .zero) (.bvar 1) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem openingFailureCannotSupplySuccessfulTypedOutputs
    {ResultType : Type} (action : M ResultType) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : action reader = .error failure) :
    ∀ result, action reader ≠ .ok result := by
  intro result success
  rw [failed] at success
  cases success

private theorem adapterHasNoOriginalConstructorParameters : recursorUArgStats.params.size = 0 := rfl

private theorem adapterCannotReuseAParameterAtAnyArgumentPosition (position : Nat) :
    recursorUArgStats.params[position]? = none := by simp [recursorUArgStats]

private theorem actualInitialWhnfCannotChooseAnotherNormalizedHeader
    (reader : Context) (inferred normalized alternate : Expr)
    (actual : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
    (other : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok alternate) :
    normalized = alternate := by
  rw [actual] at other
  cases other
  rfl

private theorem actualInferenceCannotChooseAnotherStoredSourceType
    (reader : Context) (argument inferred alternate : Expr)
    (actual : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
    (other : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok alternate) :
    inferred = alternate := by
  rw [actual] at other
  cases other
  rfl

private theorem actualOpeningRetainsInferenceInitialWhnfAndOneArgumentHistory
    (argument inferred normalized terminal : Expr) (arguments : Array Expr) (reader finalReader : Context)
    (inference : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
    (normalization : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
    (trace : RecursorUArgTrace normalized #[] reader terminal arguments finalReader) :
    RecursorUArgOpeningTrace argument reader terminal arguments finalReader := .mk inference normalization trace

private theorem actualNativeOpeningScopeDoesNotTypeGeneratedHypotheses
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := opening.scope readerWF reserved

private theorem actualOpeningArgumentsAreTheSameDeclaredNativeFields
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader) :
    RecursorFieldsDeclared finalReader.lctx arguments := opening.declared

private theorem actualNativeGetterCapturesTheSameInferredOpening
    (argument : Expr) (reader : Context) (readerWF : reader.lctx.WF)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopUArgs argument
      (fun terminal arguments => do return (terminal, arguments, ← readThe Context)) reader).WF fun result =>
      RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2 ∧
        reader.RecursorScopeFrame result.2.2 ∧ RecursorFieldsDeclared result.2.2.lctx result.2.1 :=
  mkRecInfos.loopUArgs.getTrace argument reader readerWF reserved

private theorem normalizedSourceTranslationRemainsAnExplicitSemanticPremise
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument inferred normalized : Expr} {semantic : VExpr}
    (source : UArgSourceTranslation env universes virtual argument inferred normalized semantic) :
    TrExprS env universes virtual normalized semantic := source.normalizedTranslation

private theorem normalizedSourceTypingUsesTheCompatibleInferenceAndWhnfSupport
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument inferred normalized : Expr} {semantic : VExpr}
    (source : UArgSourceTranslation env universes virtual argument inferred normalized semantic)
    (envWF : env.WF) (contextWF : virtual.WF env universes.length) :
    ∃ argumentSemantic, TrExprS env universes virtual argument argumentSemantic ∧
      env.HasType universes.length virtual.toCtx argumentSemantic semantic :=
  source.normalizedArgumentTyping envWF contextWF

private theorem exactOpeningSupportKeepsInitialAndBodyNormalizationObligationsSeparate
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument inferred normalized terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context} {semantic : VExpr}
    (inference : ((monadLift (TypeChecker.inferType argument) : M Expr) reader) = .ok inferred)
    (normalization : ((monadLift (TypeChecker.whnf inferred) : M Expr) reader) = .ok normalized)
    (trace : RecursorUArgTrace normalized #[] reader terminal arguments finalReader)
    (source : UArgSourceTranslation env universes virtual argument inferred normalized semantic)
    (annotations : IndexTraceAnnotationSupport env universes trace)
    (normalizations : IndexTraceNormalizationSupport env universes trace) :
    UArgOpeningTranslationSupport env universes (.mk inference normalization trace) virtual :=
  .mk inference normalization trace source annotations normalizations

private theorem exactSupportedOpeningDerivesItsSameActualTranslatedHistory
    {env : VEnv} {universes : List Name} {virtual : VLCtx}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (support : UArgOpeningTranslationSupport env universes opening virtual) :
    ∃ finalVirtual finalSemantic,
      TranslatedRecursorUArgOpening env universes opening virtual finalVirtual finalSemantic :=
  opening.translated envWF constants definitions correspondence reserved support

private theorem sameOpeningHistoryDerivesTheActualTerminalReaderCorrespondence
    {env : VEnv} {universes : List Name} {virtual finalVirtual : VLCtx} {semantic : VExpr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (history : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual semantic) :
    TrLCtx env universes finalReader.lctx finalVirtual ∧
      TrExprS env universes finalVirtual terminal semantic := history.finalTranslation

private theorem sameOpeningHistoryTypesOnlyTheActualAppliedRecursiveArgument
    {env : VEnv} {universes : List Name} {virtual finalVirtual : VLCtx} {semantic : VExpr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (history : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual semantic)
    (envWF : env.WF) :
    ∃ value, TrExprS env universes finalVirtual (mkAppN argument arguments) value ∧
      env.HasType universes.length finalVirtual.toCtx value semantic := history.application envWF

private theorem sameOpeningHistoryConstructsTheMixedSuffixFromOnlyItsInitialModel
    {env : VEnv} {universes : List Name} {virtual finalVirtual : VLCtx} {semantic : VExpr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (history : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual semantic)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    ∃ finalModel ids, finalModel.WF env universes ∧ finalModel.lctx = finalReader.lctx ∧
      finalModel.vlctx = finalVirtual ∧ IndexMLCtxExtension model ids finalModel ∧
      arguments.toList = ids.map Expr.fvar := history.mixedContext model modelWF native converted reserved

private theorem typedArgumentAbstractionReturnsToTheInitialParentModel
    {env : VEnv} {universes : List Name} {virtual finalVirtual : VLCtx} {semantic : VExpr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (history : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual semantic)
    (envWF : env.WF) (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes finalVirtual body bodySemantic)
    (typed : env.IsType universes.length finalVirtual.toCtx bodySemantic) :
    ∃ abstracted, TrExpr env universes virtual (finalReader.lctx.mkForall arguments body) abstracted ∧
      env.IsType universes.length virtual.toCtx abstracted :=
  history.typedAbstraction envWF model modelWF native converted reserved translated typed

private theorem argumentAbstractionAtTheTemporaryReaderWeakensAcrossTheSameSuffix
    {env : VEnv} {universes : List Name} {virtual finalVirtual : VLCtx} {semantic : VExpr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    (history : TranslatedRecursorUArgOpening env universes opening virtual finalVirtual semantic)
    (envWF : env.WF) (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes finalVirtual body bodySemantic)
    (typed : env.IsType universes.length finalVirtual.toCtx bodySemantic) :
    ∃ abstracted, TrExpr env universes finalVirtual (finalReader.lctx.mkForall arguments body) abstracted ∧
      env.IsType universes.length finalVirtual.toCtx abstracted :=
  history.typedAbstractionAtFinal envWF model modelWF native converted reserved translated typed

private theorem typedArgumentEndpointDerivesItsExactTemporaryReaderCorrespondence
    {env : VEnv} {universes : List Name} {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : TypeChecker.MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := endpoint.context

private theorem typedArgumentEndpointTranslatesItsExactTerminal
    {env : VEnv} {universes : List Name} {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : TypeChecker.MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final) :
    ∃ semantic, TrExprS env universes final.vlctx terminal semantic := endpoint.terminalTranslation

private theorem typedArgumentEndpointKeepsExactlyItsAllocatedArgumentArray
    {env : VEnv} {universes : List Name} {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : TypeChecker.MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final) :
    ∃ ids, IndexMLCtxExtension initial ids final ∧ arguments.toList = ids.map Expr.fvar := by
  obtain ⟨_, _, _, _, _, _, ids, extension, selected⟩ := endpoint
  exact ⟨ids, extension, selected⟩

private theorem typedArgumentEndpointPairsItsActualApplicationAndTerminalType
    {env : VEnv} {universes : List Name} {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : TypeChecker.MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) :
    ∃ value semantic, TrExprS env universes final.vlctx (mkAppN argument arguments) value ∧
      TrExprS env universes final.vlctx terminal semantic ∧
      env.HasType universes.length final.vlctx.toCtx value semantic := endpoint.application envWF

private theorem argumentEndpointAbstractionStillRequiresExplicitBodyTyping
    {env : VEnv} {universes : List Name} {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : TypeChecker.MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall arguments body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted :=
  endpoint.typedArgumentAbstraction envWF translated typed

private theorem actualArgumentSuffixDropPreservesTheInitialParentModel
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.dropN ids.length extension.bound = initial := extension.drop_eq

private def captureTuple (argument : Expr) : M (Expr × Array Expr × Context) :=
  mkRecInfos.loopUArgs argument fun terminal arguments => do return (terminal, arguments, ← readThe Context)

private theorem actualGetterDerivesOneFinalArgumentModelWithoutConstructorParameterBounds
    {env : VEnv} {universes : List Name} (argument : Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureTuple argument reader).WF fun result =>
      ∀ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        UArgOpeningTranslationSupport env universes opening model.vlctx) :
    (captureTuple argument reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorFieldsDeclared result.2.2.lctx result.2.1 ∧
      ∃ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        ∃ finalModel, UArgModelEndpoint env universes opening model finalModel :=
  mkRecInfos.loopUArgs.getTranslatedOpening argument reader envWF constants definitions
    model modelWF native reserved support

private theorem scopedTypedArgumentCpsLeavesMotiveHypothesisAndMinorTypingExplicit
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (argument : Expr) (next : Expr → Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    (support : (captureTuple argument reader).WF fun result =>
      ∀ opening : RecursorUArgOpeningTrace argument reader result.1 result.2.1 result.2.2,
        UArgOpeningTranslationSupport env universes opening model.vlctx)
    (nextWF : ∀ terminal arguments finalReader
      (opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader) finalModel,
      reader.RecursorScopeFrame finalReader → RecursorFieldsDeclared finalReader.lctx arguments →
      UArgModelEndpoint env universes opening model finalModel →
      (next terminal arguments finalReader).WF post) :
    (mkRecInfos.loopUArgs argument next reader).WF post :=
  mkRecInfos.loopUArgs.scopedTranslatedOpening argument next reader post envWF constants definitions
    model modelWF native reserved support nextWF

private structure ArgumentCapture where
  terminal : Expr
  arguments : Array Expr
  reader : Context
  abstracted : Expr

private def capture (argument : Expr) : M (ArgumentCapture × Context) := do
  let result ← mkRecInfos.loopUArgs argument fun terminal arguments => do
    let reader ← readThe Context
    return { terminal, arguments, reader, abstracted := reader.lctx.mkForall arguments terminal }
  return (result, ← readThe Context)

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "uarg retained native declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "uarg retained native declaration changed type/dependencies/value/order"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "uarg nonallocation reader fields changed"

private def checkSuffix (entry : Context) (normalized : Expr) (result : ArgumentCapture)
    (count : Nat) : MetaM Unit := do
  unless result.arguments.size == count && result.reader.lctx.decls.size == entry.lctx.decls.size + count do
    throwError "uarg actual argument/native allocation counts changed"
  let mut opened := normalized
  let mut current := entry
  for ordinal in [:result.arguments.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "uarg normalized argument telescope ended early"
    let argument := result.arguments[ordinal]!
    let some declaration := result.reader.lctx.find? argument.fvarId!
      | throwError "uarg actual argument declaration disappeared"
    unless argument == Expr.fvar ⟨current.ngen.curr⟩ && declaration.toExpr == argument &&
        declaration.type == peelTypeAnnotations domain &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == entry.lctx.decls.size + ordinal do
      throwError "uarg exact fresh argument/domain/dependencies/name/binder/order changed"
    current := recursorIndexContext current name binderInfo (peelTypeAnnotations domain)
    let .ok next := ((monadLift (TypeChecker.whnf (body.instantiate1 argument)) : M Expr) current)
      | throwError "uarg independently checked actual body WHNF failed"
    opened := next
  unless result.terminal == opened && result.reader.ngen.curr == current.ngen.curr &&
      result.abstracted == result.reader.lctx.mkForall result.arguments result.terminal do
    throwError "uarg actual normalized terminal/argument generator/native abstraction changed"
  checkRetained entry result.reader

private def checkReturnedBase (entry base : Context) (result : ArgumentCapture) : MetaM Unit := do
  unless base.lctx.decls.size == entry.lctx.decls.size && base.ngen.curr == entry.ngen.curr do
    throwError "uarg temporary arguments leaked into the returned base reader"
  checkRetained entry base
  for argument in result.arguments do
    unless (base.lctx.find? argument.fvarId!).isNone && !result.abstracted.fvarsList.contains argument.fvarId! do
      throwError "uarg temporary argument survived native abstraction or returned-base lookup"
  let .ok (.sort _) := ((monadLift (TypeChecker.inferType result.abstracted) : M Expr) base)
    | throwError "uarg returned native abstracted type is not inferable at the original base"

private def checkArgument (reader : Context) (argument source : Expr) (count : Nat)
    (initialReduction : Bool := false) : MetaM ArgumentCapture := do
  let .ok inferred := ((monadLift (TypeChecker.inferType argument) : M Expr) reader)
    | throwError "uarg independent actual inference failed"
  unless inferred == source do throwError "uarg actual inferred source type changed"
  let .ok normalized := ((monadLift (TypeChecker.whnf inferred) : M Expr) reader)
    | throwError "uarg independent actual initial WHNF failed"
  if initialReduction then
    unless normalized != inferred do throwError "uarg initial source/WHNF distinction collapsed"
  let .ok (result, base) := capture argument reader
    | throwError "uarg actual opening/callback/base capture failed"
  checkSuffix reader normalized result count
  let .ok applicationType := ((monadLift (TypeChecker.inferType (mkAppN argument result.arguments)) : M Expr)
    result.reader)
    | throwError "uarg actual argument application inference failed"
  let .ok normalizedApplicationType := ((monadLift (TypeChecker.whnf applicationType) : M Expr) result.reader)
    | throwError "uarg actual argument application type WHNF failed"
  unless normalizedApplicationType == result.terminal do
    throwError "uarg actual applied recursive argument no longer has its same normalized terminal type"
  checkReturnedBase reader base result
  return result

private def checkFixture (reader : Context) (source : Expr) (count : Nat)
    (initialReduction : Bool := false) : MetaM ArgumentCapture := do
  let identifier := FVarId.mk `UArgRecursiveField
  let entry := { reader with lctx := reader.lctx.mkLocalDecl identifier `recursiveField source .default }
  return ← checkArgument entry (.fvar identifier) source count initialReduction

private def dependentArguments : Expr :=
  .forallE `carrier (.sort (.succ .zero))
    (.forallE `element (.bvar 0)
      (.forallE `agreement (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.const ``Nat []) .default) .implicit) .default

private def checkConstructorParameterReuse (reader : Context) (carrier : FVarId) : MetaM Unit := do
  let nat := Expr.const ``Nat []
  let list := Expr.const ``List [.zero]
  let stats : InductiveStats := {
    lctx := reader.lctx, levels := [], resultLevel := .succ .zero,
    indConsts := #[list], params := #[.fvar carrier], nindices := #[0], isNotZero := true }
  let source := Expr.forallE `carrier (.sort (.succ .zero))
    (.forallE `recursive (.forallE `argument nat (.app list (.bvar 1)) .default)
      (.app list (.bvar 1)) .default) .implicit
  let .ok (terminal, fields, recursive, fieldReader) := mkRecInfos.loopCtorArgs stats source
      (fun terminal fields recursive => do return (terminal, fields, recursive, ← readThe Context)) reader
    | throwError "uarg actual nonzero constructor-parameter field capture failed"
  unless stats.params.size == 1 && fields.size == 1 && recursive == fields &&
      terminal == Expr.app list (.fvar carrier) do
    throwError "uarg nonzero actual constructor parameters no longer exercise real recursive field reuse"
  let expectedType := Expr.forallE `argument nat (.app list (.fvar carrier)) .default
  let result ← checkArgument fieldReader fields[0]! expectedType 1
  unless result.terminal == Expr.app list (.fvar carrier) do
    throwError "uarg dummy zero-parameter adapter accidentally substituted an actual constructor parameter"

private def checkFailures (reader : Context) : MetaM Unit := do
  let nat := Expr.const ``Nat []
  let identifier := FVarId.mk `UArgFailureField
  let direct := { reader with lctx := reader.lctx.mkLocalDecl identifier `direct nat .default }
  let higherOrder := { reader with lctx := (reader.lctx.mkLocalDecl identifier `higherOrder
    (.forallE `argument nat nat .default) .default) }
  let argument := Expr.fvar identifier
  match capture (.mvar ⟨`UArgMissingMetavariable⟩) reader with
  | .error (.other message) =>
    unless message == "kernel type checker does not support meta variables" do
      throwError "uarg actual inference exception changed"
  | _ => throwError "uarg metavariable inference failure must propagate"
  match capture (.bvar 0) reader with
  | .error (.other _) => pure ()
  | _ => throwError "uarg loose-bound-variable inference failure must propagate"
  let noInferenceFuel := { direct with fuel := { direct.fuel with recDepth := 0 } }
  match capture argument noInferenceFuel with
  | .error .deepRecursion => pure ()
  | _ => throwError "uarg inference recursion fuel failure must propagate"
  let noInitialNormalization := { direct with fuel := { direct.fuel with whnf := 0 } }
  match capture argument noInitialNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "uarg actual initial WHNF failure must propagate"
  let noBodyNormalization := { higherOrder with fuel := { higherOrder.fuel with whnf := 0 } }
  match capture argument noBodyNormalization with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "uarg actual post-allocation body WHNF failure must propagate"
  let noOpeningFuel := { direct with fuel := { direct.fuel with inductiveFuel := 0 } }
  match capture argument noOpeningFuel with
  | .error .deepRecursion => pure ()
  | _ => throwError "uarg zero opening fuel must fail at the normalized terminal"
  let terminalOnly := { higherOrder with fuel := { higherOrder.fuel with inductiveFuel := 1 } }
  match capture argument terminalOnly with
  | .error .deepRecursion => pure ()
  | _ => throwError "uarg allocated argument requires fuel for its normalized terminal"
  let oneFuel := { direct with fuel := { direct.fuel with inductiveFuel := 1 } }
  discard <| checkArgument oneFuel argument nat 0
  let twoFuel := { higherOrder with fuel := { higherOrder.fuel with inductiveFuel := 2 } }
  discard <| checkArgument twoFuel argument (.forallE `argument nat nat .default) 1
  let message := "recursive-argument callback failure"
  match mkRecInfos.loopUArgs argument (fun _ _ => (throw (.other message) : M Unit)) direct with
  | .error (.other observed) =>
    unless observed == message do throwError "uarg callback error changed"
  | _ => throwError "uarg callback error must propagate"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `UArgOldCarrier
  let element := FVarId.mk `UArgOldElement
  let oldLet := FVarId.mk `UArgOldLet
  let seeded := { reader with
    ngen := { namePrefix := `UArgSeed, idx := 61 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 23)) false }
  let nat := Expr.const ``Nat []
  discard <| checkFixture seeded nat 0
  discard <| checkFixture seeded (.forallE `argument nat nat .default) 1
  discard <| checkFixture seeded
    (.forallE `first nat (.forallE `second (.const ``Bool [])
      (.forallE `third nat nat .instImplicit) .strictImplicit) .implicit) 3
  discard <| checkFixture seeded dependentArguments 3
  discard <| checkFixture seeded (.const ``ArgumentHeaderAlias []) 1 true
  discard <| checkFixture seeded (.forallE `first nat (.const ``ArgumentHeaderAlias []) .default) 2
  discard <| checkFixture seeded (.mdata {} (.forallE `argument nat nat .default)) 1 true
  discard <| checkFixture seeded
    (.forallE `first nat (.mdata {} (.forallE `second (.const ``Bool []) nat .implicit)) .default) 2
  let aliasResult ← checkFixture seeded
    (.forallE `argument (.const ``ArgumentDomainAlias []) nat .default) 1
  let some aliasDecl := aliasResult.reader.lctx.find? aliasResult.arguments[0]!.fvarId!
    | throwError "uarg retained alias-domain declaration missing"
  unless aliasDecl.type == Expr.const ``ArgumentDomainAlias [] do
    throwError "uarg unnecessarily normalized an allocated argument domain"
  discard <| checkFixture seeded (.forallE `argument (unary ``outParam nat) nat .default) 1
  discard <| checkFixture seeded (.forallE `argument (.mdata {} (unary ``outParam nat)) nat .default) 1
  discard <| checkFixture seeded
    (.forallE `argument (optionalDomain (.fvar carrier) (.fvar element)) nat .implicit) 1
  let letField := FVarId.mk `UArgLetRecursiveField
  let letSource := Expr.forallE `argument nat nat .default
  let letReader := { seeded with lctx := (seeded.lctx.mkLetDecl letField `recursiveLet letSource
    (.lam `argument nat (.bvar 0) .default) false) }
  discard <| checkArgument letReader (.fvar letField) letSource 1
  checkConstructorParameterReuse seeded carrier
  checkFailures seeded
  logInfo "uarg runtime: sixteen successful actual inference/initial/body-WHNF captures; dependent argument IDs/dependencies/order and aliases/metadata/annotations; retained locals/lets; abstraction returns to the base without temporary arguments; nonzero actual constructor parameters; eight inference/WHNF/fuel/callback failure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "uarg unexpected or forbidden axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "uarg audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "uarg new module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundations (nativeInterfaces : List Name) : MetaM Unit := do
  let environment ← getEnv
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``TrProj.weak', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.defeqDFC', `Lean4Lean.Verify.Typing.Lemmas),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas),
      (``VEnv.HasType.defeqU_r, `Lean4Lean.Theory.Typing.UniqueTyping)] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? moduleName do
      throwError "uarg inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "uarg inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited uarg foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "uarg inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context uarg abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "uarg native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "uarg native interface provenance changed: {name}"
    logInfo m!"pinned existing native uarg interface: {name}"

#print axioms actualNativeGetterCapturesTheSameInferredOpening
#print axioms exactSupportedOpeningDerivesItsSameActualTranslatedHistory
#print axioms sameOpeningHistoryTypesOnlyTheActualAppliedRecursiveArgument
#print axioms typedArgumentAbstractionReturnsToTheInitialParentModel
#print axioms argumentAbstractionAtTheTemporaryReaderWeakensAcrossTheSameSuffix
#print axioms typedArgumentEndpointPairsItsActualApplicationAndTerminalType
#print axioms actualGetterDerivesOneFinalArgumentModelWithoutConstructorParameterBounds
#print axioms scopedTypedArgumentCpsLeavesMotiveHypothesisAndMinorTypingExplicit
#print axioms retainedParentLocalCannotUseIdentityArgumentWeakening
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``annotationPeelingDoesNotNormalizeAnAlias,
      ``metadataFieldBarrierKeepsItsActualNativeDomain,
      ``discardedOptionalDefaultIsNotAStoredDependency,
      ``retainedParentLocalCannotUseIdentityArgumentWeakening,
      ``openingFailureCannotSupplySuccessfulTypedOutputs,
      ``adapterHasNoOriginalConstructorParameters,
      ``adapterCannotReuseAParameterAtAnyArgumentPosition,
      ``actualInitialWhnfCannotChooseAnotherNormalizedHeader,
      ``actualInferenceCannotChooseAnotherStoredSourceType,
      ``actualOpeningRetainsInferenceInitialWhnfAndOneArgumentHistory,
      ``actualArgumentSuffixDropPreservesTheInitialParentModel,
      ``unary, ``optionalDomain, ``equalityDomain, ``captureTuple, ``capture, ``checkRetained,
      ``checkSuffix, ``checkReturnedBase, ``checkArgument, ``checkFixture, ``dependentArguments,
      ``checkConstructorParameterReuse, ``checkFailures, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``actualNativeOpeningScopeDoesNotTypeGeneratedHypotheses,
      ``actualOpeningArgumentsAreTheSameDeclaredNativeFields,
      ``actualNativeGetterCapturesTheSameInferredOpening] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``normalizedSourceTranslationRemainsAnExplicitSemanticPremise,
      ``normalizedSourceTypingUsesTheCompatibleInferenceAndWhnfSupport,
      ``exactOpeningSupportKeepsInitialAndBodyNormalizationObligationsSeparate,
      ``exactSupportedOpeningDerivesItsSameActualTranslatedHistory,
      ``sameOpeningHistoryDerivesTheActualTerminalReaderCorrespondence,
      ``sameOpeningHistoryTypesOnlyTheActualAppliedRecursiveArgument,
      ``sameOpeningHistoryConstructsTheMixedSuffixFromOnlyItsInitialModel,
      ``typedArgumentAbstractionReturnsToTheInitialParentModel,
      ``argumentAbstractionAtTheTemporaryReaderWeakensAcrossTheSameSuffix,
      ``typedArgumentEndpointDerivesItsExactTemporaryReaderCorrespondence,
      ``typedArgumentEndpointTranslatesItsExactTerminal,
      ``typedArgumentEndpointKeepsExactlyItsAllocatedArgumentArray,
      ``typedArgumentEndpointPairsItsActualApplicationAndTerminalType,
      ``argumentEndpointAbstractionStillRequiresExplicitBodyTyping,
      ``actualGetterDerivesOneFinalArgumentModelWithoutConstructorParameterBounds,
      ``scopedTypedArgumentCpsLeavesMotiveHypothesisAndMinorTypingExplicit] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveUArgTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveUArgTranslation native
  auditModule `Lean4Lean.Verify.InductiveUArgTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "uarg translation: 30 proof controls; pinned inherited foundations and eight existing native interfaces; global native range axiom forbidden; same terminal application typing and explicit arbitrary-body abstraction at the initial parent model; no motive/IH/minor domain correctness claim"

end InductiveUArgTranslationTest
