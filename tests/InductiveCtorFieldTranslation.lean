import Lean4Lean.Verify.InductiveBinderTyping
import Lean4Lean.Verify.InductiveMotiveContextTranslationCPS
import Lean4Lean.Verify.InductiveCtorFieldTrace
import Lean4Lean.Verify.InductiveCtorFieldTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveCtorFieldTranslationTest

abbrev ConstructorTailAlias := Nat → Nat

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def equalityDomain (carrier left right : Expr) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) carrier) left) right

private theorem metadataIsNotASyntacticConstructorBinder (metadata : MData)
    (name : Name) (domain body : Expr) (binderInfo : BinderInfo) :
    ∀ binderName binderDomain binderBody binderKind,
      Expr.mdata metadata (.forallE name domain body binderInfo) ≠
        .forallE binderName binderDomain binderBody binderKind := by
  intros
  intro equality
  cases equality

private theorem peeledAnnotationStoresItsExactCarrier (carrier : FVarId) :
    peelTypeAnnotations (unary ``outParam (.fvar carrier)) = .fvar carrier := by
  simp [unary, peelTypeAnnotations]

private theorem metadataBarrierStillKeepsTheRawField (metadata : MData) (source : Expr) :
    peelTypeAnnotations (.mdata metadata source) = .mdata metadata source := rfl

private theorem runtimeFailureDoesNotSupplySuccessfulFieldOutputs
    {ResultType : Type} (action : M ResultType) (reader : Context)
    (failure : Lean.Kernel.Exception) (failed : action reader = .error failure) :
    ∀ result, action reader ≠ .ok result := by
  intro result successful
  rw [failed] at successful
  cases successful

private theorem stoppedFieldTraceKeepsEveryActualOutput
    (stats : InductiveStats) (source : Expr) (index : Nat)
    (fields recursive : Array Expr) (reader : Context)
    (terminal : ∀ name domain body binderInfo, source ≠ .forallE name domain body binderInfo) :
    RecursorCtorFieldTrace stats source index fields recursive reader
      source index fields recursive reader := .stop terminal

private theorem parameterReuseDoesNotAllocateAFieldOrNormalizeTheBody
    (stats : InductiveStats) (name : Name) (domain body parameter : Expr) (binderInfo : BinderInfo)
    (index finalIndex : Nat) (fields recursive finalFields finalRecursive : Array Expr)
    (reader finalReader : Context) (terminal : Expr)
    (selected : stats.params[index]? = some parameter)
    (tail : RecursorCtorFieldTrace stats (body.instantiate1 parameter) (index + 1)
      fields recursive reader terminal finalIndex finalFields finalRecursive finalReader) :
    RecursorCtorFieldTrace stats (.forallE name domain body binderInfo) index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader := .parameter selected tail

private theorem classificationOccursAtTheActualNewFieldReader
    (stats : InductiveStats) (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
    (index finalIndex : Nat) (fields recursive finalFields finalRecursive : Array Expr)
    (reader finalReader : Context) (terminal : Expr) (classification : Option Nat)
    (selected : stats.params[index]? = none)
    (classified : isRecArg stats domain
      (recursorIndexContext reader name binderInfo (peelTypeAnnotations domain)) = .ok classification)
    (tail : RecursorCtorFieldTrace stats (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩))
      (index + 1) (fields.push (.fvar ⟨reader.ngen.curr⟩))
      (if classification.isSome then recursive.push (.fvar ⟨reader.ngen.curr⟩) else recursive)
      (recursorIndexContext reader name binderInfo (peelTypeAnnotations domain))
      terminal finalIndex finalFields finalRecursive finalReader) :
    RecursorCtorFieldTrace stats (.forallE name domain body binderInfo) index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader := .field selected classified tail

private theorem nativeFieldArrayMatchesExactlyTheNativeAllocationSuffix
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursive finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    ∃ allocated : List LocalDecl,
      finalReader.lctx.toList = allocated.reverse ++ reader.lctx.toList ∧
      finalFields.toList = fields.toList ++ allocated.map LocalDecl.toExpr ∧
      ∀ declaration ∈ allocated,
        declaration.value? (allowNondep := true) = none ∧ declaration.kind = .default :=
  trace.allocations

private theorem actualRecursiveSelectionOnlyEstablishesASublist
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursive finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (selected : recursive.toList.Sublist fields.toList) :
    finalRecursive.toList.Sublist finalFields.toList := trace.recursiveSublist selected

private theorem actualTerminalIsRawAndNoLongerASyntacticForall
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursive finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader) :
    ∀ name domain body binderInfo, terminal ≠ .forallE name domain body binderInfo := trace.terminal

private theorem actualNativeFieldScopeDoesNotProveMinorReaderTyping
    {stats : InductiveStats} {source terminal : Expr} {index finalIndex : Nat}
    {fields recursive finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    (trace : RecursorCtorFieldTrace stats source index fields recursive reader
      terminal finalIndex finalFields finalRecursive finalReader)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := trace.scope readerWF reserved

private theorem actualGetterCarriesTheSameFieldTraceAndRecursiveSubset
    (stats : InductiveStats) (source : Expr) (reader : Context)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    (mkRecInfos.loopCtorArgs stats source
      (fun terminal fields recursive => do return (terminal, fields, recursive, ← readThe Context))
      reader).WF fun result =>
      ∃ finalIndex, RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2 ∧
        reader.RecursorScopeFrame result.2.2.2 ∧
        RecursorFieldsDeclared result.2.2.2.lctx result.2.1 ∧
        result.2.2.1.toList.Sublist result.2.1.toList :=
  mkRecInfos.loopCtorArgs.getTrace stats source reader readerWF reserved

private theorem semanticFieldOnlyTransportNeedsActualZeroParameters (stats : InductiveStats) :
    stats.params.size ≤ 0 ↔ stats.params.size = 0 := by omega

private theorem nativeParameterReuseDoesNotDischargeFieldOnlySemanticTransport
    (stats : InductiveStats) (parameters : 0 < stats.params.size) :
    ¬ stats.params.size = 0 := by omega

private theorem parentLocalAbstractionCannotUseIdentityWeakening :
    (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 =
      .forallE (.sort .zero) (.bvar 2) ∧
      (VExpr.forallE (.sort .zero) (.bvar 1)).liftN 1 ≠
        .forallE (.sort .zero) (.bvar 1) := by
  constructor
  · rfl
  · intro equality
    cases equality

private theorem droppingOnlyActualFieldsPreservesTheInitialParentModel
    {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) :
    final.dropN ids.length extension.bound = initial := extension.drop_eq

private theorem sameForallOpeningTranslatesItsExactRawInstantiatedBody
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {reader : Context}
    {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
    {semanticDomain bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes reader.lctx virtual)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (translated : TrExprS env universes virtual (.forallE name domain body binderInfo)
      (.forallE semanticDomain bodySemantic))
    (domainTyped : env.HasType universes.length virtual.toCtx semanticDomain (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled convertedBody, CtorFieldOpening env universes reader virtual name domain body binderInfo
      semanticDomain bodySemantic level peeled convertedBody :=
  translatedForallCtorFieldOpening envWF constants definitions correspondence reserved translated domainTyped uniform

private theorem oneFieldOpeningBuildsOnlyItsActualMixedContextPush
    {env : VEnv} {universes : List Name} {virtual : VLCtx} {reader : Context}
    {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
    {semanticDomain bodySemantic peeled convertedBody : VExpr} {level : VLevel}
    (opening : CtorFieldOpening env universes reader virtual name domain body binderInfo
      semanticDomain bodySemantic level peeled convertedBody)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (converted : model.vlctx = virtual)
    (reserved : ContextReserved reader.lctx reader.ngen) :
    (ctorFieldMLCtx reader model name domain peeled binderInfo).WF env universes ∧
      (ctorFieldMLCtx reader model name domain peeled binderInfo).lctx =
        (recursorIndexContext reader name binderInfo (peelTypeAnnotations domain)).lctx ∧
      (ctorFieldMLCtx reader model name domain peeled binderInfo).vlctx =
        peeledIndexVirtualContext virtual ⟨reader.ngen.curr⟩ domain peeled :=
  opening.mixedContext model modelWF native converted reserved

private theorem fieldExtensionSelectsTheExactNativeAbstractionOrder
    {env : VEnv} {universes : List Name} {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final) (modelWF : final.WF env universes)
    {body : Expr} (closed : body.looseBVarRange' = 0) :
    final.lctx.mkForall (ids.map Expr.fvar).toArray body =
      final.mkForall ids.length extension.bound body :=
  extension.nativeBodyAbstraction modelWF closed

private theorem fieldAbstractionDropsExactlyTheConstructedMixedContextSuffix
    {env : VEnv} {universes : List Name} {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {body : Expr} {semantic : VExpr}
    (translated : TrExpr env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    TrExpr env universes initial.vlctx (final.lctx.mkForall (ids.map Expr.fvar).toArray body)
        (final.mkForall' ids.length extension.bound semantic) ∧
      env.IsType universes.length initial.vlctx.toCtx (final.mkForall' ids.length extension.bound semantic) :=
  extension.typedBodyAbstraction envWF modelWF translated typed

private theorem currentFieldReaderAbstractionMustLiftAcrossThatSameSuffix
    {env : VEnv} {universes : List Name} {initial final : TypeChecker.MLCtx} {ids : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (envWF : env.WF) (modelWF : final.WF env universes)
    {body : Expr} {semantic : VExpr}
    (translated : TrExpr env universes final.vlctx body semantic)
    (typed : env.IsType universes.length final.vlctx.toCtx semantic) :
    TrExpr env universes final.vlctx (final.lctx.mkForall (ids.map Expr.fvar).toArray body)
        ((final.mkForall' ids.length extension.bound semantic).liftN ids.length) ∧
      env.IsType universes.length final.vlctx.toCtx
        ((final.mkForall' ids.length extension.bound semantic).liftN ids.length) :=
  extension.typedBodyAbstractionAtFinal envWF modelWF translated typed

private theorem typedFieldEndpointDerivesItsExactFieldReaderCorrespondence
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursive : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader terminal finalIndex fields recursive finalReader}
    {initial final : TypeChecker.MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic) :
    final.WF env universes ∧ final.lctx = finalReader.lctx ∧
      TrLCtx env universes finalReader.lctx final.vlctx := endpoint.context

private theorem typedFieldEndpointTranslatesTheSameRawNativeTerminal
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursive : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader terminal finalIndex fields recursive finalReader}
    {initial final : TypeChecker.MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic) :
    ∃ finalSemantic, TrExprS env universes final.vlctx terminal finalSemantic := endpoint.terminalTranslation

private theorem typedFieldEndpointRetainsExactlyItsActualSelectedFieldArray
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursive : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader terminal finalIndex fields recursive finalReader}
    {initial final : TypeChecker.MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic) :
    ∃ ids, IndexMLCtxExtension initial ids final ∧ fields.toList = ids.map Expr.fvar := by
  obtain ⟨_, _, _, _, _, _, ids, extension, selected⟩ := endpoint
  exact ⟨ids, extension, selected⟩

private theorem fieldEndpointAbstractionStillNeedsTheExplicitBodyTypingPremise
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursive : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader terminal finalIndex fields recursive finalReader}
    {initial final : TypeChecker.MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial final semantic)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted,
      TrExpr env universes initial.vlctx (finalReader.lctx.mkForall fields body) abstracted ∧
      env.IsType universes.length initial.vlctx.toCtx abstracted :=
  endpoint.typedFieldAbstraction envWF translated typed

private def captureTuple (stats : InductiveStats) (source : Expr) :
    M (Expr × Array Expr × Array Expr × Context) :=
  mkRecInfos.loopCtorArgs stats source fun terminal fields recursive => do
    return (terminal, fields, recursive, ← readThe Context)

private theorem actualGetterConstructsOneFinalModelFromOneInitialModel
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (source : Expr) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semantic : VExpr} (translated : TrExprS env universes model.vlctx source semantic)
    (support : (captureTuple stats source reader).WF fun result =>
      ∀ finalIndex (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2),
        CtorFieldTraceAnnotationSupport env universes trace) :
    (captureTuple stats source reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2.2 ∧
      RecursorFieldsDeclared result.2.2.2.lctx result.2.1 ∧
      result.2.2.1.toList.Sublist result.2.1.toList ∧
      ∃ finalIndex, ∃ trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2, ∃ finalModel,
        CtorFieldModelEndpoint env universes trace model finalModel semantic :=
  mkRecInfos.loopCtorArgs.getTranslatedFields stats source reader envWF constants definitions
    fieldOnly model modelWF native reserved translated support

private theorem scopedTypedFieldCpsKeepsLaterMinorCorrectnessAsAnInput
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (source : Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : TypeChecker.MLCtx) (modelWF : model.WF env universes)
    (native : model.lctx = reader.lctx) (reserved : ContextReserved reader.lctx reader.ngen)
    {semantic : VExpr} (translated : TrExprS env universes model.vlctx source semantic)
    (support : (captureTuple stats source reader).WF fun result =>
      ∀ finalIndex (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        result.1 finalIndex result.2.1 result.2.2.1 result.2.2.2),
        CtorFieldTraceAnnotationSupport env universes trace)
    (nextWF : ∀ terminal finalIndex fields recursive finalReader
      (trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
        terminal finalIndex fields recursive finalReader) finalModel,
      reader.RecursorScopeFrame finalReader →
      RecursorFieldsDeclared finalReader.lctx fields → recursive.toList.Sublist fields.toList →
      CtorFieldModelEndpoint env universes trace model finalModel semantic →
      (next terminal fields recursive finalReader).WF post) :
    (mkRecInfos.loopCtorArgs stats source next reader).WF post :=
  mkRecInfos.loopCtorArgs.scopedTranslatedFields stats source next reader post
    envWF constants definitions fieldOnly model modelWF native reserved translated support nextWF

private structure FieldCapture where
  terminal : Expr
  fields : Array Expr
  recursive : Array Expr
  reader : Context

private def capture (stats : InductiveStats) (source : Expr) : M FieldCapture :=
  mkRecInfos.loopCtorArgs stats source fun terminal fields recursive => do
    return { terminal, fields, recursive, reader := ← readThe Context }

private def fixtureStats (reader : Context) (heads : Array Expr) (params : Array Expr := #[])
    (indices : Array Nat := #[0]) : InductiveStats :=
  { lctx := reader.lctx, levels := [], resultLevel := .succ .zero,
    indConsts := heads, params, nindices := indices, isNotZero := true }

private def checkRetained (before after : Context) : MetaM Unit := do
  for declaration in before.lctx.decls.toList.filterMap id do
    let some found := after.lctx.find? declaration.fvarId
      | throwError "constructor-fields retained declaration disappeared"
    unless found.toExpr == declaration.toExpr && found.type == declaration.type &&
        found.userName == declaration.userName && found.binderInfo == declaration.binderInfo &&
        found.index == declaration.index && found.deps == declaration.deps &&
        found.value? (allowNondep := true) == declaration.value? (allowNondep := true) do
      throwError "constructor-fields retained declaration changed type/dependencies/value/order"
  unless before.lparams == after.lparams && before.safety == after.safety &&
      before.allowPrimitive == after.allowPrimitive && before.fuel.inductiveFuel == after.fuel.inductiveFuel &&
      before.fuel.whnf == after.fuel.whnf && before.fuel.whnfEager == after.fuel.whnfEager &&
      before.fuel.lazyDelta == after.fuel.lazyDelta && before.fuel.etaExpand == after.fuel.etaExpand &&
      before.fuel.recDepth == after.fuel.recDepth do
    throwError "constructor-fields nonallocation reader fields changed"

private def checkFixture (reader : Context) (stats : InductiveStats) (source : Expr)
    (fieldCount : Nat) (recursiveOrdinals : Array Nat) : MetaM FieldCapture := do
  let .ok result := capture stats source reader
    | throwError "constructor-fields actual capture failed"
  unless result.fields.size == fieldCount && result.recursive.size == recursiveOrdinals.size &&
      result.reader.lctx.decls.size == reader.lctx.decls.size + fieldCount do
    throwError "constructor-fields field/recursive/native allocation counts changed"
  let mut opened := source
  for param in stats.params do
    let .forallE _ _ body _ := opened
      | throwError "constructor-fields constructor parameter telescope ended early"
    opened := body.instantiate1 param
  let mut generator := reader.ngen
  for ordinal in [:result.fields.size] do
    let .forallE name domain body binderInfo := opened
      | throwError "constructor-fields actual field telescope ended early"
    let value := result.fields[ordinal]!
    let some declaration := result.reader.lctx.find? value.fvarId!
      | throwError "constructor-fields actual allocated field disappeared"
    unless value == Expr.fvar ⟨generator.curr⟩ && declaration.toExpr == value &&
        declaration.userName == name && declaration.binderInfo == binderInfo &&
        declaration.index == reader.lctx.decls.size + ordinal &&
        declaration.type == peelTypeAnnotations domain &&
        declaration.deps == (peelTypeAnnotations domain).fvarsList do
      throwError "constructor-fields exact field ID/domain/dependencies/name/binder/order changed"
    opened := body.instantiate1 value
    generator := generator.next
  unless result.terminal == opened && result.reader.ngen.curr == generator.curr do
    throwError "constructor-fields raw terminal instantiation or classifier-local freshness changed"
  let expectedRecursive := recursiveOrdinals.map (fun ordinal => result.fields[ordinal]!)
  unless result.recursive == expectedRecursive do
    throwError "constructor-fields recursive subset or its exact source-field order changed"
  checkRetained reader result.reader
  return result

private def dependentFields : Expr :=
  .forallE `carrier (.sort (.succ .zero))
    (.forallE `element (.bvar 0)
      (.forallE `agreement (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
        (.const ``Nat []) .default) .implicit) .default

private def parameterFields : Expr :=
  .forallE `carrier (.sort (.succ .zero))
    (.forallE `element (.bvar 0)
      (.forallE `tail (.app (.const ``List [.zero]) (.bvar 1))
        (.app (.const ``List [.zero]) (.bvar 2)) .default) .default) .implicit

private def checkRawTerminal (reader : Context) (stats : InductiveStats) : MetaM Unit := do
  let aliasSource := Expr.const ``ConstructorTailAlias []
  let source := Expr.forallE `value (.const ``Nat []) aliasSource .default
  let result ← checkFixture reader stats source 1 #[0]
  let .ok normalized := ((monadLift (TypeChecker.whnf result.terminal) : M Expr) result.reader)
    | throwError "constructor-fields raw alias control could not normalize separately"
  unless result.terminal == aliasSource && normalized != result.terminal do
    throwError "constructor-fields unexpectedly normalized the raw constructor remainder"
  discard <| checkFixture reader stats aliasSource 0 #[]
  discard <| checkFixture reader stats (.mdata {} source) 0 #[]
  discard <| checkFixture reader stats
    (.letE `terminal (.const ``Nat []) (.lit (.natVal 0)) source false) 0 #[]

private def checkFailures (reader : Context) (stats : InductiveStats) : MetaM Unit := do
  let terminal := Expr.const ``Nat []
  let field := Expr.forallE `field terminal terminal .default
  let exhausted := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
  match capture stats terminal exhausted with
  | .error .deepRecursion => pure ()
  | _ => throwError "constructor-fields zero fuel must fail even at a terminal"
  let oneFuel := { reader with fuel := { reader.fuel with inductiveFuel := 1 } }
  discard <| checkFixture oneFuel stats terminal 0 #[]
  match capture stats field oneFuel with
  | .error .deepRecursion => pure ()
  | _ => throwError "constructor-fields field requires fuel for its raw terminal"
  let twoFuel := { reader with fuel := { reader.fuel with inductiveFuel := 2 } }
  discard <| checkFixture twoFuel stats field 1 #[0]
  let higherOrder := Expr.forallE `function
    (.forallE `first terminal (.forallE `second terminal terminal .default) .default) terminal .default
  match capture stats higherOrder twoFuel with
  | .error .deepRecursion => pure ()
  | _ => throwError "constructor-fields recursive classifier fuel failure must propagate"
  let noNormalizationFuel := { reader with fuel := { reader.fuel with whnf := 0 } }
  match capture stats field noNormalizationFuel with
  | .error .deterministicTimeout => pure ()
  | _ => throwError "constructor-fields actual classifier normalization failure must propagate"
  let message := "constructor-field callback failure"
  match mkRecInfos.loopCtorArgs stats terminal
      (fun _ _ _ => (throw (.other message) : M Unit)) reader with
  | .error (.other observed) =>
    unless observed == message do throwError "constructor-fields callback error changed"
  | _ => throwError "constructor-fields callback error must propagate"

private def runtimeFixtures (reader : Context) : MetaM Unit := do
  let carrier := FVarId.mk `CtorFieldOldCarrier
  let element := FVarId.mk `CtorFieldOldElement
  let oldLet := FVarId.mk `CtorFieldOldLet
  let seeded := { reader with
    ngen := { namePrefix := `CtorFieldSeed, idx := 53 }
    lctx := reader.lctx.mkLocalDecl carrier `oldCarrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl element `oldElement (.fvar carrier) .default
      |>.mkLetDecl oldLet `oldLet (.const ``Nat []) (.lit (.natVal 19)) false }
  let nat := Expr.const ``Nat []
  let stats := fixtureStats seeded #[nat]
  discard <| checkFixture seeded stats nat 0 #[]
  discard <| checkFixture seeded stats
    (.forallE `flag (.const ``Bool [])
      (.forallE `text (.const ``String []) nat .implicit) .default) 2 #[]
  discard <| checkFixture seeded stats (.forallE `next nat nat .default) 1 #[0]
  let function := Expr.forallE `argument nat nat .implicit
  let mixed := Expr.forallE `flag (.const ``Bool [])
    (.forallE `next nat
      (.forallE `function function
        (.forallE `text (.const ``String []) nat .instImplicit) .strictImplicit) .implicit) .default
  discard <| checkFixture seeded stats mixed 4 #[1, 2]
  discard <| checkFixture seeded (fixtureStats seeded #[nat, .const ``Bool []] #[] #[0, 0])
    (.forallE `flag (.const ``Bool []) (.forallE `next nat nat .default) .default) 2 #[0, 1]
  discard <| checkFixture seeded stats dependentFields 3 #[]
  discard <| checkFixture seeded
    (fixtureStats seeded #[.const ``List [.zero]] #[.fvar carrier]) parameterFields 2 #[1]
  discard <| checkFixture seeded stats
    (.forallE `annotated (unary ``outParam nat) nat .implicit) 1 #[0]
  discard <| checkFixture seeded stats
    (.forallE `metadata (.mdata {} (unary ``outParam nat)) nat .default) 1 #[0]
  checkRawTerminal seeded stats
  checkFailures seeded stats
  logInfo "constructor-fields runtime: fifteen successful native captures; exact fields/recursive subset/IDs/dependencies; raw constructor body and parameter reuse; five fuel/classifier/callback failure controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "constructor-fields unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "constructor-fields audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "constructor-fields new module-owned axiom {name}"
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
      throwError "constructor-fields inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "constructor-fields inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name (logical ++ [``sorryAx])
    logInfo m!"pinned inherited constructor-field foundation: {name} from {moduleName}"
  for name in [``TypeChecker.MLCtx.WF.mkForall_eq, ``TypeChecker.MLCtx.WF.mkForall_tr,
      ``TypeChecker.MLCtx.WF.mkForall_trS] do
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.TypeChecker.Basic do
      throwError "constructor-fields inherited mixed-context abstraction provenance changed: {name}"
    auditDeclaration name (logical ++ [``sorryAx] ++ nativeInterfaces)
    logInfo m!"pinned inherited mixed-context field abstraction: {name}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "constructor-fields native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name == environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "constructor-fields native interface provenance changed: {name}"
    logInfo m!"pinned existing native constructor-field interface: {name}"

#print axioms actualNativeFieldScopeDoesNotProveMinorReaderTyping
#print axioms actualGetterCarriesTheSameFieldTraceAndRecursiveSubset
#print axioms parentLocalAbstractionCannotUseIdentityWeakening
#print axioms sameForallOpeningTranslatesItsExactRawInstantiatedBody
#print axioms fieldAbstractionDropsExactlyTheConstructedMixedContextSuffix
#print axioms currentFieldReaderAbstractionMustLiftAcrossThatSameSuffix
#print axioms typedFieldEndpointDerivesItsExactFieldReaderCorrespondence
#print axioms actualGetterConstructsOneFinalModelFromOneInitialModel
#print axioms scopedTypedFieldCpsKeepsLaterMinorCorrectnessAsAnInput
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let allocationInterfaces := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq] ++ allocationInterfaces
  let native := logical ++ [``sorryAx] ++ nativeInterfaces
  for name in [``metadataIsNotASyntacticConstructorBinder, ``peeledAnnotationStoresItsExactCarrier,
      ``metadataBarrierStillKeepsTheRawField, ``runtimeFailureDoesNotSupplySuccessfulFieldOutputs,
      ``stoppedFieldTraceKeepsEveryActualOutput,
      ``parameterReuseDoesNotAllocateAFieldOrNormalizeTheBody,
      ``classificationOccursAtTheActualNewFieldReader,
      ``actualRecursiveSelectionOnlyEstablishesASublist,
      ``actualTerminalIsRawAndNoLongerASyntacticForall,
      ``semanticFieldOnlyTransportNeedsActualZeroParameters,
      ``nativeParameterReuseDoesNotDischargeFieldOnlySemanticTransport,
      ``parentLocalAbstractionCannotUseIdentityWeakening,
      ``droppingOnlyActualFieldsPreservesTheInitialParentModel,
      ``unary, ``equalityDomain, ``captureTuple, ``capture, ``fixtureStats, ``checkRetained,
      ``checkFixture, ``dependentFields, ``parameterFields, ``checkRawTerminal,
      ``checkFailures, ``runtimeFixtures] do
    auditDeclaration name logical
  for name in [``nativeFieldArrayMatchesExactlyTheNativeAllocationSuffix,
      ``actualNativeFieldScopeDoesNotProveMinorReaderTyping,
      ``actualGetterCarriesTheSameFieldTraceAndRecursiveSubset] do
    auditDeclaration name (logical ++ allocationInterfaces)
  for name in [``sameForallOpeningTranslatesItsExactRawInstantiatedBody,
      ``oneFieldOpeningBuildsOnlyItsActualMixedContextPush,
      ``fieldExtensionSelectsTheExactNativeAbstractionOrder,
      ``fieldAbstractionDropsExactlyTheConstructedMixedContextSuffix,
      ``currentFieldReaderAbstractionMustLiftAcrossThatSameSuffix,
      ``typedFieldEndpointDerivesItsExactFieldReaderCorrespondence,
      ``typedFieldEndpointTranslatesTheSameRawNativeTerminal,
      ``typedFieldEndpointRetainsExactlyItsActualSelectedFieldArray,
      ``fieldEndpointAbstractionStillNeedsTheExplicitBodyTypingPremise,
      ``actualGetterConstructsOneFinalModelFromOneInitialModel,
      ``scopedTypedFieldCpsKeepsLaterMinorCorrectnessAsAnInput] do
    auditDeclaration name native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveCtorFieldTrace (logical ++ allocationInterfaces)
  auditModule `Lean4Lean.Verify.InductiveCtorFieldTranslation native
  auditModule `Lean4Lean.Verify.InductiveCtorFieldTranslationCPS native
  auditFoundations nativeInterfaces
  let reader : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures reader
  logInfo "constructor-fields translation: 27 proof controls; inherited foundations pinned separately; typed endpoint before recursive hypotheses/minor allocations only"

end InductiveCtorFieldTranslationTest
