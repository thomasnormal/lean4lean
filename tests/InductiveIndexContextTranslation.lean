import Lean4Lean.Verify.InductiveAnnotationContext
import Lean4Lean.Verify.InductiveIndexContextTranslation
import Lean4Lean.Verify.InductiveIndexOpeningTranslation
import Lean4Lean.Verify.InductiveAnnotationTranslation
import Lean4Lean.Verify.InductiveBinderTyping
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexContextTranslationTest

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def binary (name : Name) (carrier payload : Expr) : Expr :=
  .app (.app (.const name [.succ .zero]) carrier) payload

private def optionalDomain (carrier payload : FVarId) : Expr :=
  binary ``optParam (.fvar carrier) (.fvar payload)

private def tacticDomain (carrier : FVarId) : Expr :=
  binary ``autoParam (.fvar carrier) (.const ``Lean.Syntax.missing [])

private def nestedDomain (carrier payload : FVarId) : Expr :=
  unary ``outParam (unary ``semiOutParam (optionalDomain carrier payload))

private theorem optionalPeelsToExistingCarrier (carrier payload : FVarId) :
    peelTypeAnnotations (optionalDomain carrier payload) = .fvar carrier := by
  simp [optionalDomain, binary, peelTypeAnnotations]

private theorem tacticPeelsToExistingCarrier (carrier : FVarId) :
    peelTypeAnnotations (tacticDomain carrier) = .fvar carrier := by
  simp [tacticDomain, binary, peelTypeAnnotations]

private theorem nestedPeelsToExistingCarrier (carrier payload : FVarId) :
    peelTypeAnnotations (nestedDomain carrier payload) = .fvar carrier := by
  simp [nestedDomain, unary, optionalDomain, binary, peelTypeAnnotations]

private theorem optionalNativeDependenciesAreNonempty (carrier payload : FVarId) :
    (peelTypeAnnotations (optionalDomain carrier payload)).fvarsList = [carrier] := by
  rw [optionalPeelsToExistingCarrier]
  rfl

private theorem discardedDefaultNotANativeDependency (carrier payload : FVarId) :
    (optionalDomain carrier payload).fvarsList = [carrier, payload] ∧
      (peelTypeAnnotations (optionalDomain carrier payload)).fvarsList = [carrier] := by
  exact ⟨rfl, optionalNativeDependenciesAreNonempty carrier payload⟩

private theorem nestedNativeDependenciesAreNonempty (carrier payload : FVarId) :
    (peelTypeAnnotations (nestedDomain carrier payload)).fvarsList = [carrier] := by
  rw [nestedPeelsToExistingCarrier]
  rfl

private theorem metadataBarrierRetainsBothNativeDependencies (metadata : MData)
    (carrier payload : FVarId) :
    (peelTypeAnnotations (.mdata metadata (optionalDomain carrier payload))).fvarsList =
      [carrier, payload] := rfl

private theorem rawOptionalSemanticIsNotItsCarrier (carrier payload : VExpr) :
    VExpr.app (.app (.const ``optParam [.succ .zero]) carrier) payload ≠ carrier := by
  intro equal
  have sizeEquality := congrArg sizeOf equal
  simp only [VExpr.app.sizeOf_spec, VExpr.const.sizeOf_spec] at sizeEquality
  omega

private theorem rawConstantOptionalSemanticIsNotPeeledType :
    VExpr.app (.app (.const ``optParam [.succ .zero]) (.const ``Nat [])) (.const ``Nat.zero []) ≠
      VExpr.const ``Nat [] := by
  intro equal
  cases equal

private theorem anonymousBodyConversionKeepsPeeledWitness {env : VEnv} {universes : List Name}
    {context : VLCtx} {source body : Expr} {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx source semantic level) (envWF : env.WF)
    (definitions : CanonicalAnnotationDefinitions env) (contextWF : context.WF env universes.length)
    (bodyTranslation : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled, TrExprS env universes context (peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam semantic) :: context)
        ((none, .vlam peeled) :: context) ∧
      TrExpr env universes ((none, .vlam peeled) :: context) body bodySemantic :=
  spine.anonymousBodyTranslation envWF definitions contextWF bodyTranslation

private theorem bodyConversionOffersDefinitionalNotLiteralSemanticIdentity {env : VEnv}
    {universes : List Name} {context : VLCtx} {source body : Expr}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS env universes context) env universes.length
      context.toCtx source semantic level) (envWF : env.WF)
    (definitions : CanonicalAnnotationDefinitions env) (contextWF : context.WF env universes.length)
    (bodyTranslation : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled converted, TrExprS env universes context (peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam semantic) :: context)
        ((none, .vlam peeled) :: context) ∧
      TrExprS env universes ((none, .vlam peeled) :: context) body converted ∧
      env.IsDefEqU universes.length (peeled :: context.toCtx) converted bodySemantic :=
  spine.anonymousBodyStrongTranslation envWF definitions contextWF bodyTranslation

private theorem genericCarrierTypeRemainsExplicit {env : VEnv} {context : List VExpr}
    {carrier : VExpr} (constants : CanonicalAnnotationConstants env)
    (typed : env.HasType 0 context carrier (.sort (.succ .zero))) :
    env.HasType 0 context (.app (.const ``optParam [.succ .zero]) carrier)
      (.forallE carrier (.sort (.succ .zero))) := by
  have functionTyped := VEnv.HasType.const (env := env) (U := 0) (Γ := context)
    (ci := { uvars := 1, type := optParamDefinition.type }) constants.optParam
    (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
  simpa [optParamDefinition, VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar] using
    functionTyped.app typed

private theorem actualOptionalDomainTranslation {env : VEnv} {context : VLCtx}
    {carrier payload : FVarId} {semanticCarrier semanticPayload : VExpr}
    (constants : CanonicalAnnotationConstants env)
    (carrierTyped : env.HasType 0 context.toCtx semanticCarrier (.sort (.succ .zero)))
    (payloadTyped : env.HasType 0 context.toCtx semanticPayload semanticCarrier)
    (carrierTranslated : TrExprS env [] context (.fvar carrier) semanticCarrier)
    (payloadTranslated : TrExprS env [] context (.fvar payload) semanticPayload) :
    TrExprS env [] context (optionalDomain carrier payload)
      (.app (.app (.const ``optParam [.succ .zero]) semanticCarrier) semanticPayload) := by
  have functionTyped := VEnv.HasType.const (env := env) (U := 0) (Γ := context.toCtx)
    (ci := { uvars := 1, type := optParamDefinition.type }) constants.optParam
    (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
  simp only [optParamDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at functionTyped
  exact .app (genericCarrierTypeRemainsExplicit constants carrierTyped) payloadTyped
    (.app functionTyped carrierTyped (.const constants.optParam rfl rfl) carrierTranslated) payloadTranslated

private theorem actualOptionalDomainSpine {env : VEnv} {context : VLCtx}
    {carrier payload : FVarId} {semanticCarrier semanticPayload : VExpr}
    (envWF : env.WF) (contextTypes : OnCtx context.toCtx (env.IsType 0))
    (constants : CanonicalAnnotationConstants env)
    (carrierTyped : env.HasType 0 context.toCtx semanticCarrier (.sort (.succ .zero)))
    (payloadTyped : env.HasType 0 context.toCtx semanticPayload semanticCarrier)
    (carrierTranslated : TrExprS env [] context (.fvar carrier) semanticCarrier)
    (payloadTranslated : TrExprS env [] context (.fvar payload) semanticPayload) :
    TypedAnnotationSpine (TrExprS env [] context) env 0 context.toCtx (optionalDomain carrier payload)
      (.app (.app (.const ``optParam [.succ .zero]) semanticCarrier) semanticPayload) (.succ .zero) := by
  apply TypedAnnotationSpine.ofTrExprS envWF contextTypes constants
  · simp [optionalDomain, binary, UniformAnnotationUniverse, VLevel.ofLevel]
  · exact actualOptionalDomainTranslation constants carrierTyped payloadTyped carrierTranslated payloadTranslated
  · exact (genericCarrierTypeRemainsExplicit constants carrierTyped).app payloadTyped

private theorem openingUsesExactNativeDependencyList {env : VEnv} {universes : List Name}
    {context : VLCtx} {fvar : FVarId} {source body : Expr} {semantic peeled : VExpr}
    (translation : TrExpr env universes ((none, .vlam peeled) :: context) body semantic)
    (ordered : env.Ordered)
    (pushedWF : VLCtx.WF env universes.length
      ((some (fvar, (peelTypeAnnotations source).fvarsList), .vlam peeled) :: context)) :
    TrExpr env universes
      ((some (fvar, (peelTypeAnnotations source).fvarsList), .vlam peeled) :: context)
      (body.instantiate1' (.fvar fvar)) semantic :=
  translation.openFreshFVar ordered pushedWF

private theorem nativeOptionalOpeningRetainsNonemptyDependencies {env : VEnv} {context : VLCtx}
    {ctx : Context} {name : Name} {body : Expr} {bi : BinderInfo} {carrier payload : FVarId}
    {semanticCarrier semanticPayload bodySemantic : VExpr}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env [] ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (carrierTyped : env.HasType 0 context.toCtx semanticCarrier (.sort (.succ .zero)))
    (payloadTyped : env.HasType 0 context.toCtx semanticPayload semanticCarrier)
    (carrierTranslated : TrExprS env [] context (.fvar carrier) semanticCarrier)
    (payloadTranslated : TrExprS env [] context (.fvar payload) semanticPayload)
    (bodyTranslated : TrExprS env []
      ((none, .vlam (.app (.app (.const ``optParam [.succ .zero]) semanticCarrier) semanticPayload)) :: context)
      body bodySemantic) :
    ∃ peeled, TrLCtx env [] (recursorIndexContext ctx name bi (.fvar carrier)).lctx
      ((some (⟨ctx.ngen.curr⟩, [carrier]), .vlam peeled) :: context) ∧
      TrExpr env [] ((some (⟨ctx.ngen.curr⟩, [carrier]), .vlam peeled) :: context)
        (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) bodySemantic ∧
      BinderPositionedAt (recursorIndexContext ctx name bi (.fvar carrier)) (.fvar ⟨ctx.ngen.curr⟩)
        name (.fvar carrier) bi ctx.lctx.decls.size := by
  have spine := actualOptionalDomainSpine envWF correspondence.wf.toCtx constants
    carrierTyped payloadTyped carrierTranslated payloadTranslated
  obtain ⟨peeled, _, _, pushedCorrespondence, openedBody, positioned, _⟩ :=
    spine.nativeIndexOpening (name := name) (bi := bi) envWF definitions correspondence reserved bodyTranslated
  simp only [peeledIndexVirtualContext, optionalPeelsToExistingCarrier, Expr.fvarsList] at pushedCorrespondence
  simp only [peeledIndexVirtualContext, optionalPeelsToExistingCarrier, Expr.fvarsList] at openedBody positioned
  exact ⟨peeled, pushedCorrespondence, openedBody, positioned⟩

private theorem emptyDependencyHistoryIsNotNativeOptionalContext (context : VLCtx)
    (fresh carrier payload : FVarId) (peeled : VExpr) :
    peeledIndexVirtualContext context fresh (optionalDomain carrier payload) peeled ≠
      ((some (fresh, []), .vlam peeled) :: context) := by
  simp only [peeledIndexVirtualContext, optionalNativeDependenciesAreNonempty]
  intro equal
  have headEqual := (List.cons.inj equal).1
  have namesEqual := congrArg Prod.fst headEqual
  have dependenciesEqual := congrArg Prod.snd (Option.some.inj namesEqual)
  cases dependenciesEqual

private theorem nativeReservationSuppliesVirtualFreshness {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} (correspondence : TrLCtx env universes ctx.lctx context)
    (reserved : ContextReserved ctx.lctx ctx.ngen) :
    (⟨ctx.ngen.curr⟩ : FVarId) ∉ context.fvars := by
  exact correspondence.find?_eq_none.mp (reserved.fresh correspondence.1)

private theorem actualIndexLookupKeepsAllAnchors {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semantic bodySemantic peeled : VExpr} {level : VLevel}
    (receipt : PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled) :
    ∃ declaration,
      (recursorIndexContext ctx name bi (peelTypeAnnotations domain)).lctx.find? ⟨ctx.ngen.curr⟩ =
        some declaration ∧ declaration.toExpr = .fvar ⟨ctx.ngen.curr⟩ ∧
      declaration.type = peelTypeAnnotations domain ∧ declaration.userName = name ∧
      declaration.binderInfo = bi ∧ declaration.index = ctx.lctx.decls.size :=
  receipt.2.2.2.2.1

private theorem headerTranslationFeedsNativeOpening {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi)
      (.forallE semantic bodySemantic))
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    ∃ peeled, PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled :=
  translatedForallIndexOpening envWF constants definitions correspondence reserved translated domainTyped uniform

private theorem autoHeaderOpensWithoutAnAssumedSpine {env : VEnv} {context : VLCtx}
    {ctx : Context} {name : Name} {body : Expr} {bi : BinderInfo} {carrier : FVarId}
    {semantic bodySemantic : VExpr} (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env [] ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env [] context (.forallE name (tacticDomain carrier) body bi)
      (.forallE semantic bodySemantic))
    (typed : env.HasType 0 context.toCtx semantic (.sort (.succ .zero))) :
    ∃ peeled, PeeledIndexOpening env [] ctx context name (tacticDomain carrier) body bi
      semantic bodySemantic (.succ .zero) peeled := by
  apply translatedForallIndexOpening envWF constants definitions correspondence reserved translated typed
  simp [tacticDomain, binary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem nestedHeaderOpensWithoutAnAssumedSpine {env : VEnv} {context : VLCtx}
    {ctx : Context} {name : Name} {body : Expr} {bi : BinderInfo} {carrier payload : FVarId}
    {semantic bodySemantic : VExpr} (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env [] ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env [] context (.forallE name (nestedDomain carrier payload) body bi)
      (.forallE semantic bodySemantic))
    (typed : env.HasType 0 context.toCtx semantic (.sort (.succ .zero))) :
    ∃ peeled, PeeledIndexOpening env [] ctx context name (nestedDomain carrier payload) body bi
      semantic bodySemantic (.succ .zero) peeled := by
  apply translatedForallIndexOpening envWF constants definitions correspondence reserved translated typed
  simp [nestedDomain, unary, optionalDomain, binary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem metadataBarrierHeaderOpensRetainedDomain {env : VEnv} {context : VLCtx}
    {ctx : Context} {name : Name} {body : Expr} {bi : BinderInfo} {carrier payload : FVarId}
    {semantic bodySemantic : VExpr} {level : VLevel} (metadata : MData)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env [] ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env [] context
      (.forallE name (.mdata metadata (optionalDomain carrier payload)) body bi) (.forallE semantic bodySemantic))
    (typed : env.HasType 0 context.toCtx semantic (.sort level)) :
    ∃ peeled, PeeledIndexOpening env [] ctx context name
      (.mdata metadata (optionalDomain carrier payload)) body bi semantic bodySemantic level peeled :=
  translatedForallIndexOpening envWF constants definitions correspondence reserved translated typed (by trivial)

private theorem actualCallbackConsumesSamePeeledWitness {ResultType : Type}
    {env : VEnv} {universes : List Name} {context : VLCtx} {ctx : Context}
    {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi)
      (.forallE semantic bodySemantic))
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level)
    (next : Expr → M ResultType) (post : ResultType → Prop)
    (nextWF : ∀ peeled, PeeledIndexOpening env universes ctx context name domain body bi
      semantic bodySemantic level peeled →
      (next (.fvar ⟨ctx.ngen.curr⟩) (recursorIndexContext ctx name bi (peelTypeAnnotations domain))).WF post) :
    (withLocalDecl name bi (peelTypeAnnotations domain) next ctx).WF post :=
  withLocalDecl.indexOpeningTranslation envWF constants definitions correspondence reserved
    translated domainTyped uniform next post nextWF

private def callback (source body : Expr) (name : Name) (binderInfo : BinderInfo) :
    M (Expr × Context × Expr) :=
  withLocalDecl name binderInfo (peelTypeAnnotations source) fun value => do
    return (value, ← read, body.instantiate1 value)

private theorem concreteCallbackReturnsOpeningReceipt {env : VEnv} {universes : List Name}
    {context : VLCtx} {ctx : Context} {name : Name} {domain body : Expr} {bi : BinderInfo}
    {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (correspondence : TrLCtx env universes ctx.lctx context) (reserved : ContextReserved ctx.lctx ctx.ngen)
    (translated : TrExprS env universes context (.forallE name domain body bi)
      (.forallE semantic bodySemantic))
    (domainTyped : env.HasType universes.length context.toCtx semantic (.sort level))
    (uniform : UniformAnnotationUniverse universes domain level) :
    (callback domain body name bi ctx).WF fun result =>
      result.1 = .fvar ⟨ctx.ngen.curr⟩ ∧
      result.2.1 = recursorIndexContext ctx name bi (peelTypeAnnotations domain) ∧
      result.2.2 = body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩) ∧
      ∃ peeled, PeeledIndexOpening env universes ctx context name domain body bi
        semantic bodySemantic level peeled := by
  apply withLocalDecl.indexOpeningTranslation envWF constants definitions correspondence reserved
    translated domainTyped uniform
  intro peeled receipt
  intro result success
  obtain rfl := Except.ok.inj success
  exact ⟨rfl, rfl, rfl, peeled, receipt⟩

private def checkCallback (ctx : Context) (source body : Expr) (name : Name)
    (binderInfo : BinderInfo) (expectedDependencies : List FVarId) : MetaM Unit := do
  let .ok (value, current, opened) := callback source body name binderInfo ctx
    | throwError "index-context actual withLocalDecl callback failed"
  let expectedValue := Expr.fvar ⟨ctx.ngen.curr⟩
  unless value == expectedValue && current.ngen.curr == ctx.ngen.next.curr do
    throwError "index-context callback fresh value/name-generator mismatch"
  unless current.lctx.decls.size == ctx.lctx.decls.size + 1 do
    throwError "index-context callback exact native declaration position changed"
  let some declaration := current.lctx.find? value.fvarId!
    | throwError "index-context callback actual index lookup missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations source &&
      declaration.userName == name && declaration.binderInfo == binderInfo &&
      declaration.index == ctx.lctx.decls.size do
    throwError "index-context callback stored value/type/name/binder-info/index mismatch"
  unless declaration.deps == expectedDependencies && declaration.type.fvarsList == expectedDependencies do
    throwError "index-context callback actual peeled dependency list changed"
  unless opened == body.instantiate1 expectedValue do
    throwError "index-context callback actual instantiated body changed"
  for position in [:ctx.lctx.decls.size] do
    if let some previous := ctx.lctx.getAt? position then
      let some retained := current.lctx.find? previous.fvarId
        | throwError "index-context callback removed a prior local declaration"
      unless retained.toExpr == previous.toExpr && retained.type == previous.type &&
          retained.userName == previous.userName && retained.binderInfo == previous.binderInfo &&
          retained.index == previous.index && retained.value? == previous.value? do
        throwError "index-context callback changed a prior local declaration"

private def runtimeFixtures (ctx : Context) : MetaM Unit := do
  let carrier : FVarId := ⟨`IndexTranslationCarrier⟩
  let payload : FVarId := ⟨`IndexTranslationPayload⟩
  let seeded := { ctx with
    ngen := { namePrefix := `IndexTranslationSeed, idx := 19 }
    lctx := ctx.lctx.mkLocalDecl carrier `carrier (.sort (.succ .zero)) .implicit
      |>.mkLocalDecl payload `payload (.fvar carrier) .default
      |>.mkLetDecl ⟨`IndexTranslationOldLet⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  let body := Expr.app (.bvar 0) (.fvar payload)
  for binderInfo in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    checkCallback seeded (optionalDomain carrier payload) body `optionalIndex binderInfo [carrier]
    checkCallback seeded (tacticDomain carrier) body `autoIndex binderInfo [carrier]
    checkCallback seeded (nestedDomain carrier payload) body `nestedIndex binderInfo [carrier]
    checkCallback seeded (.mdata {} (optionalDomain carrier payload)) body `barrierIndex
      binderInfo [carrier, payload]
  logInfo "index-context runtime: 16 actual callbacks; prior native locals; four binder infos; nonempty dependencies"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "index-context unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "index-context audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "index-context module-owned axiom {name}"
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
      throwError "index-context inherited foundation provenance changed: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "index-context inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    logInfo m!"pinned inherited context foundation: {name} from {moduleName}"
  for name in nativeInterfaces do
    let some (.axiomInfo _) := environment.find? name
      | throwError "index-context native interface is not an existing axiom: {name}"
    unless environment.getModuleIdxFor? name ==
        environment.getModuleIdx? `Lean4Lean.Verify.Axioms do
      throwError "index-context native interface provenance changed: {name}"
    logInfo m!"pinned existing native interface: {name}"

#print axioms TypedAnnotationSpine.anonymousBodyTranslation
#print axioms TypedAnnotationSpine.nativeIndexOpening
#print axioms translatedForallIndexOpening
#print axioms withLocalDecl.indexOpeningTranslation
#print axioms concreteCallbackReturnsOpeningReceipt
#print axioms runtimeFixtures

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inherited := logical ++ [``sorryAx]
  let nativeInterfaces := [``Expr.instantiate1_eq, ``PersistentArray.toList'_push,
    ``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert]
  let native := inherited ++ nativeInterfaces
  for theoremName in [``optionalPeelsToExistingCarrier, ``tacticPeelsToExistingCarrier,
      ``nestedPeelsToExistingCarrier, ``optionalNativeDependenciesAreNonempty,
      ``discardedDefaultNotANativeDependency, ``nestedNativeDependenciesAreNonempty,
      ``metadataBarrierRetainsBothNativeDependencies, ``rawOptionalSemanticIsNotItsCarrier,
      ``rawConstantOptionalSemanticIsNotPeeledType, ``genericCarrierTypeRemainsExplicit,
      ``emptyDependencyHistoryIsNotNativeOptionalContext] do
    auditDeclaration theoremName logical
  for functionName in [``runtimeFixtures, ``checkCallback, ``callback] do
    auditDeclaration functionName logical
  for theoremName in [``anonymousBodyConversionKeepsPeeledWitness,
      ``bodyConversionOffersDefinitionalNotLiteralSemanticIdentity, ``actualOptionalDomainTranslation,
      ``actualOptionalDomainSpine, ``openingUsesExactNativeDependencyList] do
    auditDeclaration theoremName inherited
  for theoremName in [``nativeOptionalOpeningRetainsNonemptyDependencies,
      ``nativeReservationSuppliesVirtualFreshness, ``actualIndexLookupKeepsAllAnchors,
      ``headerTranslationFeedsNativeOpening, ``autoHeaderOpensWithoutAnAssumedSpine,
      ``nestedHeaderOpensWithoutAnAssumedSpine, ``metadataBarrierHeaderOpensRetainedDomain,
      ``actualCallbackConsumesSamePeeledWitness, ``concreteCallbackReturnsOpeningReceipt] do
    auditDeclaration theoremName native
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditModule `Lean4Lean.Verify.InductiveAnnotationContext inherited
  auditModule `Lean4Lean.Verify.InductiveIndexContextTranslation native
  auditModule `Lean4Lean.Verify.InductiveIndexOpeningTranslation native
  auditFoundations nativeInterfaces
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  runtimeFixtures ctx
  logInfo "index-context translation: 25 proof controls; three clean-core and three inherited-boundary module censuses"

end InductiveIndexContextTranslationTest
