import Lean4Lean.Verify.InductiveAnnotationDomainPeeling
import Lean4Lean.Verify.InductiveTelescopeTranslation
import Lean4Lean.Verify.InductiveBinderTranslation
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open private annotationLevels_ofArity from Lean4Lean.Verify.InductiveAnnotationDomainPeeling

namespace InductiveAnnotationTranslationTest

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def binary (name : Name) (carrier payload : Expr) : Expr :=
  .app (.app (.const name [.succ .zero]) carrier) payload

private def semanticUnary (name : Name) (carrier : VExpr) : VExpr :=
  .app (.const name [.succ .zero]) carrier

private def semanticBinary (name : Name) (carrier payload : VExpr) : VExpr :=
  .app (.app (.const name [.succ .zero]) carrier) payload

private def fixtureEnvironment : VEnv where
  constants name :=
    if name = ``Nat then some { uvars := 0, type := .sort (.succ .zero) }
    else if name = ``Nat.zero then some { uvars := 0, type := .const ``Nat [] }
    else if name = ``Lean.Syntax then some { uvars := 0, type := .sort (.succ .zero) }
    else if name = ``Lean.Syntax.missing then some { uvars := 0, type := .const ``Lean.Syntax [] }
    else if name = ``outParam then some { uvars := 1, type := (unaryAnnotationDefinition ``outParam).type }
    else if name = ``semiOutParam then
      some { uvars := 1, type := (unaryAnnotationDefinition ``semiOutParam).type }
    else if name = ``optParam then some { uvars := 1, type := optParamDefinition.type }
    else if name = ``autoParam then some { uvars := 1, type := autoParamDefinition.type }
    else none
  defeqs definition := definition = unaryAnnotationDefinition ``outParam ∨
    definition = unaryAnnotationDefinition ``semiOutParam ∨
    definition = optParamDefinition ∨ definition = autoParamDefinition

private theorem fixtureConstants : CanonicalAnnotationConstants fixtureEnvironment := by
  constructor <;> simp [fixtureEnvironment]

private theorem fixtureDefinitions : CanonicalAnnotationDefinitions fixtureEnvironment := by
  constructor <;> simp [fixtureEnvironment]

private theorem natTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``Nat []) (.sort (.succ .zero)) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``Nat) (ls := [])
    (ci := { uvars := 0, type := .sort (.succ .zero) })
    (by simp [fixtureEnvironment]) (by simp) rfl

private theorem zeroTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``Nat.zero []) (.const ``Nat []) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``Nat.zero) (ls := [])
    (ci := { uvars := 0, type := .const ``Nat [] })
    (by simp [fixtureEnvironment]) (by simp) rfl

private theorem tacticTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``Lean.Syntax.missing []) (.const ``Lean.Syntax []) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``Lean.Syntax.missing) (ls := [])
    (ci := { uvars := 0, type := .const ``Lean.Syntax [] })
    (by simp [fixtureEnvironment]) (by simp) rfl

private theorem natTranslated (context : VLCtx) : TrExprS fixtureEnvironment [] context
    (.const ``Nat []) (.const ``Nat []) :=
  .const (ci := { uvars := 0, type := .sort (.succ .zero) })
    (by simp [fixtureEnvironment]) rfl rfl

private theorem zeroTranslated (context : VLCtx) : TrExprS fixtureEnvironment [] context
    (.const ``Nat.zero []) (.const ``Nat.zero []) :=
  .const (ci := { uvars := 0, type := .const ``Nat [] })
    (by simp [fixtureEnvironment]) rfl rfl

private theorem tacticTranslated (context : VLCtx) : TrExprS fixtureEnvironment [] context
    (.const ``Lean.Syntax.missing []) (.const ``Lean.Syntax.missing []) :=
  .const (ci := { uvars := 0, type := .const ``Lean.Syntax [] })
    (by simp [fixtureEnvironment]) rfl rfl

private theorem optionalFunctionTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``optParam [.succ .zero])
    (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort (.succ .zero)))) := by
  simpa [optParamDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``optParam) (ls := [.succ .zero])
    (ci := { uvars := 1, type := optParamDefinition.type })
    fixtureConstants.optParam (by simp [VLevel.WF]) rfl

private theorem autoFunctionTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``autoParam [.succ .zero])
    (.forallE (.sort (.succ .zero)) (.forallE (.const ``Lean.Syntax []) (.sort (.succ .zero)))) := by
  simpa [autoParamDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``autoParam) (ls := [.succ .zero])
    (ci := { uvars := 1, type := autoParamDefinition.type })
    fixtureConstants.autoParam (by simp [VLevel.WF]) rfl

private theorem optionalAppliedTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.app (.const ``optParam [.succ .zero]) (.const ``Nat []))
    (.forallE (.const ``Nat []) (.sort (.succ .zero))) := by
  simpa [VExpr.inst, VExpr.instVar] using (optionalFunctionTyped context).app (natTyped context)

private theorem autoAppliedTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.app (.const ``autoParam [.succ .zero]) (.const ``Nat []))
    (.forallE (.const ``Lean.Syntax []) (.sort (.succ .zero))) := by
  simpa only [VExpr.inst] using (autoFunctionTyped context).app (natTyped context)

private theorem optionalActualTranslation (context : VLCtx) : TrExprS fixtureEnvironment [] context
    (binary ``optParam (.const ``Nat []) (.const ``Nat.zero []))
    (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) := by
  apply TrExprS.app (optionalAppliedTyped context.toCtx) (zeroTyped context.toCtx)
  · apply TrExprS.app (optionalFunctionTyped context.toCtx) (natTyped context.toCtx)
    · exact .const fixtureConstants.optParam rfl rfl
    · exact natTranslated context
  · exact zeroTranslated context

private theorem autoActualTranslation (context : VLCtx) : TrExprS fixtureEnvironment [] context
    (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing []))
    (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])) := by
  apply TrExprS.app (autoAppliedTyped context.toCtx) (tacticTyped context.toCtx)
  · apply TrExprS.app (autoFunctionTyped context.toCtx) (natTyped context.toCtx)
    · exact .const fixtureConstants.autoParam rfl rfl
    · exact natTranslated context
  · exact tacticTranslated context

private theorem optionalSourceTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.sort (.succ .zero)) :=
  (optionalAppliedTyped context).app (zeroTyped context)

private theorem autoSourceTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing []))
    (.sort (.succ .zero)) :=
  (autoAppliedTyped context).app (tacticTyped context)

private theorem optionalUniform : UniformAnnotationUniverse []
    (binary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.succ .zero) := by
  simp [binary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem autoUniform : UniformAnnotationUniverse []
    (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])) (.succ .zero) := by
  simp [binary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem optionalSpineExtracted (envWF : fixtureEnvironment.WF) :
    TypedAnnotationSpine (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (binary ``optParam (.const ``Nat []) (.const ``Nat.zero []))
      (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.succ .zero) :=
  TypedAnnotationSpine.ofTrExprS envWF (by trivial) fixtureConstants optionalUniform
    (optionalActualTranslation []) (optionalSourceTyped [])

private theorem autoSpineExtracted (envWF : fixtureEnvironment.WF) :
    TypedAnnotationSpine (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing []))
      (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])) (.succ .zero) :=
  TypedAnnotationSpine.ofTrExprS envWF (by trivial) fixtureConstants autoUniform
    (autoActualTranslation []) (autoSourceTyped [])

private theorem carriersAndPayloadsComeFromTranslation {env : VEnv} {universes : List Name}
    {context : VLCtx} {sourceCarrier sourcePayload : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF) (contextTypes : OnCtx context.toCtx (env.IsType universes.length))
    (constants : CanonicalAnnotationConstants env)
    (uniform : UniformAnnotationUniverse universes (binary ``optParam sourceCarrier sourcePayload) level)
    (translated : TrExprS env universes context (binary ``optParam sourceCarrier sourcePayload) semantic)
    (typed : env.HasType universes.length context.toCtx semantic (.sort level)) :
    TypedAnnotationSpine (TrExprS env universes context) env universes.length context.toCtx
      (binary ``optParam sourceCarrier sourcePayload) semantic level :=
  TypedAnnotationSpine.ofTrExprS envWF contextTypes constants uniform translated typed

private theorem unaryFunctionTyped (name : Name) (context : List VExpr)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type }) :
    fixtureEnvironment.HasType 0 context (.const name [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by
  simpa [unaryAnnotationDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := name) (ls := [.succ .zero])
    (ci := { uvars := 1, type := (unaryAnnotationDefinition name).type })
    lookup (by simp [VLevel.WF]) rfl

private theorem wrappedCarrierTyped (name : Name) (context : List VExpr) (carrier : VExpr)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type })
    (typed : fixtureEnvironment.HasType 0 context carrier (.sort (.succ .zero))) :
    fixtureEnvironment.HasType 0 context (semanticUnary name carrier) (.sort (.succ .zero)) :=
  (unaryFunctionTyped name context lookup).app typed

private theorem wrappedCarrierTranslated (name : Name) (context : VLCtx)
    (source : Expr) (carrier : VExpr)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type })
    (typed : fixtureEnvironment.HasType 0 context.toCtx carrier (.sort (.succ .zero)))
    (translated : TrExprS fixtureEnvironment [] context source carrier) :
    TrExprS fixtureEnvironment [] context (unary name source) (semanticUnary name carrier) :=
  .app (unaryFunctionTyped name context.toCtx lookup) typed (.const lookup rfl rfl) translated

private def nestedSource : Expr := unary ``outParam (unary ``semiOutParam
  (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])))

private def nestedSemantic : VExpr := semanticUnary ``outParam (semanticUnary ``semiOutParam
  (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])))

private theorem nestedActualTranslation (context : VLCtx) :
    TrExprS fixtureEnvironment [] context nestedSource nestedSemantic :=
  wrappedCarrierTranslated _ context _ _ fixtureConstants.outParam
    (wrappedCarrierTyped _ context.toCtx _ fixtureConstants.semiOutParam (autoSourceTyped context.toCtx))
    (wrappedCarrierTranslated _ context _ _ fixtureConstants.semiOutParam
      (autoSourceTyped context.toCtx) (autoActualTranslation context))

private theorem nestedSourceTyped (context : List VExpr) :
    fixtureEnvironment.HasType 0 context nestedSemantic (.sort (.succ .zero)) :=
  wrappedCarrierTyped _ context _ fixtureConstants.outParam
    (wrappedCarrierTyped _ context _ fixtureConstants.semiOutParam (autoSourceTyped context))

private theorem nestedUniform : UniformAnnotationUniverse [] nestedSource (.succ .zero) := by
  simp [nestedSource, unary, binary, UniformAnnotationUniverse, VLevel.ofLevel]

private theorem nestedSpineExtracted (envWF : fixtureEnvironment.WF) :
    TypedAnnotationSpine (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      nestedSource nestedSemantic (.succ .zero) :=
  TypedAnnotationSpine.ofTrExprS envWF (by trivial) fixtureConstants nestedUniform
    (nestedActualTranslation []) (nestedSourceTyped [])

private theorem metadataBarrierStillTranslates (metadata : MData) (context : VLCtx) :
    TrExprS fixtureEnvironment [] context (.mdata metadata nestedSource) nestedSemantic :=
  .mdata (nestedActualTranslation context)

private theorem metadataBarrierExtractedWithoutPeeling (envWF : fixtureEnvironment.WF) (metadata : MData) :
    TypedAnnotationSpine (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (.mdata metadata nestedSource) nestedSemantic (.succ .zero) :=
  TypedAnnotationSpine.ofTrExprS envWF (by trivial) fixtureConstants (by trivial)
    (metadataBarrierStillTranslates metadata []) (nestedSourceTyped [])

private theorem metadataBarrierUniform (universes : List Name) (metadata : MData)
    (source : Expr) (level : VLevel) :
    UniformAnnotationUniverse universes (.mdata metadata source) level := by trivial

private theorem unrecognizedUnaryUniform (universes : List Name) (source : Expr) (level : VLevel) :
    UniformAnnotationUniverse universes (unary `UnrecognizedAnnotation source) level := by
  simp [unary, UniformAnnotationUniverse]

private theorem equivalentDistinctLevels :
    (VLevel.max .zero (.succ .zero)) ≈ VLevel.succ .zero ∧
      (VLevel.max .zero (.succ .zero)) ≠ VLevel.succ .zero := by
  constructor
  · rfl
  · intro equal
    cases equal

private theorem equivalentLevelsFailSyntacticUniformity (source : Expr) :
    ¬ UniformAnnotationUniverse []
      (.app (.const ``outParam [.max .zero (.succ .zero)]) source) (.succ .zero) := by
  simp [UniformAnnotationUniverse, VLevel.ofLevel]

private theorem equivalentUniverseAnnotationActuallyTranslates :
    TrExprS fixtureEnvironment [] []
      (.app (.const ``outParam [.max .zero (.succ .zero)]) (.const ``Nat []))
      (.app (.const ``outParam [.max .zero (.succ .zero)]) (.const ``Nat [])) := by
  have functionTyped : fixtureEnvironment.HasType 0 []
      (.const ``outParam [.max .zero (.succ .zero)])
      (.forallE (.sort (.max .zero (.succ .zero))) (.sort (.max .zero (.succ .zero)))) := by
    simpa [unaryAnnotationDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
      (env := fixtureEnvironment) (c := ``outParam) (ls := [.max .zero (.succ .zero)])
      (ci := { uvars := 1, type := (unaryAnnotationDefinition ``outParam).type })
      fixtureConstants.outParam (by simp [VLevel.WF]) rfl
  have carrierTyped : fixtureEnvironment.HasType 0 [] (.const ``Nat [])
      (.sort (.max .zero (.succ .zero))) :=
    VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := .succ .zero)
      (l' := .max .zero (.succ .zero)) (by trivial) (by trivial) rfl) (natTyped [])
  exact .app functionTyped carrierTyped (.const fixtureConstants.outParam rfl rfl) (natTranslated [])

private theorem noncanonicalArityFailsUniformity (source : Expr) :
    ¬ UniformAnnotationUniverse [] (.app (.const ``outParam []) source) (.succ .zero) := by
  simp [UniformAnnotationUniverse]

private theorem noncanonicalArityStillPeels (source : Expr) :
    peelTypeAnnotations (.app (.const ``outParam []) source) = peelTypeAnnotations source := by
  simp [peelTypeAnnotations]

private theorem openedFreshHistoryIsSameWitness {env : VEnv} {universes : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr}
    (opened : OpenedTelescope type steps terminal) (translated : TrExprS env universes context type semantic)
    (ordered : env.Ordered) (contextWF : context.WF env universes.length)
    (fresh : FreshBinderValues context.fvars steps) : TranslatedBinderHistory env universes context steps :=
  opened.translatedHistory translated ordered contextWF fresh

private theorem rawDomainsUseEvolvingContexts {env : VEnv} {universes : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr}
    (opened : OpenedTelescope type steps terminal) (translated : TrExprS env universes context type semantic)
    (ordered : env.Ordered) (contextWF : context.WF env universes.length)
    (fresh : FreshBinderValues context.fvars steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧ (∀ position, (contexts position).WF env universes.length) ∧
      ∀ position step, steps[position]? = some step → ∃ semanticDomain,
        TrExprS env universes (contexts position) step.domain semanticDomain ∧
        env.HasType universes.length (contexts position).toCtx semanticDomain (.sort (levels position)) :=
  opened.translatedDomains translated ordered contextWF fresh

private def binderStep (role : BinderRole) (id : FVarId) : BinderStep where
  role := role
  name := `translationIndex
  domain := binary ``optParam (.const ``Nat []) (.const ``Nat.zero [])
  bi := .implicit
  value := .fvar id

private theorem bothRolesRequireVirtualFreshness (existing : List FVarId) (role : BinderRole)
    (id : FVarId) (fresh : id ∉ existing) : FreshBinderValues existing [binderStep role id] :=
  .cons rfl fresh .nil

private theorem reusedVirtualFVarExcluded (role : BinderRole) (id : FVarId) :
    ¬ FreshBinderValues [id] [binderStep role id] := by
  intro freshness
  cases freshness with
  | cons value fresh _ =>
    have sameId := Expr.fvar.inj value
    subst sameId
    exact fresh (List.mem_cons_self ..)

private theorem repeatedVirtualFVarExcluded (role : BinderRole) (id : FVarId) :
    ¬ FreshBinderValues [] [binderStep role id, binderStep role id] := by
  intro freshness
  cases freshness with
  | cons value _ tail =>
    have sameId := Expr.fvar.inj value
    subst sameId
    exact reusedVirtualFVarExcluded role id tail

private def singletonHeader : Expr := .forallE `translationIndex
  (binary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.sort (.succ .zero)) .implicit

private def singletonSemanticHeader : VExpr := .forallE
  (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.sort (.succ .zero))

private theorem singletonHeaderTranslated :
    TrExprS fixtureEnvironment [] [] singletonHeader singletonSemanticHeader :=
  .forallE ⟨.succ .zero, optionalSourceTyped []⟩
    ⟨.succ (.succ .zero), VEnv.HasType.sort (by trivial)⟩ (optionalActualTranslation []) (.sort rfl)

private theorem singletonHeaderOpened (id : FVarId) :
    OpenedTelescope singletonHeader [binderStep .index id] (.sort (.succ .zero)) := by
  apply OpenedTelescope.bind .index `translationIndex _ .implicit (.fvar id)
  simpa only [Expr.instantiate1_eq, Expr.instantiate1'] using OpenedTelescope.sort (.succ .zero)

private theorem singletonOpenedHasActualRawTranslations (envWF : fixtureEnvironment.WF) (id : FVarId) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = [] ∧ (∀ position, (contexts position).WF fixtureEnvironment 0) ∧
      BinderRawDomainTranslations fixtureEnvironment [] contexts levels [binderStep .index id] :=
  (singletonHeaderOpened id).domainTranslations singletonHeaderTranslated envWF.ordered (by trivial)
    (bothRolesRequireVirtualFreshness [] .index id (by simp))

private theorem singletonRawTranslations (id : FVarId) :
    BinderRawDomainTranslations fixtureEnvironment [] (fun _ => [])
      (fun _ => .succ .zero) [binderStep .index id] := by
  intro position step selected
  cases position with
  | zero =>
    have sameStep : binderStep .index id = step := Option.some.inj selected
    subst step
    exact ⟨_, optionalActualTranslation [], optionalSourceTyped []⟩
  | succ position => simp at selected

private theorem singletonRawUniform (id : FVarId) :
    BinderRawDomainUniverseUniform [] (fun _ => .succ .zero) [binderStep .index id] := by
  intro position step selected
  cases position with
  | zero =>
    have sameStep : binderStep .index id = step := Option.some.inj selected
    subst step
    exact optionalUniform
  | succ position => simp at selected

private theorem singletonActualIndexType (envWF : fixtureEnvironment.WF) (id : FVarId)
    (ctx : Context) (declared : BinderStepsIndexDeclared ctx [binderStep .index id])
    (decl : LocalDecl) (lookup : ctx.lctx.find? id = some decl) :
    SourceHasType (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      decl.type (.sort (.succ .zero)) := by
  have receipt := (singletonRawTranslations id).typingReceipt envWF (by intro; trivial)
    fixtureConstants fixtureDefinitions (singletonRawUniform id) declared
  exact receipt.2.2 0 (binderStep .index id) decl rfl rfl lookup

private theorem actualOpenedWitnessRetainsConditionalTyping {env : VEnv} {universes : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr} {ctx : Context}
    (opened : OpenedTelescope type steps terminal) (translated : TrExprS env universes context type semantic)
    (envWF : env.WF) (contextWF : context.WF env universes.length)
    (fresh : FreshBinderValues context.fvars steps) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (declared : BinderStepsIndexDeclared ctx steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧ (∀ position, (contexts position).WF env universes.length) ∧
      BinderRawDomainTranslations env universes contexts levels steps ∧
      (BinderRawDomainUniverseUniform universes levels steps →
        BinderRawDomainHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels steps ∧
        BinderStoredIndexDomainHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels steps ∧
        BinderStoredIndexTypeHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels ctx steps) :=
  opened.translatedTypingReceipt translated envWF contextWF fresh constants definitions declared

private def plainStep (id : FVarId) : BinderStep where
  role := .index
  name := `plainTranslationIndex
  domain := .const ``Nat []
  bi := .default
  value := .fvar id

private def plainHeader : Expr := .forallE `plainTranslationIndex (.const ``Nat [])
  (.sort (.succ .zero)) .default

private theorem plainHeaderTranslated : TrExprS fixtureEnvironment [] [] plainHeader
    (.forallE (.const ``Nat []) (.sort (.succ .zero))) :=
  .forallE ⟨.succ .zero, natTyped []⟩
    ⟨.succ (.succ .zero), VEnv.HasType.sort (by trivial)⟩ (natTranslated []) (.sort rfl)

private theorem plainHeaderOpened (id : FVarId) :
    OpenedTelescope plainHeader [plainStep id] (.sort (.succ .zero)) := by
  apply OpenedTelescope.bind .index `plainTranslationIndex _ .default (.fvar id)
  simpa only [Expr.instantiate1_eq, Expr.instantiate1'] using OpenedTelescope.sort (.succ .zero)

private theorem plainDomainUniformAtEveryExtractedLevel (id : FVarId) (levels : Nat → VLevel) :
    BinderRawDomainUniverseUniform [] levels [plainStep id] := by
  intro position step selected
  cases position with
  | zero =>
    have sameStep : plainStep id = step := Option.some.inj selected
    subst step
    trivial
  | succ position => simp at selected

private theorem actualPlainHeaderReachesStoredTyping (envWF : fixtureEnvironment.WF) (id : FVarId)
    (ctx : Context) (declared : BinderStepsIndexDeclared ctx [plainStep id]) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = [] ∧ (∀ position, (contexts position).WF fixtureEnvironment 0) ∧
      BinderRawDomainTranslations fixtureEnvironment [] contexts levels [plainStep id] ∧
      BinderRawDomainHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
        fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels [plainStep id] ∧
      BinderStoredIndexDomainHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
        fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels [plainStep id] ∧
      BinderStoredIndexTypeHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
        fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels ctx [plainStep id] := by
  have fresh : FreshBinderValues [] [plainStep id] := .cons rfl (by simp) .nil
  obtain ⟨contexts, levels, initial, contextsWF, domains, continuation⟩ :=
    (plainHeaderOpened id).translatedTypingReceipt plainHeaderTranslated envWF (by trivial) fresh
      fixtureConstants fixtureDefinitions declared
  obtain ⟨raw, peeled, stored⟩ := continuation (plainDomainUniformAtEveryExtractedLevel id levels)
  exact ⟨contexts, levels, initial, contextsWF, domains, raw, peeled, stored⟩

private def equivalentLevel : VLevel := .max .zero (.succ .zero)

private theorem natEquivalentTyped (context : List VExpr) : fixtureEnvironment.HasType 0 context
    (.const ``Nat []) (.sort equivalentLevel) :=
  VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := .succ .zero)
    (l' := equivalentLevel) (by trivial) (by trivial) rfl) (natTyped context)

private theorem equivalentUnaryFunctionTyped (name : Name) (context : List VExpr)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type }) :
    fixtureEnvironment.HasType 0 context (.const name [equivalentLevel])
      (.forallE (.sort equivalentLevel) (.sort equivalentLevel)) := by
  simpa [unaryAnnotationDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := name) (ls := [equivalentLevel]) lookup
    (by simp [equivalentLevel, VLevel.WF]) rfl

private theorem equivalentUnaryTyped (name : Name) (context : List VExpr)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type }) :
    fixtureEnvironment.HasType 0 context (.app (.const name [equivalentLevel]) (.const ``Nat []))
      (.sort (.succ .zero)) := by
  have typed := (equivalentUnaryFunctionTyped name context lookup).app (natEquivalentTyped context)
  simp only [VExpr.inst] at typed
  exact VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := equivalentLevel)
    (l' := .succ .zero) (by trivial) (by trivial) rfl) typed

private theorem equivalentUnaryTranslated (name : Name) (context : VLCtx)
    (lookup : fixtureEnvironment.constants name =
      some { uvars := 1, type := (unaryAnnotationDefinition name).type }) :
    TrExprS fixtureEnvironment [] context
      (.app (.const name [.max .zero (.succ .zero)]) (.const ``Nat []))
      (.app (.const name [equivalentLevel]) (.const ``Nat [])) :=
  .app (equivalentUnaryFunctionTyped name context.toCtx lookup) (natEquivalentTyped context.toCtx)
    (.const lookup rfl rfl) (natTranslated context)

private theorem nonuniformOutParamPeels (envWF : fixtureEnvironment.WF) :
    ∃ peeled, TrExprS fixtureEnvironment [] [] (.const ``Nat []) peeled ∧
      fixtureEnvironment.IsDefEq 0 []
        (.app (.const ``outParam [equivalentLevel]) (.const ``Nat [])) peeled (.sort (.succ .zero)) := by
  simpa only [peelTypeAnnotations] using
    (equivalentUnaryTranslated ``outParam [] fixtureConstants.outParam).peeledDomain
      envWF (by trivial) fixtureConstants fixtureDefinitions
      (equivalentUnaryTyped ``outParam [] fixtureConstants.outParam)

private theorem nonuniformSemiOutParamPeels (envWF : fixtureEnvironment.WF) :
    SourceHasType (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (.const ``Nat []) (.sort (.succ .zero)) := by
  simpa only [peelTypeAnnotations] using
    (equivalentUnaryTranslated ``semiOutParam [] fixtureConstants.semiOutParam).peeledDomainHasType
      envWF (by trivial) fixtureConstants fixtureDefinitions
      (equivalentUnaryTyped ``semiOutParam [] fixtureConstants.semiOutParam)

private theorem nonuniformOptionalFunctionTyped (context : List VExpr) :
    fixtureEnvironment.HasType 0 context (.const ``optParam [equivalentLevel])
      (.forallE (.sort equivalentLevel) (.forallE (.bvar 0) (.sort equivalentLevel))) := by
  simpa [optParamDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``optParam) (ls := [equivalentLevel]) fixtureConstants.optParam
    (by simp [equivalentLevel, VLevel.WF]) rfl

private theorem nonuniformAutoFunctionTyped (context : List VExpr) :
    fixtureEnvironment.HasType 0 context (.const ``autoParam [equivalentLevel])
      (.forallE (.sort equivalentLevel) (.forallE (.const ``Lean.Syntax []) (.sort equivalentLevel))) := by
  simpa [autoParamDefinition, VExpr.instL, VLevel.inst] using VEnv.HasType.const
    (env := fixtureEnvironment) (c := ``autoParam) (ls := [equivalentLevel]) fixtureConstants.autoParam
    (by simp [equivalentLevel, VLevel.WF]) rfl

private theorem nonuniformOptionalAppliedTyped (context : List VExpr) :
    fixtureEnvironment.HasType 0 context (.app (.const ``optParam [equivalentLevel]) (.const ``Nat []))
      (.forallE (.const ``Nat []) (.sort equivalentLevel)) := by
  simpa [VExpr.inst, VExpr.instVar] using
    (nonuniformOptionalFunctionTyped context).app (natEquivalentTyped context)

private theorem nonuniformAutoAppliedTyped (context : List VExpr) :
    fixtureEnvironment.HasType 0 context (.app (.const ``autoParam [equivalentLevel]) (.const ``Nat []))
      (.forallE (.const ``Lean.Syntax []) (.sort equivalentLevel)) := by
  simpa [VExpr.inst, VExpr.instVar] using
    (nonuniformAutoFunctionTyped context).app (natEquivalentTyped context)

private theorem nonuniformOptionalTranslated : TrExprS fixtureEnvironment [] []
    (.app (.app (.const ``optParam [.max .zero (.succ .zero)]) (.const ``Nat [])) (.const ``Nat.zero []))
    (.app (.app (.const ``optParam [equivalentLevel]) (.const ``Nat [])) (.const ``Nat.zero [])) :=
  .app (nonuniformOptionalAppliedTyped []) (zeroTyped [])
    (.app (nonuniformOptionalFunctionTyped []) (natEquivalentTyped [])
      (.const fixtureConstants.optParam rfl rfl) (natTranslated [])) (zeroTranslated [])

private theorem nonuniformAutoTranslated : TrExprS fixtureEnvironment [] []
    (.app (.app (.const ``autoParam [.max .zero (.succ .zero)]) (.const ``Nat []))
      (.const ``Lean.Syntax.missing []))
    (.app (.app (.const ``autoParam [equivalentLevel]) (.const ``Nat []))
      (.const ``Lean.Syntax.missing [])) :=
  .app (nonuniformAutoAppliedTyped []) (tacticTyped [])
    (.app (nonuniformAutoFunctionTyped []) (natEquivalentTyped [])
      (.const fixtureConstants.autoParam rfl rfl) (natTranslated [])) (tacticTranslated [])

private theorem nonuniformOptionalPeels (envWF : fixtureEnvironment.WF) :
    SourceHasType (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (.const ``Nat []) (.sort equivalentLevel) := by
  simpa only [peelTypeAnnotations] using nonuniformOptionalTranslated.peeledDomainHasType
    envWF (by trivial) fixtureConstants fixtureDefinitions
    (by simpa only [VExpr.inst] using (nonuniformOptionalAppliedTyped []).app (zeroTyped []))

private theorem nonuniformAutoPeels (envWF : fixtureEnvironment.WF) :
    SourceHasType (TrExprS fixtureEnvironment [] []) fixtureEnvironment 0 []
      (.const ``Nat []) (.sort equivalentLevel) := by
  simpa only [peelTypeAnnotations] using nonuniformAutoTranslated.peeledDomainHasType
    envWF (by trivial) fixtureConstants fixtureDefinitions
    (by simpa only [VExpr.inst] using (nonuniformAutoAppliedTyped []).app (tacticTyped []))

private def nonuniformNestedSource : Expr :=
  .app (.const ``outParam [.max .zero (.succ .zero)]) nestedSource

private def nonuniformNestedSemantic : VExpr := .app (.const ``outParam [equivalentLevel]) nestedSemantic

private theorem nonuniformNestedTranslated :
    TrExprS fixtureEnvironment [] [] nonuniformNestedSource nonuniformNestedSemantic := by
  have carrierTyping := VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := .succ .zero)
    (l' := equivalentLevel) (by trivial) (by trivial) rfl) (nestedSourceTyped [])
  exact .app (equivalentUnaryFunctionTyped ``outParam [] fixtureConstants.outParam) carrierTyping
    (.const fixtureConstants.outParam rfl rfl) (nestedActualTranslation [])

private theorem nonuniformNestedTyped :
    fixtureEnvironment.HasType 0 [] nonuniformNestedSemantic (.sort (.succ .zero)) := by
  have carrierTyping := VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := .succ .zero)
    (l' := equivalentLevel) (by trivial) (by trivial) rfl) (nestedSourceTyped [])
  have typed := (equivalentUnaryFunctionTyped ``outParam [] fixtureConstants.outParam).app carrierTyping
  simp only [VExpr.inst] at typed
  exact VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := equivalentLevel)
    (l' := .succ .zero) (by trivial) (by trivial) rfl) typed

private theorem nonuniformNestedNotUniform (level : VLevel) :
    ¬ UniformAnnotationUniverse [] nonuniformNestedSource level := by
  intro uniform
  cases level <;> simp [nonuniformNestedSource, nestedSource, unary, binary,
    UniformAnnotationUniverse, VLevel.ofLevel] at uniform

private theorem nonuniformNestedPeels (envWF : fixtureEnvironment.WF) :
    ∃ peeled, TrExprS fixtureEnvironment [] [] (.const ``Nat []) peeled ∧
      fixtureEnvironment.IsDefEq 0 [] nonuniformNestedSemantic peeled (.sort (.succ .zero)) := by
  simpa only [nonuniformNestedSource, nestedSource, unary, binary, peelTypeAnnotations, ↓reduceIte] using
    nonuniformNestedTranslated.peeledDomain envWF (by trivial) fixtureConstants fixtureDefinitions
      nonuniformNestedTyped

private theorem nonuniformBodyConversion (envWF : fixtureEnvironment.WF) :
    ∃ peeled, TrExprS fixtureEnvironment [] [] (.const ``Nat []) peeled ∧
      fixtureEnvironment.IsDefEq 0 [] nonuniformNestedSemantic peeled (.sort (.succ .zero)) ∧
      VLCtx.IsDefEq fixtureEnvironment 0 [(none, .vlam nonuniformNestedSemantic)] [(none, .vlam peeled)] ∧
      TrExpr fixtureEnvironment [] [(none, .vlam peeled)] (.bvar 0) (.bvar 0) := by
  simpa only [nonuniformNestedSource, nestedSource, unary, binary, peelTypeAnnotations, ↓reduceIte] using
    nonuniformNestedTranslated.peeledAnonymousBodyTranslation envWF (by trivial) fixtureConstants
      fixtureDefinitions nonuniformNestedTyped (.bvar rfl)

private theorem nonuniformMetadataBarrier (envWF : fixtureEnvironment.WF) (metadata : MData) :
    ∃ peeled, TrExprS fixtureEnvironment [] [] (.mdata metadata nonuniformNestedSource) peeled ∧
      fixtureEnvironment.IsDefEq 0 [] nonuniformNestedSemantic peeled (.sort (.succ .zero)) := by
  exact (TrExprS.mdata nonuniformNestedTranslated).peeledDomain envWF (by trivial) fixtureConstants
    fixtureDefinitions nonuniformNestedTyped

private def nonuniformIndexStep (id : FVarId) : BinderStep :=
  ⟨.index, `nonuniformIndex, nonuniformNestedSource, .implicit, .fvar id⟩

private def nonuniformHeader : Expr :=
  .forallE `nonuniformIndex nonuniformNestedSource (.sort (.succ .zero)) .implicit

private theorem nonuniformHeaderTranslated : TrExprS fixtureEnvironment [] [] nonuniformHeader
    (.forallE nonuniformNestedSemantic (.sort (.succ .zero))) :=
  .forallE ⟨_, nonuniformNestedTyped⟩
    ⟨_, VEnv.HasType.sort (by trivial)⟩ nonuniformNestedTranslated (.sort rfl)

private theorem nonuniformHeaderOpened (id : FVarId) :
    OpenedTelescope nonuniformHeader [nonuniformIndexStep id] (.sort (.succ .zero)) := by
  apply OpenedTelescope.bind .index `nonuniformIndex _ .implicit (.fvar id)
  simpa only [Expr.instantiate1_eq, Expr.instantiate1'] using OpenedTelescope.sort (.succ .zero)

private theorem nonuniformHeaderStoredReceipt (envWF : fixtureEnvironment.WF) (id : FVarId)
    (ctx : Context) (declared : BinderStepsIndexDeclared ctx [nonuniformIndexStep id]) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = [] ∧ (∀ position, (contexts position).WF fixtureEnvironment 0) ∧
      BinderRawDomainTranslations fixtureEnvironment [] contexts levels [nonuniformIndexStep id] ∧
      BinderRawDomainHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
          fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels [nonuniformIndexStep id] ∧
        BinderStoredIndexDomainHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
          fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels [nonuniformIndexStep id] ∧
        BinderStoredIndexTypeHasType (fun position => TrExprS fixtureEnvironment [] (contexts position))
          fixtureEnvironment 0 (fun position => (contexts position).toCtx) levels ctx [nonuniformIndexStep id] :=
  (nonuniformHeaderOpened id).peeledTypingReceipt nonuniformHeaderTranslated envWF (by trivial)
    (.cons rfl (by simp [VLCtx.fvars]) .nil)
    fixtureConstants fixtureDefinitions declared

private theorem actualOpenedWitnessNeedsNoUniformity {env : VEnv} {universes : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr} {ctx : Context}
    (opened : OpenedTelescope type steps terminal) (translated : TrExprS env universes context type semantic)
    (envWF : env.WF) (contextWF : context.WF env universes.length)
    (fresh : FreshBinderValues context.fvars steps) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (declared : BinderStepsIndexDeclared ctx steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧ (∀ position, (contexts position).WF env universes.length) ∧
      BinderRawDomainTranslations env universes contexts levels steps ∧
      BinderRawDomainHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels steps ∧
        BinderStoredIndexDomainHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels steps ∧
        BinderStoredIndexTypeHasType (fun position => TrExprS env universes (contexts position))
          env universes.length (fun position => (contexts position).toCtx) levels ctx steps :=
  opened.peeledTypingReceipt translated envWF contextWF fresh constants definitions declared

private def annotationRuntimeControls : MetaM Unit := do
  let nativeEnv := (← getEnv).toKernelEnv
  let reader : Context :=
    { env := nativeEnv, lparams := [], safety := .safe, allowPrimitive := false,
      fuel := { recDepth := 256 } }
  let nat := Expr.const ``Nat []
  let zero := Expr.const ``Nat.zero []
  let tactic := Expr.const ``Lean.Syntax.missing []
  let level := Level.max .zero (.succ .zero)
  let unaryAt := fun name carrier => Expr.app (.const name [level]) carrier
  let binaryAt := fun name carrier payload => Expr.app (unaryAt name carrier) payload
  let mut checks := 0
  for source in [unaryAt ``outParam nat, unaryAt ``semiOutParam nat,
      binaryAt ``optParam nat zero, binaryAt ``autoParam nat tactic, nonuniformNestedSource,
      unaryAt ``outParam (binaryAt ``optParam (unary ``semiOutParam nat) zero),
      binaryAt ``optParam (binary ``autoParam nat tactic) zero,
      binaryAt ``autoParam (unary ``outParam nat) tactic] do
    let .ok (.sort _) := (monadLift (TypeChecker.checkType source) : M Expr) reader
      | throwError "nonuniform annotation type checking rejected {source}"
    unless peelTypeAnnotations source == nat do
      throwError "nonuniform annotation failed to peel to Nat"
    let .ok true := (monadLift (TypeChecker.isDefEq source nat) : M Bool) reader
      | throwError "nonuniform annotation carrier conversion failed"
    checks := checks + 1
  for source in [unaryAt ``outParam zero, binaryAt ``optParam nat tactic,
      binaryAt ``autoParam nat zero, .app (.const ``outParam []) nat,
      .app (.const ``outParam [level, level]) nat,
      .app (.const ``outParam [.param `UndeclaredUniverse]) nat,
      .app (.const ``outParam [.mvar ⟨`UnassignedUniverse⟩]) nat] do
    match (monadLift (TypeChecker.checkType source) : M Expr) reader with
    | .error _ => checks := checks + 1
    | .ok _ => throwError "malformed annotation unexpectedly type checked {source}"
  for source in [Expr.mdata {} nonuniformNestedSource, .const ``outParam [level],
      .app (.const ``optParam [level]) nat, .app (.const ``id [.succ .zero]) nat] do
    unless peelTypeAnnotations source == source do
      throwError "annotation peeling crossed an unsupported shape"
    checks := checks + 1
  for safety in [DefinitionSafety.safe, .unsafe] do
    for parameters in [0, 1] do
      let headers : Array InductiveType :=
        #[{ name := `NonuniformHeaderControl, type := nonuniformHeader, ctors := [] }]
      let computation : M (InductiveStats × Context) :=
        checkInductiveTypes parameters headers fun stats => do return (stats, ← readThe Context)
      let .ok (stats, checked) := computation { reader with safety }
        | throwError "native nonuniform first header checking failed"
      unless stats.params.size == parameters && stats.nindices == #[1 - parameters] &&
          checked.lctx.numIndices == 1 do
        throwError "native nonuniform first header allocation changed"
      for declaration in checked.lctx do
        unless declaration.type == nat do throwError "native nonuniform header stored an unpeeled domain"
      checks := checks + 1
  unless checks == 23 do throwError "annotation runtime control count changed"
  logInfo m!"annotation-domain-peeling: {checks} runtime controls"

private def auditDeclaration (name : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName && axiomName != ``Expr.looseBVarRange_eq do
      throwError "annotation-translation unexpected axiom {axiomName} in {name}"
  logInfo m!"{name}: axioms = {repr axioms}"

private def auditExactDeclaration (name : Name) (expected : List Name) : MetaM Unit := do
  auditDeclaration name expected
  let axioms ← collectAxioms name
  for axiomName in expected do
    unless axioms.contains axiomName do
      throwError "annotation-domain-peeling expected axiom {axiomName} absent from {name}"

private def auditDomainPeelingManifests : MetaM Unit := do
  let logical := [``propext, ``Quot.sound]
  let admitted := logical ++ [``Classical.choice, ``sorryAx]
  let manifests : List (Name × List Name) :=
    [(``annotationLevels_ofArity, logical),
      (Name.str ``annotationLevels_ofArity "_simp_1_1", [``propext]),
      (``TrExprS.peeledDomain, admitted),
      (Name.str ``TrExprS.peeledDomain "_simp_1_1", [``propext]),
      (``TrExprS.peeledDomainHasType, admitted),
      (``TrExprS.peeledAnonymousBodyTranslation, admitted),
      (Name.str ``TrExprS.peeledAnonymousBodyTranslation "match_1_1", [])]
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? `Lean4Lean.Verify.InductiveAnnotationDomainPeeling
    | throwError "annotation-domain-peeling manifest module absent"
  let mut declarations := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "annotation-domain-peeling module-owned axiom {name}"
      unless (manifests.map Prod.fst).contains name do
        throwError "annotation-domain-peeling unaudited declaration {name}"
  unless declarations == manifests.length do
    throwError "annotation-domain-peeling exact manifest census changed"
  for (name, expected) in manifests do
    auditExactDeclaration name expected
  auditExactDeclaration ``BinderRawDomainTranslations.peeledTypingReceipt admitted
  auditExactDeclaration ``OpenedTelescope.peeledTypingReceipt (admitted ++ [``Expr.instantiate1_eq])
  logInfo m!"annotation-domain-peeling: {declarations} exhaustive production manifests; 2 binder manifests"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "annotation-translation audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "annotation-translation module-owned axiom {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      auditDeclaration name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditFoundationBoundary : MetaM Unit := do
  let environment ← getEnv
  for (name, moduleName) in [(``TrProj, `Lean4Lean.Verify.Typing.Expr),
      (``VEnv.IsDefEqU.forallE_inv, `Lean4Lean.Theory.Typing.Injectivity),
      (``VEnv.IsDefEq.uniq, `Lean4Lean.Theory.Typing.UniqueTyping),
      (``TrExprS.inst_fvar, `Lean4Lean.Verify.Typing.Lemmas)] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "annotation-translation foundation module absent: {moduleName}"
    unless environment.getModuleIdxFor? name == some moduleIndex do
      throwError "annotation-translation inherited admission root changed origin: {name}"
    let axioms ← collectAxioms name
    unless axioms.contains ``sorryAx do
      throwError "annotation-translation inherited foundation admission unexpectedly vanished: {name}"
    auditDeclaration name [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
    logInfo m!"pinned inherited admitted foundation: {name} from {moduleName}"

#print axioms TypedAnnotationSpine.ofTrExprS
#print axioms OpenedTelescope.translatedDomains
#print axioms BinderRawDomainTranslations.typingReceipt
#print axioms OpenedTelescope.translatedTypingReceipt
#print axioms actualPlainHeaderReachesStoredTyping

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let admitted := logical ++ [``sorryAx]
  let binding := admitted ++ [``Expr.instantiate1_eq]
  for theoremName in [``fixtureConstants, ``fixtureDefinitions, ``natTyped, ``zeroTyped,
      ``tacticTyped, ``optionalFunctionTyped, ``autoFunctionTyped, ``optionalAppliedTyped,
      ``autoAppliedTyped, ``optionalSourceTyped, ``autoSourceTyped, ``optionalUniform, ``autoUniform,
      ``unaryFunctionTyped, ``wrappedCarrierTyped, ``nestedSourceTyped, ``nestedUniform,
      ``metadataBarrierUniform, ``unrecognizedUnaryUniform, ``equivalentDistinctLevels,
      ``equivalentLevelsFailSyntacticUniformity, ``noncanonicalArityFailsUniformity,
      ``noncanonicalArityStillPeels, ``bothRolesRequireVirtualFreshness, ``reusedVirtualFVarExcluded,
      ``repeatedVirtualFVarExcluded, ``singletonRawUniform, ``plainDomainUniformAtEveryExtractedLevel] do
    auditDeclaration theoremName logical
  for theoremName in [``natTranslated, ``zeroTranslated, ``tacticTranslated,
      ``optionalActualTranslation, ``autoActualTranslation, ``optionalSpineExtracted,
      ``autoSpineExtracted, ``carriersAndPayloadsComeFromTranslation, ``wrappedCarrierTranslated,
      ``nestedActualTranslation, ``nestedSpineExtracted, ``metadataBarrierStillTranslates,
      ``metadataBarrierExtractedWithoutPeeling, ``equivalentUniverseAnnotationActuallyTranslates,
      ``singletonHeaderTranslated, ``singletonRawTranslations, ``singletonActualIndexType,
      ``plainHeaderTranslated] do
    auditDeclaration theoremName admitted
  for theoremName in [``openedFreshHistoryIsSameWitness, ``rawDomainsUseEvolvingContexts,
      ``singletonHeaderOpened, ``singletonOpenedHasActualRawTranslations,
      ``actualOpenedWitnessRetainsConditionalTyping, ``plainHeaderOpened,
      ``actualPlainHeaderReachesStoredTyping] do
    auditDeclaration theoremName binding
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationTranslation,
      `Lean4Lean.Verify.InductiveAnnotationDomainPeeling,
      `Lean4Lean.Verify.InductiveTelescopeTranslation, `Lean4Lean.Verify.InductiveBinderTranslation] do
    auditModule moduleName binding
  for theoremName in [``natEquivalentTyped, ``equivalentUnaryFunctionTyped, ``equivalentUnaryTyped,
      ``nonuniformOptionalFunctionTyped, ``nonuniformAutoFunctionTyped, ``nonuniformOptionalAppliedTyped,
      ``nonuniformAutoAppliedTyped, ``nonuniformNestedTyped, ``nonuniformNestedNotUniform] do
    auditExactDeclaration theoremName [``propext, ``Quot.sound]
  for theoremName in [``equivalentUnaryTranslated, ``nonuniformOutParamPeels, ``nonuniformSemiOutParamPeels,
      ``nonuniformOptionalTranslated, ``nonuniformAutoTranslated, ``nonuniformOptionalPeels,
      ``nonuniformAutoPeels, ``nonuniformNestedTranslated, ``nonuniformNestedPeels,
      ``nonuniformBodyConversion, ``nonuniformMetadataBarrier, ``nonuniformHeaderTranslated] do
    auditExactDeclaration theoremName admitted
  auditExactDeclaration ``actualOpenedWitnessNeedsNoUniformity binding
  auditExactDeclaration ``nonuniformHeaderOpened [``Expr.instantiate1_eq]
  auditExactDeclaration ``nonuniformHeaderStoredReceipt binding
  for declarationName in [``equivalentLevel, ``nonuniformNestedSource, ``nonuniformNestedSemantic,
      ``nonuniformIndexStep, ``nonuniformHeader] do
    auditExactDeclaration declarationName []
  auditDomainPeelingManifests
  annotationRuntimeControls
  auditFoundationBoundary
  logInfo "annotation-translation: 53 prior / 24 nonuniform proof controls; clean core and pinned inherited bridge boundaries"

end InductiveAnnotationTranslationTest
