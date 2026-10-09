import Lean4Lean.Verify.InductiveAnnotationSemantics
import Lean4Lean.Verify.InductiveAnnotationTyping
import Lean4Lean.Verify.InductiveBinderTyping
import Lean4Lean.Verify.ExprBoundedRange
import Lean4Lean.Verify.Typing.Expr
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveAnnotationTypingTest

private def unary (name : Name) (carrier : Expr) : Expr :=
  .app (.const name [.succ .zero]) carrier

private def binary (name : Name) (carrier extra : Expr) : Expr :=
  .app (.app (.const name [.succ .zero]) carrier) extra

private def semanticUnary (name : Name) (carrier : VExpr) : VExpr :=
  .app (.const name [.succ .zero]) carrier

private def semanticBinary (name : Name) (carrier extra : VExpr) : VExpr :=
  .app (.app (.const name [.succ .zero]) carrier) extra

private def canonicalEnvironment : VEnv where
  constants name :=
    if name = ``Nat then some { uvars := 0, type := .sort (.succ .zero) }
    else if name = ``Nat.zero then some { uvars := 0, type := .const ``Nat [] }
    else if name = ``Lean.Syntax then some { uvars := 0, type := .sort (.succ .zero) }
    else if name = ``Lean.Syntax.missing then some { uvars := 0, type := .const ``Lean.Syntax [] }
    else if name = ``outParam then
      some { uvars := 1, type := (unaryAnnotationDefinition ``outParam).type }
    else if name = ``semiOutParam then
      some { uvars := 1, type := (unaryAnnotationDefinition ``semiOutParam).type }
    else if name = ``optParam then some { uvars := 1, type := optParamDefinition.type }
    else if name = ``autoParam then some { uvars := 1, type := autoParamDefinition.type }
    else none
  defeqs definition := definition = unaryAnnotationDefinition ``outParam ∨
    definition = unaryAnnotationDefinition ``semiOutParam ∨
    definition = optParamDefinition ∨ definition = autoParamDefinition

private theorem canonicalDefinitions : CanonicalAnnotationDefinitions canonicalEnvironment := by
  constructor <;> simp [canonicalEnvironment]

private theorem natTyping : canonicalEnvironment.HasType 0 [] (.const ``Nat [])
    (.sort (.succ .zero)) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := canonicalEnvironment) (c := ``Nat) (ls := [])
    (ci := { uvars := 0, type := .sort (.succ .zero) })
    (by simp [canonicalEnvironment]) (by simp) rfl

private theorem optionalDefaultTyping : canonicalEnvironment.HasType 0 [] (.const ``Nat.zero [])
    (.const ``Nat []) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := canonicalEnvironment) (c := ``Nat.zero) (ls := [])
    (ci := { uvars := 0, type := .const ``Nat [] })
    (by simp [canonicalEnvironment]) (by simp) rfl

private theorem autoSyntaxPayloadTyping : canonicalEnvironment.HasType 0 []
    (.const ``Lean.Syntax.missing []) (.const ``Lean.Syntax []) := by
  simpa only [VExpr.instL] using VEnv.HasType.const
    (env := canonicalEnvironment) (c := ``Lean.Syntax.missing) (ls := [])
    (ci := { uvars := 0, type := .const ``Lean.Syntax [] })
    (by simp [canonicalEnvironment]) (by simp) rfl

private theorem outParamCanonicalCompatibility : canonicalEnvironment.IsDefEq 0 []
    (semanticUnary ``outParam (.const ``Nat [])) (.const ``Nat []) (.sort (.succ .zero)) :=
  canonicalDefinitions.outParam_isDefEq (by trivial) natTyping

private theorem semiOutParamCanonicalCompatibility : canonicalEnvironment.IsDefEq 0 []
    (semanticUnary ``semiOutParam (.const ``Nat [])) (.const ``Nat []) (.sort (.succ .zero)) :=
  canonicalDefinitions.semiOutParam_isDefEq (by trivial) natTyping

private theorem optParamRequiresCarrierPayload (ordered : canonicalEnvironment.Ordered) :
    canonicalEnvironment.IsDefEq 0 []
      (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero []))
      (.const ``Nat []) (.sort (.succ .zero)) :=
  canonicalDefinitions.optParam_isDefEq ordered (by trivial) natTyping optionalDefaultTyping

private theorem autoParamRequiresSyntaxPayload (ordered : canonicalEnvironment.Ordered) :
    canonicalEnvironment.IsDefEq 0 []
      (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing []))
      (.const ``Nat []) (.sort (.succ .zero)) :=
  canonicalDefinitions.autoParam_isDefEq ordered (by trivial) natTyping autoSyntaxPayloadTyping

private theorem emptyEnvironmentLacksCanonicalDefinitions :
    ¬ CanonicalAnnotationDefinitions VEnv.empty := by
  intro definitions
  exact definitions.outParam

private inductive FixtureTranslation : Expr → VExpr → Prop where
  | nat : FixtureTranslation (.const ``Nat []) (.const ``Nat [])
  | zero : FixtureTranslation (.const ``Nat.zero []) (.const ``Nat.zero [])
  | syntax : FixtureTranslation (.const ``Lean.Syntax.missing []) (.const ``Lean.Syntax.missing [])
  | unary {source semantic} (name : Name) (carrier : FixtureTranslation source semantic) :
      FixtureTranslation (unary name source) (semanticUnary name semantic)
  | binary {sourceCarrier carrier sourceExtra extra} (name : Name)
      (carrierTranslated : FixtureTranslation sourceCarrier carrier)
      (extraTranslated : FixtureTranslation sourceExtra extra) :
      FixtureTranslation (binary name sourceCarrier sourceExtra) (semanticBinary name carrier extra)

private theorem natSpine : TypedAnnotationSpine FixtureTranslation canonicalEnvironment 0 []
    (.const ``Nat []) (.const ``Nat []) (.succ .zero) :=
  .base rfl .nat natTyping

private theorem optionalSourceSpine : TypedAnnotationSpine FixtureTranslation canonicalEnvironment 0 []
    (binary ``optParam (.const ``Nat []) (.const ``Nat.zero []))
    (semanticBinary ``optParam (.const ``Nat []) (.const ``Nat.zero [])) (.succ .zero) :=
  .optParam (.succ .zero) (by trivial) (.binary _ .nat .zero) optionalDefaultTyping natSpine

private theorem autoSourceSpine : TypedAnnotationSpine FixtureTranslation canonicalEnvironment 0 []
    (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing []))
    (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])) (.succ .zero) :=
  .autoParam (.succ .zero) (by trivial) (.binary _ .nat .syntax) autoSyntaxPayloadTyping natSpine

private def nestedSource : Expr := unary ``outParam (unary ``semiOutParam
  (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])))

private def nestedSemantic : VExpr := semanticUnary ``outParam (semanticUnary ``semiOutParam
  (semanticBinary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])))

private theorem nestedSourceSpine : TypedAnnotationSpine FixtureTranslation canonicalEnvironment 0 []
    nestedSource nestedSemantic (.succ .zero) :=
  .outParam (.succ .zero) (by trivial) (.unary _ (.unary _ (.binary _ .nat .syntax)))
    (.semiOutParam (.succ .zero) (by trivial) (.unary _ (.binary _ .nat .syntax)) autoSourceSpine)

private theorem nestedSyntaxPeels : peelTypeAnnotations nestedSource = .const ``Nat [] := by
  simp [nestedSource, unary, binary, peelTypeAnnotations]

private theorem metadataBarrierPreservesAnnotations (metadata : MData) :
    peelTypeAnnotations (.mdata metadata nestedSource) = .mdata metadata nestedSource := rfl

private theorem unrecognizedUnaryPreserved (name : Name) (source : Expr)
    (notOut : name ≠ ``outParam) (notSemi : name ≠ ``semiOutParam) :
    peelTypeAnnotations (unary name source) = unary name source := by
  simp only [unary, peelTypeAnnotations, notOut, notSemi, false_or, ↓reduceIte]

private theorem unrecognizedBinaryPreserved (name : Name) (source extra : Expr)
    (notOptional : name ≠ ``optParam) (notAuto : name ≠ ``autoParam) :
    peelTypeAnnotations (binary name source extra) = binary name source extra := by
  simp only [binary, peelTypeAnnotations, notOptional, notAuto, false_or, ↓reduceIte]

private theorem optionalWrongArityPreserved (source : Expr) :
    peelTypeAnnotations (unary ``optParam source) = unary ``optParam source := by
  simp [unary, peelTypeAnnotations]

private theorem unaryWrongArityPreserved (source extra : Expr) :
    peelTypeAnnotations (binary ``outParam source extra) = binary ``outParam source extra := by
  simp [binary, peelTypeAnnotations]

private theorem arbitraryLevelsRemainSyntacticallyTotal (levels : List Level) (source : Expr) :
    peelTypeAnnotations (.app (.const ``outParam levels) source) = peelTypeAnnotations source := by
  simp [peelTypeAnnotations]

private theorem nestedSemanticCompatibility (ordered : canonicalEnvironment.Ordered) :
    ∃ peeled, FixtureTranslation (peelTypeAnnotations nestedSource) peeled ∧
      canonicalEnvironment.IsDefEq 0 [] nestedSemantic peeled (.sort (.succ .zero)) :=
  nestedSourceSpine.peelTypeAnnotations canonicalDefinitions ordered

private theorem nestedRawTypeRequiresExplicitSpine (ordered : canonicalEnvironment.Ordered) :
    SourceHasType FixtureTranslation canonicalEnvironment 0 [] nestedSource (.sort (.succ .zero)) :=
  nestedSourceSpine.sourceHasType canonicalDefinitions ordered

private theorem nestedStoredDomainTypeRequiresExplicitSpine (ordered : canonicalEnvironment.Ordered) :
    SourceHasType FixtureTranslation canonicalEnvironment 0 []
      (peelTypeAnnotations nestedSource) (.sort (.succ .zero)) :=
  nestedSourceSpine.peeledHasType canonicalDefinitions ordered

private theorem nestedInhabitantConversion (ordered : canonicalEnvironment.Ordered)
    (inhabitant : VExpr) (typed : canonicalEnvironment.HasType 0 [] inhabitant nestedSemantic) :
    ∃ peeled, FixtureTranslation (peelTypeAnnotations nestedSource) peeled ∧
      canonicalEnvironment.HasType 0 [] inhabitant peeled :=
  nestedSourceSpine.inhabitantConversion canonicalDefinitions ordered typed

private theorem metadataBarrierNeedsExplicitTyping {translation : Expr → VExpr → Prop}
    {environment : VEnv} {universeCount : Nat} {context : List VExpr} {semantic : VExpr}
    {level : VLevel} (metadata : MData)
    (translated : translation (.mdata metadata nestedSource) semantic)
    (typed : environment.HasType universeCount context semantic (.sort level)) :
    TypedAnnotationSpine translation environment universeCount context
      (.mdata metadata nestedSource) semantic level :=
  .base rfl translated typed

private theorem unrecognizedAnnotationNeedsExplicitTyping {translation : Expr → VExpr → Prop}
    {environment : VEnv} {universeCount : Nat} {context : List VExpr} {semantic : VExpr}
    {level : VLevel} (name : Name) (source : Expr)
    (notOut : name ≠ ``outParam) (notSemi : name ≠ ``semiOutParam)
    (translated : translation (unary name source) semantic)
    (typed : environment.HasType universeCount context semantic (.sort level)) :
    TypedAnnotationSpine translation environment universeCount context (unary name source) semantic level :=
  .base (unrecognizedUnaryPreserved name source notOut notSemi) translated typed

private def indexStep (id : FVarId) : BinderStep where
  role := .index
  name := `typedIndex
  domain := nestedSource
  bi := .implicit
  value := .fvar id

private theorem singletonIndexStoredDomainTyping (id : FVarId) (ordered : canonicalEnvironment.Ordered) :
    BinderStoredIndexDomainHasType (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) [indexStep id] := by
  intro position step selected _
  cases position with
  | zero =>
    have sameStep : indexStep id = step := Option.some.inj selected
    subst step
    exact nestedStoredDomainTypeRequiresExplicitSpine ordered
  | succ position => simp at selected

private theorem singletonActualIndexDeclarationTyping (id : FVarId) (ordered : canonicalEnvironment.Ordered)
    (ctx : Context) (declared : BinderStepsIndexDeclared ctx [indexStep id]) :
    BinderStoredIndexTypeHasType (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) ctx [indexStep id] :=
  (singletonIndexStoredDomainTyping id ordered).storedIndexTypeHasType declared

private theorem actualLookupTypeJudgment {translation : Nat → Expr → VExpr → Prop}
    {environment : VEnv} {universeCount : Nat} {contexts : Nat → List VExpr} {levels : Nat → VLevel}
    {ctx : Context} {steps : List BinderStep} {position : Nat} {step : BinderStep} {decl : LocalDecl}
    (typed : BinderStoredIndexTypeHasType translation environment universeCount contexts levels ctx steps)
    (selected : steps[position]? = some step) (index : step.role = .index)
    (lookup : ctx.lctx.find? step.value.fvarId! = some decl) :
    SourceHasType (translation position) environment universeCount (contexts position)
      decl.type (.sort (levels position)) :=
  typed position step decl selected index lookup

private theorem storedDeclarationUsesSameLookup {translation : Expr → VExpr → Prop}
    {environment : VEnv} {universeCount : Nat} {context : List VExpr} {type : VExpr} {ctx : Context}
    {value domain : Expr} {name : Name} {binderInfo : BinderInfo}
    (declared : BinderDeclaredAt ctx value name domain binderInfo)
    (typed : SourceHasType translation environment universeCount context domain type) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧ decl.type = domain ∧
      SourceHasType translation environment universeCount context decl.type type :=
  declared.typeHasType typed

private theorem parameterOnlyLookupTypingVacuous {translation : Nat → Expr → VExpr → Prop}
    {environment : VEnv} {universeCount : Nat} {contexts : Nat → List VExpr} {levels : Nat → VLevel}
    (ctx : Context) (parameter : BinderStep) (role : parameter.role = .parameter) :
    BinderStoredIndexTypeHasType translation environment universeCount contexts levels ctx [parameter] := by
  intro position step decl selected index _
  cases position with
  | zero =>
    have sameStep : parameter = step := Option.some.inj selected
    subst step
    rw [role] at index
    cases index
  | succ position => simp at selected

private theorem trExprSBridgeExplicitlyAdmitted {environment : VEnv} {universeNames : List Name}
    {context : VLCtx} {source : Expr} {semantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine (TrExprS environment universeNames context) environment
      universeNames.length context.toCtx source semantic level)
    (definitions : CanonicalAnnotationDefinitions environment) (ordered : environment.Ordered) :
    SourceHasType (TrExprS environment universeNames context) environment universeNames.length context.toCtx
      (peelTypeAnnotations source) (.sort level) :=
  spine.peeledHasType definitions ordered

private theorem closureAndBoundDoNotSupplyTranslation :
    BVarRangeFits (.const ``Nat []) ∧ (Expr.const ``Nat []).Closed 0 ∧
      ¬ SourceHasType (fun _ _ => False) canonicalEnvironment 0 [] (.const ``Nat [])
        (.sort (.succ .zero)) := by
  refine ⟨True.intro, True.intro, ?_⟩
  rintro ⟨semantic, translated, _⟩
  exact translated

private theorem singletonIndexTypedSpines (id : FVarId) :
    BinderRawDomainTypedSpines (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) [indexStep id] := by
  intro position step selected
  cases position with
  | zero =>
    have sameStep : indexStep id = step := Option.some.inj selected
    subst step
    exact ⟨nestedSemantic, nestedSourceSpine⟩
  | succ position => simp at selected

private theorem rawAndPeeledAndStoredTypingShareHistory (id : FVarId)
    (ordered : canonicalEnvironment.Ordered) (ctx : Context)
    (declared : BinderStepsIndexDeclared ctx [indexStep id]) :
    BinderRawDomainHasType (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) [indexStep id] ∧
    BinderStoredIndexDomainHasType (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) [indexStep id] ∧
    BinderStoredIndexTypeHasType (fun _ => FixtureTranslation) canonicalEnvironment 0
      (fun _ => []) (fun _ => .succ .zero) ctx [indexStep id] :=
  (singletonIndexTypedSpines id).typingReceipt canonicalDefinitions ordered declared

private def audit (declarationName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms declarationName
  for axiomName in axioms do
    unless axiomName != ``Expr.looseBVarRange_eq && axiomName != ``sorryAx && allowed.contains axiomName do
      throwError "annotation-typing unexpected axiom {axiomName} in {declarationName}"
  logInfo m!"{declarationName}: axioms = {repr axioms}"

private def auditModule (moduleName : Name) (allowed : List Name) : MetaM Unit := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName
    | throwError "annotation-typing audited module absent: {moduleName}"
  let mut declarations := 0
  let mut theorems := 0
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      declarations := declarations + 1
      if information matches .axiomInfo _ then
        throwError "annotation-typing module-owned axiom: {name}"
      if information matches .thmInfo _ then
        theorems := theorems + 1
      audit name allowed
  logInfo m!"{moduleName}: declarations incl private/generated = {declarations}; theorems = {theorems}"

private def auditAdmittedBridge : MetaM Unit := do
  let axioms ← collectAxioms ``trExprSBridgeExplicitlyAdmitted
  unless axioms.contains ``sorryAx do
    throwError "annotation-typing TrExprS foundation admission boundary unexpectedly disappeared"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains axiomName do
      throwError "annotation-typing unexpected admitted-bridge axiom {axiomName}"
  logInfo m!"separately admitted TrExprS bridge: axioms = {repr axioms}"

#print axioms CanonicalAnnotationDefinitions.optParam_isDefEq
#print axioms CanonicalAnnotationDefinitions.autoParam_isDefEq
#print axioms TypedAnnotationSpine.peeledHasType
#print axioms BinderRawDomainTypedSpines.typingReceipt
#print axioms trExprSBridgeExplicitlyAdmitted

run_meta
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [``canonicalDefinitions, ``natTyping, ``optionalDefaultTyping,
      ``autoSyntaxPayloadTyping, ``outParamCanonicalCompatibility, ``semiOutParamCanonicalCompatibility,
      ``optParamRequiresCarrierPayload, ``autoParamRequiresSyntaxPayload,
      ``emptyEnvironmentLacksCanonicalDefinitions, ``natSpine, ``optionalSourceSpine,
      ``autoSourceSpine, ``nestedSourceSpine, ``nestedSyntaxPeels,
      ``metadataBarrierPreservesAnnotations, ``unrecognizedUnaryPreserved,
      ``unrecognizedBinaryPreserved, ``optionalWrongArityPreserved,
      ``unaryWrongArityPreserved, ``arbitraryLevelsRemainSyntacticallyTotal,
      ``nestedSemanticCompatibility, ``nestedRawTypeRequiresExplicitSpine,
      ``nestedStoredDomainTypeRequiresExplicitSpine, ``nestedInhabitantConversion,
      ``metadataBarrierNeedsExplicitTyping, ``unrecognizedAnnotationNeedsExplicitTyping,
      ``singletonIndexStoredDomainTyping, ``singletonActualIndexDeclarationTyping,
      ``actualLookupTypeJudgment, ``storedDeclarationUsesSameLookup,
      ``parameterOnlyLookupTypingVacuous, ``closureAndBoundDoNotSupplyTranslation,
      ``singletonIndexTypedSpines, ``rawAndPeeledAndStoredTypingShareHistory] do
    audit theoremName logical
  for moduleName in [`Lean4Lean.Verify.InductiveAnnotationSemantics,
      `Lean4Lean.Verify.InductiveAnnotationTyping, `Lean4Lean.Verify.InductiveBinderTyping] do
    auditModule moduleName logical
  auditAdmittedBridge
  logInfo "annotation-typing: 34 focused proof controls; three clean module censuses; one separate admitted bridge"

end InductiveAnnotationTypingTest
