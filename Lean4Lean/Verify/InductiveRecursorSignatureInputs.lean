import Lean4Lean.Verify.InductiveConstructorRegistration
import Lean4Lean.Verify.InductiveMinorTranslation
import Lean4Lean.Verify.InductiveHeaderParameterApplications

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open private relatedMemberLeft from Lean4Lean.Verify.InductiveConstructorSemanticReceipts

structure RecursorConstantInput (environment : VEnv) (universes : List Name) (virtual : VLCtx)
    (name : Name) (levels : List Level) (source : Expr) where
  semanticType : VExpr
  semanticValue : VExpr
  sourceTranslated : TrExprS environment universes virtual source semanticType
  sourceTypehood : environment.IsType universes.length virtual.toCtx semanticType
  valueTranslated : TrExprS environment universes virtual (.const name levels) semanticValue
  valueTyped : environment.HasType universes.length virtual.toCtx semanticValue semanticType

theorem RecursorConstantInput.ofTranslation
    (environmentWF : environment.WF)
    (lookup : environment.constants name = some constant)
    (translated : TrExprS environment originalUniverses [] source constant.type)
    (universeCount : originalUniverses.length = constant.uvars)
    (model : MLCtx) (modelWF : model.WF environment universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = originalUniverses.length) :
    Nonempty (RecursorConstantInput environment universes model.vlctx name levels
      (source.instantiateLevelParams originalUniverses levels)) := by
  have levelWF := VLevel.WF.of_mapM_ofLevel mapped
  have closedType : environment.IsType constant.uvars [] constant.type :=
    environmentWF.ordered.constWF lookup
  have instantiatedType : environment.IsType universes.length [] (constant.type.instL semanticLevels) := by
    simpa only [List.map_nil] using closedType.instL levelWF
  have instantiatedSource : TrExpr environment universes []
      (source.instantiateLevelParams originalUniverses levels) (constant.type.instL semanticLevels) := by
    simpa only [VLCtx.instL] using translated.instL (Δ := []) environmentWF trivial mapped arity.symm
  have weakening := VLCtx.FVLift.from_nil model.noBV
  obtain ⟨semanticType, sourceTranslated, equality⟩ :=
    instantiatedSource.weakFV environmentWF weakening modelWF.tr.wf
  have sourceTypehood := (instantiatedType.weakN environmentWF.ordered weakening.toCtx).defeqU_l
    environmentWF modelWF.tr.wf.toCtx equality.symm
  have count : semanticLevels.length = constant.uvars :=
    (List.mapM_eq_some.mp mapped).length_eq.symm.trans (arity.trans universeCount)
  have valueTyped : environment.HasType universes.length []
      (.const name semanticLevels) (constant.type.instL semanticLevels) :=
    .const lookup levelWF count
  have reachedTyped := (valueTyped.weakN environmentWF.ordered weakening.toCtx).defeqU_r
    environmentWF modelWF.tr.wf.toCtx equality.symm
  exact ⟨{
    semanticType, semanticValue := .const name semanticLevels, sourceTranslated, sourceTypehood,
    valueTranslated := .const lookup mapped (arity.trans universeCount),
    valueTyped := by simpa only [VExpr.liftN] using reachedTyped }⟩

theorem ConstructorConstantRegistration.constructorInput
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source)
    (model : MLCtx) (modelWF : model.WF registration.semantic universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = root.lparams.length) :
    Nonempty (RecursorConstantInput registration.semantic universes model.vlctx source.name levels
      (source.type.instantiateLevelParams root.lparams levels)) := by
  obtain ⟨constructor, _, nativeLookup, semanticLookup, translated⟩ :=
    registration.constructorConstant typeMember index source sourceGet
  apply RecursorConstantInput.ofTranslation registration.semanticWF semanticLookup
    (originalUniverses := root.lparams)
  · simpa only [declareConstructors.metadataVal, ConstantInfo.type, ConstantInfo.toConstantVal]
      using translated.2.2
  · simpa only [declareConstructors.metadataVal, ConstantInfo.levelParams, ConstantInfo.toConstantVal]
      using translated.2.1
  · exact modelWF
  · exact mapped
  · exact arity

theorem ConstructorConstantRegistration.headerInput
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    (typeMember : type ∈ types)
    (model : MLCtx) (modelWF : model.WF registration.semantic universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = root.lparams.length) :
    Nonempty (RecursorConstantInput registration.semantic universes model.vlctx type.name levels
      (type.type.instantiateLevelParams root.lparams levels)) := by
  obtain ⟨header, member, translated⟩ := relatedMemberLeft receipts.translated.2.2
    (Array.mem_toList_iff.mpr typeMember)
  have lookup := registration.increase.constants
    (VEnv.addInductHeaders.constants receipts.registered member)
  have nativeLookup : registration.semantic.constants type.name = some header.toVConstant := by
    simpa only [translated.1] using lookup
  exact RecursorConstantInput.ofTranslation registration.semanticWF nativeLookup
    (translated.2.2.1.mono ((VEnv.addInductHeaders.le receipts.registered).trans registration.increase))
    translated.2.1 model modelWF mapped arity

theorem RecursorConstantInput.alignedType
    (input : RecursorConstantInput environment universes virtual name levels source)
    (environmentWF : environment.WF) (contextWF : virtual.WF environment universes.length)
    (translated : TrExprS environment universes virtual source semantic) :
    environment.HasType universes.length virtual.toCtx input.semanticValue semantic :=
  input.valueTyped.defeqU_r environmentWF contextWF.toCtx
    (input.sourceTranslated.uniq environmentWF (.refl environmentWF contextWF) translated)

theorem RecursorConstantInput.applyParameters
    (input : RecursorConstantInput environment universes model.vlctx name levels source)
    (arguments : ElimNestedInductive.TypedParameterArguments environment universes model
      input.semanticType replacements semantics resultType) :
    TrExprS environment universes model.vlctx ((Expr.const name levels).mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments input.semanticValue semantics) ∧
    environment.HasType universes.length model.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments input.semanticValue semantics) resultType :=
  arguments.apply input.valueTranslated input.valueTyped

theorem RecursorConstantInput.applyHeaderParameters
    (input : RecursorConstantInput environment universes model.vlctx name levels source)
    (parameters : HeaderParameterApplicationInput environment universes model stats source)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes) :
    ∃ value, TrExprS environment universes model.vlctx (mkAppN (.const name levels) stats.params) value ∧
      environment.HasType universes.length model.vlctx.toCtx value parameters.result :=
  parameters.application environmentWF modelWF input.valueTranslated
    (input.alignedType environmentWF modelWF.tr.wf parameters.sourceTranslated)

theorem TranslatedRecursorCtorFieldTrace.initialTranslation
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {index finalIndex : Nat}
    {fields recursiveFields finalFields finalRecursive : Array Expr} {reader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source index fields recursiveFields reader
      terminal finalIndex finalFields finalRecursive finalReader}
    (history : TranslatedRecursorCtorFieldTrace environment universes trace
      virtual semantic finalVirtual finalSemantic) :
    TrExprS environment universes virtual source semantic := by
  cases history with
  | stop _ _ translated => exact translated
  | field _ _ _ translated _ _ => exact translated

theorem CtorFieldModelEndpoint.constantInputApplication
    {environment : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context} {model fieldModel : MLCtx} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint environment universes trace model fieldModel semantic)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (input : RecursorConstantInput environment universes model.vlctx name levels source) :
    ∃ value terminalSemantic,
      TrExprS environment universes fieldModel.vlctx (mkAppN (.const name levels) fields) value ∧
      TrExprS environment universes fieldModel.vlctx terminal terminalSemantic ∧
      environment.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic := by
  have endpointCopy := endpoint
  obtain ⟨_, _, history, _⟩ := endpointCopy
  exact endpoint.application environmentWF input.valueTranslated
    (input.alignedType environmentWF modelWF.tr.wf history.initialTranslation)

theorem CtorFieldModelEndpoint.registeredConstructorApplication
    {root : TypeChecker.VContext} {original reader : Context} {nparams : Nat}
    {types : Array InductiveType} {stats : InductiveStats} {actual final : Kernel.Environment}
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual} {isUnsafe : Bool}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final)
    {type : InductiveType} (typeMember : type ∈ types) (index : Nat) (source : Constructor)
    (sourceGet : type.ctors[index]? = some source)
    {universes : List Name} {levels : List Level} {semanticLevels : List VLevel}
    {model fieldModel : MLCtx} (modelWF : model.WF registration.semantic universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = root.lparams.length)
    {terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {fieldReader initialReader : Context} {semantic : VExpr}
    {trace : RecursorCtorFieldTrace stats (source.type.instantiateLevelParams root.lparams levels)
      0 #[] #[] initialReader terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint registration.semantic universes trace model fieldModel semantic) :
    ∃ value terminalSemantic,
      TrExprS registration.semantic universes fieldModel.vlctx
        (mkAppN (.const source.name levels) fields) value ∧
      TrExprS registration.semantic universes fieldModel.vlctx terminal terminalSemantic ∧
      registration.semantic.HasType universes.length fieldModel.vlctx.toCtx value terminalSemantic := by
  obtain ⟨input⟩ := registration.constructorInput typeMember index source sourceGet model modelWF mapped arity
  exact endpoint.constantInputApplication registration.semanticWF modelWF input

def RecursorSignatureInputs (environment : VEnv) (originalUniverses : List Name)
    (types : Array InductiveType) : Prop :=
  ∀ (universes : List Name) (levels : List Level) (semanticLevels : List VLevel) (model : MLCtx),
    model.WF environment universes →
    levels.mapM (VLevel.ofLevel universes) = some semanticLevels →
    levels.length = originalUniverses.length → ∀ type ∈ types,
      Nonempty (RecursorConstantInput environment universes model.vlctx type.name levels
        (type.type.instantiateLevelParams originalUniverses levels)) ∧
      ∀ (index : Nat) (source : Constructor), type.ctors[index]? = some source →
        Nonempty (RecursorConstantInput environment universes model.vlctx source.name levels
          (source.type.instantiateLevelParams originalUniverses levels))

theorem ConstructorConstantRegistration.signatureInputs
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    {receipts : ConstructorSemanticReceipts stage isUnsafe}
    (registration : ConstructorConstantRegistration receipts final) :
    RecursorSignatureInputs registration.semantic root.lparams types := by
  intro universes levels semanticLevels model modelWF mapped arity type member
  exact ⟨registration.headerInput member model modelWF mapped arity,
    fun index source sourceGet => registration.constructorInput member index source sourceGet
      model modelWF mapped arity⟩

theorem checkInductiveTypes.recursorSignatureContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage isUnsafe,
          ∃ registration : ConstructorConstantRegistration receipts final,
            RecursorSignatureInputs registration.semantic root.lparams types := by
  refine (checkInductiveTypes.constructorConstantContinuation nparams types numNested isUnsafe next
    root reader aligned empty different constants definitions ordinary safetyBound constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, ⟨registration⟩⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration, registration.signatureInputs⟩

theorem run.recursorSignatureContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ∃ receipts : ConstructorSemanticReceipts stage (reader.safety != .safe),
          ∃ registration : ConstructorConstantRegistration receipts final,
            RecursorSignatureInputs registration.semantic root.lparams types.toArray := by
  refine (run.constructorConstantContinuation nparams types numNested root reader aligned empty
    different constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, receipts, ⟨registration⟩⟩
  exact ⟨stats, current, actual, final, stage, receipts, registration, registration.signatureInputs⟩

end Lean4Lean.AddInductive
