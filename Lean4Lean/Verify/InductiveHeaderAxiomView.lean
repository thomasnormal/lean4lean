import Lean4Lean.Verify.InductiveMutualHeaderTyping
import Lean4Lean.Verify.OrdinaryInterfaces
import Lean4Lean.Verify.InductiveFrontendRestoration

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.zipInductiveHeaders from Lean4Lean.Verify.InductiveHeaders
open private Lean4Lean.AddInductive.typedHeaderList from Lean4Lean.Verify.InductiveMutualHeaderTyping
open private Lean4Lean.AddInductive.readWF Lean4Lean.AddInductive.bindWF
  from Lean4Lean.Verify.InductiveStats

def headerAxiomInfo (info : InductiveVal) : ConstantInfo :=
  .axiomInfo { toConstantVal := info.toConstantVal, isUnsafe := info.isUnsafe }

def HeaderRegistrationRecord (information : ConstantInfo) : Prop :=
  ∃ header, information = .inductInfo header

def HeaderAxiomRegistrationRecord (information : ConstantInfo) : Prop :=
  ∃ header, information = headerAxiomInfo header

def headerTypeValue (info : ConstantInfo) : Name × List Name × Expr × DefinitionSafety × Option Expr :=
  (info.name, info.levelParams, info.type, info.safety, info.value?)

theorem headerAxiomInfo.typeValue (info : InductiveVal) :
    headerTypeValue (headerAxiomInfo info) = headerTypeValue (.inductInfo info) := rfl

def HeaderAxiomAgreement (actual shadow : Kernel.Environment) : Prop :=
  ∀ name, (actual.find? name).map headerTypeValue = (shadow.find? name).map headerTypeValue

def HeaderAxiomLookupAgreement (changed : Name → Prop) (actual shadow : Kernel.Environment) : Prop :=
  ∀ name, actual.find? name = shadow.find? name ∨ changed name ∧
    ∃ header, actual.find? name = some (.inductInfo header) ∧
      shadow.find? name = some (headerAxiomInfo header)

theorem HeaderAxiomLookupAgreement.refl (changed : Name → Prop) (env : Kernel.Environment) :
    HeaderAxiomLookupAgreement changed env env :=
  fun _ => .inl rfl

theorem HeaderAxiomLookupAgreement.signatures
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) : HeaderAxiomAgreement actual shadow := by
  intro name
  rcases agreement name with same | ⟨_, header, actualLookup, shadowLookup⟩
  · rw [same]
  · rw [actualLookup, shadowLookup]
    rfl

theorem HeaderAxiomAgreement.refl (env : Kernel.Environment) : HeaderAxiomAgreement env env :=
  fun _ => rfl

theorem HeaderAxiomAgreement.none_iff (agreement : HeaderAxiomAgreement actual shadow) (name : Name) :
    actual.find? name = none ↔ shadow.find? name = none := by
  have same := agreement name
  cases actualEntry : actual.find? name <;> cases shadowEntry : shadow.find? name <;> simp_all

theorem HeaderAxiomAgreement.values (agreement : HeaderAxiomAgreement actual shadow) (name : Name) :
    (actual.find? name).bind ConstantInfo.value? = (shadow.find? name).bind ConstantInfo.value? := by
  have same := agreement name
  cases actualEntry : actual.find? name <;> cases shadowEntry : shadow.find? name <;>
    simp_all [headerTypeValue]

private theorem headerViewLookup (env : Kernel.Environment) (info : ConstantInfo)
    (wellFormed : env.constants.WF) (fresh : env.constants.find? info.name = none) (name : Name) :
    (env.add info).find? name = if info.name == name then some info else env.find? name := by
  have nextWF := wellFormed.insert info.name info fresh
  rw [Kernel.Environment.find?, Kernel.Environment.add_constants, nextWF.find?'_eq_find?,
    wellFormed.find?_insert, ← wellFormed.find?'_eq_find?]
  rfl

theorem HeaderAxiomAgreement.addHeader (agreement : HeaderAxiomAgreement actual shadow)
    (info : InductiveVal) (actualWF : actual.constants.WF) (shadowWF : shadow.constants.WF)
    (actualFresh : actual.constants.find? info.name = none)
    (shadowFresh : shadow.constants.find? info.name = none) :
    HeaderAxiomAgreement (actual.add (.inductInfo info)) (shadow.add (headerAxiomInfo info)) := by
  intro name
  rw [headerViewLookup actual (.inductInfo info) actualWF actualFresh,
    headerViewLookup shadow (headerAxiomInfo info) shadowWF shadowFresh]
  change (if info.name == name then some (ConstantInfo.inductInfo info) else actual.find? name).map _ =
    (if info.name == name then some (headerAxiomInfo info) else shadow.find? name).map _
  split
  · exact congrArg some (headerAxiomInfo.typeValue info).symm
  · exact agreement name

def headerAxiomView (env : Kernel.Environment) (infos : List InductiveVal) : Kernel.Environment :=
  infos.foldl (fun current info => current.add (headerAxiomInfo info)) env

theorem HeaderAxiomLookupAgreement.addHeader
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (info : InductiveVal)
    (member : changed info.name) (actualWF : actual.constants.WF) (shadowWF : shadow.constants.WF)
    (actualFresh : actual.constants.find? info.name = none)
    (shadowFresh : shadow.constants.find? info.name = none) :
    HeaderAxiomLookupAgreement changed (actual.add (.inductInfo info)) (shadow.add (headerAxiomInfo info)) := by
  intro name
  rw [headerViewLookup actual (.inductInfo info) actualWF actualFresh,
    headerViewLookup shadow (headerAxiomInfo info) shadowWF shadowFresh]
  by_cases same : info.name = name
  · simp only [ConstantInfo.name, ConstantInfo.toConstantVal, headerAxiomInfo,
      same, beq_self_eq_true, if_true]
    exact .inr ⟨same ▸ member, info, rfl, rfl⟩
  · simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, headerAxiomInfo,
      beq_iff_eq, same, if_false] using agreement name

private theorem registerHeaderAxiomView (infos : List InductiveVal) (allowPrimitive : Bool)
    (actual shadow : Kernel.Environment) (semantic : VEnv) (headers : List VInductiveType)
    (changed : Name → Prop)
    (actualWF : actual.constants.WF) (history : TrEnv safety shadow semantic)
    (agreement : HeaderAxiomAgreement actual shadow)
    (lookups : HeaderAxiomLookupAgreement changed actual shadow)
    (members : ∀ info ∈ infos, changed info.name)
    (models : List.Forall₂ (fun (info : InductiveVal) (header : VInductiveType) => info.name = header.name ∧
      TrConstant safety semantic (.inductInfo info) header.toVConstant) infos headers)
    (typesWF : ∀ header ∈ headers, header.toVConstant.WF semantic) :
    (infos.foldlM (fun (current : Kernel.Environment) (info : InductiveVal) => do
      Kernel.Environment.checkName current info.name allowPrimitive
      pure (current.add (.inductInfo info))) actual).WF fun result =>
      ∃ final, semantic.addInductHeaders headers = some final ∧
        TrEnv safety (headerAxiomView shadow infos) final ∧
        HeaderAxiomAgreement result (headerAxiomView shadow infos) ∧
        HeaderAxiomLookupAgreement changed result (headerAxiomView shadow infos) ∧
        NativeValueFrame shadow (headerAxiomView shadow infos) ∧
        (allowPrimitive = false → NativePrimitiveFrame shadow (headerAxiomView shadow infos)) ∧
        FreshRegistrationTrace HeaderRegistrationRecord actual result ∧
        FreshRegistrationTrace HeaderAxiomRegistrationRecord shadow (headerAxiomView shadow infos) := by
  induction infos generalizing actual shadow semantic headers with
  | nil =>
    cases models
    exact .pure ⟨semantic, rfl, history, agreement, lookups, .refl history.map_wf,
      (fun _ => .refl history.map_wf), .refl actual, .refl shadow⟩
  | cons info infos induction =>
    cases models with
    | cons model remaining =>
      rename_i header headers
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (checkName.WF actualWF info.name allowPrimitive).bind fun _ ⟨absent, primitive⟩ => ?_
      have fresh : actual.constants.find? info.name = none := by
        simpa only [Kernel.Environment.find?, actualWF.find?'_eq_find?] using absent
      have shadowAbsent := (agreement.none_iff info.name).mp absent
      have shadowFresh : shadow.constants.find? info.name = none := by
        simpa only [Kernel.Environment.find?, history.map_wf.find?'_eq_find?] using shadowAbsent
      have semanticFresh : semantic.constants header.name = none := by
        apply Option.not_isSome_iff_eq_none.mp
        rw [Option.isSome_iff_exists]
        rintro ⟨constant, present⟩
        obtain ⟨native, present, _⟩ := history.find?_iff.mpr ⟨constant, present⟩
        rw [← model.1, shadowAbsent] at present
        contradiction
      obtain ⟨next, step⟩ : ∃ next, semantic.addConst info.name header.toVConstant = some next := by
        simp [VEnv.addConst, model.1, semanticFresh]
      have nextHistory : TrEnv safety (shadow.add (headerAxiomInfo info)) next := by
        exact TrEnv'.axiom (show TrConstant safety semantic (headerAxiomInfo info) header.toVConstant
          from model.2) shadowFresh (typesWF header (by simp)) step history
      have shadowFrame := NativeValueFrame.addConst (ci := headerAxiomInfo info)
        history.map_wf shadowFresh rfl
      have nextAgreement := agreement.addHeader info actualWF history.map_wf fresh shadowFresh
      have nextLookups := lookups.addHeader info (members info (by simp))
        actualWF history.map_wf fresh shadowFresh
      refine (induction (actual.add (.inductInfo info)) (shadow.add (headerAxiomInfo info)) next headers
        (actualWF.insert _ _ fresh) nextHistory nextAgreement nextLookups
        (fun info member => members info (by simp [member]))
        (Lean4Lean.List.Forall₂.imp (fun _ _ model => ⟨model.1, model.2.mono (VEnv.addConst_le step)⟩) remaining)
        (fun header member => (typesWF header (by simp [member])).mono (VEnv.addConst_le step))).mono ?_
      rintro result ⟨final, registered, finalHistory, finalAgreement, finalLookups, finalFrame,
        finalPrimitives, actualTrace, shadowTrace⟩
      refine ⟨final, ?_, finalHistory, finalAgreement, finalLookups, shadowFrame.trans finalFrame, ?_, ?_, ?_⟩
      · simpa only [VEnv.addInductHeaders, ← model.1, step, bind, Option.bind] using registered
      · intro disabled
        exact (NativePrimitiveFrame.addConst (ci := headerAxiomInfo info) history.map_wf
          shadowFresh (by
            change Kernel.Environment.primitives.contains info.name = false
            cases enabled : Kernel.Environment.primitives.contains info.name with
            | false => rfl
            | true =>
              have allowed := primitive enabled
              rw [disabled] at allowed
              cases allowed)).trans (finalPrimitives disabled)
      · exact (FreshRegistrationTrace.step (.refl actual) (.inductInfo info) ⟨info, rfl⟩ fresh).trans actualTrace
      · exact (FreshRegistrationTrace.step (.refl shadow) (headerAxiomInfo info) ⟨info, rfl⟩ shadowFresh).trans shadowTrace

theorem AddInductive.declareInductiveTypes.strongHeaderAxiomRegistrationView
    (reader : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (history : TrEnv safety reader.env semantic)
    (safetyBound : safety ≤ if isUnsafe then .unsafe else .safe)
    (sizes : stats.nindices.size = types.size)
    (models : List.Forall₂ (TrInductiveHeader semantic reader.lparams) types.toList headers)
    (typesWF : ∀ header ∈ headers, header.toVConstant.WF semantic) :
    (AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe reader).WF fun actual =>
      ∃ shadow final, semantic.addInductHeaders headers = some final ∧ TrEnv safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) ∧
        FreshRegistrationTrace HeaderRegistrationRecord reader.env actual ∧
        FreshRegistrationTrace HeaderAxiomRegistrationRecord reader.env shadow := by
  unfold AddInductive.declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  refine (registerHeaderAxiomView _ reader.allowPrimitive reader.env reader.env semantic headers
    (fun name => ∃ type ∈ types, type.name = name)
    history.map_wf history (.refl _) (.refl _ _) ?_ ?_ typesWF).mono ?_
  · intro info member
    rw [Array.mem_toList_iff] at member
    obtain ⟨index, bound, rfl⟩ := Array.mem_iff_getElem.mp member
    have typeBound : index < types.size := by
      simp only [Array.size_zipWith] at bound
      omega
    refine ⟨types[index], Array.getElem_mem typeBound, ?_⟩
    simp only [Array.getElem_zipWith]
  · rw [Array.toList_zipWith]
    refine Lean4Lean.zipInductiveHeaders _ ?_ (by simpa using sizes) models
    intro type index header model
    refine ⟨model.1, ?_, model.2.1, model.2.2⟩
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial] using safetyBound
  · rintro actual ⟨final, registered, finalHistory, agreement, lookups, frame, primitives,
      actualTrace, shadowTrace⟩
    exact ⟨_, final, registered, finalHistory, agreement, frame, lookups, primitives, actualTrace, shadowTrace⟩

theorem AddInductive.declareInductiveTypes.strongHeaderAxiomLookupView
    (reader : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (history : TrEnv safety reader.env semantic)
    (safetyBound : safety ≤ if isUnsafe then .unsafe else .safe)
    (sizes : stats.nindices.size = types.size)
    (models : List.Forall₂ (TrInductiveHeader semantic reader.lparams) types.toList headers)
    (typesWF : ∀ header ∈ headers, header.toVConstant.WF semantic) :
    (AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe reader).WF fun actual =>
      ∃ shadow final, semantic.addInductHeaders headers = some final ∧ TrEnv safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
  refine (AddInductive.declareInductiveTypes.strongHeaderAxiomRegistrationView reader stats nparams types
    numNested isUnsafe history safetyBound sizes models typesWF).mono ?_
  rintro actual ⟨shadow, final, registered, finalHistory, agreement, frame, lookups, primitives, _, _⟩
  exact ⟨shadow, final, registered, finalHistory, agreement, frame, lookups, primitives⟩

theorem AddInductive.declareInductiveTypes.strongHeaderAxiomView
    (reader : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (history : TrEnv safety reader.env semantic)
    (safetyBound : safety ≤ if isUnsafe then .unsafe else .safe)
    (sizes : stats.nindices.size = types.size)
    (models : List.Forall₂ (TrInductiveHeader semantic reader.lparams) types.toList headers)
    (typesWF : ∀ header ∈ headers, header.toVConstant.WF semantic) :
    (AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe reader).WF fun actual =>
      ∃ shadow final, semantic.addInductHeaders headers = some final ∧ TrEnv safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
  refine (AddInductive.declareInductiveTypes.strongHeaderAxiomLookupView reader stats nparams types
    numNested isUnsafe history safetyBound sizes models typesWF).mono ?_
  rintro actual ⟨shadow, final, registered, finalHistory, agreement, frame, _, primitives⟩
  exact ⟨shadow, final, registered, finalHistory, agreement, frame, primitives⟩

theorem TypeChecker.MLCtx.WF.monoEnv {model : TypeChecker.MLCtx}
    (typed : model.WF semantic universes) (increase : semantic ≤ final) : model.WF final universes := by
  induction model with
  | nil => trivial
  | vlam identifier name type semanticType binder model induction =>
    obtain ⟨base, fresh, translated, isType⟩ := typed
    exact ⟨induction base, fresh, translated.mono increase, isType.mono increase⟩
  | vlet identifier name type value semanticType semanticValue model induction =>
    obtain ⟨base, fresh, typeTranslated, valueTranslated, hasType⟩ := typed
    exact ⟨induction base, fresh, typeTranslated.mono increase, valueTranslated.mono increase,
      hasType.mono increase⟩

def TypeChecker.VContext.inHeaderAxiomView (checker : TypeChecker.VContext)
    (shadow : Kernel.Environment) (semantic : VEnv) (increase : checker.venv ≤ semantic)
    (history : TrEnv checker.safety shadow semantic) (primitives : NativePrimitiveFrame checker.env shadow) :
    TypeChecker.VContext := {
  checker with
  env := shadow
  venv := semantic
  trenv := history
  hasPrimitives := checker.trenv.checkerEnv.hasPrimitives_of_frame history.checkerEnv increase
    checker.hasPrimitives primitives
  safePrimitives := by
    intro name info found primitive
    exact checker.safePrimitives ((primitives.find? checker.trenv.map_wf primitive).symm.trans found) primitive
  mlctx_wf := checker.mlctx_wf.monoEnv increase }

theorem TypeChecker.VContext.inHeaderAxiomView.context (checker : TypeChecker.VContext)
    (shadow : Kernel.Environment) (semantic : VEnv) (increase : checker.venv ≤ semantic)
    (history : TrEnv checker.safety shadow semantic) (primitives : NativePrimitiveFrame checker.env shadow) :
    (checker.inHeaderAxiomView shadow semantic increase history primitives).toContext =
      { checker.toContext with env := shadow } := rfl

theorem TypeChecker.VState.WF.headerAxiomReset (checker : TypeChecker.VContext)
    (shadow : Kernel.Environment) (semantic : VEnv) (increase : checker.venv ≤ semantic)
    (history : TrEnv checker.safety shadow semantic) (primitives : NativePrimitiveFrame checker.env shadow)
    (initialWF : ({} : TypeChecker.VState).WF checker) :
    ({} : TypeChecker.VState).WF (checker.inHeaderAxiomView shadow semantic increase history primitives) :=
  TypeChecker.VState.WF.reset _ initialWF.ngen_wf

theorem AddInductive.checkInductiveTypes.strongHeaderAxiomView
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : AddInductive.Context)
    (aligned : AddInductive.HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (safetyBound : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (AddInductive.checkInductiveTypes nparams types
      (fun stats => AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe) reader).WF
      fun actual => ∃ headers shadow final,
        List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types.toList headers ∧
        (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
        checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
  intro actual accepted
  obtain ⟨headers, _, models, typesWF, _, _⟩ := AddInductive.checkInductiveTypes.headersChecker
    nparams types numNested isUnsafe checker reader aligned empty different constants definitions
    safetyBound actual accepted
  have nativeEnv : checker.env = reader.env := congrArg TypeChecker.Context.env aligned
  have history : TrEnv checker.safety reader.env checker.venv := nativeEnv ▸ checker.trenv
  have registered : (AddInductive.checkInductiveTypes nparams types
      (fun stats => AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe) reader).WF
      fun actual => ∃ shadow final,
        checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
    apply AddInductive.checkInductiveTypes.frameHeaderSizes
    intro stats current sizes frame
    simpa only [frame.env, frame.allowPrimitive] using
      AddInductive.declareInductiveTypes.strongHeaderAxiomView current stats nparams types numNested isUnsafe
        (by simpa only [frame.env] using history) safetyBound sizes.1
        (by simpa only [frame.lparams] using models) typesWF
  obtain ⟨shadow, final, added, finalHistory, agreement, values, primitives⟩ := registered actual accepted
  exact ⟨headers, shadow, final, models, typesWF, added, finalHistory, agreement, values, primitives⟩

theorem AddInductive.checkInductiveTypes.headerAxiomViewStage
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : AddInductive.InductiveStats → Kernel.Environment → AddInductive.M resultType)
    (checker : TypeChecker.VContext) (reader : AddInductive.Context)
    (aligned : AddInductive.HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (safetyBound : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (AddInductive.checkInductiveTypes nparams types (fun stats => do
      let actual ← AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe
      next stats actual) reader).WF fun _ => ∃ headers actual shadow final,
        List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types.toList headers ∧
        (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
        checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
  intro result accepted
  have typed := AddInductive.checkInductiveTypes.headersWF nparams types _
    checker reader aligned empty different constants definitions result accepted
  obtain ⟨headers, models, typesWF⟩ := Lean4Lean.AddInductive.typedHeaderList
    types.toList checker.venv reader.lparams (by
      intro type member
      obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      exact typed parent bound)
  have nativeEnv : checker.env = reader.env := congrArg TypeChecker.Context.env aligned
  have history : TrEnv checker.safety reader.env checker.venv := nativeEnv ▸ checker.trenv
  have staged : (AddInductive.checkInductiveTypes nparams types (fun stats => do
      let actual ← AddInductive.declareInductiveTypes stats nparams types numNested isUnsafe
      next stats actual) reader).WF fun _ => ∃ actual shadow final,
        checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
        HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
        (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
    apply AddInductive.checkInductiveTypes.frameHeaderSizes
    intro stats current sizes frame
    refine (AddInductive.declareInductiveTypes.strongHeaderAxiomView current stats nparams types numNested isUnsafe
      (by simpa only [frame.env] using history) safetyBound sizes.1
      (by simpa only [frame.lparams] using models) typesWF).bind ?_
    rintro actual ⟨shadow, final, added, finalHistory, agreement, values, primitives⟩
    intro _ _
    exact ⟨actual, shadow, final, added, finalHistory, agreement,
      by simpa only [frame.env] using values,
      by simpa only [frame.env, frame.allowPrimitive] using primitives⟩
  obtain ⟨actual, shadow, final, added, finalHistory, agreement, values, primitives⟩ := staged result accepted
  exact ⟨headers, actual, shadow, final, models, typesWF, added, finalHistory, agreement, values, primitives⟩

theorem AddInductive.run.headerAxiomViewStage
    (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : AddInductive.Context)
    (aligned : AddInductive.HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (ordinarySafety : checker.safety ≠ .partial) :
    (AddInductive.run nparams types numNested reader).WF fun _ => ∃ headers actual shadow final,
      List.Forall₂ (TrInductiveHeader checker.venv reader.lparams) types headers ∧
      (∀ header ∈ headers, header.toVConstant.WF checker.venv) ∧
      checker.venv.addInductHeaders headers = some final ∧ TrEnv checker.safety shadow final ∧
      HeaderAxiomAgreement actual shadow ∧ NativeValueFrame reader.env shadow ∧
      (reader.allowPrimitive = false → NativePrimitiveFrame reader.env shadow) := by
  have sameSafety : checker.safety = reader.safety := congrArg TypeChecker.Context.safety aligned
  have safetyBound : checker.safety ≤ if reader.safety != .safe then .unsafe else .safe := by
    rw [← sameSafety]
    cases mode : checker.safety with
    | safe => decide
    | «unsafe» => decide
    | «partial» => exact False.elim (ordinarySafety mode)
  unfold AddInductive.run
  apply Lean4Lean.AddInductive.readWF
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  simpa only [List.toList_toArray] using AddInductive.checkInductiveTypes.headerAxiomViewStage
    nparams types.toArray numNested (reader.safety != .safe) _ checker reader aligned empty
    different constants definitions safetyBound

end Lean4Lean
