import Lean4Lean.Verify.InductiveNativeRestorationBridge

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! A frontend scope can be consumed together with an independently constructed semantic
    registration witness.  The map equalities are explicit: the native scope supplies the
    source-side well-formedness, while `RegistrationEvidence` supplies the positive
    inductive history seen by the checker. -/
theorem SafeInductiveFrontendScope.toCheckerEnvInductive
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q := by
  have hconstantsWF : env.constants.WF := by
    exact scope.originalWF
  subst constants
  exact producer.toCheckerEnvInductive env result history rfl hresultConstants
    hconstantsWF hrecursors hvalues

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q := by
  have hresultConstants := restored.registrationConstants producer halign hconstants
  subst constants
  exact producer.toCheckerEnvInductive original result history rfl hresultConstants
    history.map_wf hrecursors hvalues

theorem NativeInductive.RestoredRecordEvidence.registrationHistory
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult := by
  refine ⟨restored.registrationConstants producer halign hconstants, ?_⟩
  exact producer.to_trEnvInductive history history.map_wf hrecursors

theorem NativeInductive.RestoredRecordEvidence.registrationAlignmentHistory
    {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (haligned : Aligned safety constants semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult := by
  have hresult := restored.registrationConstants producer halign hconstants
  have halignment := restored.registrationAlignment producer halign hconstants hresult haligned
  refine ⟨halignment.1, hresult, ?_⟩
  exact producer.to_trEnvInductive history history.map_wf hrecursors

theorem SafeInductiveRestorationMetadata.toRestoredRecordEvidence
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List NativeInductive.RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map NativeInductive.RegistrationEntry.toConstantInfo) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) := by
  obtain ⟨preprocessing, staged, hpre, hrun, _, _, _, _, hbranch, hinstalled⟩ := metadata.stages
  refine ⟨preprocessing, staged, hpre, hrun, ?_⟩
  intro hnested
  cases hbranch with
  | direct hnoaux => exact False.elim (hnested hnoaux)
  | nested _ htrace =>
    have hreceipt := hinstalled hnested (coverage preprocessing staged hpre hrun hnested)
    let registration : RestoredRegistrationEvidence preprocessing staged
        (types.map (·.name)) (mkAuxRecNameMap staged types).2 env
        (restoredEnvironmentRecords preprocessing staged types) result :=
      ⟨htrace, hreceipt⟩
    let restored := NativeInductive.RestoredRegistrationEvidence.toRestoredRecordEvidence
      registration (entries preprocessing staged) (records_eq preprocessing staged hpre hrun)
    refine ⟨⟨restored, ?_⟩⟩
    exact NativeInductive.RestoredRegistrationEvidence.toRestoredRecordEvidence_entries
      registration (entries preprocessing staged) (records_eq preprocessing staged hpre hrun)

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List NativeInductive.RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map NativeInductive.RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q) := by
  obtain ⟨preprocessing, staged, hpre, hrun, hrestored⟩ :=
    metadata.toRestoredRecordEvidence coverage entries records_eq
  refine ⟨preprocessing, staged, hpre, hrun, ?_⟩
  intro hnested
  obtain ⟨⟨restored, hentries⟩⟩ := hrestored hnested
  have halign : restored.entries = producer.orderedEntries := by
    calc
      restored.entries = entries preprocessing staged := hentries
      _ = producer.orderedEntries := entry_eq preprocessing staged hpre hrun hnested
  exact restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues

end Lean4Lean
