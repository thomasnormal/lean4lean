import Lean4Lean.Verify.InductiveNativeRestorationBridge
import Lean4Lean.Verify.InductiveRestorationRules

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open AddInductive
open AddInductive.declareConstructors

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

theorem NativeInductive.RestoredRecordEvidence.registrationAlignmentHistory_of_sourceTypehood
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact restored.registrationAlignmentHistory producer halign hconstants history
    history.aligned hrecursors

theorem NativeInductive.RestoredRecordEvidence.registrationRuleResults
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ entry ∈ restored.entries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule := by
  intro entry hmem
  have hproducer : entry ∈ producer.orderedEntries := by
    rw [← halign]
    exact hmem
  exact producer.orderedRuleResultsOf ruleResults entry hproducer

theorem NativeInductive.RestoredRecordEvidence.registrationModelShapes
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.ModelShape := by
  intro entry hmem
  apply producer.orderedModelShape
  rw [← halign]
  exact hmem

theorem NativeInductive.RestoredRecordEvidence.registrationMetadata
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.Metadata decl producer.constructors := by
  intro entry hmem
  apply producer.orderedMetadata
  rw [← halign]
  exact hmem

theorem NativeInductive.RestoredRecordEvidence.registrationRecursorRuleTranslation
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {entry : NativeInductive.RecursorEntry} (hentry : .recursor entry ∈ restored.entries)
    {rule : RecursorRule} (hrule : rule ∈ entry.info.rules) :
    ∃ semantic, TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic := by
  have hproducer : (.recursor entry : NativeInductive.RegistrationEntry) ∈ producer.orderedEntries := by
    rw [← halign]
    exact hentry
  have hmem : entry ∈ producer.recursors := by
    simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append,
      List.mem_map] at hproducer
    rcases hproducer with hphase | hrecursors
    · simp at hphase
    · obtain ⟨entry', hentry', heq⟩ := hrecursors
      cases heq
      exact hentry'
  exact producer.recursorRuleTranslation entry hmem rule hrule

theorem NativeInductive.RestoredRecordEvidence.sourceRecursorRuleTranslation
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = (mkRecName types[index].name))
    (hrecursorName : ∀ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = entry.info.name) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
      result.find? recursor.name = some (.recInfo recursor) ∧
      entry.info.name = mkRecName types[index].name ∧
      recursor.rules.length = types[index].ctors.length ∧
      recursor.rules[ctorIndex]? = some rule ∧
      staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧
      rule.nfields = info.numFields ∧
      rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic := by
  obtain ⟨recursor, rule, info, hresult, hlength, hrule, hctorInfo, hmetadata, hfields,
      hnumFields, hfieldCount, htotal⟩ := hlookups.finalRule index hindex ctorIndex hctor
  have hrecursorName := hrecursorName recursor hresult
  have hinstalled := restored.entryInstalled hentry
  have hinstalled' : result.find? recursor.name = some (.recInfo entry.info) := by
    rw [hrecursorName]
    change result.find? entry.info.name = some (.recInfo entry.info)
    exact hinstalled
  have hrecursor : recursor = entry.info := by
    have heq : (.recInfo recursor : ConstantInfo) = .recInfo entry.info :=
      Option.some.inj (hresult.symm.trans hinstalled')
    cases heq
    rfl
  have hruleMem : rule ∈ entry.info.rules := by
    rw [← hrecursor]
    exact List.mem_of_getElem? hrule
  obtain ⟨semantic, hsemantic⟩ :=
    restored.registrationRecursorRuleTranslation producer halign hentry hruleMem
  exact ⟨recursor, rule, info, semantic, hresult, hname, hlength, hrule, hctorInfo, hmetadata,
    hfields, hnumFields, hfieldCount, htotal, hsemantic⟩

theorem NativeInductive.RestoredRecordEvidence.sourceRecursorRuleResults
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = (mkRecName types[index].name))
    (hrecursorName : ∀ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = entry.info.name)
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
      result.find? recursor.name = some (.recInfo recursor) ∧
      entry.info.name = mkRecName types[index].name ∧
      recursor.rules.length = types[index].ctors.length ∧
      recursor.rules[ctorIndex]? = some rule ∧
      staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧
      rule.nfields = info.numFields ∧
      rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      Result entry rule := by
  obtain ⟨recursor, rule, info, semantic, hresult, hname', hlength, hrule, hctorInfo,
      hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic⟩ :=
    restored.sourceRecursorRuleTranslation producer halign hlookups index hindex ctorIndex hctor
      hentry hname hrecursorName
  have hrecursorName' := hrecursorName recursor hresult
  have hinstalled := restored.entryInstalled hentry
  have hinstalled' : result.find? recursor.name = some (.recInfo entry.info) := by
    rw [hrecursorName']
    change result.find? entry.info.name = some (.recInfo entry.info)
    exact hinstalled
  have hrecursor : recursor = entry.info := by
    have heq : (.recInfo recursor : ConstantInfo) = .recInfo entry.info :=
      Option.some.inj (hresult.symm.trans hinstalled')
    cases heq
    rfl
  have hruleMem : rule ∈ entry.info.rules := by
    rw [← hrecursor]
    exact List.mem_of_getElem? hrule
  have hproducer : entry ∈ producer.recursors := by
    have hordered : (.recursor entry : NativeInductive.RegistrationEntry) ∈ producer.orderedEntries := by
      rw [← halign]
      exact hentry
    simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append,
      List.mem_map] at hordered
    rcases hordered with hphase | hrecursors
    · simp at hphase
    · obtain ⟨entry', hentry', heq⟩ := hrecursors
      cases heq
      exact hentry'
  exact ⟨recursor, rule, info, semantic, hresult, hname', hlength, hrule, hctorInfo,
    hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic,
    ruleResult entry hproducer rule hruleMem⟩

theorem NativeInductive.RestoredRecordEvidence.sourceRecursorRules
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : NativeInductive.RecursorEntry,
        (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
      (hctor : ctorIndex < types[index].ctors.length),
      ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
        (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
        result.find? recursor.name = some (.recInfo recursor) ∧
        entry.info.name = mkRecName types[index].name ∧
        recursor.rules.length = types[index].ctors.length ∧
        recursor.rules[ctorIndex]? = some rule ∧
        staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
        SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
        SourceConstructorFields nparams types[index] ctorIndex info ∧
        rule.nfields = info.numFields ∧
        rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
        nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
        TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
        Result entry rule := by
  intro index hindex ctorIndex hctor
  obtain ⟨entry, hentry, hname'⟩ := hentry index hindex
  obtain ⟨recursor, hresult, hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields,
      hfieldCount, htotal⟩ := hlookups.finalRule index hindex ctorIndex hctor
  obtain ⟨recursor, rule, info, semantic, hresult, hentryName, hlength, hrule, hctorInfo,
      hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic, hresultRule⟩ :=
    restored.sourceRecursorRuleResults producer halign hlookups index hindex ctorIndex hctor
      hentry hname' (fun recursor hlookup =>
      (hrecursor index hindex recursor hlookup).trans hname'.symm) ruleResult
  exact ⟨entry, recursor, rule, info, semantic, hresult, hentryName, hlength, hrule, hctorInfo,
    hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic, hresultRule⟩

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues

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

theorem SafeInductiveRestorationMetadata.sourceRecursorRulesAndRestoredRecordEvidence
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
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) := by
  obtain ⟨sourcePreprocessing, sourceStaged, hpreSource, hrunSource, hprefix, hlookups⟩ :=
    metadata.sourceRecursorRules
  obtain ⟨restoredPreprocessing, restoredStaged, hpreRestored, hrunRestored, hrestored⟩ :=
    metadata.toRestoredRecordEvidence coverage entries records_eq
  have hpre : sourcePreprocessing = restoredPreprocessing :=
    Except.ok.inj (hpreSource.symm.trans hpreRestored)
  subst restoredPreprocessing
  have hrun : sourceStaged = restoredStaged :=
    Except.ok.inj (hrunSource.symm.trans hrunRestored)
  subst restoredStaged
  exact ⟨sourcePreprocessing, sourceStaged, hpreSource, hrunSource, hprefix, hlookups,
    hrestored⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndRestoredRecordEvidence
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
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context)
      (constructors : Kernel.Environment) (elimLevel : Level) (infos : Array RecInfo)
      (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) := by
  obtain ⟨sourcePreprocessing, sourceStaged, stats, root, constructors, elimLevel, infos, source,
      hpreSource, hrunSource, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hbranch, hlookups⟩ := metadata.sourceRecursorRuleStages
  obtain ⟨restoredPreprocessing, restoredStaged, hpreRestored, hrunRestored, hrestored⟩ :=
    metadata.toRestoredRecordEvidence coverage entries records_eq
  have hpre : sourcePreprocessing = restoredPreprocessing :=
    Except.ok.inj (hpreSource.symm.trans hpreRestored)
  subst restoredPreprocessing
  have hrun : sourceStaged = restoredStaged :=
    Except.ok.inj (hrunSource.symm.trans hrunRestored)
  subst restoredStaged
  exact ⟨sourcePreprocessing, sourceStaged, stats, root, constructors, elimLevel, infos, source,
    hpreSource, hrunSource, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, hrestored⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleResultsAndRestoredRecordEvidence
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
    {decl : VInductDecl}
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : NativeInductive.RecursorEntry,
          (.recursor entry : NativeInductive.RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) ∧
      (preprocessing.aux2nested.size ≠ 0 →
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr),
            result.find? recursor.name = some (.recInfo recursor) ∧
            entry.info.name = mkRecName types[index].name ∧
            recursor.rules.length = types[index].ctors.length ∧
            recursor.rules[ctorIndex]? = some rule ∧
            staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
            SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
            SourceConstructorFields nparams types[index] ctorIndex info ∧
            rule.nfields = info.numFields ∧
            rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
            nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type ∧
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            Result entry rule) := by
  obtain ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩ :=
    metadata.sourceRecursorRules
  obtain ⟨restoredPreprocessing, restoredStaged, hpreRestored, hrunRestored, hrestored⟩ :=
    metadata.toRestoredRecordEvidence coverage entries records_eq
  have hpre' : preprocessing = restoredPreprocessing :=
    Except.ok.inj (hpre.symm.trans hpreRestored)
  subst restoredPreprocessing
  have hrun' : staged = restoredStaged :=
    Except.ok.inj (hrun.symm.trans hrunRestored)
  subst restoredStaged
  refine ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups, ?_, ?_⟩
  · intro hnested
    exact hrestored hnested
  · intro hnested
    obtain ⟨⟨restored, hentries⟩⟩ := hrestored hnested
    have halign : restored.entries = producer.orderedEntries := by
      calc
        restored.entries = entries preprocessing staged := hentries
        _ = producer.orderedEntries := entry_eq preprocessing staged hpre hrun hnested
    have hentry' : ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : NativeInductive.RecursorEntry,
          (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries ∧
          entry.info.name = mkRecName types[index].name := by
      intro index hindex
      obtain ⟨entry, hmem, hname⟩ := hentry preprocessing staged hpre hrun hnested index hindex
      exact ⟨entry, hentries ▸ hmem, hname⟩
    exact restored.sourceRecursorRules producer halign hlookups hrecursor hentry' ruleResult

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

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_of_sourceTypehood
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
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
  exact restored.toCheckerEnvInductive_of_sourceTypehood producer halign hconstants history
    hsource hvalues

end Lean4Lean
