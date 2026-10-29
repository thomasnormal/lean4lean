import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Verify.InductiveNativeAlignment
import Lean4Lean.Verify.InductiveNativeTrace
import Lean4Lean.Verify.InductiveRestorationMetadata
import Lean4Lean.Verify.InductiveNativeRestorationBridge
import Lean4Lean.Verify.InductiveFrontendCheckerBridge
import Lean4Lean.Verify.InductiveReductionConsumer
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.InductiveNativeBridge

open Lean Lean4Lean Lean4Lean.NativeInductive
open Lean4Lean.AddInductive.declareConstructors

#check AddInduct.ofEvidence
#check Lean.Expr.getAppNumArgs_eq_getAppArgs_size
#check AddInductive.dispatcherConstructorFieldBoundOfNativeEtaStructEntryReceipt_auto
#check AddInduct.map_wf
#check AddInduct.lookupReceipt
#check NativeInductive.RegistrationEvidence.to_trEnvInductive_and_aligned
#check NativeInductive.RegistrationEvidence.to_trEnvInductive_and_aligned_of_sourceTypehood
#check NativeInductive.RegistrationEvidence.toCheckerEnvInductive_and_aligned
#check VEnvs.InductiveWF
#check VEnvs.WF.toInductiveWF
#check VEnvs.InductiveWF.addInductWithRecursors
#check VEnvs.InductiveWF.addInductWithRecursors_and_aligned
#check VEnvs.InductiveWF.addRegistrationEvidence
#check VEnvs.InductiveWF.addRegistrationEvidence_of_sourceTypehood
#check VEnvs.InductiveWF.addRegistrationEvidence_of_sourceTypehood_and_aligned
#check VEnvs.InductiveWF.addRegistrationEvidence_of_sourceTypehood_and_aligned_and_checker
#check VEnvs.InductiveWF.map_wf
#check VEnvs.InductiveWF.venv_wf
#check VEnvs.InductiveWF.toCheckerEnvInductive
#check VEnvs.InductiveWF.toCheckerEnvInductive_and_wf
#check addDecl.safeInductiveFrontendInductiveWF
#check addDecl.safeInductiveFrontendInductiveWF_of_sourceTypehood
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleResultSemanticsAndIotaTargetReductionExact
#check AddInductive.GeneratedRecursorRuleIotaTargetOrdinaryExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetOrdinaryExactOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetOrdinaryExactOf
#check CheckerEnvInductive.map_wf
#check CheckerEnvInductive.venv_wf
#check AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorVDeclWF
#check AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerVDeclWF
#check AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerWithModelAndVDeclWF

example {env : Kernel.Environment} {ves : VEnvs} {Q : Bool}
    (model : VEnvs.InductiveWF env ves Q) : env.constants.WF :=
  model.map_wf

example {env : Kernel.Environment} {ves : VEnvs} {Q : Bool}
    (model : VEnvs.InductiveWF env ves Q)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType}
    {check : Bool} {fuel : FuelConfig}
    (frontend : ∀ (allowPrimitive : Bool) (result : Kernel.Environment),
      SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result →
      ∃ resultVes : VEnvs,
        VEnvs.InductiveWF result resultVes Q ∧
          ∀ safety, ves.venv safety ≤ resultVes.venv safety) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ resultVes : VEnvs,
        VEnvs.InductiveWF result resultVes Q ∧
          ∀ safety, ves.venv safety ≤ resultVes.venv safety :=
  addDecl.safeInductiveFrontendInductiveWF model lparams nparams types check fuel frontend

example {env : Kernel.Environment} {ves : VEnvs} {Q : Bool}
    (model : VEnvs.InductiveWF env ves Q)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType}
    {check : Bool} {fuel : FuelConfig} {decl : VInductDecl}
    (registration : ∀ (allowPrimitive : Bool) (result : Kernel.Environment),
      SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result →
      ∃ (resultVes : VEnvs)
        (evidence : ∀ safety,
          NativeInductive.RegistrationEvidence env.constants (ves.venv safety) decl
            result.constants (resultVes.venv safety)),
        (∀ safety entry, entry ∈ (evidence safety).recursors →
          ∃ semantic,
            TrExprS (evidence safety).constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
            (evidence safety).constructorEnv.IsType entry.info.levelParams.length [] semantic) ∧
        (∀ {safety}, (resultVes.venv safety).HasPrimitives) ∧
        (∀ {n ci}, result.find? n = some ci →
          Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []) ∧
        (∀ {safety safety'}, safety ≤ safety' →
          resultVes.venv safety' ≤ resultVes.venv safety)) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ resultVes : VEnvs,
        VEnvs.InductiveWF result resultVes Q ∧
          ∀ safety, ves.venv safety ≤ resultVes.venv safety :=
  addDecl.safeInductiveFrontendInductiveWF_of_sourceTypehood model lparams nparams types check fuel decl
    registration

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∃ (allowPrimitive : Bool), Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
                AddInductive.GeneratedRecursorRuleIotaTargetResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  exact addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaTargetResults_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResults

example {env : Kernel.Environment} {ves : VEnvs}
    (model : VEnvs.WF env ves) : VEnvs.InductiveWF env ves env.quotInit :=
  model.toInductiveWF

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {decl : VInductDecl}
    {inductiveConstants : DefinitionSafety → ConstMap}
    {inductiveEnvs : DefinitionSafety → VEnv}
    {recursors : DefinitionSafety → List RecursorVal}
    {models : DefinitionSafety → List VConstVal}
    (model : VEnvs.InductiveWF env ves Q)
    (registration : ∀ safety,
      AddInductWithRecursorsEvidence safety env.constants (ves.venv safety) decl
        (inductiveConstants safety) (inductiveEnvs safety) (recursors safety)
        (models safety) result.constants (resultVes.venv safety))
    (declarationWF : ∀ safety,
      VDecl.WF (ves.venv safety) (.induct decl) (inductiveEnvs safety))
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety) :
    VEnvs.InductiveWF result resultVes Q :=
  model.addInductWithRecursors decl inductiveConstants inductiveEnvs recursors models
    registration declarationWF hasPrimitives safePrimitives mono

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {decl : VInductDecl}
    {inductiveConstants : DefinitionSafety → ConstMap}
    {inductiveEnvs : DefinitionSafety → VEnv}
    {recursors : DefinitionSafety → List RecursorVal}
    {models : DefinitionSafety → List VConstVal}
    (model : VEnvs.InductiveWF env ves Q)
    (registration : ∀ safety,
      AddInductWithRecursorsEvidence safety env.constants (ves.venv safety) decl
        (inductiveConstants safety) (inductiveEnvs safety) (recursors safety)
        (models safety) result.constants (resultVes.venv safety))
    (declarationWF : ∀ safety,
      VDecl.WF (ves.venv safety) (.induct decl) (inductiveEnvs safety))
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety) :
    VEnvs.InductiveWF result resultVes Q ∧
      ∀ {safety}, Aligned safety result.constants (resultVes.venv safety) :=
  model.addInductWithRecursors_and_aligned decl inductiveConstants inductiveEnvs recursors models
    registration declarationWF hasPrimitives safePrimitives mono

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {decl : VInductDecl}
    (model : VEnvs.InductiveWF env ves Q)
    (evidence : ∀ safety,
      NativeInductive.RegistrationEvidence env.constants (ves.venv safety) decl
        result.constants (resultVes.venv safety))
    (hrecursors : ∀ safety entry, entry ∈ (evidence safety).recursors →
      entry.model.toVConstant.WF (evidence safety).constructorEnv)
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety) :
    VEnvs.InductiveWF result resultVes Q :=
  model.addRegistrationEvidence decl evidence hrecursors hasPrimitives safePrimitives mono

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {decl : VInductDecl}
    (model : VEnvs.InductiveWF env ves Q)
    (evidence : ∀ safety,
      NativeInductive.RegistrationEvidence env.constants (ves.venv safety) decl
        result.constants (resultVes.venv safety))
    (hsource : ∀ safety entry, entry ∈ (evidence safety).recursors → ∃ semantic,
      TrExprS (evidence safety).constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      (evidence safety).constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety) :
    VEnvs.InductiveWF result resultVes Q :=
  model.addRegistrationEvidence_of_sourceTypehood decl evidence hsource
    hasPrimitives safePrimitives mono

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {decl : VInductDecl}
    (model : VEnvs.InductiveWF env ves Q)
    (evidence : ∀ safety,
      NativeInductive.RegistrationEvidence env.constants (ves.venv safety) decl
        result.constants (resultVes.venv safety))
    (haligned : ∀ {safety}, Aligned safety env.constants (ves.venv safety))
    (hsource : ∀ safety entry, entry ∈ (evidence safety).recursors → ∃ semantic,
      TrExprS (evidence safety).constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      (evidence safety).constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety) :
    VEnvs.InductiveWF result resultVes Q ∧
      ∀ {safety}, Aligned safety result.constants (resultVes.venv safety) :=
  model.addRegistrationEvidence_of_sourceTypehood_and_aligned decl evidence haligned hsource
    hasPrimitives safePrimitives mono

example {env result : Kernel.Environment} {ves resultVes : VEnvs} {Q : Bool}
    {safety : DefinitionSafety} {decl : VInductDecl}
    (model : VEnvs.InductiveWF env ves Q)
    (evidence : ∀ safety,
      NativeInductive.RegistrationEvidence env.constants (ves.venv safety) decl
        result.constants (resultVes.venv safety))
    (haligned : ∀ {safety}, Aligned safety env.constants (ves.venv safety))
    (hsource : ∀ safety entry, entry ∈ (evidence safety).recursors → ∃ semantic,
      TrExprS (evidence safety).constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      (evidence safety).constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hasPrimitives : ∀ {safety}, (resultVes.venv safety).HasPrimitives)
    (safePrimitives : ∀ {n ci}, result.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (mono : ∀ {safety safety'}, safety ≤ safety' →
      resultVes.venv safety' ≤ resultVes.venv safety)
    (safeValues : ∀ {name ci value}, result.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr (resultVes.venv safety) ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    VEnvs.InductiveWF result resultVes Q ∧
      CheckerEnvInductive safety result (resultVes.venv safety) Q ∧
      Aligned safety result.constants (resultVes.venv safety) :=
  model.addRegistrationEvidence_of_sourceTypehood_and_aligned_and_checker decl evidence haligned
    hsource hasPrimitives safePrimitives mono safeValues

example {env : Kernel.Environment} {ves : VEnvs} {Q : Bool}
    (model : VEnvs.InductiveWF env ves Q) (safety : DefinitionSafety)
    (safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr (ves.venv safety) ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety env (ves.venv safety) Q :=
  model.toCheckerEnvInductive safety safeValues

example {env : Kernel.Environment} {ves : VEnvs} {Q : Bool}
    (model : VEnvs.InductiveWF env ves Q) (safety : DefinitionSafety)
    (safeValues : ∀ {name ci value}, env.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr (ves.venv safety) ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety env (ves.venv safety) Q ∧
      env.constants.WF ∧ (ves.venv safety).WF :=
  model.toCheckerEnvInductive_and_wf safety safeValues

example {env : Kernel.Environment} {venv : VEnv} {Q : Bool}
    (checker : CheckerEnvInductive safety env venv Q) :
    env.constants.WF ∧ venv.WF :=
  ⟨checker.map_wf, checker.venv_wf⟩

example {constants resultConstants : ConstMap}
    {env resultEnv : VEnv} {decl : VInductDecl}
    (evidence : AddInductEvidence .safe constants env decl resultConstants resultEnv) :
    AddInduct constants env decl resultConstants resultEnv :=
  .ofEvidence evidence

example {constants resultConstants : ConstMap}
    {env resultEnv : VEnv} {decl : VInductDecl}
    (evidence : AddInductEvidence .safe constants env decl resultConstants resultEnv) :
    env.addInduct decl = some resultEnv :=
  (AddInduct.ofEvidence evidence).to_addInduct

#check AddInductive.LocalRecursorRuleRhsScope.ruleResultSemanticsAndIota
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRec
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecWithType
#check AddInductive.GeneratedRecursorRuleIotaTargetReduction.toOrdinary
#check AddInductive.GeneratedConstructorRuleRhsResult.iotaTargetReductionOf
#check inductiveReduceRec.eq_some_of_normalizedApplication
#check inductiveReduceRec.eq_some_of_normalizedConstant
#check inductiveReduceRec.eq_some_of_kNormalizedConstant
#check inductiveReduceRec.eq_some_of_normalizedNatLiteral
#check inductiveReduceRec.eq_some_of_normalizedStringLiteral
#check inductiveReduceRec.eq_some_of_kNormalizedApplication
#check inductiveReduceRec.eq_some_of_kNormalizedNatLiteral
#check inductiveReduceRec.eq_some_of_kNormalizedStringLiteral
#check inductiveReduceRec.eq_some_of_normalizedStructure
#check inductiveReduceRec.eq_some_of_kNormalizedStructure
#check AddInductive.dispatcherConditionalShapeOfReplacementDecomposition
#check AddInductive.dispatcherArgumentSliceDecomposition
#check AddInductive.dispatcherConstructorSliceDecomposition
#check AddInductive.dispatcherConditionalShapeOfCanonicalDecomposition
#check AddInductive.dispatcherConditionalShapeOfCanonicalOutput
#check AddInductive.dispatcherFieldCountOfConstructorMetadata
#check AddInductive.dispatcherConstructorFieldBoundOfNativeEtaStructEntryReceipt
#check AddInductive.dispatcherConditionalShapeOfMetadataOutput
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceipt
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputWithRuleLookup
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNormalizedNatLiteral
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNormalizedConstant
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNormalizedApplication
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfKNormalizedApplication
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfKNormalizedConstant
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfKNormalizedStringLiteralExpansion
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfKNormalizedNatLiteral
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfStringLiteralExpansion
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralMetadataExact
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookup
#check AddInductive.dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookupAndAdaptation
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureMetadataExact
#check AddInductive.instantiateLevelParams_eq_self_of_noLevelParam
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_inductiveReduceRecExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_dispatcherConditionalExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationMetadataExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureExact
#check AddInductive.GeneratedRecursorRuleIotaTargetReductionExact
#check AddInductEvidence.lookupReceipt
#check AddInductWithRecursorsEvidence.recursorLookup
#check AddInductWithRecursorsEvidence.lookupReceipt
#check AddInductWithRecursorsEvidence.inductiveDeclWF
#check AddInductWithRecursorsEvidence.result_wf
#check AddInductWithRecursorsEvidence.to_trEnvInductive
#check AddInductWithRecursorsEvidence.toCheckerEnvInductive
#check AddInductWithRecursorsEvidence.toCheckerEnvInductive_and_wf
#check AddInductWithRecursorsEvidence.toCheckerEnvInductive_and_aligned
#check AddInductWithRecursorsEvidence.toCheckerEnvInductive_and_aligned_and_wf
#check AddInductWithRecursorsEvidence.toCheckerEnvInductive_and_registrationWF
#check RegistrationEvidence.toCheckerEnvInductive_and_wf
#check RegistrationEvidence.toCheckerEnvInductive_and_aligned
#check RegistrationEvidence.toCheckerEnvInductive_and_aligned_and_wf
#check RegistrationEvidence.toCheckerEnvInductive_and_registrationWF
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationWF
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationWF_of_sourceTypehood
#check SafeInductiveFrontendScope.toCheckerEnv
#check SafeInductiveFrontendScope.toCheckerEnv_of_sourceTypehood
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_aligned_and_registrationWF
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_aligned_and_registrationWF_of_sourceTypehood
#check SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_aligned_and_registrationWF_of_frontendSourceTypehood
#check SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_aligned_and_registrationWF
#check SafeInductiveRestorationMetadata.toCheckerEnv_of_frontendSourceTypehood
#check SafeInductiveRestorationMetadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
#check SafeInductiveRestorationMetadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
#check SafeInductiveRestorationMetadata.toCheckerEnv
#check NativeInductive.RestoredRecordEvidence.toCheckerEnv_of_sourceTypehood
#check NativeInductive.RestoredRecordEvidence.toCheckerEnv
#check addDecl.toCheckerEnv_of_restorationStages
#check addDecl.toCheckerEnv_of_checkedPrimitive_and_restorationStages
#check addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleIotaTargetResults_of_restorationStages
#check addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleIotaTargetResults_of_checkedPrimitive_and_restorationStages
#check addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages
#check addDecl.toCheckerEnv_of_frontendScope
#check addDecl.toCheckerEnv_of_checkedPrimitive_and_frontendScope
#check AddInductive.GeneratedConstructorRuleRhsResult.iotaTargetReductionOfExact
#check AddInductive.GeneratedRecursorRuleIotaTargetReductionExact.toOrdinary
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleIotaTargetReductionOf
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleIotaTargetReductionExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultsAndIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultsAndIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultsAndIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetReductionOf
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaTargetOrdinaryOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetOrdinaryOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetReductionsOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetReductionsOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetReductionOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetReductionOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaTargetReductionOf
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaTargetResultExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaTargetReductionsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetReductionExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaTargetResultsExact
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaTargetOrdinaryOf

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
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
    CheckerEnv .safe result semanticResult :=
  restored.toCheckerEnv producer halign hconstants history hrecursors hvalues
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetReduction
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetReduction
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetReductions
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetReductions
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetReduction
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetReductions
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetReductionExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetOrdinary
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetOrdinary
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetOrdinary
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetOrdinary
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetReduction
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetOrdinary
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetReduction
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetOrdinaryExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetReductionExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaTargetReductionExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaTargetReductionsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetResultsExact
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetResultExact
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetResult
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetResult
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultsAndIotaTargetResult
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetResult
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaTargetResults
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetResult
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleIotaTargetResults
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIota
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIota
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact
#check AddInductive.GeneratedRecursorRuleIotaTargetResultExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehoodExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleResultSemanticsIndexed
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleResultSemanticsFromIndexed
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleSemanticsFromIndexed
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleResultSemanticsAndIotaBaseAndTargetResults
#check AddInductive.LocalRecursorRuleRhsScope.completeRuleResultSemanticsAndIotaBaseAndTargetResultsSplit

#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIota
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResults
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultsAndIota
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RegistrationEvidence.recursorGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIota
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RegistrationEvidence.orderedGeneratedRuleResultsAndIotaBaseAndTargetResults
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_orderedEntryLookup
#check SafeInductiveFrontendScope.toCheckerEnvInductive_of_explicitHistory
#check SafeInductiveFrontendScope.toCheckerEnvInductive_of_explicitHistoryAndMapWF
#check NativeInductive.RegistrationEvidence.orderedEntryReceiptAndMap
#check NativeInductive.RegistrationEvidence.orderedEntryReceiptAndMapAndAlignment
#check NativeInductive.RegistrationEvidence.to_legacyAddInduct
#check NativeInductive.RegistrationEvidence.to_legacyAddInduct_and_aligned
#check SafeInductiveFrontendScope.toCheckerEnvInductive_of_explicitHistoryAndMapWF_and_orderedEntryReceiptAndMapAndAlignment
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_orderedEntryReceiptAndMapAndAlignment
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaTargetResults
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults
#check addDecl.checkedPrimitiveRegistrationRealizationAndOrderedEntryLookup
#check SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults_of_sourceTypehood
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaTargetResults_of_sourceTypehood
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults_of_checkedPrimitive
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaTargetResults_of_checkedPrimitive
#check SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults_of_sourceTypehood
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults_of_restorationStages
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaTargetResults_of_checkedPrimitive_and_restorationStages
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
#check addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnv_and_sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationGeneratedRuleResultsAndIota
#check NativeInductive.RestoredRecordEvidence.registrationGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationGeneratedRuleResultsAndIota
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerAndMapWFGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerAndMapWFGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check NativeInductive.RestoredRecordEvidence.registrationReceiptAndMap
#check NativeInductive.RestoredRecordEvidence.registrationReceiptAndMapAndOrderedEntryFindPrime
#check NativeInductive.RestoredRecordEvidence.registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment
#check NativeInductive.RestoredRecordEvidence.registrationReceiptAndMapAndAlignment
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationReceiptAndMapAndAlignment
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.registrationSemanticAndStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics_of_checkedPrimitive
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics_of_restorationStages
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence_of_checkedPrimitive
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence_of_restorationStages
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructural_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultAndIotaBaseAndTargetResults
#check NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResultsAndIotaBaseAndTargetResults
#check SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndCheckerGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.orderedGeneratedRuleResultAndIotaBaseAndTargetResults_of_generatedRuleResults
#check addDecl.orderedGeneratedRuleResultsAndIotaBaseAndTargetResults_of_generatedRuleResults
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerStructuralIotaBaseAndTargetResults_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
#check addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
#check addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultsAndIotaBaseAndTargetResults
#check addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
#check addDecl.checkedPrimitiveModelAndConstructiveHistoryAndVDeclWF
#check addDecl.checkedPrimitiveModelAndCheckerHistoryAndVDeclWF
#check addDecl.checkedPrimitiveModelAndCheckerHistoryAndVDeclWF_of_restorationStages
#check addDecl.checkedPrimitiveModelAndCheckerHistoryIotaBaseAndTargetResultsAndVDeclWF
#check addDecl.checkedPrimitiveModelAndCheckerHistoryIotaBaseAndTargetResultsAndVDeclWF_of_restorationStages
#check addDecl.checkedPrimitiveModelAndRestoredAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
#check addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
#check addDecl.checkedPrimitiveModelAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
#check addDecl.checkedPrimitiveModelAndGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
        AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
  have h := evidence.recursorGeneratedRuleResultAndIota ruleResults
  have hGeneratedPlural := evidence.recursorGeneratedRuleResults ruleResults
  have hPlural := evidence.recursorGeneratedRuleResultsAndIota ruleResults
  have _ := hGeneratedPlural
  exact h

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
        AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
  have h := evidence.recursorGeneratedRuleResultAndIotaBaseAndTargetResults ruleResults
  have hPlural := evidence.recursorGeneratedRuleResultsAndIotaBaseAndTargetResults ruleResults
  exact h

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleResultsAndIota ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleResultAndIotaBaseAndTargetResults ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleResultsAndIotaBaseAndTargetResults ruleResults

example {env : VEnv} {universes : List Name} {stats : AddInductive.InductiveStats}
    {motives minors : Array Expr} {ctx : AddInductive.Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : AddInductive.GeneratedRecursorRuleResult env universes stats motives minors
      ctx constructor minor rule) :
    AddInductive.GeneratedRecursorRuleIotaKind env universes stats motives minors
      ctx constructor minor rule :=
  result.iotaKind

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules,
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.recursorGeneratedRuleIotaKind ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules,
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.recursorGeneratedRuleIotaBaseAndTargetResults ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleIotaKinds ruleResults

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  evidence.orderedGeneratedRuleIotaBaseAndTargetResults ruleResults

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result :=
  evidence.to_addInduct

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    AddInductEvidence .safe constants env decl evidence.constructorConstants
      evidence.constructorEnv :=
  evidence.to_addInductEvidence hconstants

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    AddInduct constants env decl evidence.constructorConstants evidence.constructorEnv :=
  evidence.to_legacyAddInduct hconstants

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    evidence.constructorConstants.WF :=
  (evidence.to_legacyAddInduct hconstants).map_wf hconstants

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      (∀ info ∈ headers, evidence.constructorConstants.find? info.name =
        some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, evidence.constructorConstants.find? ctor.name =
        some (.ctorInfo ctor)) := by
  obtain ⟨headers, constructors, headerEnv, _, _, hheaders, hconstructors⟩ :=
    (evidence.to_legacyAddInduct hconstants).lookupReceipt hconstants
  exact ⟨headers, constructors, headerEnv, hheaders, hconstructors⟩

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) (haligned : Aligned .safe constants env) :
    AddInduct constants env decl evidence.constructorConstants evidence.constructorEnv ∧
      Aligned .safe evidence.constructorConstants evidence.constructorEnv :=
  evidence.to_legacyAddInduct_and_aligned hconstants haligned

example {safety : DefinitionSafety} {Q : Bool}
    {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (history : TrEnvInductive safety constants Q env)
    (haligned : Aligned safety constants env) (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    TrEnvInductive safety resultConstants Q result ∧
      Aligned safety resultConstants result :=
  evidence.to_trEnvInductive_and_aligned history haligned hconstants hrecursors

example {safety : DefinitionSafety} {Q : Bool}
    {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (history : TrEnvInductive safety constants Q env)
    (haligned : Aligned safety constants env) (hconstants : constants.WF)
    (hsource : ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    TrEnvInductive safety resultConstants Q result ∧
      Aligned safety resultConstants result :=
  evidence.to_trEnvInductive_and_aligned_of_sourceTypehood
    history haligned hconstants hsource

example {safety : DefinitionSafety} {Q : Bool}
    {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (native resultNative : Kernel.Environment)
    (history : TrEnvInductive safety native.constants Q env)
    (hmap : native.constants = constants) (hresultMap : resultNative.constants = resultConstants)
    (haligned : Aligned safety constants env) (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      resultNative.constants.find? name = some ci →
      safety ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr result ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive safety resultNative result Q ∧
      Aligned safety resultConstants result :=
  evidence.toCheckerEnvInductive_and_aligned native resultNative history hmap hresultMap
    haligned hconstants hrecursors hvalues

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      (∀ info ∈ headers, evidence.constructorConstants.find? info.name =
        some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, evidence.constructorConstants.find? ctor.name =
        some (.ctorInfo ctor)) := by
  obtain ⟨headers, constructors, headerEnv, _, _, hheaders, hconstructors⟩ :=
    (evidence.to_addInductEvidence hconstants).lookupReceipt hconstants
  exact ⟨headers, constructors, headerEnv, hheaders, hconstructors⟩

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    ∀ info ∈ evidence.recursors.map (·.info),
      resultConstants.find? info.name = some (.recInfo info) := by
  intro info hinfo
  exact (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).recursorLookup
    hconstants info hinfo

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    ∃ (headers : List InductiveVal) (constructors : List ConstructorVal) (headerEnv : VEnv),
      (∀ info ∈ headers, resultConstants.find? info.name =
        some (.inductInfo info)) ∧
      (∀ ctor ∈ constructors, resultConstants.find? ctor.name =
        some (.ctorInfo ctor)) ∧
      (∀ info ∈ evidence.recursors.map (·.info), resultConstants.find? info.name =
        some (.recInfo info)) := by
  obtain ⟨headers, constructors, headerEnv, _, _, hheaders, hconstructors, hrecursors⟩ :=
    (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).lookupReceipt hconstants
  exact ⟨headers, constructors, headerEnv, hheaders, hconstructors, hrecursors⟩

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    ∀ entry ∈ evidence.orderedEntries,
      resultConstants.find? entry.toConstantInfo.name = some entry.toConstantInfo :=
  evidence.orderedEntryLookup hconstants hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertRecursors (insertConstructors (insertHeaders constants evidence.headers)
      evidence.constructors) evidence.recursors :=
  evidence.native_map

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    FreshOrdered constants evidence.orderedEntries :=
  evidence.orderedFresh

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrdered constants evidence.orderedEntries :=
  evidence.orderedMap

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrderedModel constants evidence.orderedEntries :=
  evidence.orderedModelMap

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : HeaderEntry} (hmem : entry ∈ evidence.headers) :
    ∃ type ∈ decl.types, entry.model = type.toVConstVal :=
  evidence.headerModelMembership hmem

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : ConstructorEntry} (hmem : entry ∈ evidence.constructors) :
    ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor :=
  evidence.constructorModelMembership hmem

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, match entry with
      | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
      | .constructor entry => ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
      | .recursor _ => True :=
  evidence.orderedModelMembership

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv ∧
        entry.ModelShape ∧
        (∃ semantic, match entry with
          | .header entry =>
            TrExprS env entry.info.levelParams [] entry.info.type semantic
          | .constructor entry =>
            TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
          | .recursor entry =>
            TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic) ∧
        match entry with
          | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
          | .constructor entry =>
            ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
          | .recursor _ => True :=
  evidence.orderedEntryReceipt

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrdered constants evidence.orderedEntries :=
  evidence.orderedEntryReceiptAndMap |>.2

example {safety : DefinitionSafety} {constants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {resultConstants : ConstMap}
    (evidence : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (haligned : Aligned safety constants semanticEnv) :
    Aligned safety resultConstants semanticResult :=
  evidence.orderedEntryReceiptAndMapAndAlignment haligned |>.2

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, entry.ModelShape :=
  evidence.orderedModelShape

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length :=
  evidence.orderedModelShapeToConstantInfo

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry =>
        TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry =>
        TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic :=
  evidence.orderedTypeTranslation

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertInfos constants
      ((evidence.headers.map HeaderEntry.toConstantInfo ++
        evidence.constructors.map ConstructorEntry.toConstantInfo ++
        evidence.recursors.map RecursorEntry.toConstantInfo).reverse) :=
  evidence.native_map_records

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv :=
  evidence.orderedSemantic

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Metadata decl evidence.constructors :=
  evidence.orderedMetadata

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics result :=
  evidence.orderedRuleSemantics

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics result ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True :=
  evidence.orderedRuleResultsOf ruleResults

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS result entry.info.levelParams [] rule.rhs semantic ∧ True :=
  evidence.recursorRuleResult ruleResults

example {entry : RegistrationEntry} {env headerEnv constructorEnv : VEnv}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    entry.ModelShape :=
  hsemantic.modelShape

example {entry : RegistrationEntry} {env headerEnv constructorEnv : VEnv}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry => TrExprS headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry => TrExprS constructorEnv entry.info.levelParams [] entry.info.type semantic :=
  hsemantic.typeTranslation

example {entry : RegistrationEntry} (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length :=
  hshape.toConstantInfo

example {entry : RegistrationEntry} {constants : ConstMap} (hshape : entry.ModelShape) :
    entry.insert constants = constants.insert entry.model.name entry.toConstantInfo :=
  entry.insert_modelShape hshape

example {constants : ConstMap} {entries : List RegistrationEntry}
    (hshape : ∀ entry ∈ entries, entry.ModelShape) :
    insertOrdered constants entries = insertOrderedModel constants entries :=
  insertOrdered_modelShape constants entries hshape

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors,
      TrConstVal .safe evidence.constructorEnv (.recInfo entry.info) entry.model :=
  evidence.recursor_translation_receipt

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS result entry.info.levelParams [] rule.rhs semantic :=
  evidence.recursorRuleTranslation

private def receiptRecursor : RecursorVal := {
  name := `Receipt.rec
  levelParams := []
  type := .sort .zero
  all := []
  numParams := 0
  numIndices := 0
  numMotives := 0
  numMinors := 0
  rules := []
  k := false
  isUnsafe := false }

example (env : VEnv) :
    TrConstVal .safe env (.recInfo receiptRecursor)
      { name := `Receipt.rec, uvars := 0, type := .sort .zero } := by
  refine ⟨⟨DefinitionSafety.le_rfl, rfl, .sort rfl⟩, rfl⟩

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) :
    ∃ infos, result.constants = NativeInductive.insertInfos original.constants infos :=
  NativeInductive.FreshRegistrationTrace.constants_eq trace

example (env : Kernel.Environment) (hwf : env.constants.WF) :
    env.constants = NativeInductive.insertInfos env.constants [].reverse :=
  (RestoredRegistrationReceipt.empty env hwf).map

example {original current result : Kernel.Environment} {first second : List ConstantInfo}
    (left : RestoredRegistrationReceipt original first current)
    (right : RestoredRegistrationReceipt current second result) :
    result.constants = NativeInductive.insertInfos original.constants (first ++ second).reverse :=
  (left.trans right).map

example {original result : Kernel.Environment} {headers constructors recursors : List ConstantInfo}
    (receipt : RestoredRegistrationReceipt original (headers ++ constructors ++ recursors) result) :
    result.constants =
      NativeInductive.insertInfos
        (NativeInductive.insertInfos
          (NativeInductive.insertInfos original.constants headers.reverse) constructors.reverse)
        recursors.reverse :=
  receipt.mapPhases

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {types : List InductiveType} {info : ConstantInfo}
    (hmem : info ∈ restoredEnvironmentRecords preprocessing staged types) :
    RestoredInductiveRecord preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 info :=
  restoredEnvironmentRecords.typedPartition preprocessing staged types hmem

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hsources : RestorationSources staged types) (env : Kernel.Environment)
    (hwf : env.constants.WF) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      RestoredRegistrationEvidence preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2 env (restoredEnvironmentRecords preprocessing staged types) result.2 :=
  restoreInductiveEnvironment.evidence preprocessing staged types lparams allowPrimitive fuel hsources env hwf

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = NativeInductive.insertInfos original.constants
      (evidence.entries.map NativeInductive.RegistrationEntry.toConstantInfo).reverse :=
  evidence.map

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) :
    result.constants = NativeInductive.insertOrdered original.constants evidence.entries :=
  evidence.orderedMap

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) :
    result.find? entry.toConstantInfo.name = some entry.toConstantInfo :=
  evidence.entryInstalled hmem

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {info : ConstantInfo} (hmem : info ∈ records) :
    ∃ entry ∈ evidence.entries, info = entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.typedRecord hmem

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) :
    ∃ name info, staged.find? name = some info :=
  evidence.sourceLookup hmem

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) {entry : NativeInductive.RegistrationEntry}
    (hmem : entry ∈ evidence.entries) (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
      result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
      ∃ name info, staged.find? name = some info :=
  evidence.entryModelReceipt hmem hshape

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (evidence : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records) (hshape : ∀ entry ∈ evidence.entries, entry.ModelShape) :
    ∀ entry ∈ evidence.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info :=
  evidence.orderedModelReceipt hshape

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaBaseAndTargetResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleResultsAndIota producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  have hPlural := restored.sourceRecursorGeneratedRuleResultsAndIotaBaseAndTargetResults producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaBaseAndTargetResults producer halign
    hconstants history hrecursors hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.registrationIotaBaseAndTargetResults producer halign ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info :=
  restored.fromRegistrationEvidence producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.Semantic semanticEnv producer.headerEnv producer.constructorEnv ∧
        entry.Metadata decl producer.constructors ∧
        entry.RuleSemantics semanticResult ∧
        entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap
          entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info :=
  restored.registrationReceipt producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants) :
    result.constants = NativeInductive.insertOrdered constants restored.entries :=
  restored.registrationMap producer halign hconstants hresultConstants

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) :
    result.constants = resultConstants :=
  restored.registrationConstants producer halign hconstants

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (haligned : Aligned safety constants semanticEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = NativeInductive.insertOrdered original.constants restored.entries :=
  restored.registrationAlignment producer halign hconstants hresultConstants haligned

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
    CheckerEnvInductive .safe result semanticResult Q :=
  restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues

example {Result : RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) :=
  restored.toCheckerEnvInductive_and_registrationRuleResults producer halign hconstants history
    hrecursors hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationGeneratedRuleResultsAndIota
    producer halign hconstants history hrecursors hvalues ruleResults
  have hPlural := restored.toCheckerEnvInductive_and_registrationGeneratedRuleResultsAndIotaBaseAndTargetResults
    producer halign hconstants history hrecursors hvalues ruleResults
  have hNamed := restored.toCheckerEnvInductive_and_registrationGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign hconstants history hrecursors hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationIotaKinds producer halign hconstants history
    hrecursors hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationIotaTargetResults producer halign
    hconstants history hrecursors hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationIotaKinds_of_sourceTypehood producer halign
    hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaKinds_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_ruleResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  restored.registrationHistory producer halign hconstants history hrecursors

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (haligned : Aligned safety constants semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult :=
  restored.registrationAlignmentHistory producer halign hconstants history haligned hrecursors

example {safety : DefinitionSafety}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult :=
  restored.registrationAlignmentHistory_of_sourceTypehood producer halign hconstants history hsource

example {Result : RecursorEntry → RecursorRule → Prop}
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ entry ∈ restored.entries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule :=
  restored.registrationRuleResults producer halign ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.registrationGeneratedRuleResultsAndIota producer halign ruleResults
  have hPlural := restored.registrationGeneratedRuleResultsAndIotaBaseAndTargetResults
    producer halign ruleResults
  have hNamed := restored.registrationGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ restored.entries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleIotaKind semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule :=
  restored.registrationIotaKinds producer halign ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.ModelShape :=
  restored.registrationModelShapes producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries, entry.Metadata decl producer.constructors :=
  restored.registrationMetadata producer halign

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {entry : RecursorEntry} (hentry : .recursor entry ∈ restored.entries)
    {rule : RecursorRule} (hrule : rule ∈ entry.info.rules) :
    ∃ semantic, TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.registrationRecursorRuleTranslation producer halign hentry hrule

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
    CheckerEnvInductive .safe result semanticResult Q :=
  restored.toCheckerEnvInductive_of_sourceTypehood producer halign hconstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleIotaTargetResults_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hPlural := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryIota := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryPair := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryGenerated := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryGeneratedPlural := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have _ := hOrdinary
  have _ := hOrdinaryIota
  have _ := hOrdinaryPair
  have _ := hOrdinaryGenerated
  have _ := hOrdinaryGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationIotaBaseAndTargetResults (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModel := addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults
    (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
    hsource hvalues ruleResult hrecursor hentry
  have hModelGenerated :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedPluralOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationGeneratedOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationGeneratedPluralOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have _ := h
  have _ := hGenerated
  have _ := hModel
  have _ := hModelGenerated
  have _ := hModelOrdinary
  have _ := hModelGeneratedOrdinary
  have _ := hModelGeneratedPluralOrdinary
  have _ := hRegistrationOrdinary
  have _ := hRegistrationGeneratedOrdinary
  have _ := hRegistrationGeneratedPluralOrdinary
  trivial


example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ (allowPrimitive : Bool),
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ (allowPrimitive : Bool),
      ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (allowPrimitive : Bool) preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationIotaBaseAndTargetResults_of_restorationStages
    (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv)
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv)
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hModel := addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults_of_restorationStages
    (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
    hsource hvalues ruleResult hrecursor hentry
  have hModelGenerated :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hModelGeneratedPluralOrdinary :=
    addDecl.checkedPrimitiveModelAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationGeneratedOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have hRegistrationGeneratedPluralOrdinary :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history
      hsource hvalues ruleResult hrecursor hentry
  have _ := h
  have _ := hGenerated
  have _ := hModel
  have _ := hModelGenerated
  have _ := hModelOrdinary
  have _ := hModelGeneratedOrdinary
  have _ := hModelGeneratedPluralOrdinary
  have _ := hRegistrationOrdinary
  have _ := hRegistrationGeneratedOrdinary
  have _ := hRegistrationGeneratedPluralOrdinary
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) :=
  metadata.toRestoredRecordEvidence coverage entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
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
          evidence.entries = entries preprocessing staged }) :=
  metadata.sourceRecursorRulesAndRestoredRecordEvidence coverage entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context)
      (constructors : Kernel.Environment) (elimLevel : Level) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
      AddInductive.RecursorMinorIndexing preprocessing.types.toArray infos ∧
      AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : NativeInductive.RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries preprocessing staged }) :=
  metadata.sourceRecursorRuleStagesAndRestoredRecordEvidence coverage entries records_eq

example {Result : RecursorEntry → RecursorRule → Prop}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
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
          ∃ (entry : RecursorEntry) (recursor : RecursorVal)
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
            Result entry rule) :=
  metadata.sourceRecursorRuleResultsAndRestoredRecordEvidence coverage entries records_eq producer
    entry_eq hrecursor hentry ruleResult

example {Result : RecursorEntry → RecursorRule → Prop}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (producer : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) : True := by
  have h := metadata.sourceRecursorRuleStagesResultsAndRestoredRecordEvidence coverage entries
    records_eq producer entry_eq hrecursor hentry ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨allowPrimitive, metadata, haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_restorationStages
      hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics
    history producer hconstants hresultConstants hrecursors hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∃ (allowPrimitive : Bool), Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_checkedPrimitive
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_checkedPrimitive
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∃ allowPrimitive,
      SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result ∧
      Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_restorationStages
    hmap hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    SafeInductiveRestorationMetadata env lparams nparams types true fuel result ∧
      Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleIotaTargetResults_of_checkedPrimitive_and_restorationStages
    hmap hcheck hresult history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) :
    ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result)
      (staged : Kernel.Environment) (stats : AddInductive.InductiveStats)
      (root : AddInductive.Context) (constructors : Kernel.Environment)
      (elimLevel : Level) (infos : Array AddInductive.RecInfo) (source : AddInductive.Context),
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Aligned .safe resultConstants semanticResult ∧
        CheckerEnvInductive .safe result semanticResult Q) := by
  have hIota := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hCombined := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hPlural := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have _ := hCombined
  have _ := hPlural
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hlookups,
      hbranch, hfinal⟩ :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  exact ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hlookups, fun hnested => ⟨(hfinal hnested).1, (hfinal hnested).2.2.2.1⟩⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) :
    ∃ preprocessing staged stats root constructors elimLevel infos source,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) root constructors staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Aligned .safe resultConstants semanticResult ∧
        CheckerEnvInductive .safe result semanticResult Q) := by
  have hIota := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hCombined := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hPlural := addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := hCombined
  have _ := hPlural
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, _, _, _, _, _, hsources, _, _, hfinal⟩ :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  exact ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hsources, fun hnested =>
      ⟨(hfinal hnested).1, (hfinal hnested).2.2.2.1⟩⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
        CheckerEnvInductive .safe result semanticResult Q) :=
  metadata.toCheckerEnvInductive coverage entries records_eq producer entry_eq hconstants history
    hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
        CheckerEnvInductive .safe result semanticResult Q) :=
  metadata.toCheckerEnvInductive_of_sourceTypehood coverage entries records_eq producer entry_eq
    hconstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q := by
  exact metadata.toCheckerEnvInductive_of_frontendSourceTypehood producer hconstants
    hresultConstants history hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 → CheckerEnv .safe result semanticResult) :=
  metadata.toCheckerEnv coverage entries records_eq producer entry_eq hconstants history
    hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
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
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaKinds
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaBaseAndTargetResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood_and_generatedRuleResults
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context}
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota := metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentIotaBaseAndTargetResultsSemantics
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hSemanticIota :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hSemanticCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hSemanticPluralCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationPluralCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationSemanticsOrdinary :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationIotaOrdinary :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationCombinedOrdinary :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRegistrationPluralCombinedOrdinary :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hAlignmentCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hAlignmentPluralCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hRestoredIota :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordIotaBaseAndTargetResultsEvidence
      coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hRestoredCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultAndIotaBaseAndTargetResultsEvidence
      coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hRestoredPluralCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence
      coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hCheckerCombined :=
    metadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaBaseAndTargetResults
      (stats := stats) (infos := infos) (source := source) (universes := universes)
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      (ruleResult := fun entry hentry rule hrule =>
        ruleResult stats infos source entry hentry rule hrule)
      hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResult
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := restored.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    producer halign hconstants history hsource hvalues ruleResult
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult :=
  restored.registrationConstructive producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants.WF :=
  restored.registrationMapWF producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hconstantsWF : constants.WF) (hsemanticEnvWF : semanticEnv.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants.WF :=
  restored.registrationMapWF_of_sourceTypehood producer halign hconstants hconstantsWF
    hsemanticEnvWF hsource

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveAndMapWF producer halign hconstants hconstantsWF hrecursors

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants) :
    result.constants = resultConstants ∧ result.constants.WF ∧
      result.constants = insertOrdered constants restored.entries ∧
      (∀ entry ∈ restored.entries,
        entry.Semantic semanticEnv producer.headerEnv producer.constructorEnv ∧
        entry.Metadata decl producer.constructors ∧
        entry.RuleSemantics semanticResult ∧
        entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length ∧
        result.find? entry.toConstantInfo.name = some entry.toConstantInfo ∧
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap
          entry.toConstantInfo ∧
        ∃ name info, staged.find? name = some info) :=
  restored.registrationReceiptAndMap producer halign hconstants hresultConstants

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants) :
    ∀ entry ∈ restored.entries,
      resultConstants.find?' entry.toConstantInfo.name = some entry.toConstantInfo := by
  exact (restored.registrationReceiptAndMapAndOrderedEntryFindPrime producer halign hconstants
    hresultConstants).2.2.2

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (haligned : Aligned safety constants semanticEnv) :
    Aligned safety resultConstants semanticResult :=
  (restored.registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment producer halign
    hconstants hresultConstants haligned).2

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (haligned : Aligned safety constants semanticEnv) :
    Aligned safety resultConstants semanticResult := by
  exact (restored.registrationReceiptAndMapAndAlignment producer halign hconstants
    hresultConstants haligned).2.2.2.2

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe resultConstants Q semanticResult)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (haligned : Aligned .safe constants semanticEnv) :
    CheckerEnvInductive .safe result semanticResult Q :=
  (restored.toCheckerEnvInductive_and_registrationReceiptAndMapAndAlignment producer halign
    hconstants hresultConstants history hvalues haligned).1

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe resultConstants Q semanticResult)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (haligned : Aligned .safe constants semanticEnv) :
    CheckerEnvInductive .safe result semanticResult Q :=
  (restored.toCheckerEnvInductive_and_registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment
    producer halign hconstants hresultConstants history hvalues haligned).1

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants) (hconstantsWF : constants.WF)
    (hsemanticEnvWF : semanticEnv.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveAndMapWF_of_sourceTypehood producer halign hconstants
    hconstantsWF hsemanticEnvWF hsource

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult :=
  restored.registrationConstructiveHistory producer halign hconstants history
    hconstantsWF hrecursors

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveHistoryAndMapWF producer halign hconstants history
    hconstantsWF hrecursors

example {safety : DefinitionSafety} {constants : ConstMap}
    {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive safety constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      TrEnvInductive safety resultConstants Q semanticResult ∧
      Aligned safety resultConstants semanticResult ∧ result.constants.WF :=
  restored.registrationConstructiveHistoryAndMapWF_of_sourceTypehood producer halign hconstants
    history hconstantsWF hsource

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule,
      rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants = resultConstants ∧
      AddInductWithRecursorsEvidence .safe constants semanticEnv decl
        producer.constructorConstants producer.constructorEnv
        (producer.recursors.map (·.info)) (producer.recursors.map (·.model))
        resultConstants semanticResult ∧
      Aligned .safe resultConstants semanticResult ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  have hCombined := restored.registrationConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  have hOrdinary := restored.registrationConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  have hPluralCombined := restored.registrationConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResults
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  exact restored.registrationConstructiveCheckerIotaBaseAndTargetResults producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries) :
    ∀ entry ∈ restored.entries,
      entry.ModelShape ∧ entry.Metadata decl producer.constructors ∧
      match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.registrationStructuralReceipts producer halign

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (hlookup : result.find? name = some info) :
    original.find? name = some info ∨
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.lookup hwf name info hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (habsent : original.find? name = none)
    (hlookup : result.find? name = some info) :
    RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newLookup hwf name info habsent hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) :
    original.find? info.name = some info ∨
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.recordClassification hwf hmem

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) (habsent : original.find? info.name = none) :
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newRecordClassification hwf hmem habsent

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) :
    result.find? info.name = some info ∧
      (original.find? info.name = some info ∨
        RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :=
  evidence.recordReceipt hwf hmem

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) {info : ConstantInfo}
    (hmem : info ∈ records) (habsent : original.find? info.name = none) :
    result.find? info.name = some info ∧
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap info :=
  evidence.newRecordReceipt hwf hmem habsent

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {records : List ConstantInfo}
    (evidence : RestoredRegistrationEvidence preprocessing staged allIndNames recNameMap
      original records result) (hwf : original.constants.WF) :
    ∀ info ∈ records,
      result.find? info.name = some info ∧
        (original.find? info.name = some info ∨
          RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :=
  evidence.recordsReceipt hwf

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment}
    {original result : Kernel.Environment} {types : List InductiveType}
    (evidence : RestoredRegistrationEvidence preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2
      original (restoredEnvironmentRecords preprocessing staged types) result)
    (entries : List RegistrationEntry)
    (records_eq : restoredEnvironmentRecords preprocessing staged types =
      entries.map RegistrationEntry.toConstantInfo) :
    NativeInductive.RestoredRecordEvidence preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 original result
      (restoredEnvironmentRecords preprocessing staged types) :=
  NativeInductive.RestoredRegistrationEvidence.toRestoredRecordEvidence evidence entries records_eq

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q :=
  scope.toCheckerEnvInductive history producer hconstants hresultConstants hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {resultConstants : ConstMap} {semanticResult : VEnv} {Q : Bool}
    (history : TrEnvInductive .safe resultConstants Q semanticResult)
    (hresultConstants : result.constants = resultConstants)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q :=
  scope.toCheckerEnvInductive_of_explicitHistory history hresultConstants hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticResult : VEnv} {Q : Bool}
    (history : TrEnvInductive .safe resultConstants Q semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧ constants.WF :=
  scope.toCheckerEnvInductive_of_explicitHistoryAndMapWF history hconstants
    hresultConstants hvalues

example {safety : DefinitionSafety} {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe resultConstants Q semanticResult)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (haligned : Aligned safety constants semanticEnv) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (result.constants = resultConstants ∧ constants.WF) ∧
      (((∀ entry ∈ producer.orderedEntries,
        entry.Semantic semanticEnv producer.headerEnv producer.constructorEnv ∧
          entry.ModelShape ∧
          (∃ semantic, match entry with
            | .header entry =>
              TrExprS semanticEnv entry.info.levelParams [] entry.info.type semantic
            | .constructor entry =>
              TrExprS producer.headerEnv entry.info.levelParams [] entry.info.type semantic
            | .recursor entry =>
              TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic) ∧
          match entry with
            | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
            | .constructor entry =>
              ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
            | .recursor _ => True) ∧
        resultConstants = NativeInductive.insertOrdered constants producer.orderedEntries) ∧
        Aligned safety resultConstants semanticResult) :=
  scope.toCheckerEnvInductive_of_explicitHistoryAndMapWF_and_orderedEntryReceiptAndMapAndAlignment
    history producer hconstants hresultConstants hvalues haligned

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        result.constants.find? entry.toConstantInfo.name = some entry.toConstantInfo) :=
  scope.toCheckerEnvInductive_and_orderedEntryLookup history producer hconstants
    hresultConstants hrecursors hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_and_ruleResults history producer hconstants hresultConstants
    hrecursors hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_of_sourceTypehood_and_ruleResults history producer hconstants
    hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  scope.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = mkRecName types[index].name)
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
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic :=
  restored.sourceRecursorRuleTranslation producer halign hlookups index hindex ctorIndex hctor
    hentry hname hrecursorName

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length)
    {entry : NativeInductive.RecursorEntry}
    (hentry : (.recursor entry : RegistrationEntry) ∈ restored.entries)
    (hname : entry.info.name = mkRecName types[index].name)
    (hrecursorName : ∀ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = entry.info.name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
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
      True :=
  restored.sourceRecursorRuleResults producer halign hlookups index hindex ctorIndex hctor
    hentry hname hrecursorName ruleResult

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry,
        (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name)
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
      (hctor : ctorIndex < types[index].ctors.length),
      ∃ (entry : RecursorEntry) (recursor : RecursorVal) (rule : RecursorRule)
        (info : ConstructorVal) (semantic : VExpr),
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
        True :=
  restored.sourceRecursorRules producer halign hlookups hrecursor hentry ruleResult

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleResults producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleIotaKinds producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleIotaBaseAndTargetResults producer halign hlookups
    (stats := stats) (infos := infos) (source := source) (universes := universes)
    ruleResult hrecursor hentry
  have hCombined := restored.sourceRecursorGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign hlookups (stats := stats) (infos := infos) (source := source)
    (universes := universes) ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants.WF := by
  have hCombined := restored.registrationConstructiveCheckerAndMapWFGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  have hOrdinary := restored.registrationConstructiveCheckerAndMapWFGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  have hPluralCombined := restored.registrationConstructiveCheckerAndMapWFGeneratedRuleResultsAndIotaBaseAndTargetResults
    producer halign hconstants history hconstantsWF hrecursors hvalues hsource ruleResults
  exact (restored.registrationConstructiveCheckerAndMapWFIotaBaseAndTargetResults producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults).2.2.2.2.2.2

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hconstantsWF : constants.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    result.constants.WF := by
  exact (restored.registrationConstructiveCheckerAndMapWF producer halign hconstants history
    hconstantsWF hrecursors hvalues hsource ruleResults).2.2.2.2.2.2

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleStructural producer halign hlookups
    ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleStructuralIotaBaseAndTargetResults producer halign
    hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults
    producer halign hlookups ruleResult hrecursor hentry
  have hCombined :=
    restored.sourceRecursorGeneratedRuleStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      producer halign hlookups ruleResult hrecursor hentry
  have hPluralCombined :=
    restored.sourceRecursorGeneratedRuleStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      producer halign hlookups ruleResult hrecursor hentry
  have _ := hCombined
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  have hOrdinary := restored.toCheckerEnv_and_sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  have hNamed := restored.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  have hPluralNamed := restored.toCheckerEnvInductive_and_sourceRecursorGeneratedRuleStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) :
    CheckerEnvInductive .safe result semanticResult Q := by
  exact (restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults producer
    halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry).1

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleIotaKinds
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule,
      rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.registrationSemanticAndStructuralIotaBaseAndTargetResults producer halign hconstants history hsource
    hvalues hlookups ruleResult hrecursor hentry
  have hCombined :=
    restored.registrationSemanticAndStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  have hPluralCombined :=
    restored.registrationSemanticAndStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  have _ := hCombined
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} {preprocessing : ElimNestedInductive.Result}
    {staged : Kernel.Environment} {allIndNames : List Name} {recNameMap : NameMap Name}
    {original result : Kernel.Environment} {records : List ConstantInfo} {Q : Bool}
    (restored : NativeInductive.RestoredRecordEvidence preprocessing staged allIndNames recNameMap
      original result records)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (halign : restored.entries = producer.orderedEntries)
    (hconstants : original.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) : True := by
  have h := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaBaseAndTargetResults
    producer halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence
    coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {fuel : FuelConfig}
    (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
    (source : AddInductive.Context)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hrun : AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams true fuel) = .ok staged)
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (hrestored : preprocessing.aux2nested.size ≠ 0 →
      Nonempty { evidence : RestoredRecordEvidence preprocessing staged
          (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
          (restoredEnvironmentRecords preprocessing staged types) //
        evidence.entries = entries preprocessing staged })
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : preprocessing.aux2nested.size ≠ 0 →
      entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStructuralSemantics_of_stage
    preprocessing staged stats infos source hpre hrun hlookups entries hrestored producer
    entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := metadata.sourceRecursorRuleStagesGeneratedResultsAndChecker
    coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndCheckerIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndCheckerGeneratedRuleResultAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hPluralCombined :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndCheckerGeneratedRuleResultsAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralIota :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralOrdinary :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralCombined :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralCombinedOrdinary :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralPluralCombined :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStructuralPluralCombinedOrdinary :=
    metadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_toCheckerEnv
      coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationHistory history producer hconstants hresultConstants hrecursors

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationHistory_of_sourceTypehood history producer hconstants hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.registrationAlignmentHistory_of_sourceTypehood history producer hconstants
    hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  scope.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationHistory history producer hconstants hresultConstants hrecursors

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationHistory_of_sourceTypehood history producer hconstants hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.registrationAlignmentHistory_of_sourceTypehood history producer hconstants
    hresultConstants hsource

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource hvalues

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → True) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, True) :=
  metadata.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnv .safe result semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  metadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnv .safe result semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries, entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule ∧
              AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  metadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo) :
    ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result)
      (staged : Kernel.Environment) (stats : AddInductive.InductiveStats)
      (root : AddInductive.Context) (constructors : Kernel.Environment)
      (elimLevel : Level) (infos : Array AddInductive.RecInfo) (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Nonempty { evidence : RestoredRecordEvidence preprocessing staged
            (types.map (·.name)) (mkAuxRecNameMap staged types).2 env result
            (restoredEnvironmentRecords preprocessing staged types) //
          evidence.entries = entries allowPrimitive preprocessing staged }) := by
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hlookups,
      hbranch, hrestored⟩ :=
    addDecl.sourceRecursorRuleStagesAndRestoredRecordEvidence_of_restorationStages
      hmap hresult coverage entries records_eq
  exact ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hprefix, hlookups, hrestored⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordIotaBaseAndTargetResultsEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have h :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hCombined :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultAndIotaBaseAndTargetResultsEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have _ := h
  have _ := hCombined
  have _ := hPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo) : True := by
  have h := addDecl.sourceRecursorRuleStagesAndRestoredRecordEvidence_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq
  have _metadata : SafeInductiveRestorationMetadata env lparams nparams types true fuel result := h.1
  have _stages := h.2
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordIotaBaseAndTargetResultsEvidence_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hCombined :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultAndIotaBaseAndTargetResultsEvidence_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have hPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hrecursor hentry ruleResult
  have _ := h
  have _ := hCombined
  have _ := hPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have hStages :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStagesGenerated :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStagesGeneratedPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have h := addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have _ := h
  have _ := hStagesGenerated
  have _ := hStagesGeneratedPlural
  have _ := hGenerated
  have _ := hGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have hStages :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStagesGenerated :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hStagesGeneratedPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistrationGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have h := addDecl.checkedPrimitiveModelAndRegistrationSemanticsIotaBaseAndTargetResults_of_restorationStages (venv := venv)
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndRegistrationSemanticsGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have _ := h
  have _ := hStagesGenerated
  have _ := hStagesGeneratedPlural
  have _ := hGenerated
  have _ := hGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hIotaOrdinary :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural_of_restorationStages
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have hmCombined :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have hmPluralCombined :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have hmIota :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralIotaBaseAndTargetResults_of_restorationStages
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hm
  have _ := hmCombined
  have _ := hmIota
  trivial

/- Regression: restoration-stage checker-structural source stages retain
   generated rule results and paired base/target iota endpoints. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hIotaOrdinary :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hIotaPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hIotaPluralOrdinary :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages_toCheckerEnv
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hSemanticIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hSemanticIotaPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural_of_restorationStages
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hIotaPlural
  have _ := hSemanticIota
  have _ := hSemanticIotaPlural
  have _ := hm
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndChecker_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hSemanticIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have hmCombined :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have hmPluralCombined :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have hmIota :=
    addDecl.checkedPrimitiveModelAndCheckerStructuralIotaBaseAndTargetResults
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
      ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hSemanticIota
  have _ := hm
  have _ := hmCombined
  have _ := hmIota
  trivial

/- Regression: checker-structural source stages retain generated rule results
   together with their paired base/target iota endpoints. -/
/- Regression: semantic-structural source stages retain generated rule
   results and paired base/target iota endpoints. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hSemanticIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hSemanticIotaPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hSemanticIota
  have _ := hSemanticIotaPlural
  have _ := hm
  trivial

/- Regression: checker-structural source stages retain generated rule results
   together with their paired base/target iota endpoints. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_checkedPrimitive
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry
  have hIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hIotaPlural :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructuralGeneratedRuleResultsAndIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hSemanticIota :=
    addDecl.sourceRecursorRuleStagesGeneratedResultsAndSemanticStructuralIotaBaseAndTargetResults_of_checkedPrimitive
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
      hvalues ruleResult hrecursor hentry
  have hm := addDecl.checkedPrimitiveModelAndCheckerStructural
    hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants history hsource
    hvalues ruleResult hrecursor hentry venv
  have _ := h
  have _ := hIota
  have _ := hIotaPlural
  have _ := hSemanticIota
  have _ := hm
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : ∀ allowPrimitive,
      InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel)
    (entries : ∀ allowPrimitive, ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries allowPrimitive preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries allowPrimitive preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ allowPrimitive preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries allowPrimitive preprocessing staged ∧
          entry.info.name = mkRecName types[index].name) : True := by
  have h := addDecl.sourceRecursorRuleStagesGeneratedResultsAndCheckerStructural_of_restorationStages
    hmap hresult coverage entries records_eq producer entry_eq hconstants history hsource hvalues
    ruleResult hrecursor hentry
  have _ := h
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorFieldStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, hpre, hrun, hprefix, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _ := hpre
  have _ := hrun
  have _ := hprefix
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorFieldStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _ := hpre
  have _ := hrun
  have _ := hprefix
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.constructorFieldStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.constructorFieldStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecordStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source, isK,
      hpre, hrun, hscope, hprefix, hframe, hlevels, hcounts, hindexing, hdistinct, hsource,
      hbranch, hnames, hrecords⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hlevels
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsource
  have _ := hbranch
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecordStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source, isK,
      hpre, hrun, hscope, hprefix, hframe, hlevels, hcounts, hindexing, hdistinct, hsource,
      hbranch, hnames, hrecords⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hlevels
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsource
  have _ := hbranch
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecords_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK,
      hpre, hrun, hlevels, hnames, hrecords⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRecords_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK,
      hpre, hrun, hlevels, hnames, hrecords⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hrecords
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleAt_of_restorationStages hmap hresult index hindex ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK,
      before, after, sourceRule, finalRule, info, hpre, hrun, hlevels, hnames, hbefore, hafter,
      hsource, hfinal, hctorName, hctorEq, hfieldsEq, hrhs, hlookup, hmetadata, hfields, hcount, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _sourceRule : RecursorRule := sourceRule
  have _finalRule : RecursorRule := finalRule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hsource
  have _ := hfinal
  have _ := hctorName
  have _ := hctorEq
  have _ := hfieldsEq
  have _ := hrhs
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  have _ := hcount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleAt_of_checkedPrimitive hmap hcheck hresult index hindex ctorIndex hctor
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK,
      before, after, sourceRule, finalRule, info, hpre, hrun, hlevels, hnames, hbefore, hafter,
      hsource, hfinal, hctorName, hctorEq, hfieldsEq, hrhs, hlookup, hmetadata, hfields, hcount, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _sourceRule : RecursorRule := sourceRule
  have _finalRule : RecursorRule := finalRule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hsource
  have _ := hfinal
  have _ := hctorName
  have _ := hctorEq
  have _ := hfieldsEq
  have _ := hrhs
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  have _ := hcount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.originalRecursorFinalHeader_of_restorationStages hmap hresult index hindex
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK, before, after,
      hpre, hrun, hlevels, hnames, hbefore, hafter, hheader, hall, htype⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hheader
  have _ := hall
  have _ := htype
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.originalRecursorFinalHeader_of_checkedPrimitive hmap hcheck hresult index hindex
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK, before, after,
      hpre, hrun, hlevels, hnames, hbefore, hafter, hheader, hall, htype⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _before : RecursorVal := before
  have _after : RecursorVal := after
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hnames
  have _ := hbefore
  have _ := hafter
  have _ := hheader
  have _ := hall
  have _ := htype
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRuleStages_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hnodup, hframe, hcounts, hindexing, hdistinct, hsources,
      hbranch, hnames, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hnodup
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hbranch
  have _ := hnames
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.originalRecursorRuleStages_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hnodup, hframe, hcounts, hindexing, hdistinct, hsources,
      hbranch, hnames, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hnodup
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hbranch
  have _ := hnames
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleLookup_of_restorationStages hmap hresult index hindex ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, recursor, rule, info,
      hpre, hrun, hlookup, hcount, hrule, hname, hctorLookup, hmetadata, hfields, hfieldCount, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _recursor : RecursorVal := recursor
  have _rule : RecursorRule := rule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hcount
  have _ := hrule
  have _ := hname
  have _ := hctorLookup
  have _ := hmetadata
  have _ := hfields
  have _ := hfieldCount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) : True := by
  have h := addDecl.originalRecursorRuleLookup_of_checkedPrimitive hmap hcheck hresult index hindex ctorIndex hctor
  obtain ⟨preprocessing, staged, recursor, rule, info,
      hpre, hrun, hlookup, hcount, hrule, hname, hctorLookup, hmetadata, hfields, hfieldCount, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _recursor : RecursorVal := recursor
  have _rule : RecursorRule := rule
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hcount
  have _ := hrule
  have _ := hname
  have _ := hctorLookup
  have _ := hmetadata
  have _ := hfields
  have _ := hfieldCount
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.sourceRecursorHeader_of_restorationStages hmap hresult index hindex
  obtain ⟨allowPrimitive, preprocessing, staged, stats, elimLevel, infos, source, isK, recursor,
      hpre, hrun, hlevels, hlookup, hheader⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _recursor : RecursorVal := recursor
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hlookup
  have _ := hheader
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (index : Nat) (hindex : index < types.length) : True := by
  have h := addDecl.sourceRecursorHeader_of_checkedPrimitive hmap hcheck hresult index hindex
  obtain ⟨preprocessing, staged, stats, elimLevel, infos, source, isK, recursor,
      hpre, hrun, hlevels, hlookup, hheader⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _isK : Bool := isK
  have _recursor : RecursorVal := recursor
  have _ := hpre
  have _ := hrun
  have _ := hlevels
  have _ := hlookup
  have _ := hheader
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorLookups_of_restorationStages hmap hresult
  obtain ⟨allowPrimitive, preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  have h := addDecl.sourceConstructorLookups_of_checkedPrimitive hmap hcheck hresult
  obtain ⟨preprocessing, staged, stats, root, constructors,
      hpre, hrun, hscope, hprefix, hbranch, hlookups⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hbranch
  have _ := hlookups
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorLookup_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hdirect, hnested⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hdirect
  have _ := hnested
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorLookup_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hdirect, hnested⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hdirect
  have _ := hnested
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorFieldsLookup_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hfields⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorFieldsLookup_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hmetadata, hfields⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hmetadata
  have _ := hfields
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorArity_of_restorationStages hmap hresult typeIndex htype ctorIndex hctor
  obtain ⟨allowPrimitive, preprocessing, staged, info, hpre, hrun, hlookup, hfields, htotal⟩ := h
  have _allowPrimitive : Bool := allowPrimitive
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hfields
  have _ := htotal
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) : True := by
  have h := addDecl.sourceConstructorArity_of_checkedPrimitive hmap hcheck hresult typeIndex htype ctorIndex hctor
  obtain ⟨preprocessing, staged, info, hpre, hrun, hlookup, hfields, htotal⟩ := h
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _info : ConstructorVal := info
  have _ := hpre
  have _ := hrun
  have _ := hlookup
  have _ := hfields
  have _ := htotal
  trivial

example {ctx : AddInductive.Context} {safety : DefinitionSafety} {venv : VEnv}
    {types : List InductiveType} {numParams numNested : Nat} {isUnsafe : Bool}
    (hchecker : CheckerEnv safety ctx.env venv)
    (shape : Environment.PrimitiveInductiveDecl ctx.lparams numParams types isUnsafe) :
    (AddInductive.checkInductiveTypes numParams types.toArray (fun stats => do
      AddInductive.withEnv
        (← AddInductive.declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
          AddInductive.checkConstructors types.toArray stats isUnsafe
          AddInductive.declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) = some ctorEnv ∧
        ctorEnv.WF ∧ CheckerEnv safety env' ctorEnv := by
  exact AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerWithModel
    ctx numParams types numNested isUnsafe hchecker
    ((Environment.checkPrimitiveInductive.eq_true_iff ctx.env ctx.lparams numParams types isUnsafe).mpr shape)

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (venv : VEnv) : True := by
  obtain ⟨decl, hkind, hheaders, hdeclWF, htranslation, hscope⟩ :=
    addDecl.checkedPrimitiveFrontendAndModel hmap hcheck hresult venv
  have _decl : VInductDecl := decl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hlookups, hchecker⟩ :=
    addDecl.checkedPrimitiveModelAndRecursorStages hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hlookups
  have _ := hchecker
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
      hlookups, hbranch, hfinal⟩ :=
    addDecl.checkedPrimitiveModelAndGeneratedRuleIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hfinal
  trivial

/- Regression: the checked-primitive restoration boundary keeps the generated
   rule result and its paired base/target iota endpoints on one witness. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
      hlookups, hbranch, hfinal⟩ :=
    addDecl.checkedPrimitiveModelAndGeneratedRuleResultAndIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have hPlural :=
    addDecl.checkedPrimitiveModelAndGeneratedRuleResultsAndIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hfinal
  have _ := hPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hrestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredRuleIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hrestored
  trivial

/- Regression: restored-record evidence retains the generated rule result and
   its paired base/target iota endpoints under the same witness. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 →
      ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry,
          (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (venv : VEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hrestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredRuleResultAndIotaBaseAndTargetResultsEvidence hmap hcheck hresult coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hrestored
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (venv : VEnv) : True := by
  have _combined :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredRuleEvidence hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hrecursor hentry ruleResult
      hrecursors venv
  obtain ⟨modelDeclCombined, hkindCombined, hheadersCombined, hdeclWFCombined,
      htranslationCombined, hregistrationCombined,
      ⟨preprocessingCombined, stagedCombined, statsCombined, rootCombined,
        constructorsCombined, elimLevelCombined, infosCombined, sourceCombined,
        hpreCombined, hrunCombined, hscopeCombined, hprefixCombined, hlookupsCombined,
        hsemanticCombined⟩⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hresultConstants history hsource
      hvalues ruleResult hrecursor hentry hrecursors venv
  have _modelDeclCombined : VInductDecl := modelDeclCombined
  have _ := hkindCombined
  have _ := hheadersCombined
  have _ := hdeclWFCombined
  have _ := htranslationCombined
  have _ := hregistrationCombined
  have _preCombined : ElimNestedInductive.Result := preprocessingCombined
  have _stagedCombined : Kernel.Environment := stagedCombined
  have _statsCombined : AddInductive.InductiveStats := statsCombined
  have _rootCombined : AddInductive.Context := rootCombined
  have _constructorsCombined : Kernel.Environment := constructorsCombined
  have _elimLevelCombined : Level := elimLevelCombined
  have _infosCombined : Array AddInductive.RecInfo := infosCombined
  have _sourceCombined : AddInductive.Context := sourceCombined
  have _ := hpreCombined
  have _ := hrunCombined
  have _ := hscopeCombined
  have _ := hprefixCombined
  have _ := hlookupsCombined
  have _ := hsemanticCombined
  obtain ⟨modelDeclRestored, hkindRestored, hheadersRestored, hdeclWFRestored,
      htranslationRestored,
      ⟨preprocessingRestored, stagedRestored, statsRestored, rootRestored,
        constructorsRestored, elimLevelRestored, infosRestored, sourceRestored,
        hpreRestored, hrunRestored, hscopeRestored, hprefixRestored, hlookupsRestored,
        hsemanticRestored, hfinalRestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentSemantics hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult
      hrecursor hentry venv
  have _modelDeclRestored : VInductDecl := modelDeclRestored
  have _kindRestored := hkindRestored
  have _headersRestored := hheadersRestored
  have _declWFRestored := hdeclWFRestored
  have _translationRestored := htranslationRestored
  have _preRestored : ElimNestedInductive.Result := preprocessingRestored
  have _stagedRestored : Kernel.Environment := stagedRestored
  have _statsRestored : AddInductive.InductiveStats := statsRestored
  have _rootRestored : AddInductive.Context := rootRestored
  have _constructorsRestored : Kernel.Environment := constructorsRestored
  have _elimLevelRestored : Level := elimLevelRestored
  have _infosRestored : Array AddInductive.RecInfo := infosRestored
  have _sourceRestored : AddInductive.Context := sourceRestored
  have _ := hpreRestored
  have _ := hrunRestored
  have _ := hscopeRestored
  have _ := hprefixRestored
  have _ := hlookupsRestored
  have _ := hsemanticRestored
  have _ := hfinalRestored
  obtain ⟨modelDeclRestoredIota, hkindRestoredIota, hheadersRestoredIota,
      hdeclWFRestoredIota, htranslationRestoredIota,
      ⟨preprocessingRestoredIota, stagedRestoredIota, statsRestoredIota,
        rootRestoredIota, constructorsRestoredIota, elimLevelRestoredIota,
        infosRestoredIota, sourceRestoredIota, hpreRestoredIota,
        hrunRestoredIota, hscopeRestoredIota, hprefixRestoredIota,
        hlookupsRestoredIota, hsemanticRestoredIota, hfinalRestoredIota⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants
      hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDeclRestoredIota : VInductDecl := modelDeclRestoredIota
  have _ := hkindRestoredIota
  have _ := hheadersRestoredIota
  have _ := hdeclWFRestoredIota
  have _ := htranslationRestoredIota
  have _preRestoredIota : ElimNestedInductive.Result := preprocessingRestoredIota
  have _stagedRestoredIota : Kernel.Environment := stagedRestoredIota
  have _statsRestoredIota : AddInductive.InductiveStats := statsRestoredIota
  have _rootRestoredIota : AddInductive.Context := rootRestoredIota
  have _constructorsRestoredIota : Kernel.Environment := constructorsRestoredIota
  have _elimLevelRestoredIota : Level := elimLevelRestoredIota
  have _infosRestoredIota : Array AddInductive.RecInfo := infosRestoredIota
  have _sourceRestoredIota : AddInductive.Context := sourceRestoredIota
  have _ := hpreRestoredIota
  have _ := hrunRestoredIota
  have _ := hscopeRestoredIota
  have _ := hprefixRestoredIota
  have _ := hlookupsRestoredIota
  have _ := hsemanticRestoredIota
  have _ := hfinalRestoredIota
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
        hlookups, hbranch, hsemantic⟩⟩ :=
    addDecl.checkedPrimitiveModelAndAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _combinedAlignment :=
    addDecl.checkedPrimitiveModelAndAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants hresultConstants
      history hsource hvalues ruleResult hrecursor hentry venv
  have _combinedAlignmentPlural :=
    addDecl.checkedPrimitiveModelAndAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants hresultConstants
      history hsource hvalues ruleResult hrecursor hentry venv
  have _ := _combinedAlignment
  have _ := _combinedAlignmentPlural
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hsemantic
  trivial

/- Regression: restored alignment semantics retain the generated rule result
   and paired base/target iota endpoints under one witness. -/
/- Regression: constructive restored alignment retains the generated rule
   result and paired base/target iota endpoints under one witness. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (venv : VEnv) : True := by
  have _combined :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredRuleEvidence hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hrecursor hentry ruleResult
      hrecursors venv
  obtain ⟨modelDeclCombined, hkindCombined, hheadersCombined, hdeclWFCombined,
      htranslationCombined, hregistrationCombined,
      ⟨preprocessingCombined, stagedCombined, statsCombined, rootCombined,
        constructorsCombined, elimLevelCombined, infosCombined, sourceCombined,
        hpreCombined, hrunCombined, hscopeCombined, hprefixCombined, hlookupsCombined,
        hsemanticCombined⟩⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hresultConstants history hsource
      hvalues ruleResult hrecursor hentry hrecursors venv
  have _combinedConstructivePlural :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hresultConstants history hsource
      hvalues ruleResult hrecursor hentry hrecursors venv
  have _modelDeclCombined : VInductDecl := modelDeclCombined
  have _ := hkindCombined
  have _ := hheadersCombined
  have _ := hdeclWFCombined
  have _ := htranslationCombined
  have _ := hregistrationCombined
  have _preCombined : ElimNestedInductive.Result := preprocessingCombined
  have _stagedCombined : Kernel.Environment := stagedCombined
  have _statsCombined : AddInductive.InductiveStats := statsCombined
  have _rootCombined : AddInductive.Context := rootCombined
  have _constructorsCombined : Kernel.Environment := constructorsCombined
  have _elimLevelCombined : Level := elimLevelCombined
  have _infosCombined : Array AddInductive.RecInfo := infosCombined
  have _sourceCombined : AddInductive.Context := sourceCombined
  have _ := hpreCombined
  have _ := hrunCombined
  have _ := hscopeCombined
  have _ := hprefixCombined
  have _ := hlookupsCombined
  have _ := hsemanticCombined
  have _ := _combinedConstructivePlural
  obtain ⟨modelDeclRestored, hkindRestored, hheadersRestored, hdeclWFRestored,
      htranslationRestored,
      ⟨preprocessingRestored, stagedRestored, statsRestored, rootRestored,
        constructorsRestored, elimLevelRestored, infosRestored, sourceRestored,
        hpreRestored, hrunRestored, hscopeRestored, hprefixRestored, hlookupsRestored,
        hsemanticRestored, hfinalRestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentSemantics hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult
      hrecursor hentry venv
  have _modelDeclRestored : VInductDecl := modelDeclRestored
  have _kindRestored := hkindRestored
  have _headersRestored := hheadersRestored
  have _declWFRestored := hdeclWFRestored
  have _translationRestored := htranslationRestored
  have _preRestored : ElimNestedInductive.Result := preprocessingRestored
  have _stagedRestored : Kernel.Environment := stagedRestored
  have _statsRestored : AddInductive.InductiveStats := statsRestored
  have _rootRestored : AddInductive.Context := rootRestored
  have _constructorsRestored : Kernel.Environment := constructorsRestored
  have _elimLevelRestored : Level := elimLevelRestored
  have _infosRestored : Array AddInductive.RecInfo := infosRestored
  have _sourceRestored : AddInductive.Context := sourceRestored
  have _ := hpreRestored
  have _ := hrunRestored
  have _ := hscopeRestored
  have _ := hprefixRestored
  have _ := hlookupsRestored
  have _ := hsemanticRestored
  have _ := hfinalRestored
  obtain ⟨modelDeclRestoredIota, hkindRestoredIota, hheadersRestoredIota,
      hdeclWFRestoredIota, htranslationRestoredIota,
      ⟨preprocessingRestoredIota, stagedRestoredIota, statsRestoredIota,
        rootRestoredIota, constructorsRestoredIota, elimLevelRestoredIota,
        infosRestoredIota, sourceRestoredIota, hpreRestoredIota,
        hrunRestoredIota, hscopeRestoredIota, hprefixRestoredIota,
        hlookupsRestoredIota, hsemanticRestoredIota, hfinalRestoredIota⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants
      hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDeclRestoredIota : VInductDecl := modelDeclRestoredIota
  have _ := hkindRestoredIota
  have _ := hheadersRestoredIota
  have _ := hdeclWFRestoredIota
  have _ := htranslationRestoredIota
  have _preRestoredIota : ElimNestedInductive.Result := preprocessingRestoredIota
  have _stagedRestoredIota : Kernel.Environment := stagedRestoredIota
  have _statsRestoredIota : AddInductive.InductiveStats := statsRestoredIota
  have _rootRestoredIota : AddInductive.Context := rootRestoredIota
  have _constructorsRestoredIota : Kernel.Environment := constructorsRestoredIota
  have _elimLevelRestoredIota : Level := elimLevelRestoredIota
  have _infosRestoredIota : Array AddInductive.RecInfo := infosRestoredIota
  have _sourceRestoredIota : AddInductive.Context := sourceRestoredIota
  have _ := hpreRestoredIota
  have _ := hrunRestoredIota
  have _ := hscopeRestoredIota
  have _ := hprefixRestoredIota
  have _ := hlookupsRestoredIota
  have _ := hsemanticRestoredIota
  have _ := hfinalRestoredIota
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
        hlookups, hbranch, hsemantic⟩⟩ :=
    addDecl.checkedPrimitiveModelAndAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hsemantic
  trivial

/- Regression: restored alignment semantics retain the generated rule result
   and paired base/target iota endpoints under one witness. -/
example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types true fuel)
    (entries : ElimNestedInductive.Result → Kernel.Environment → List RegistrationEntry)
    (records_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      restoredEnvironmentRecords preprocessing staged types =
        (entries preprocessing staged).map RegistrationEntry.toConstantInfo)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (entry_eq : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → entries preprocessing staged = producer.orderedEntries)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length) (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) → recursor.name = mkRecName types[index].name)
    (hentry : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams true fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → ∀ (index : Nat) (hindex : index < types.length),
        ∃ entry : RecursorEntry, (.recursor entry : RegistrationEntry) ∈ entries preprocessing staged ∧
          entry.info.name = mkRecName types[index].name)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (venv : VEnv) : True := by
  have _combined :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredRuleEvidence hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hrecursor hentry ruleResult
      hrecursors venv
  obtain ⟨modelDeclCombined, hkindCombined, hheadersCombined, hdeclWFCombined,
      htranslationCombined, hregistrationCombined,
      ⟨preprocessingCombined, stagedCombined, statsCombined, rootCombined,
        constructorsCombined, elimLevelCombined, infosCombined, sourceCombined,
        hpreCombined, hrunCombined, hscopeCombined, hprefixCombined, hlookupsCombined,
        hsemanticCombined⟩⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRestoredAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult
      coverage entries records_eq producer entry_eq hconstants hresultConstants history hsource
      hvalues ruleResult hrecursor hentry hrecursors venv
  have _modelDeclCombined : VInductDecl := modelDeclCombined
  have _ := hkindCombined
  have _ := hheadersCombined
  have _ := hdeclWFCombined
  have _ := htranslationCombined
  have _ := hregistrationCombined
  have _preCombined : ElimNestedInductive.Result := preprocessingCombined
  have _stagedCombined : Kernel.Environment := stagedCombined
  have _statsCombined : AddInductive.InductiveStats := statsCombined
  have _rootCombined : AddInductive.Context := rootCombined
  have _constructorsCombined : Kernel.Environment := constructorsCombined
  have _elimLevelCombined : Level := elimLevelCombined
  have _infosCombined : Array AddInductive.RecInfo := infosCombined
  have _sourceCombined : AddInductive.Context := sourceCombined
  have _ := hpreCombined
  have _ := hrunCombined
  have _ := hscopeCombined
  have _ := hprefixCombined
  have _ := hlookupsCombined
  have _ := hsemanticCombined
  obtain ⟨modelDeclRestored, hkindRestored, hheadersRestored, hdeclWFRestored,
      htranslationRestored,
      ⟨preprocessingRestored, stagedRestored, statsRestored, rootRestored,
        constructorsRestored, elimLevelRestored, infosRestored, sourceRestored,
        hpreRestored, hrunRestored, hscopeRestored, hprefixRestored, hlookupsRestored,
        hsemanticRestored, hfinalRestored⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentSemantics hmap hcheck hresult coverage entries
      records_eq producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult
      hrecursor hentry venv
  have _modelDeclRestored : VInductDecl := modelDeclRestored
  have _kindRestored := hkindRestored
  have _headersRestored := hheadersRestored
  have _declWFRestored := hdeclWFRestored
  have _translationRestored := htranslationRestored
  have _preRestored : ElimNestedInductive.Result := preprocessingRestored
  have _stagedRestored : Kernel.Environment := stagedRestored
  have _statsRestored : AddInductive.InductiveStats := statsRestored
  have _rootRestored : AddInductive.Context := rootRestored
  have _constructorsRestored : Kernel.Environment := constructorsRestored
  have _elimLevelRestored : Level := elimLevelRestored
  have _infosRestored : Array AddInductive.RecInfo := infosRestored
  have _sourceRestored : AddInductive.Context := sourceRestored
  have _ := hpreRestored
  have _ := hrunRestored
  have _ := hscopeRestored
  have _ := hprefixRestored
  have _ := hlookupsRestored
  have _ := hsemanticRestored
  have _ := hfinalRestored
  obtain ⟨modelDeclRestoredIota, hkindRestoredIota, hheadersRestoredIota,
      hdeclWFRestoredIota, htranslationRestoredIota,
      ⟨preprocessingRestoredIota, stagedRestoredIota, statsRestoredIota,
        rootRestoredIota, constructorsRestoredIota, elimLevelRestoredIota,
        infosRestoredIota, sourceRestoredIota, hpreRestoredIota,
        hrunRestoredIota, hscopeRestoredIota, hprefixRestoredIota,
        hlookupsRestoredIota, hsemanticRestoredIota, hfinalRestoredIota⟩⟩ :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentGeneratedRuleResultAndIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants
      hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _combinedRestoredPlural :=
    addDecl.checkedPrimitiveModelAndRestoredAlignmentGeneratedRuleResultsAndIotaBaseAndTargetResultsSemantics
      hmap hcheck hresult coverage entries records_eq producer entry_eq hconstants
      hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDeclRestoredIota : VInductDecl := modelDeclRestoredIota
  have _ := hkindRestoredIota
  have _ := hheadersRestoredIota
  have _ := hdeclWFRestoredIota
  have _ := htranslationRestoredIota
  have _preRestoredIota : ElimNestedInductive.Result := preprocessingRestoredIota
  have _stagedRestoredIota : Kernel.Environment := stagedRestoredIota
  have _statsRestoredIota : AddInductive.InductiveStats := statsRestoredIota
  have _rootRestoredIota : AddInductive.Context := rootRestoredIota
  have _constructorsRestoredIota : Kernel.Environment := constructorsRestoredIota
  have _elimLevelRestoredIota : Level := elimLevelRestoredIota
  have _infosRestoredIota : Array AddInductive.RecInfo := infosRestoredIota
  have _sourceRestoredIota : AddInductive.Context := sourceRestoredIota
  have _ := hpreRestoredIota
  have _ := hrunRestoredIota
  have _ := hscopeRestoredIota
  have _ := hprefixRestoredIota
  have _ := hlookupsRestoredIota
  have _ := hsemanticRestoredIota
  have _ := hfinalRestoredIota
  have _ := _combinedRestoredPlural
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
        hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
        hlookups, hbranch, hsemantic⟩⟩ :=
    addDecl.checkedPrimitiveModelAndAlignmentIotaBaseAndTargetResultsSemantics hmap hcheck hresult coverage entries records_eq
      producer entry_eq hconstants hresultConstants history hsource hvalues ruleResult hrecursor hentry venv
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _preprocessing : ElimNestedInductive.Result := preprocessing
  have _staged : Kernel.Environment := staged
  have _stats : AddInductive.InductiveStats := stats
  have _root : AddInductive.Context := root
  have _constructors : Kernel.Environment := constructors
  have _elimLevel : Level := elimLevel
  have _infos : Array AddInductive.RecInfo := infos
  have _source : AddInductive.Context := source
  have _ := hpre
  have _ := hrun
  have _ := hscope
  have _ := hprefix
  have _ := hframe
  have _ := hcounts
  have _ := hindexing
  have _ := hdistinct
  have _ := hsources
  have _ := hlookups
  have _ := hbranch
  have _ := hsemantic
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRegistration (venv := venv) hmap hcheck hresult
      producer hconstants hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hregistration, hlookup⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationAndOrderedEntryLookup hmap hcheck hresult
      producer hconstants hresultConstants hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _registration := hregistration
  have _lookup := hlookup
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, allowPrimitive,
      hscope, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveHistory_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := hscope
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, allowPrimitive,
      hscope, hregistration⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveRegistration_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration,
      hhistory⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveHistory (venv := venv) hmap hcheck hresult
      producer hconstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, haligned, hmap', hhistory,
      hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndCheckerHistory (venv := venv) hmap hcheck hresult producer
      hconstants hresultConstants history hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  have hCombined :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_sourceTypehood
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
      ruleResults
  have hPluralCombined :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
      ruleResults
  have _ := hCombined
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
    hvalues ruleResults
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults
  have _ := hOrdinary
  have _ := hGenerated
  have _ := hGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults
  have _ := hOrdinary
  have _ := hGenerated
  have _ := hGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hGenerated :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults
  have hGeneratedPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults
  have _ := hOrdinary
  have _ := hGenerated
  have _ := hGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hscope, hregistration,
      haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood (venv := venv)
      hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _scope := hscope
  have _registration := hregistration
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
    ruleResults
  have hOrdinaryIota := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
    ruleResults
  have hOrdinaryPair := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
    ruleResults
  have hOrdinaryGenerated := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
    ruleResults
  have hOrdinaryGeneratedPlural := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_sourceTypehood_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource hvalues
    ruleResults
  have _ := hOrdinary
  have _ := hOrdinaryIota
  have _ := hOrdinaryPair
  have _ := hOrdinaryGenerated
  have _ := hOrdinaryGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hregistration⟩ :=
    addDecl.checkedPrimitiveRegistrationRealization hmap hcheck hresult producer hconstants
      hresultConstants hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationAndHistory hmap hcheck hresult producer
      hconstants hresultConstants history hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨scope, hmodelResult, hmap, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment hmap hcheck hresult
      producer hconstants hresultConstants history hrecursors
  have _scope := scope
  have _modelResult := hmodelResult
  have _map := hmap
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationAndHistory_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAlignmentAndRegistration_of_restorationStages
      hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation,
      allowPrimitive, scope, hmodelResult, hmapResult, hregistration, hhistory,
      haligned⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveAlignmentPackage_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _allowPrimitive : Bool := allowPrimitive
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _registration := hregistration
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  obtain ⟨modelDecl, hkind, hheaders, hdeclWF, htranslation, hmetadata, hscope,
      hregistration, haligned, hmap', hhistory, hchecker, hresults⟩ :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults
  have _modelDecl : VInductDecl := modelDecl
  have _kind := hkind
  have _headers := hheaders
  have _declWF := hdeclWF
  have _translation := htranslation
  have _metadata := hmetadata
  have _scope := hscope
  have _registration := hregistration
  have _aligned := haligned
  have _map := hmap'
  have _history := hhistory
  have _checker := hchecker
  have _results := hresults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) : True := by
  obtain ⟨hscope, hregistration⟩ :=
    metadata.toFrontendScopeAndConstructiveRegistration producer hconstants hrecursors
  have _scope := hscope
  have _registration := hregistration
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) : True := by
  obtain ⟨scope, hmodelResult, hmapResult, hhistory, haligned⟩ :=
    addDecl.checkedPrimitiveRegistrationRealizationHistoryAndAlignment_of_sourceTypehood
      hmap hcheck hresult producer hconstants hresultConstants history hsource
  have _scope := scope
  have _modelResult := hmodelResult
  have _mapResult := hmapResult
  have _history := hhistory
  have _aligned := haligned
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result) : True := by
  obtain ⟨scope, hpreserves⟩ :=
    addDecl.checkedPrimitiveFrontendPreserves hmap hcheck hresult
  have _scope := scope
  have _preserves := hpreserves
  trivial

example {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} (evidence : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult) {stats : AddInductive.InductiveStats}
    {infos : Array AddInductive.RecInfo} {source : AddInductive.Context}
    {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (entry : RecursorEntry) (hentry : entry ∈ evidence.recursors)
    (rule : RecursorRule) (hrule : rule ∈ entry.info.rules) : True := by
  obtain ⟨constructor, minor, hiota⟩ :=
    evidence.recursorGeneratedRuleIotaKind ruleResults entry hentry rule hrule
  have targetResult := hiota.targetResult
  let targetResult' := targetResult
  obtain ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
      htranslated, htyped, hkind⟩ := targetResult
  have _constructor : Constructor := constructor
  have _minor : Expr := minor
  have _target : TypeChecker.MLCtx := target
  have _count : Nat := count
  have _arguments : List VExpr := arguments
  have _replacements : List Expr := replacements
  have _resultType : VExpr := resultType
  have _insertionLift : Lift := insertionLift
  have _rhsSemantic : VExpr := rhsSemantic
  have _translated := htranslated
  have _typed := htyped
  have _kind := hkind
  have _typedProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.hasType targetResult'
  have _sortProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.sortArity targetResult'
  have _translatedProjection := AddInductive.GeneratedRecursorRuleIotaTargetResult.translated targetResult'
  have _baseProjection := hiota.baseResult
  have _sharedProjection := hiota.baseAndTargetResults
  have _pairedBaseProjection := AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults.baseResult
    hiota.baseAndTargetResults
  have _pairedTargetProjection := AddInductive.GeneratedRecursorRuleIotaBaseAndTargetResults.targetResult
    hiota.baseAndTargetResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hrecursors : ∀ entry ∈ producer.recursors, entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hPlural := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_restorationStages
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinary := addDecl.checkedPrimitiveModelAndConstructiveCheckerPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryIota := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryPair := addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryGenerated := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have hOrdinaryGeneratedPlural := addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaBaseAndTargetResultsPackage_of_restorationStages_toCheckerEnv
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
    hsource hvalues ruleResults
  have _ := hOrdinary
  have _ := hOrdinaryIota
  have _ := hOrdinaryPair
  have _ := hOrdinaryGenerated
  have _ := hOrdinaryGeneratedPlural
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := scope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := metadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndCheckerHistoryIotaBaseAndTargetResults
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
    hsource hvalues ruleResults
  have hRestoration :=
    addDecl.checkedPrimitiveModelAndCheckerHistory_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
      hsource hvalues ruleResults
  have hRestorationIota :=
    addDecl.checkedPrimitiveModelAndCheckerHistoryIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
      hsource hvalues ruleResults
  have hRestorationCombined :=
    addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
      hsource hvalues ruleResults
  have hRestorationPluralCombined :=
    addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultsAndIotaBaseAndTargetResults_of_restorationStages
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
      hsource hvalues ruleResults
  have _ := hRestoration
  have _ := hRestorationIota
  have _ := hRestorationCombined
  trivial

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultAndIotaBaseAndTargetResults
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
    hsource hvalues ruleResults
  have hPlural := addDecl.checkedPrimitiveModelAndCheckerHistoryGeneratedRuleResultsAndIotaBaseAndTargetResults
    (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history
    hsource hvalues ruleResults
  trivial

example {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} (producer : RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ entry ∈ producer.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) : True := by
  have h := addDecl.orderedGeneratedRuleIotaBaseAndTargetResults_of_generatedRuleResults
    producer ruleResults
  have hCombined := addDecl.orderedGeneratedRuleResultAndIotaBaseAndTargetResults_of_generatedRuleResults
    producer ruleResults
  have hPluralCombined := addDecl.orderedGeneratedRuleResultsAndIotaBaseAndTargetResults_of_generatedRuleResults
    producer ruleResults
  trivial

example {m : Type → Type} [Monad m]
    {environment : Kernel.Environment} {expression reduced : Expr}
    {normalize infer : Expr → m Expr} {compare : Expr → Expr → m Bool}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {check : Bool} {fuel : FuelConfig}
    (hmap : env.constants.WF)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types false = .ok true)
    (hresult : addDecl env (.inductDecl lparams nparams types false) check fuel = .ok result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool} {venv : VEnv}
    (producer : RegistrationEvidence constants semanticEnv decl resultConstants semanticResult)
    (hconstants : env.constants = constants) (hresultConstants : result.constants = resultConstants)
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (envWF : semanticEnv.WF)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci → .safe ≤ ci.safety → ci.safety = .safe →
      ci.value? = some value → TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (targetWF : ∀ target : TypeChecker.MLCtx, target.WF semanticEnv universes)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (reduction : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ (rule : RecursorRule), rule ∈ entry.info.rules →
      ∀ (constructor : Constructor) (minor : Expr),
      ∀ (target : TypeChecker.MLCtx) (count : Nat) (arguments : List VExpr)
        (resultType : VExpr) (insertionLift : Lift) (replacements : List Expr)
        (rhsSemantic : VExpr),
        TrExprS semanticEnv universes target.vlctx (rule.rhs.mkAppList replacements)
          (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
            (arguments.map (VExpr.lift' · insertionLift))) →
        semanticEnv.HasType universes.length target.vlctx.toCtx
          (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
            (arguments.map (VExpr.lift' · insertionLift)))
          (resultType.lift' insertionLift) →
        semanticEnv.SortArity universes.length target.vlctx.toCtx count
          (resultType.lift' insertionLift) →
        inductiveReduceRec environment expression normalize infer compare = pure (some reduced) ∧
        reduced = rule.rhs.mkAppList replacements)
    (reductionExact : ∀ (entry : RecursorEntry), entry ∈ producer.recursors →
      ∀ (rule : RecursorRule), rule ∈ entry.info.rules →
      ∀ (constructor : Constructor) (minor : Expr),
      ∀ (target : TypeChecker.MLCtx) (count : Nat) (arguments : List VExpr)
        (resultType : VExpr) (insertionLift : Lift) (replacements : List Expr)
        (rhsSemantic : VExpr),
        TrExprS semanticEnv universes target.vlctx (rule.rhs.mkAppList replacements)
          (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
            (arguments.map (VExpr.lift' · insertionLift))) →
        semanticEnv.HasType universes.length target.vlctx.toCtx
          (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
            (arguments.map (VExpr.lift' · insertionLift)))
          (resultType.lift' insertionLift) →
        semanticEnv.SortArity universes.length target.vlctx.toCtx count
          (resultType.lift' insertionLift) →
        inductiveReduceRec environment expression normalize infer compare =
          pure (some (rule.rhs.mkAppList replacements))) : True := by
  have hRest :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reduction
  have hRestPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reduction
  have hSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reduction
  have hSourcePlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reduction
  have hSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reduction
  have hSourceRestorationPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reduction
  have hExactReduction :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactReductionPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactReductionSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactReductionSourcePlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactReductionSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactReductionSourceRestorationPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactResultRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactResultsRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactResultSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactResultsSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactResultSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactResultsSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactIotaReductionRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactIotaReductionSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactIotaReductionSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetReductionPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactIotaResultRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hrecursors
      hsource hvalues ruleResults reductionExact
  have hExactIotaResultSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactIotaResultSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetResultPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history hsource
      hvalues ruleResults reductionExact
  have hExactIotaOrdinaryRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hrecursors
      hsource hvalues targetWF ruleResults reductionExact
  have hExactIotaOrdinarySource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have hExactIotaOrdinarySourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have hOrdinary :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hrecursors
      hsource hvalues targetWF ruleResults reduction
  have hOrdinaryPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hrecursors
      hsource hvalues targetWF ruleResults reduction
  have hOrdinarySource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reduction
  have hOrdinarySourcePlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reduction
  have hOrdinarySourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reduction
  have hOrdinarySourceRestorationPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStages_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reduction
  have hExact :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hrecursors
      hsource hvalues targetWF ruleResults reductionExact
  have hExactPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hrecursors
      hsource hvalues targetWF ruleResults reductionExact
  have hExactSource :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have hExactSourcePlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehoodExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have hExactSourceRestoration :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have hExactSourceRestorationPlural :=
    addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultsAndIotaTargetOrdinaryPackage_of_sourceTypehood_and_restorationStagesExact_toCheckerEnv
      (venv := venv) hmap hcheck hresult producer hconstants hresultConstants history envWF hsource
      hvalues targetWF ruleResults reductionExact
  have _ := hRest
  have _ := hRestPlural
  have _ := hSource
  have _ := hSourcePlural
  have _ := hSourceRestoration
  have _ := hSourceRestorationPlural
  have _ := hExactReduction
  have _ := hExactReductionPlural
  have _ := hExactReductionSource
  have _ := hExactReductionSourcePlural
  have _ := hExactReductionSourceRestoration
  have _ := hExactReductionSourceRestorationPlural
  have _ := hExactResultRestoration
  have _ := hExactResultsRestoration
  have _ := hExactResultSource
  have _ := hExactResultsSource
  have _ := hExactResultSourceRestoration
  have _ := hExactResultsSourceRestoration
  have _ := hExactIotaReductionRestoration
  have _ := hExactIotaReductionSource
  have _ := hExactIotaReductionSourceRestoration
  have _ := hExactIotaResultRestoration
  have _ := hExactIotaResultSource
  have _ := hExactIotaResultSourceRestoration
  have _ := hExactIotaOrdinaryRestoration
  have _ := hExactIotaOrdinarySource
  have _ := hExactIotaOrdinarySourceRestoration
  have _ := hOrdinary
  have _ := hOrdinaryPlural
  have _ := hOrdinarySource
  have _ := hOrdinarySourcePlural
  have _ := hOrdinarySourceRestoration
  have _ := hOrdinarySourceRestorationPlural
  have _ := hExact
  have _ := hExactPlural
  have _ := hExactSource
  have _ := hExactSourcePlural
  have _ := hExactSourceRestoration
  have _ := hExactSourceRestorationPlural
  trivial

run_meta
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx?
      `Lean4Lean.Verify.InductiveNativeRestorationBridge
    | throwError "restored native record bridge module absent"
  for (name, information) in environment.constants do
    if environment.getModuleIdxFor? name == some moduleIndex then
      if information matches .axiomInfo _ then
        throwError "restored native record bridge introduces an axiom: {name}"
      if information.type.hasSorry then
        throwError "restored native record bridge has an admitted type: {name}"
      if let some value := information.value? (allowOpaque := true) then
        if value.hasSorry then
          throwError "restored native record bridge has an admitted value: {name}"
      for dependency in (← collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains dependency do
          throwError "unexpected restored native record bridge dependency {dependency} in {name}"
  logInfo "restored native record bridge: all owned types and proof values checked; only standard logic and the retained translation relation admission are allowed transitively"

end Lean4Lean.Tests.InductiveNativeBridge
