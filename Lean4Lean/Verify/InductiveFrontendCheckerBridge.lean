import Lean4Lean.Verify.InductiveNativeRestorationBridge
import Lean4Lean.Verify.InductiveRestorationRules
import Lean4Lean.Verify.InductiveGeneratedRuleResult

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

theorem SafeInductiveFrontendScope.registrationHistory
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
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult := by
  have hconstantsWF : constants.WF := by
    rw [← hconstants]
    exact scope.originalWF
  refine ⟨hresultConstants, ?_⟩
  exact producer.to_trEnvInductive history hconstantsWF hrecursors

theorem SafeInductiveFrontendScope.registrationHistory_of_sourceTypehood
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact scope.registrationHistory history producer hconstants hresultConstants hrecursors

theorem SafeInductiveFrontendScope.registrationAlignmentHistory
    {safety : DefinitionSafety}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive safety constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult := by
  have hconstantsWF : constants.WF := by
    rw [← hconstants]
    exact scope.originalWF
  have hhistory := producer.to_trEnvInductive history hconstantsWF hrecursors
  exact ⟨hhistory.aligned, hresultConstants, hhistory⟩

theorem SafeInductiveFrontendScope.registrationAlignmentHistory_of_sourceTypehood
    {safety : DefinitionSafety}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive safety constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact scope.registrationAlignmentHistory history producer hconstants hresultConstants hrecursors

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood
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
      TrEnvInductive .safe resultConstants Q semanticResult := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact ⟨scope.toCheckerEnvInductive history producer hconstants hresultConstants
      hrecursors hvalues,
    scope.registrationHistory history producer hconstants hresultConstants hrecursors⟩

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_and_ruleResults
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) := by
  exact ⟨scope.toCheckerEnvInductive history producer hconstants hresultConstants hrecursors hvalues,
    producer.orderedRuleResultsOf ruleResults⟩

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_of_sourceTypehood_and_ruleResults
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  exact scope.toCheckerEnvInductive_and_ruleResults history producer hconstants
    hresultConstants hrecursors hvalues ruleResults

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      result.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr semanticResult ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) := by
  have hchecker := scope.toCheckerEnvInductive_of_sourceTypehood_and_ruleResults
    history producer hconstants hresultConstants hsource hvalues ruleResults
  have hhistory := scope.registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource
  exact ⟨hchecker.1, hhistory.1, hhistory.2, hchecker.2⟩

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
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
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  have hchecker := scope.toCheckerEnvInductive_of_sourceTypehood_and_ruleResults
    history producer hconstants hresultConstants hsource hvalues ruleResults
  have hhistory := scope.registrationHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource
  have hresults : ∀ entry ∈ producer.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
    intro entry hmem
    simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append] at hmem
    rcases hmem with hphase | hrecursors
    · rcases hphase with hheaders | hconstructors
      · rcases List.mem_map.mp hheaders with ⟨header, _, rfl⟩
        exact ⟨trivial, trivial⟩
      · rcases List.mem_map.mp hconstructors with ⟨constructor, _, rfl⟩
        exact ⟨trivial, trivial⟩
    · rcases List.mem_map.mp hrecursors with ⟨recursor, hentry, rfl⟩
      refine ⟨?_, ?_⟩
      · intro rule hrule
        exact producer.recursorRuleTranslation recursor hentry rule hrule
      · intro rule hrule
        obtain ⟨semantic, hsemantic⟩ := producer.recursorRuleTranslation recursor hentry rule hrule
        exact ⟨semantic, hsemantic, ruleResults recursor hentry rule hrule⟩
  exact ⟨hchecker.1, hhistory.1, hhistory.2, hresults⟩

theorem SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
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
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  have hpackage := scope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults
  have halignment := scope.registrationAlignmentHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource
  exact ⟨halignment.1, hpackage.2.1, hpackage.2.2.1, hpackage.1, hpackage.2.2.2⟩

theorem NativeInductive.RegistrationEvidence.recursorGeneratedRuleResult
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} (evidence : NativeInductive.RegistrationEvidence constants
      semanticEnv decl resultConstants semanticResult)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
  intro entry hentry rule hrule
  exact evidence.recursorRuleResult
    (Result := fun _ rule => ∃ (constructor : Constructor) (minor : Expr),
      AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
        (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    ruleResults entry hentry rule hrule

theorem NativeInductive.RegistrationEvidence.orderedGeneratedRuleResults
    {constants : ConstMap} {semanticEnv semanticResult : VEnv} {decl : VInductDecl}
    {resultConstants : ConstMap} (evidence : NativeInductive.RegistrationEvidence constants
      semanticEnv decl resultConstants semanticResult)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ evidence.recursors →
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
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
  intro entry hmem
  simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, _, rfl⟩
      exact ⟨trivial, trivial⟩
    · rcases List.mem_map.mp hconstructors with ⟨constructor, _, rfl⟩
      exact ⟨trivial, trivial⟩
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hentry, rfl⟩
    refine ⟨?_, ?_⟩
    · intro rule hrule
      exact evidence.recursorRuleTranslation recursor hentry rule hrule
    · intro rule hrule
      exact evidence.recursorGeneratedRuleResult ruleResults recursor hentry rule hrule

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

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationRuleResults
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) := by
  exact ⟨restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues,
    restored.registrationRuleResults producer halign ruleResults⟩

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationAlignmentHistory_and_ruleResults_of_sourceTypehood
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have halignment := restored.registrationAlignmentHistory producer halign hconstants
    history history.aligned hrecursors
  have hcheckerRules := restored.toCheckerEnvInductive_and_registrationRuleResults producer
    halign hconstants history hrecursors hvalues ruleResults
  exact ⟨halignment.1, halignment.2.1, halignment.2.2, hcheckerRules.1, hcheckerRules.2⟩

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_and_registrationAlignmentHistory_and_generatedRuleResultSemantics_of_sourceTypehood
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    Aligned .safe resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ entry ∈ restored.entries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have halignment := restored.registrationAlignmentHistory_of_sourceTypehood
    producer halign hconstants history hsource
  have hchecker := restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues
  have hresults := restored.registrationRuleResults
    (Result := fun entry rule => ∃ semantic,
      TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
      ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    producer halign
    (fun entry hentry rule hrule => by
      obtain ⟨semantic, hsemantic⟩ := producer.recursorRuleTranslation entry hentry rule hrule
      exact ⟨semantic, hsemantic, ruleResults entry hentry rule hrule⟩)
  exact ⟨halignment.1, halignment.2.1, halignment.2.2, hchecker, hresults⟩

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
  obtain ⟨recursor, rule, info, _semantic, hresult, hname', hlength, hrule, hctorInfo,
      hmetadata, hfields, hnumFields, hfieldCount, htotal, _hsemantic⟩ :=
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
  obtain ⟨semantic, hsemantic, hresultRule⟩ :=
    producer.recursorRuleResult ruleResult entry hproducer rule hruleMem
  exact ⟨recursor, rule, info, semantic, hresult, hname', hlength, hrule, hctorInfo,
    hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic, hresultRule⟩

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

theorem NativeInductive.RestoredRecordEvidence.sourceRecursorGeneratedRuleResults
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
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : NativeInductive.RecursorEntry,
        (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) :
    ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
      (hctor : ctorIndex < types[index].ctors.length),
      ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
        (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
        (constructor : Constructor) (minor : Expr),
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
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
  intro index hindex ctorIndex hctor
  obtain ⟨entry, recursor, rule, info, semantic, hresult, hentryName, hlength, hrule,
      hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal, hsemantic, hgenerated⟩ :=
    restored.sourceRecursorRules producer halign hlookups hrecursor hentry
      (fun entry hentry rule hrule =>
        ruleResult entry hentry rule hrule)
      index hindex ctorIndex hctor
  obtain ⟨constructor, minor, hgenerated⟩ := hgenerated
  exact ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
    hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
    hsemantic, hgenerated⟩

theorem NativeInductive.RestoredRecordEvidence.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
    (hrecursor : ∀ (index : Nat) (hindex : index < types.length)
      (recursor : RecursorVal),
      result.find? recursor.name = some (.recInfo recursor) →
      recursor.name = mkRecName types[index].name)
    (hentry : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : NativeInductive.RecursorEntry,
        (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      (∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
        (hctor : ctorIndex < types[index].ctors.length),
        ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
          (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
          (constructor : Constructor) (minor : Expr),
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
          ∃ (generatedConstructor : Constructor) (generatedMinor : Expr),
            AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
              (infos.map (·.motive)) (infos.flatMap (·.minors)) source
              generatedConstructor generatedMinor rule) := by
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  refine ⟨restored.toCheckerEnvInductive producer halign hconstants history hrecursors hvalues, ?_⟩
  intro index hindex ctorIndex hctor
  obtain ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
      hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
      hsemantic, hgenerated⟩ := restored.sourceRecursorGeneratedRuleResults producer halign
    hlookups ruleResult hrecursor hentry index hindex ctorIndex hctor
  exact ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
    hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
    hsemantic, ⟨constructor, minor, hgenerated⟩⟩

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

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence
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
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : NativeInductive.RecursorEntry),
      entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
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
          evidence.entries = entries preprocessing staged }) ∧
      (preprocessing.aux2nested.size ≠ 0 →
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
            (constructor : Constructor) (minor : Expr),
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
            ∃ (generatedConstructor : Constructor) (generatedMinor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source
                generatedConstructor generatedMinor rule) := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored⟩ :=
    metadata.sourceRecursorRuleStagesAndRestoredRecordEvidence coverage entries records_eq
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, hrestored, ?_⟩
  intro hnested
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
  intro index hindex ctorIndex hctor
  obtain ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
      hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
      hsemantic, hgenerated⟩ := restored.sourceRecursorGeneratedRuleResults producer halign
    hlookups (fun entry hmem rule hrule => ruleResult stats infos source entry hmem rule hrule)
    hrecursor hentry' index hindex ctorIndex hctor
  exact ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
    hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
    hsemantic, ⟨constructor, minor, hgenerated⟩⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndChecker
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : NativeInductive.RecursorEntry),
      entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
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
          entry.info.name = mkRecName types[index].name) :
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
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q ∧
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
            (constructor : Constructor) (minor : Expr),
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
            ∃ (generatedConstructor : Constructor) (generatedMinor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source
                generatedConstructor generatedMinor rule) := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored, hresults⟩ :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, ?_⟩
  intro hnested
  obtain ⟨⟨restored, hentries⟩⟩ := hrestored hnested
  have halign : restored.entries = producer.orderedEntries := by
    calc
      restored.entries = entries preprocessing staged := hentries
      _ = producer.orderedEntries := entry_eq preprocessing staged hpre hrun hnested
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have hchecker := restored.toCheckerEnvInductive producer halign hconstants history
    hrecursors hvalues
  have hentry' : ∀ (index : Nat) (hindex : index < types.length),
      ∃ entry : NativeInductive.RecursorEntry,
        (.recursor entry : NativeInductive.RegistrationEntry) ∈ restored.entries ∧
        entry.info.name = mkRecName types[index].name := by
    intro index hindex
    obtain ⟨entry, hmem, hname⟩ := hentry preprocessing staged hpre hrun hnested index hindex
    exact ⟨entry, hentries ▸ hmem, hname⟩
  refine ⟨hchecker, ?_⟩
  intro index hindex ctorIndex hctor
  obtain ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
      hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
      hsemantic, hgenerated⟩ := hresults hnested index hindex ctorIndex hctor
  exact ⟨entry, recursor, rule, info, semantic, constructor, minor, hresult, hentryName,
    hlength, hrule, hctorInfo, hmetadata, hfields, hnumFields, hfieldCount, htotal,
    hsemantic, hgenerated⟩

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

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {stats : AddInductive.InductiveStats} {infos : Array AddInductive.RecInfo}
    {source : AddInductive.Context} {universes : List Name}
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
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
          entry.info.name = mkRecName types[index].name) :
    ∃ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q ∧
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
            (constructor : Constructor) (minor : Expr),
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
            ∃ (generatedConstructor : Constructor) (generatedMinor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source
                generatedConstructor generatedMinor rule) := by
  obtain ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups, hrestored, _⟩ :=
    metadata.sourceRecursorRuleResultsAndRestoredRecordEvidence coverage entries records_eq
      producer entry_eq hrecursor
      (fun preprocessing staged hpre hrun hnested index hindex =>
        hentry preprocessing staged hpre hrun hnested index hindex)
      (Result := fun entry rule => ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
      ruleResult
  refine ⟨preprocessing, staged, hpre, hrun, ?_⟩
  intro hnested
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
  exact restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults producer
    halign hconstants history hsource hvalues hlookups ruleResult hrecursor hentry'

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood_and_generatedRuleResults
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : NativeInductive.RecursorEntry),
      entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
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
          entry.info.name = mkRecName types[index].name) :
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
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q ∧
        result.constants = resultConstants ∧
        TrEnvInductive .safe resultConstants Q semanticResult ∧
        ∀ (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
          (hctor : ctorIndex < types[index].ctors.length),
          ∃ (entry : NativeInductive.RecursorEntry) (recursor : RecursorVal)
            (rule : RecursorRule) (info : ConstructorVal) (semantic : VExpr)
            (constructor : Constructor) (minor : Expr),
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
            ∃ (generatedConstructor : Constructor) (generatedMinor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source
                generatedConstructor generatedMinor rule) := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored, hresults⟩ :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, ?_⟩
  intro hnested
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
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have hchecker := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
    producer halign hconstants history hsource hvalues hlookups (ruleResult stats infos source)
      hrecursor hentry'
  have hhistory := restored.registrationHistory producer halign hconstants history hrecursors
  exact ⟨hchecker.1, hhistory.1, hhistory.2, hchecker.2⟩

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResults_of_sourceTypehood
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
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
    (ruleResult : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → ∃ (constructor : Constructor) (minor : Expr),
        AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules,
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  exact metadata.toFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues
    (fun entry hentry rule hrule => ruleResult entry hentry rule hrule)

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
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
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
              TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
              ∃ (constructor : Constructor) (minor : Expr),
                AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                  (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) :=
  metadata.toFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndRegistrationSemantics
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : NativeInductive.RecursorEntry),
      entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
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
          entry.info.name = mkRecName types[index].name) :
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
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        CheckerEnvInductive .safe result semanticResult Q ∧
        result.constants = resultConstants ∧
        TrEnvInductive .safe resultConstants Q semanticResult ∧
        ∀ entry ∈ producer.orderedEntries,
          entry.RuleSemantics semanticResult ∧ match entry with
            | .header _ | .constructor _ => True
            | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
                TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
                ∃ (constructor : Constructor) (minor : Expr),
                  AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                    (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored, _⟩ :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, ?_⟩
  intro hnested
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
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have hchecker := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
    producer halign hconstants history hsource hvalues hlookups (ruleResult stats infos source)
      hrecursor hentry'
  have hhistory := restored.registrationHistory producer halign hconstants history hrecursors
  have hresults : ∀ entry ∈ producer.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
    intro entry hmem
    simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append] at hmem
    rcases hmem with hphase | hrecursors
    · rcases hphase with hheaders | hconstructors
      · rcases List.mem_map.mp hheaders with ⟨header, _, rfl⟩
        exact ⟨trivial, trivial⟩
      · rcases List.mem_map.mp hconstructors with ⟨constructor, _, rfl⟩
        exact ⟨trivial, trivial⟩
    · rcases List.mem_map.mp hrecursors with ⟨recursor, hentry, rfl⟩
      refine ⟨?_, ?_⟩
      · intro rule hrule
        exact producer.recursorRuleTranslation recursor hentry rule hrule
      · intro rule hrule
        obtain ⟨semantic, hsemantic⟩ := producer.recursorRuleTranslation recursor hentry rule hrule
        exact ⟨semantic, hsemantic, ruleResult stats infos source recursor hentry rule hrule⟩
  exact ⟨hchecker.1, hhistory.1, hhistory.2, hresults⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesGeneratedResultsAndAlignmentSemantics
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
        (.const ci.name (VLevel.params ci.levelParams.length)))
    {universes : List Name}
    (ruleResult : ∀ (stats : AddInductive.InductiveStats) (infos : Array AddInductive.RecInfo)
      (source : AddInductive.Context) (entry : NativeInductive.RecursorEntry),
      entry ∈ producer.recursors → ∀ rule, rule ∈ entry.info.rules →
        ∃ (constructor : Constructor) (minor : Expr),
          AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule)
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
          entry.info.name = mkRecName types[index].name) :
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
      RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        Aligned .safe resultConstants semanticResult ∧
        result.constants = resultConstants ∧
        TrEnvInductive .safe resultConstants Q semanticResult ∧
        CheckerEnvInductive .safe result semanticResult Q ∧
        ∀ entry ∈ producer.orderedEntries,
          entry.RuleSemantics semanticResult ∧ match entry with
            | .header _ | .constructor _ => True
            | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
                TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
                ∃ (constructor : Constructor) (minor : Expr),
                  AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                    (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule) := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
      hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored, _⟩ :=
    metadata.sourceRecursorRuleStagesGeneratedResultsAndRestoredRecordEvidence coverage entries
      records_eq producer entry_eq hrecursor hentry ruleResult
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, ?_⟩
  intro hnested
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
  have hrecursors := producer.recursorWF_of_sourceTypehood
    (producer.constructorEnvWF history.wf) hsource
  have hchecker := restored.toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResults
    producer halign hconstants history hsource hvalues hlookups (ruleResult stats infos source)
      hrecursor hentry'
  have hhistory := restored.registrationHistory producer halign hconstants history hrecursors
  have hresults : ∀ entry ∈ producer.orderedEntries,
      entry.RuleSemantics semanticResult ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, ∃ semantic,
            TrExprS semanticResult entry.info.levelParams [] rule.rhs semantic ∧
            ∃ (constructor : Constructor) (minor : Expr),
              AddInductive.GeneratedRecursorRuleResult semanticEnv universes stats
                (infos.map (·.motive)) (infos.flatMap (·.minors)) source constructor minor rule := by
    intro entry hmem
    simp only [NativeInductive.RegistrationEvidence.orderedEntries, List.mem_append] at hmem
    rcases hmem with hphase | hrecursors
    · rcases hphase with hheaders | hconstructors
      · rcases List.mem_map.mp hheaders with ⟨header, _, rfl⟩
        exact ⟨trivial, trivial⟩
      · rcases List.mem_map.mp hconstructors with ⟨constructor, _, rfl⟩
        exact ⟨trivial, trivial⟩
    · rcases List.mem_map.mp hrecursors with ⟨recursor, hentry, rfl⟩
      refine ⟨?_, ?_⟩
      · intro rule hrule
        exact producer.recursorRuleTranslation recursor hentry rule hrule
      · intro rule hrule
        obtain ⟨semantic, hsemantic⟩ := producer.recursorRuleTranslation recursor hentry rule hrule
        exact ⟨semantic, hsemantic, ruleResult stats infos source recursor hentry rule hrule⟩
  exact ⟨hhistory.2.aligned, hhistory.1, hhistory.2, hchecker.1, hresults⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStagesResultsAndRestoredRecordEvidence
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
  obtain ⟨sourcePreprocessing, sourceStaged, stats, root, constructors, elimLevel, infos, source,
      hpreSource, hrunSource, hscope, hprefix, hframe, hcounts, hindexing, hdistinct,
      hsources, hlookups, hbranch, hrestored⟩ :=
    metadata.sourceRecursorRuleStagesAndRestoredRecordEvidence coverage entries records_eq
  obtain ⟨resultPreprocessing, resultStaged, hpreResult, hrunResult, hprefixResult,
      hlookupsResult, hrestoredResult, hresults⟩ :=
    metadata.sourceRecursorRuleResultsAndRestoredRecordEvidence coverage entries records_eq
      producer entry_eq hrecursor hentry ruleResult
  have hpre : sourcePreprocessing = resultPreprocessing :=
    Except.ok.inj (hpreSource.symm.trans hpreResult)
  subst resultPreprocessing
  have hrun : sourceStaged = resultStaged :=
    Except.ok.inj (hrunSource.symm.trans hrunResult)
  subst resultStaged
  exact ⟨sourcePreprocessing, sourceStaged, stats, root, constructors, elimLevel, infos, source,
    hpreSource, hrunSource, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources,
    hlookups, hbranch, hrestored, hresults⟩

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

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_of_frontendSourceTypehood
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
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
  exact metadata.toFrontendScope.toCheckerEnvInductive history producer hconstants
    hresultConstants hrecursors hvalues

theorem SafeInductiveRestorationMetadata.registrationHistory
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hrecursors : ∀ entry ∈ producer.recursors,
      entry.model.toVConstant.WF producer.constructorEnv) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.toFrontendScope.registrationHistory history producer hconstants hresultConstants hrecursors

theorem SafeInductiveRestorationMetadata.registrationHistory_of_sourceTypehood
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive .safe constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.toFrontendScope.registrationHistory_of_sourceTypehood history producer hconstants
    hresultConstants hsource

theorem SafeInductiveRestorationMetadata.registrationAlignmentHistory_of_sourceTypehood
    {safety : DefinitionSafety}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    {constants resultConstants : ConstMap} {semanticEnv semanticResult : VEnv}
    {decl : VInductDecl} {Q : Bool}
    (history : TrEnvInductive safety constants Q semanticEnv)
    (producer : NativeInductive.RegistrationEvidence constants semanticEnv decl
      resultConstants semanticResult)
    (hconstants : env.constants = constants)
    (hresultConstants : result.constants = resultConstants)
    (hsource : ∀ entry ∈ producer.recursors, ∃ semantic,
      TrExprS producer.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      producer.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    Aligned safety resultConstants semanticResult ∧
      result.constants = resultConstants ∧
      TrEnvInductive safety resultConstants Q semanticResult :=
  metadata.toFrontendScope.registrationAlignmentHistory_of_sourceTypehood history producer
    hconstants hresultConstants hsource

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
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
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult :=
  metadata.toFrontendScope.toCheckerEnvInductive_and_registrationHistory_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues

theorem SafeInductiveRestorationMetadata.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    {Result : NativeInductive.RecursorEntry → RecursorRule → Prop}
    {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
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
    (ruleResults : ∀ (entry : NativeInductive.RecursorEntry), entry ∈ producer.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    CheckerEnvInductive .safe result semanticResult Q ∧
      result.constants = resultConstants ∧
      TrEnvInductive .safe resultConstants Q semanticResult ∧
      (∀ entry ∈ producer.orderedEntries,
        entry.RuleSemantics semanticResult ∧ match entry with
          | .header _ | .constructor _ => True
          | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule) :=
  metadata.toFrontendScope.toCheckerEnvInductive_and_registrationHistory_and_ruleResults_of_sourceTypehood
    history producer hconstants hresultConstants hsource hvalues ruleResults

end Lean4Lean
