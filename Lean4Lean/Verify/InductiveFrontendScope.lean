import Lean4Lean.Verify.InductiveRunScope
import Lean4Lean.Verify.InductiveSourceChecks
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open ElimNestedInductive (ContextReserved)

def inductivePreprocessing (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) : Except Exception ElimNestedInductive.Result :=
  (ElimNestedInductive.run fuel.inductiveFuel nparams types env).run'
    { lvls := lparams.map .param, newTypes := types.toArray }

def inductiveScopeContext (env : Environment) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig) : AddInductive.Context :=
  { env, allowPrimitive, lparams, fuel, safety := .safe }

def NonNestedInductivePreprocessing (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) : Prop :=
  ∀ preprocessing, inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
    preprocessing.aux2nested.size = 0

structure NonNestedInductiveScope (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (result : Environment) : Prop where
  sources : InductiveSourcesNoMVarNoFVar types
  stages : ∃ preprocessing, inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
    preprocessing.aux2nested.size = 0 ∧
    ∃ (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      stats.SafeRunScope nparams preprocessing.types.toArray 0
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result

theorem NonNestedInductivePreprocessing.of_result {env : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {fuel : FuelConfig}
    {preprocessing : ElimNestedInductive.Result}
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hnoaux : preprocessing.aux2nested.size = 0) :
    NonNestedInductivePreprocessing env lparams nparams types fuel := by
  intro other hother
  have heq : preprocessing = other := Except.ok.inj (hpre.symm.trans hother)
  simpa only [← heq] using hnoaux

theorem NonNestedInductiveScope.preserves {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (hscope : NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result) :
    result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) := by
  obtain ⟨_, _, _, stats, root, constructors, hrun⟩ := hscope.stages
  exact ⟨hrun.resultWF, hrun.toSafeRunRegistration.preservesOriginal⟩

theorem NonNestedInductiveScope.localRules {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (hscope : NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (stats : AddInductive.InductiveStats)
      (root : AddInductive.Context) (constructors : Environment)
      (infos : Array AddInductive.RecInfo) (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      preprocessing.aux2nested.size = 0 ∧
      stats.SafeRunScope nparams preprocessing.types.toArray 0
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
      AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source result := by
  obtain ⟨preprocessing, hpre, hnoaux, stats, root, constructors, hrun⟩ := hscope.stages
  obtain ⟨infos, source, hframe, hcounts, hdistinct⟩ := hrun.localRules
  exact ⟨preprocessing, stats, root, constructors, infos, source, hpre, hnoaux, hrun, hframe, hcounts, hdistinct⟩

theorem Environment.addInductive.safeStages (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      InductiveSourcesNoMVarNoFVar types ∧
      ∃ preprocessing, inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        (preprocessing.aux2nested.size = 0 →
          ∃ (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
            stats.SafeRunScope nparams preprocessing.types.toArray 0
              (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result) := by
  unfold Environment.addInductive
  refine (Environment.checkInductiveSources.WF env types).bind ?_
  intro _ hsources
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro _ _
  refine Except.WF.bind (Q := fun preprocessing =>
    inductivePreprocessing env lparams nparams types fuel = .ok preprocessing) (fun _ hpre => hpre) ?_
  intro preprocessing hpre
  dsimp only
  refine (AddInductive.run.safeScope nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) rfl hmap .nil (ContextReserved.empty _)).bind ?_
  intro added hrun
  split
  · rename_i hnoaux
    exact .pure ⟨hsources, preprocessing, hpre, fun _ => by simpa only [hnoaux] using hrun⟩
  · rename_i hnested
    exact fun _ _ => ⟨hsources, preprocessing, hpre, fun hnoaux => False.elim (hnested hnoaux)⟩

theorem Environment.addInductive.safeNonNested (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF)
    (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result := by
  refine (Environment.addInductive.safeStages env lparams nparams types allowPrimitive fuel hmap).mono ?_
  rintro result ⟨hsources, preprocessing, hpre, hbranch⟩
  have hnoaux := hnonNested preprocessing hpre
  exact ⟨hsources, preprocessing, hpre, hnoaux, hbranch hnoaux⟩

theorem Environment.addInductive.safeNonNestedResult (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) (preprocessing : ElimNestedInductive.Result)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing)
    (hnoaux : preprocessing.aux2nested.size = 0) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result :=
  Environment.addInductive.safeNonNested env lparams nparams types allowPrimitive fuel hmap
    (NonNestedInductivePreprocessing.of_result hpre hnoaux)

theorem addDecl.safeNonNestedInductive (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF)
    (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, NonNestedInductiveScope env lparams nparams types allowPrimitive fuel result := by
  unfold addDecl
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro allowPrimitive _
  exact (Environment.addInductive.safeNonNested env lparams nparams types allowPrimitive fuel hmap hnonNested).mono
    fun result hscope => ⟨allowPrimitive, hscope⟩

theorem addDecl.safeNonNestedPreserves (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF)
    (hnonNested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  (addDecl.safeNonNestedInductive env lparams nparams types check fuel hmap hnonNested).mono
    fun _ ⟨_, hscope⟩ => hscope.preserves

namespace AddInductive
open TypeChecker (MLCtx)

theorem InductiveStats.SafeRunScope.registeredScopedTranslatedAppliedRecursorTypes
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes stats types elimLevel lparams
    isK isUnsafe ({ root with env := constructors } : Context) next post envWF constants definitions
    fieldOnly model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    nextWF

/- The frontend scope carries the same concrete generated rule-result package
   as the registration CPS layer.  Keep the complete stored-rule semantics
   callback separate: indexed constructor receipts alone do not cover every
   stored rule. -/
theorem InductiveStats.SafeRunScope.registeredScopedGeneratedRuleResultCPS
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS venv universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult venv universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS venv universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedGeneratedRuleResultCPS stats types elimLevel lparams isK isUnsafe
    ({ root with env := constructors } : Context) next post envWF constants definitions fieldOnly model
    modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    nextWF

theorem InductiveStats.SafeRunScope.registeredScopedGeneratedRuleIotaCPS
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS venv universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult venv universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS venv universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedGeneratedRuleIotaCPS stats types elimLevel lparams isK isUnsafe
    ({ root with env := constructors } : Context) next post envWF constants definitions fieldOnly model
    modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    nextWF

/- Expose the complete generated rule result and its paired base/target iota
   endpoint through the frontend scope wrapper, preserving the same CPS
   registration witness for both continuation premises. -/
theorem InductiveStats.SafeRunScope.registeredScopedGeneratedRuleIotaBaseAndTargetResultsCPS
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS venv universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult venv universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS venv universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedGeneratedRuleIotaCPS stats types elimLevel lparams isK isUnsafe
    ({ root with env := constructors } : Context) next post envWF constants definitions fieldOnly model
    modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    nextWF

/- Expose the complete generated rule result and its paired base/target iota
   endpoint through the frontend scope wrapper, preserving the same CPS
   registration witness for both continuation premises. -/
theorem InductiveStats.SafeRunScope.registeredScopedGeneratedRuleResultAndIotaCPS
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS venv universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult venv universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS venv universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedGeneratedRuleResultAndIotaCPS stats types elimLevel lparams isK isUnsafe
    ({ root with env := constructors } : Context) next post envWF constants definitions fieldOnly model
    modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
      registeredWF retained metadata rhsScope results completeRuleSemantics =>
      nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
        registeredWF retained metadata rhsScope results completeRuleSemantics)

theorem InductiveStats.SafeRunScope.registeredScopedGeneratedRuleResultAndIotaBaseAndTargetResultsCPS
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS venv universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult venv universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt venv universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS venv universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults venv universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS venv universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  have nativeEnvWF : ({ root with env := constructors } : Context).env.constants.WF := by
    simpa only [Context.env] using hscope.registration.resultWF
  exact mkRecInfos.registeredScopedGeneratedRuleResultAndIotaCPS stats types elimLevel lparams isK isUnsafe
    ({ root with env := constructors } : Context) next post envWF constants definitions fieldOnly model
    modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
      registeredWF retained metadata rhsScope results completeRuleSemantics =>
      nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
        registeredWF retained metadata rhsScope results completeRuleSemantics)

theorem InductiveStats.SafeRunScope.registeredScopedTranslatedAppliedInitialAndFinalTypehood
    {ResultType : Type} {venv : VEnv} {universes : List Name}
    {nparams numNested : Nat} {types : Array InductiveType}
    {original root : Context} {constructors registeredEnv : Kernel.Environment}
    (hscope : InductiveStats.SafeRunScope stats nparams types numNested original root constructors
      registeredEnv)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : venv.WF) (constants : CanonicalAnnotationConstants venv)
    (definitions : CanonicalAnnotationDefinitions venv) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF venv universes)
    (native : model.lctx = ({ root with env := constructors } : Context).lctx)
    (reserved : ContextReserved ({ root with env := constructors } : Context).lctx
      ({ root with env := constructors } : Context).ngen)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[]
          ({ root with env := constructors } : Context) result.1 result.2,
        RecursorParentPassTranslationSupport venv universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[]
        ({ root with env := constructors } : Context) parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass venv universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport venv universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context))
        ({ root with env := constructors } : Context)).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) result.1 result.2 model finalModel →
        ∀ parent, parent < types.size →
          RecursorSelectedDomainSupport venv universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      ({ root with env := constructors } : Context).RecursorScopeFrame finalReader →
      RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint venv universes stats types elimLevel
        ({ root with env := constructors } : Context) finalInfos finalReader model finalModel →
      (RecursorInitialTypehood venv universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood venv universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      registeredEnv.constants.WF →
      (∀ name info, ({ root with env := constructors } : Context).env.find? name = some info →
        registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe
          ({ root with env := constructors } : Context)
        next result.1 result.2.1 result.2.2).WF post := by
  refine hscope.registeredScopedTranslatedAppliedRecursorTypes elimLevel lparams isK isUnsafe
    next post envWF constants definitions fieldOnly model modelWF native reserved mapped parentSupport
    minorSupport domainSupport ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope
  have initial : RecursorInitialTypehood venv universes stats types elimLevel finalInfos finalReader
      model lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.rawTypehood, receipt.storedTypehood,
      receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  have final : RecursorFinalTypehood venv universes stats types elimLevel finalInfos finalReader
      finalModel lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.finalRawTypehood, receipt.finalStoredTypehood,
      receipt.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint
    ⟨initial, final⟩ registeredWF retained metadata rhsScope

end AddInductive

end Lean4Lean
