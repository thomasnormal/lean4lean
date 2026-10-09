import Lean4Lean.Verify.InductiveRunScope
import Lean4Lean.Verify.InductiveSourceChecks

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

end Lean4Lean
