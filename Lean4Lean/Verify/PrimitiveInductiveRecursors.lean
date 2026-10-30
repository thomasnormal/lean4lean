import Lean4Lean.Verify.PrimitiveInductiveRegistration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

private theorem addDecl.safeCanonicalRecursorRegistration
    (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF)
    (hnested : NonNestedInductivePreprocessing env lparams nparams types fuel) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF (fun result =>
      ∃ allowPrimitive preprocessing stats root constructors,
        ∃ (elimLevel : Level) (infos : Array AddInductive.RecInfo)
          (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        preprocessing.aux2nested.size = 0 ∧
        stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) root constructors result ∧
        ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
        AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
        stats.RecursorOffsetMetadata preprocessing.types.toArray elimLevel infos lparams
          source.lctx isK false source result ∧
        (∀ index, index < preprocessing.types.toArray.size → ∃ info : RecursorVal,
          result.find? (mkRecName preprocessing.types.toArray[index]!.name) =
            some (.recInfo info) ∧
          ∃ rules,
            AddInductive.mkRecRules preprocessing.types.toArray elimLevel stats index
              (infos.map (·.motive)) (infos.flatMap (·.minors))
              (AddInductive.recursorMinorOffset preprocessing.types.toArray index) source =
              .ok (rules, AddInductive.recursorMinorOffset preprocessing.types.toArray (index + 1)) ∧
            info.rules = rules ∧
            info = AddInductive.declareRecursors.metadataVal stats preprocessing.types.toArray
              elimLevel infos lparams source.lctx isK false index rules) ∧
        AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos
          source result) := by
  refine (addDecl.safeNonNestedInductive env lparams nparams types check fuel hmap hnested).mono ?_
  rintro result ⟨allowPrimitive, scope⟩
  obtain ⟨preprocessing, hpre, hnoaux, stats, root, constructors, hrun⟩ := scope.stages
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hmetadata, hdistinct⟩ := hrun.recursors
  refine ⟨allowPrimitive, preprocessing, stats, root, constructors, elimLevel, infos, source, isK,
    hpre, hnoaux, ?_, hframe, hcounts, hmetadata, ?_, hdistinct⟩
  · simpa only [hnoaux] using hrun
  · intro index hindex
    obtain ⟨rules, hrules, hfind⟩ := hmetadata index hindex
    refine ⟨_, hfind, rules, hrules, rfl, rfl⟩

theorem addDecl.safeCanonicalBoolRecursors
    (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl [] 0 [canonicalBoolType] false) check fuel).WF (fun result =>
      ∃ allowPrimitive preprocessing stats root constructors,
        ∃ (elimLevel : Level) (infos : Array AddInductive.RecInfo)
          (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env [] 0 [canonicalBoolType] fuel = .ok preprocessing ∧
        preprocessing.aux2nested.size = 0 ∧
        stats.SafeRunScope 0 preprocessing.types.toArray preprocessing.aux2nested.size
          (inductiveScopeContext env [] allowPrimitive fuel) root constructors result ∧
        ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
        AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
        stats.RecursorOffsetMetadata preprocessing.types.toArray elimLevel infos []
          source.lctx isK false source result ∧
        (∀ index, index < preprocessing.types.toArray.size → ∃ info : RecursorVal,
          result.find? (mkRecName preprocessing.types.toArray[index]!.name) =
            some (.recInfo info) ∧
          ∃ rules,
            AddInductive.mkRecRules preprocessing.types.toArray elimLevel stats index
              (infos.map (·.motive)) (infos.flatMap (·.minors))
              (AddInductive.recursorMinorOffset preprocessing.types.toArray index) source =
              .ok (rules, AddInductive.recursorMinorOffset preprocessing.types.toArray (index + 1)) ∧
            info.rules = rules ∧
            info = AddInductive.declareRecursors.metadataVal stats preprocessing.types.toArray
              elimLevel infos [] source.lctx isK false index rules) ∧
        AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos
          source result) :=
  addDecl.safeCanonicalRecursorRegistration env [] 0 [canonicalBoolType] check fuel hmap
    (canonicalBoolNonNested env fuel)

theorem addDecl.safeCanonicalNatRecursors
    (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) (hmap : env.constants.WF) :
    (addDecl env (.inductDecl [] 0 [canonicalNatType binderName binderInfo] false) check fuel).WF
      (fun result =>
        ∃ allowPrimitive preprocessing stats root constructors,
          ∃ (elimLevel : Level) (infos : Array AddInductive.RecInfo)
            (source : AddInductive.Context) (isK : Bool),
          inductivePreprocessing env [] 0 [canonicalNatType binderName binderInfo] fuel =
            .ok preprocessing ∧
          preprocessing.aux2nested.size = 0 ∧
          stats.SafeRunScope 0 preprocessing.types.toArray preprocessing.aux2nested.size
            (inductiveScopeContext env [] allowPrimitive fuel) root constructors result ∧
          ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
          AddInductive.RecursorInfoCounts preprocessing.types.toArray infos ∧
          stats.RecursorOffsetMetadata preprocessing.types.toArray elimLevel infos []
            source.lctx isK false source result ∧
          (∀ index, index < preprocessing.types.toArray.size → ∃ info : RecursorVal,
            result.find? (mkRecName preprocessing.types.toArray[index]!.name) =
              some (.recInfo info) ∧
            ∃ rules,
              AddInductive.mkRecRules preprocessing.types.toArray elimLevel stats index
                (infos.map (·.motive)) (infos.flatMap (·.minors))
                (AddInductive.recursorMinorOffset preprocessing.types.toArray index) source =
                .ok (rules, AddInductive.recursorMinorOffset preprocessing.types.toArray (index + 1)) ∧
              info.rules = rules ∧
              info = AddInductive.declareRecursors.metadataVal stats preprocessing.types.toArray
                elimLevel infos [] source.lctx isK false index rules) ∧
          AddInductive.LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos
            source result) :=
  addDecl.safeCanonicalRecursorRegistration env [] 0
    [canonicalNatType binderName binderInfo] check fuel hmap
    (canonicalNatNonNested env fuel binderName binderInfo)

end Lean4Lean
