import Lean4Lean.Verify.InductiveRecursorNames

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open AddInductive
open AddInductive.declareConstructors

theorem mkRecName_injective : Function.Injective mkRecName := by
  intro first second heq
  change Name.str first "rec" = Name.str second "rec" at heq
  exact (Name.str.inj heq).1

structure OriginalRecursorNames (types : List InductiveType) (staged : Environment) : Prop where
  outside : ∀ index (hindex : index < types.length),
    mkRecName types[index].name ∉ (mkAuxRecNameMap staged types).1
  absent : ∀ index (hindex : index < types.length),
    (mkAuxRecNameMap staged types).2.find? (mkRecName types[index].name) = none
  identity : ∀ index (hindex : index < types.length),
    (mkAuxRecNameMap staged types).2.getD (mkRecName types[index].name) (mkRecName types[index].name) =
      mkRecName types[index].name

theorem AddInductive.InductiveStats.SafeRunScope.originalRecursorNames
    {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveNamePrefix types.toArray rewritten) (hnodup : (rewritten.toList.map (·.name)).Nodup) :
    OriginalRecursorNames types staged := by
  have houtside : ∀ index (hindex : index < types.length),
      mkRecName types[index].name ∉ (mkAuxRecNameMap staged types).1 := by
    cases types with
    | nil => intro index hindex; simp at hindex
    | cons type types =>
      intro index hindex
      have harray : index < (type :: types).toArray.size := by simpa using hindex
      have hnot : (type :: types)[index].name ∉ (rewritten.toList.map (·.name)).drop (type :: types).length := by
        have hnot := hprefix.suffixNotMem hnodup index harray
        rw [getElem!_pos (type :: types).toArray index harray, List.getElem_toArray] at hnot
        simpa only [List.size_toArray] using hnot
      have hnotRec : mkRecName (type :: types)[index].name ∉
          ((rewritten.map (·.name)).toList.drop (type :: types).length).map mkRecName := by
        intro hmem
        obtain ⟨name, hname, heq⟩ := List.mem_map.mp hmem
        have hsame := mkRecName_injective heq
        simp only [Array.toList_map] at hname
        rw [hsame] at hname
        exact hnot hname
      have hzero : 0 < (type :: types).toArray.size := by simp
      have hrewritten := Nat.lt_of_lt_of_le hzero hprefix.size
      let info := declareInductiveTypes.metadataVal stats nparams rewritten numNested false
        original.lparams rewritten[0] stats.nindices[0]!
      have hname : rewritten[0].name = type.name := by
        simpa only [getElem!_pos, hzero, hrewritten, List.getElem_toArray, List.getElem_cons_zero] using
          hprefix.names 0 hzero
      have hlookup : staged.find? type.name = some (.inductInfo info) := by
        simpa only [hname] using scope.toSafeRunRegistration.headerMetadata 0 hrewritten
      rw [mkAuxRecNameMap.names staged type types info hlookup]
      split
      · exact hnotRec
      · simp
  exact ⟨houtside, fun index hindex => mkAuxRecNameMap.find?_eq_none staged types _ (houtside index hindex),
    fun index hindex => mkAuxRecNameMap.getD_eq_self staged types _ (houtside index hindex)⟩

theorem SourceRecursorRules.restoreOriginal {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Environment) (nameMap : NameMap Name) (recName : Name)
    (hidentity : nameMap.getD recName recName = recName) :
    SourceRecursorRules nparams ctors (rules.map (restoredRecursorRule preprocessing staged nameMap recName)) := by
  simpa only [hidentity, BEq.rfl, ↓reduceIte] using hrules.restoredPairs preprocessing staged nameMap recName

theorem SourceRecursorRuleConstructors.restoreOriginal {nparams : Nat} {lparams : List Name}
    {parent : InductiveType} {rules : List RecursorRule} {staged : Environment}
    (hconstructors : SourceRecursorRuleConstructors nparams lparams parent rules staged)
    (preprocessing : ElimNestedInductive.Result) (nameMap : NameMap Name) (recName : Name)
    (hidentity : nameMap.getD recName recName = recName) :
    SourceRecursorRuleConstructors nparams lparams parent
      (rules.map (restoredRecursorRule preprocessing staged nameMap recName)) staged := by
  intro index hindex
  obtain ⟨rule, info, hrule, hlookup, hmetadata, hfields, hname, hcount⟩ := hconstructors index hindex
  refine ⟨restoredRecursorRule preprocessing staged nameMap recName rule, info, ?_,
    hlookup, hmetadata, hfields, ?_, hcount⟩
  · simp only [List.getElem?_map, hrule, Option.map_some]
  · simpa only [restoredRecursorRule, hidentity, BEq.rfl, ↓reduceIte] using hname

def OriginalRecursorRuleLookups (nparams : Nat) (lparams : List Name) (types : List InductiveType)
    (preprocessing : ElimNestedInductive.Result) (staged result : Environment) : Prop :=
  ∀ index (hindex : index < types.length), ∃ (source final : RecursorVal),
    staged.find? (mkRecName types[index].name) = some (.recInfo source) ∧
    result.find? (mkRecName types[index].name) = some (.recInfo final) ∧
    final.name = mkRecName types[index].name ∧ SourceRecursorRules nparams types[index].ctors final.rules ∧
    SourceRecursorRuleConstructors nparams lparams types[index] final.rules staged ∧
    (preprocessing.aux2nested.size = 0 → final = source) ∧
    (preprocessing.aux2nested.size ≠ 0 → final =
      restoredRecursorVal preprocessing staged (types.map (·.name)) (mkAuxRecNameMap staged types).2
        (mkRecName types[index].name) source)

theorem SourceRecursorRuleLookups.originalNames {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (hnames : OriginalRecursorNames types staged) :
    OriginalRecursorRuleLookups nparams lparams types preprocessing staged result := by
  intro index hindex
  obtain ⟨source, hlookup, hname, hrules, hconstructors, hdirect, hnested⟩ := hlookups index hindex
  by_cases haux : preprocessing.aux2nested.size = 0
  · exact ⟨source, source, hlookup, hdirect haux, hname, hrules, hconstructors,
      fun _ => rfl, fun hne => False.elim (hne haux)⟩
  · let final := restoredRecursorVal preprocessing staged (types.map (·.name)) (mkAuxRecNameMap staged types).2
      (mkRecName types[index].name) source
    have hfinalName : final.name = mkRecName types[index].name := hnames.identity index hindex
    have hfinalLookup := hnested haux
    change result.find? final.name = some (.recInfo final) at hfinalLookup
    rw [hfinalName] at hfinalLookup
    exact ⟨source, final, hlookup, hfinalLookup, hfinalName,
      hrules.restoreOriginal _ _ _ _ (hnames.identity index hindex),
      hconstructors.restoreOriginal _ _ _ (hnames.identity index hindex),
      fun heq => False.elim (haux heq), fun _ => rfl⟩

theorem OriginalRecursorRuleLookups.at {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal),
      result.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      recursor.rules.length = types[index].ctors.length ∧ recursor.rules[ctorIndex]? = some rule ∧
      rule.ctor = types[index].ctors[ctorIndex].name ∧
      staged.find? rule.ctor = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧ rule.nfields = info.numFields ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type := by
  obtain ⟨_, recursor, _, hlookup, _, hrules, hconstructors, _, _⟩ := hlookups index hindex
  obtain ⟨rule, info, hrule, hctorLookup, hmetadata, hfields, hname, hcount⟩ := hconstructors ctorIndex hctor
  have hctorName : rule.ctor = types[index].ctors[ctorIndex].name := by
    simpa only [hmetadata.name, getElem!_pos, hctor] using hname
  exact ⟨recursor, rule, info, hlookup, hrules.count, hrule, hctorName,
    by simpa only [hctorName] using hctorLookup, hmetadata, hfields, hcount,
    by simpa only [hcount, getElem!_pos, hctor] using hfields.total⟩

theorem SafeInductiveRestorationMetadata.originalRecursorRuleStages {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment)
      (stats : InductiveStats) (root : AddInductive.Context) (constructors : Environment)
      (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      (preprocessing.types.map (·.name)).Nodup ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts preprocessing.types.toArray infos ∧ RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      OriginalRecursorNames types staged ∧ OriginalRecursorRuleLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source, hpre, hrun,
    hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hbranch, hlookups⟩ := metadata.sourceRecursorRuleStages
  have hnodup := AddInductive.run.datatypeNamesNodup nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) metadata.originalWF staged hrun
  have hnames := hscope.originalRecursorNames hprefix.toInductiveNamePrefix (by simpa only [List.toList_toArray] using hnodup)
  exact ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hnodup, hframe, hcounts, hindexing, hdistinct, hsources, hbranch, hnames,
    hlookups.originalNames hnames⟩

theorem SafeInductiveRestorationMetadata.originalRecursorRules {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
      OriginalRecursorRuleLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, _, _, _, _, _, _, hpre, hrun, _, hprefix, _, _, _, _, _, _, _, hnames, hlookups⟩ :=
    metadata.originalRecursorRuleStages
  exact ⟨preprocessing, staged, hpre, hrun, hprefix, hnames, hlookups⟩

theorem Environment.addInductive.safeOriginalRecursorRules (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
        OriginalRecursorRuleLookups nparams lparams types preprocessing staged result :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.originalRecursorRules

theorem addDecl.safeInductiveOriginalRecursorRules (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
        OriginalRecursorRuleLookups nparams lparams types preprocessing staged result :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.originalRecursorRules⟩

end Lean4Lean
