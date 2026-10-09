import Lean4Lean.Verify.InductiveRestorationArity

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open AddInductive
open AddInductive.declareConstructors

theorem InductiveSignaturePrefix.minorOffset {original rewritten : Array InductiveType}
    (hprefix : InductiveSignaturePrefix original rewritten) (index : Nat) (hindex : index ≤ original.size) :
    recursorMinorOffset rewritten index = recursorMinorOffset original index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    have horiginal : index < original.size := by omega
    have hrewritten := Nat.lt_of_lt_of_le horiginal hprefix.size
    rw [recursorMinorOffset.succ rewritten index hrewritten,
      recursorMinorOffset.succ original index horiginal, ih (by omega), hprefix.constructorCount index horiginal]

theorem InductiveSignaturePrefix.sourceMinor {original rewritten : Array InductiveType} {infos : Array RecInfo}
    (hprefix : InductiveSignaturePrefix original rewritten) (hindexing : RecursorMinorIndexing rewritten infos)
    (parent : Nat) (hparent : parent < original.size) (index : Nat)
    (hindex : index < original[parent]!.ctors.length) :
    ∃ minor, infos[parent]!.minors[index]? = some minor ∧
      (infos.flatMap (·.minors))[recursorMinorOffset original parent + index]? = some minor := by
  have hrewritten := Nat.lt_of_lt_of_le hparent hprefix.size
  have hctor : index < rewritten[parent]!.ctors.length := by
    rw [hprefix.constructorCount parent hparent]
    exact hindex
  simpa only [hprefix.minorOffset parent (Nat.le_of_lt hparent)] using hindexing.at parent hrewritten index hctor

theorem InductiveArityPrefix.constructorFields {original rewritten : Array InductiveType}
    (hprefix : InductiveArityPrefix original rewritten) (nparams index : Nat) (hindex : index < original.size) :
    rewritten[index]!.ctors.map (fun ctor => (ctor.name, arity 0 ctor.type - nparams)) =
      original[index]!.ctors.map (fun ctor => (ctor.name, arity 0 ctor.type - nparams)) := by
  apply List.ext_getElem
  · simp only [List.length_map, hprefix.constructorCount index hindex]
  · intro ctorIndex hrewritten horiginal
    have hctor : ctorIndex < original[index]!.ctors.length := by simpa only [List.length_map] using horiginal
    have hctorRewritten : ctorIndex < rewritten[index]!.ctors.length := by
      simpa only [List.length_map] using hrewritten
    have hname := hprefix.constructorNameAt index hindex ctorIndex hctor
    have harity := hprefix.constructorArityAt index hindex ctorIndex hctor
    simp only [getElem!_pos, hctor, hctorRewritten] at hname harity
    simp only [List.getElem_map, hname, harity]

def SourceRecursorRules (nparams : Nat) (ctors : List Constructor) (rules : List RecursorRule) : Prop :=
  rules.map (fun rule => (rule.ctor, rule.nfields)) =
    ctors.map (fun ctor => (ctor.name, arity 0 ctor.type - nparams))

theorem SourceRecursorRules.count {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) : rules.length = ctors.length := by
  simpa only [List.length_map] using congrArg List.length hrules

theorem SourceRecursorRules.names {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) : rules.map (·.ctor) = ctors.map (·.name) := by
  simpa only [List.map_map] using congrArg (List.map Prod.fst) hrules

theorem SourceRecursorRules.fieldCounts {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) :
    rules.map (·.nfields) = ctors.map (fun ctor => arity 0 ctor.type - nparams) := by
  simpa only [List.map_map] using congrArg (List.map Prod.snd) hrules

theorem SourceRecursorRules.at {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (index : Nat) (ctor : Constructor)
    (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧ rule.ctor = ctor.name ∧ rule.nfields = arity 0 ctor.type - nparams := by
  have hget : (rules.map (fun rule => (rule.ctor, rule.nfields)))[index]? =
      some (ctor.name, arity 0 ctor.type - nparams) := by
    rw [hrules]
    simp [hctor]
  cases hrule : rules[index]? with
  | none => simp [hrule] at hget
  | some rule =>
    have heq : (rule.ctor, rule.nfields) = (ctor.name, arity 0 ctor.type - nparams) := by
      simpa [hrule] using hget
    exact ⟨rule, rfl, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

def SourceRecursorRuleConstructors (nparams : Nat) (lparams : List Name)
    (parent : InductiveType) (rules : List RecursorRule) (env : Environment) : Prop :=
  ∀ index (hindex : index < parent.ctors.length), ∃ (rule : RecursorRule) (info : ConstructorVal),
    rules[index]? = some rule ∧ env.find? parent.ctors[index].name = some (.ctorInfo info) ∧
    SourceConstructorMetadata nparams lparams parent index info ∧ SourceConstructorFields nparams parent index info ∧
    rule.ctor = info.name ∧ rule.nfields = info.numFields

theorem AddInductive.InductiveStats.SafeRunScope.sourceRuleConstructors
    {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) (typeIndex : Nat) (htype : typeIndex < types.length)
    (rules : List RecursorRule) (hrules : SourceRecursorRules nparams types[typeIndex].ctors rules) :
    SourceRecursorRuleConstructors nparams original.lparams types[typeIndex] rules staged := by
  intro ctorIndex hctor
  obtain ⟨rule, hrule, hname, hfields⟩ := hrules.at ctorIndex types[typeIndex].ctors[ctorIndex]
    (List.getElem?_eq_getElem hctor)
  obtain ⟨_, info, _, _, _, hlookup, hmetadata⟩ :=
    scope.sourceConstructor hprefix.toInductiveSignaturePrefix typeIndex htype ctorIndex hctor
  have hchecked := scope.sourceConstructorFields hprefix typeIndex htype ctorIndex hctor info hlookup
  refine ⟨rule, info, hrule, hlookup, hmetadata, hchecked, ?_, ?_⟩
  · simpa only [hmetadata.name, getElem!_pos, hctor] using hname
  · simpa only [hchecked.fields, getElem!_pos, hctor] using hfields

def SourceRecursorRuleSources (nparams : Nat) (types : List InductiveType) (rewritten : Array InductiveType)
    (stats : InductiveStats) (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context)
    (staged : Environment) : Prop :=
  ∀ index (hindex : index < types.length), ∃ recursor : RecursorVal,
    staged.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
    recursor.name = mkRecName types[index].name ∧
    mkRecRules rewritten elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
      (recursorMinorOffset types.toArray index) source =
        .ok (recursor.rules, recursorMinorOffset types.toArray (index + 1)) ∧
    SourceRecursorRules nparams types[index].ctors recursor.rules ∧
    SourceRecursorRuleConstructors nparams source.lparams types[index] recursor.rules staged

theorem AddInductive.InductiveStats.SafeRunScope.sourceRuleSources
    {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context),
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts rewritten infos ∧ RecursorMinorIndexing rewritten infos ∧
      LocalRecursorRuleRhsDistinct stats rewritten infos source staged ∧
      SourceRecursorRuleSources nparams types rewritten stats elimLevel infos source staged := by
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hmetadata, hdistinct⟩ := scope.recursors
  refine ⟨elimLevel, infos, source, hframe, hcounts, hcounts.minorIndexing, hdistinct, ?_⟩
  intro index hindex
  have harray : index < types.toArray.size := by simpa using hindex
  have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
  have hname : rewritten[index]!.name = types[index].name := by
    simpa only [getElem!_pos, harray, List.getElem_toArray] using hprefix.names index harray
  obtain ⟨rules, hrecipe, hlookup⟩ := hmetadata index hrewritten
  let recursor := declareRecursors.metadataVal stats rewritten elimLevel infos original.lparams source.lctx isK false index rules
  have hparams : stats.params.size = nparams := by
    have hnonzero : rewritten.size ≠ 0 := by omega
    simpa only [InductiveStats.ParamsCount, if_neg hnonzero] using scope.registration.traces.2.1
  have hfields := mkRecRules.fieldCounts rewritten elimLevel stats index (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset rewritten index) source scope.registration.traces.2.2.1
    (rules, recursorMinorOffset rewritten (index + 1)) hrecipe
  have hsourceRules : SourceRecursorRules nparams types[index].ctors recursor.rules := by
    change rules.map (fun rule => (rule.ctor, rule.nfields)) = _
    rw [hfields, hparams, hprefix.constructorFields nparams index harray]
    simp only [getElem!_pos, harray, List.getElem_toArray]
  have hrootParams := scope.rootScope.toHeaderFrame.lparams
  refine ⟨recursor, by simpa only [hname] using hlookup, ?_, ?_, hsourceRules, ?_⟩
  · change mkRecName rewritten[index]!.name = mkRecName types[index].name
    rw [hname]
  · simpa only [hprefix.minorOffset index (Nat.le_of_lt harray),
      hprefix.minorOffset (index + 1) (by omega)] using hrecipe
  · simpa only [hframe.toHeaderFrame.lparams, hrootParams] using
      scope.sourceRuleConstructors hprefix index hindex recursor.rules hsourceRules

theorem restoredRecursorRule.fieldCount (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (nameMap : NameMap Name) (recName : Name) (rule : RecursorRule) :
    (restoredRecursorRule preprocessing staged nameMap recName rule).nfields = rule.nfields := rfl

theorem restoredRecursorVal.ruleAt (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allNames : List Name) (nameMap : NameMap Name) (recName : Name) (recursor : RecursorVal)
    (index : Nat) (rule : RecursorRule) (hrule : recursor.rules[index]? = some rule) :
    (restoredRecursorVal preprocessing staged allNames nameMap recName recursor).rules[index]? =
      some (restoredRecursorRule preprocessing staged nameMap recName rule) := by
  simp only [restoredRecursorVal, List.getElem?_map, hrule, Option.map_some]

theorem SourceRecursorRules.restoredPairs {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Environment) (nameMap : NameMap Name) (recName : Name) :
    (rules.map (restoredRecursorRule preprocessing staged nameMap recName)).map (fun rule => (rule.ctor, rule.nfields)) =
      ctors.map (fun ctor =>
        (if nameMap.getD recName recName == recName then ctor.name else preprocessing.restoreCtorName staged ctor.name,
          arity 0 ctor.type - nparams)) := by
  simpa only [List.map_map, restoredRecursorRule] using
    congrArg (List.map fun pair : Name × Nat =>
      (if nameMap.getD recName recName == recName then pair.1 else preprocessing.restoreCtorName staged pair.1, pair.2)) hrules

def SourceRecursorRuleLookups (nparams : Nat) (lparams : List Name) (types : List InductiveType)
    (preprocessing : ElimNestedInductive.Result) (staged result : Environment) : Prop :=
  ∀ index (hindex : index < types.length), ∃ recursor : RecursorVal,
    staged.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
    recursor.name = mkRecName types[index].name ∧
    SourceRecursorRules nparams types[index].ctors recursor.rules ∧
    SourceRecursorRuleConstructors nparams lparams types[index] recursor.rules staged ∧
    (preprocessing.aux2nested.size = 0 →
      result.find? (mkRecName types[index].name) = some (.recInfo recursor)) ∧
    (preprocessing.aux2nested.size ≠ 0 →
      let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2 (mkRecName types[index].name) recursor
      result.find? restored.name = some (.recInfo restored))

theorem SourceRecursorRuleLookups.finalRecursor {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) :
    ∃ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) ∧ recursor.rules.length = types[index].ctors.length ∧
      recursor.rules.map (·.nfields) = types[index].ctors.map (fun ctor => arity 0 ctor.type - nparams) := by
  obtain ⟨recursor, _, hname, hrules, _, hdirect, hnested⟩ := hlookups index hindex
  by_cases haux : preprocessing.aux2nested.size = 0
  · exact ⟨recursor, by simpa only [hname] using hdirect haux, hrules.count, hrules.fieldCounts⟩
  · refine ⟨restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 (mkRecName types[index].name) recursor, hnested haux, ?_, ?_⟩
    · simpa only [restoredRecursorVal, List.length_map] using hrules.count
    · simpa only [restoredRecursorVal, List.map_map, restoredRecursorRule] using hrules.fieldCounts

theorem SourceRecursorRuleLookups.finalRule {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[index].ctors.length) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal),
      result.find? recursor.name = some (.recInfo recursor) ∧
      recursor.rules.length = types[index].ctors.length ∧ recursor.rules[ctorIndex]? = some rule ∧
      staged.find? types[index].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧ rule.nfields = info.numFields ∧
      rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type := by
  obtain ⟨recursor, _, hname, hrules, hconstructors, hdirect, hnested⟩ := hlookups index hindex
  obtain ⟨rule, info, hrule, hlookup, hmetadata, hfields, _, hcount⟩ := hconstructors ctorIndex hctor
  have hfieldCount : rule.nfields = arity 0 types[index].ctors[ctorIndex].type - nparams := by
    simpa only [getElem!_pos, hctor] using hcount.trans hfields.fields
  have htotal : nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type := by
    simpa only [hcount, getElem!_pos, hctor] using hfields.total
  by_cases haux : preprocessing.aux2nested.size = 0
  · exact ⟨recursor, rule, info, by simpa only [hname] using hdirect haux,
      hrules.count, hrule, hlookup, hmetadata, hfields, hcount, hfieldCount, htotal⟩
  · let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 (mkRecName types[index].name) recursor
    exact ⟨restored, restoredRecursorRule preprocessing staged (mkAuxRecNameMap staged types).2
        (mkRecName types[index].name) rule, info, hnested haux,
      by simpa only [restored, restoredRecursorVal, List.length_map] using hrules.count,
      restoredRecursorVal.ruleAt _ _ _ _ _ _ ctorIndex rule hrule,
      hlookup, hmetadata, hfields, hcount, hfieldCount, htotal⟩

theorem SafeInductiveRestorationMetadata.sourceRecursorRuleStages {env result : Environment} {lparams : List Name}
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
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts preprocessing.types.toArray infos ∧ RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRuleSources nparams types preprocessing.types.toArray stats elimLevel infos source staged ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, _, _, _, hbranch, hinstalled⟩ :=
    metadata.completeStages
  have hprefix := inductivePreprocessing.arities env lparams nparams types fuel preprocessing hpre
  obtain ⟨elimLevel, infos, source, hframe, hcounts, hindexing, hdistinct, hsources⟩ := hscope.sourceRuleSources hprefix
  refine ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source,
    hpre, hrun, hscope, hprefix, hframe, hcounts, hindexing, hdistinct, hsources, hbranch, ?_⟩
  intro index hindex
  obtain ⟨recursor, hlookup, hname, _, hrules, hconstructors⟩ := hsources index hindex
  have hparams : source.lparams = lparams :=
    hframe.toHeaderFrame.lparams.trans hscope.rootScope.toHeaderFrame.lparams
  refine ⟨recursor, hlookup, hname, hrules, by simpa only [hparams] using hconstructors, ?_, ?_⟩
  · intro hnoaux
    cases hbranch with
    | direct _ => exact hlookup
    | nested hnested _ => exact False.elim (hnested hnoaux)
  · intro hnested
    have harray : index < types.toArray.size := by simpa using hindex
    have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
    have hrawname : preprocessing.types.toArray[index].name = types[index].name := by
      simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.names index harray
    have hheader := hscope.toSafeRunRegistration.headerMetadata index hrewritten
    rw [hrawname] at hheader
    exact (hinstalled hnested).mainRecursor types[index] (List.getElem_mem hindex) _ hheader recursor hlookup

theorem SafeInductiveRestorationMetadata.sourceRecursorRules {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, _, _, _, _, _, _, hpre, hrun, _, hprefix, _, _, _, _, _, _, hlookups⟩ :=
    metadata.sourceRecursorRuleStages
  exact ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩

theorem Environment.addInductive.safeSourceRecursorRules (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceRecursorRuleLookups nparams lparams types preprocessing staged result :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.sourceRecursorRules

theorem addDecl.safeInductiveSourceRecursorRules (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceRecursorRuleLookups nparams lparams types preprocessing staged result :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.sourceRecursorRules⟩

end Lean4Lean
