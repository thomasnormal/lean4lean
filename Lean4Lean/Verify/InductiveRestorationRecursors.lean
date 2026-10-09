import Lean4Lean.Verify.InductiveRestorationRuleNames

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open AddInductive
open AddInductive.declareConstructors

def SourceRecursorRecords (nparams : Nat) (types : List InductiveType) (rewritten : Array InductiveType)
    (stats : InductiveStats) (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context)
    (isK : Bool) (staged : Environment) : Prop :=
  ∀ index (hindex : index < types.length), ∃ recursor : RecursorVal,
    staged.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
    recursor.name = mkRecName types[index].name ∧
    recursor = declareRecursors.metadataVal stats rewritten elimLevel infos source.lparams source.lctx
      isK false index recursor.rules ∧
    mkRecRules rewritten elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
      (recursorMinorOffset types.toArray index) source =
        .ok (recursor.rules, recursorMinorOffset types.toArray (index + 1)) ∧
    SourceRecursorRules nparams types[index].ctors recursor.rules ∧
    SourceRecursorRuleConstructors nparams source.lparams types[index] recursor.rules staged

theorem SourceRecursorRecords.ruleSources {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {staged : Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged) :
    SourceRecursorRuleSources nparams types rewritten stats elimLevel infos source staged := by
  intro index hindex
  obtain ⟨recursor, hlookup, hname, _, hrecipe, hrules, hconstructors⟩ := records index hindex
  exact ⟨recursor, hlookup, hname, hrecipe, hrules, hconstructors⟩

theorem AddInductive.InductiveStats.SafeRunScope.sourceRecursorRecords
    {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts rewritten infos ∧ RecursorMinorIndexing rewritten infos ∧
      LocalRecursorRuleRhsDistinct stats rewritten infos source staged ∧
      SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged := by
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hmetadata, hdistinct⟩ := scope.recursors
  refine ⟨elimLevel, infos, source, isK, hframe, hcounts, hcounts.minorIndexing, hdistinct, ?_⟩
  intro index hindex
  have harray : index < types.toArray.size := by simpa using hindex
  have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
  have hname : rewritten[index]!.name = types[index].name := by
    simpa only [getElem!_pos, harray, List.getElem_toArray] using hprefix.names index harray
  obtain ⟨rules, hrecipe, hlookup⟩ := hmetadata index hrewritten
  have hparams : stats.params.size = nparams := by
    have hnonzero : rewritten.size ≠ 0 := by omega
    simpa only [InductiveStats.ParamsCount, if_neg hnonzero] using scope.registration.traces.2.1
  have hlevels : source.lparams = original.lparams :=
    hframe.toHeaderFrame.lparams.trans scope.rootScope.toHeaderFrame.lparams
  let recursor := declareRecursors.metadataVal stats rewritten elimLevel infos source.lparams source.lctx
    isK false index rules
  have hfields := mkRecRules.fieldCounts rewritten elimLevel stats index (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset rewritten index) source scope.registration.traces.2.2.1
    (rules, recursorMinorOffset rewritten (index + 1)) hrecipe
  have hrules : SourceRecursorRules nparams types[index].ctors recursor.rules := by
    change rules.map (fun rule => (rule.ctor, rule.nfields)) = _
    rw [hfields, hparams, hprefix.constructorFields nparams index harray]
    simp only [getElem!_pos, harray, List.getElem_toArray]
  refine ⟨recursor, by simpa only [recursor, hlevels, hname] using hlookup, ?_, rfl, ?_, hrules, ?_⟩
  · change mkRecName rewritten[index]!.name = mkRecName types[index].name
    rw [hname]
  · simpa only [hprefix.minorOffset index (Nat.le_of_lt harray),
      hprefix.minorOffset (index + 1) (by omega)] using hrecipe
  · simpa only [hlevels] using scope.sourceRuleConstructors hprefix index hindex recursor.rules hrules

theorem restoredRecursorRule.originalRecord (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (nameMap : NameMap Name) (recName : Name) (rule : RecursorRule)
    (hidentity : nameMap.getD recName recName = recName) :
    restoredRecursorRule preprocessing staged nameMap recName rule =
      { rule with rhs := preprocessing.restoreNested staged rule.rhs nameMap } := by
  simp only [restoredRecursorRule, hidentity, BEq.rfl, ↓reduceIte]

def OriginalRecursorRestoration (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) (before after : RecursorVal) : Prop :=
  after = if preprocessing.aux2nested.size = 0 then before else
    { before with
      type := preprocessing.restoreNested staged before.type (mkAuxRecNameMap staged types).2
      all := types.map (·.name)
      rules := before.rules.map fun rule =>
        { rule with rhs := preprocessing.restoreNested staged rule.rhs (mkAuxRecNameMap staged types).2 } }

theorem OriginalRecursorRuleLookups.restoration {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (lookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (names : OriginalRecursorNames types staged) (index : Nat) (hindex : index < types.length)
    (before : RecursorVal) (hbefore : staged.find? (mkRecName types[index].name) = some (.recInfo before))
    (hname : before.name = mkRecName types[index].name) :
    ∃ after : RecursorVal, result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
      OriginalRecursorRestoration preprocessing staged types before after ∧
      SourceRecursorRules nparams types[index].ctors after.rules ∧
      SourceRecursorRuleConstructors nparams lparams types[index] after.rules staged := by
  obtain ⟨actual, after, hactual, hafter, _, hrules, hconstructors, hdirect, hnested⟩ := lookups index hindex
  have heq : actual = before := ConstantInfo.recInfo.inj (Option.some.inj (hactual.symm.trans hbefore))
  subst actual
  refine ⟨after, hafter, ?_, hrules, hconstructors⟩
  unfold OriginalRecursorRestoration
  split
  · rename_i haux
    exact hdirect haux
  · rename_i haux
    rw [hnested haux]
    have hrules : before.rules.map (restoredRecursorRule preprocessing staged (mkAuxRecNameMap staged types).2
        (mkRecName types[index].name)) = before.rules.map (fun rule =>
          { rule with rhs := preprocessing.restoreNested staged rule.rhs (mkAuxRecNameMap staged types).2 }) := by
      apply List.map_congr_left
      intro rule _
      exact restoredRecursorRule.originalRecord preprocessing staged _ _ rule (names.identity index hindex)
    simp only [restoredRecursorVal]
    rw [names.identity index hindex, hrules, ← hname]

structure RecursorHeaderMetadata (nparams : Nat) (lparams : List Name) (name : Name)
    (rewritten : Array InductiveType) (stats : InductiveStats) (elimLevel : Level)
    (isK : Bool) (index : Nat) (info : RecursorVal) : Prop where
  name : info.name = mkRecName name
  levelParams : info.levelParams = getRecLevelParams elimLevel lparams
  numParams : info.numParams = nparams
  numIndices : info.numIndices = stats.nindices[index]!
  numMotives : info.numMotives = rewritten.size
  numMinors : info.numMinors = (rewritten.toList.flatMap (·.ctors)).length
  k : info.k = isK
  isUnsafe : info.isUnsafe = false

theorem SourceRecursorRecords.header {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {staged : Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged)
    (hcounts : RecursorInfoCounts rewritten infos) (hparams : stats.params.size = nparams)
    (index : Nat) (hindex : index < types.length) (recursor : RecursorVal)
    (hlookup : staged.find? (mkRecName types[index].name) = some (.recInfo recursor)) :
    RecursorHeaderMetadata nparams source.lparams types[index].name rewritten stats elimLevel isK index recursor := by
  obtain ⟨actual, hactual, hname, hrecord, _⟩ := records index hindex
  have heq : actual = recursor := ConstantInfo.recInfo.inj (Option.some.inj (hactual.symm.trans hlookup))
  subst actual
  refine ⟨hname, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun info : RecursorVal => info.levelParams) hrecord
  · simpa only [declareRecursors.metadataVal, hparams] using congrArg RecursorVal.numParams hrecord
  · exact congrArg RecursorVal.numIndices hrecord
  · simpa only [declareRecursors.metadataVal, hcounts.motiveTotal] using congrArg RecursorVal.numMotives hrecord
  · simpa only [declareRecursors.metadataVal, hcounts.minorTotal] using congrArg RecursorVal.numMinors hrecord
  · exact congrArg RecursorVal.k hrecord
  · exact congrArg RecursorVal.isUnsafe hrecord

theorem OriginalRecursorRestoration.header {nparams : Nat} {lparams : List Name} {name : Name}
    {rewritten : Array InductiveType} {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat}
    {preprocessing : ElimNestedInductive.Result} {staged : Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index before) :
    RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index after := by
  unfold OriginalRecursorRestoration at restoration
  split at restoration
  · rw [restoration]
    exact header
  · rw [restoration]
    exact ⟨header.name, header.levelParams, header.numParams, header.numIndices,
      header.numMotives, header.numMinors, header.k, header.isUnsafe⟩

theorem OriginalRecursorRestoration.type {preprocessing : ElimNestedInductive.Result}
    {staged : Environment} {types : List InductiveType} {before after : RecursorVal}
    (restoration : OriginalRecursorRestoration preprocessing staged types before after) :
    after.type = if preprocessing.aux2nested.size = 0 then before.type else
      preprocessing.restoreNested staged before.type (mkAuxRecNameMap staged types).2 := by
  unfold OriginalRecursorRestoration at restoration
  rw [restoration]
  split <;> rfl

theorem OriginalRecursorRestoration.all {preprocessing : ElimNestedInductive.Result}
    {staged : Environment} {types : List InductiveType} {before after : RecursorVal}
    (restoration : OriginalRecursorRestoration preprocessing staged types before after) :
    after.all = if preprocessing.aux2nested.size = 0 then before.all else types.map (·.name) := by
  unfold OriginalRecursorRestoration at restoration
  rw [restoration]
  split <;> rfl

theorem OriginalRecursorRestoration.ruleAt {preprocessing : ElimNestedInductive.Result}
    {staged : Environment} {types : List InductiveType} {before after : RecursorVal}
    (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (index : Nat) (rule : RecursorRule) (hrule : before.rules[index]? = some rule) :
    after.rules[index]? = some (if preprocessing.aux2nested.size = 0 then rule else
      { rule with rhs := preprocessing.restoreNested staged rule.rhs (mkAuxRecNameMap staged types).2 }) := by
  unfold OriginalRecursorRestoration at restoration
  rw [restoration]
  split
  · exact hrule
  · simp only [List.getElem?_map, hrule, Option.map_some]

def OriginalRecursorRecords (nparams : Nat) (types : List InductiveType) (rewritten : Array InductiveType)
    (stats : InductiveStats) (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context)
    (isK : Bool) (preprocessing : ElimNestedInductive.Result) (staged result : Environment) : Prop :=
  ∀ index (hindex : index < types.length), ∃ (before after : RecursorVal),
    staged.find? (mkRecName types[index].name) = some (.recInfo before) ∧
    result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
    before = declareRecursors.metadataVal stats rewritten elimLevel infos source.lparams source.lctx
      isK false index before.rules ∧
    mkRecRules rewritten elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
      (recursorMinorOffset types.toArray index) source =
        .ok (before.rules, recursorMinorOffset types.toArray (index + 1)) ∧
    RecursorHeaderMetadata nparams source.lparams types[index].name rewritten stats elimLevel isK index after ∧
    OriginalRecursorRestoration preprocessing staged types before after ∧
    SourceRecursorRules nparams types[index].ctors after.rules ∧
    SourceRecursorRuleConstructors nparams source.lparams types[index] after.rules staged

theorem SourceRecursorRecords.restoredRecords {nparams : Nat} {types : List InductiveType}
    {rewritten : Array InductiveType} {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo}
    {source : AddInductive.Context} {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged)
    (hcounts : RecursorInfoCounts rewritten infos) (hprefix : InductiveNamePrefix types.toArray rewritten)
    (hparams : stats.ParamsCount nparams rewritten.size)
    (names : OriginalRecursorNames types staged)
    (lookups : OriginalRecursorRuleLookups nparams source.lparams types preprocessing staged result) :
    OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result := by
  intro index hindex
  have hnonzero : rewritten.size ≠ 0 := by
    have harray : index < types.toArray.size := by simpa using hindex
    have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
    omega
  have hparamCount : stats.params.size = nparams := by
    simpa only [InductiveStats.ParamsCount, if_neg hnonzero] using hparams
  obtain ⟨before, hbefore, hname, hrecord, hrecipe, _, _⟩ := records index hindex
  obtain ⟨after, hafter, hrestoration, hrules, hconstructors⟩ := lookups.restoration names index hindex before hbefore hname
  exact ⟨before, after, hbefore, hafter, hrecord, hrecipe,
    hrestoration.header (records.header hcounts hparamCount index hindex before hbefore), hrestoration, hrules, hconstructors⟩

theorem OriginalRecursorRecords.finalHeader {nparams : Nat} {types : List InductiveType}
    {rewritten : Array InductiveType} {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo}
    {source : AddInductive.Context} {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (records : OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result)
    (index : Nat) (hindex : index < types.length) :
    ∃ (before after : RecursorVal), staged.find? (mkRecName types[index].name) = some (.recInfo before) ∧
      result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
      RecursorHeaderMetadata nparams source.lparams types[index].name rewritten stats elimLevel isK index after ∧
      after.all = (if preprocessing.aux2nested.size = 0 then (rewritten.map (·.name)).toList else types.map (·.name)) ∧
      after.type = (if preprocessing.aux2nested.size = 0 then
        (declareRecursors.metadataVal stats rewritten elimLevel infos source.lparams source.lctx isK false index before.rules).type
        else preprocessing.restoreNested staged
          (declareRecursors.metadataVal stats rewritten elimLevel infos source.lparams source.lctx isK false index before.rules).type
          (mkAuxRecNameMap staged types).2) := by
  obtain ⟨before, after, hbefore, hafter, hrecord, _, hheader, hrestoration, _⟩ := records index hindex
  have hall : before.all = (rewritten.map (·.name)).toList := congrArg RecursorVal.all hrecord
  have htype := congrArg (fun info : RecursorVal => info.type) hrecord
  exact ⟨before, after, hbefore, hafter, hheader,
    by simpa only [hall] using hrestoration.all, by simpa only [htype] using hrestoration.type⟩

theorem OriginalRecursorRecords.ruleAt {nparams : Nat} {types : List InductiveType}
    {rewritten : Array InductiveType} {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo}
    {source : AddInductive.Context} {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (records : OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat) (hctor : ctorIndex < types[index].ctors.length) :
    ∃ (before after : RecursorVal) (sourceRule finalRule : RecursorRule) (info : ConstructorVal),
      staged.find? (mkRecName types[index].name) = some (.recInfo before) ∧
      result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
      before.rules[ctorIndex]? = some sourceRule ∧ after.rules[ctorIndex]? = some finalRule ∧
      finalRule.ctor = types[index].ctors[ctorIndex].name ∧ finalRule.ctor = sourceRule.ctor ∧
      finalRule.nfields = sourceRule.nfields ∧
      finalRule.rhs = (if preprocessing.aux2nested.size = 0 then sourceRule.rhs else
        preprocessing.restoreNested staged sourceRule.rhs (mkAuxRecNameMap staged types).2) ∧
      staged.find? finalRule.ctor = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams source.lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧ finalRule.nfields = info.numFields ∧
      nparams + finalRule.nfields = arity 0 types[index].ctors[ctorIndex].type := by
  obtain ⟨before, after, hbefore, hafter, _, _, _, hrestoration, hrules, hconstructors⟩ := records index hindex
  have hlength : after.rules.length = before.rules.length := by
    unfold OriginalRecursorRestoration at hrestoration
    rw [hrestoration]
    split <;> simp only [List.length_map]
  have hbound : ctorIndex < before.rules.length := by rw [← hlength, hrules.count]; exact hctor
  let sourceRule := before.rules[ctorIndex]
  have hsource : before.rules[ctorIndex]? = some sourceRule := List.getElem?_eq_getElem hbound
  obtain ⟨finalRule, info, hfinal, hlookup, hmetadata, hfields, hname, hcount⟩ := hconstructors ctorIndex hctor
  have heq : finalRule = (if preprocessing.aux2nested.size = 0 then sourceRule else
      { sourceRule with rhs := preprocessing.restoreNested staged sourceRule.rhs (mkAuxRecNameMap staged types).2 }) :=
    Option.some.inj (hfinal.symm.trans (hrestoration.ruleAt ctorIndex sourceRule hsource))
  have hctorName : finalRule.ctor = types[index].ctors[ctorIndex].name := by
    simpa only [hmetadata.name, getElem!_pos, hctor] using hname
  refine ⟨before, after, sourceRule, finalRule, info, hbefore, hafter, hsource, hfinal, hctorName, ?_, ?_, ?_,
    by simpa only [hctorName] using hlookup, hmetadata, hfields, hcount, ?_⟩
  · rw [heq]; split <;> rfl
  · rw [heq]; split <;> rfl
  · rw [heq]; split <;> rfl
  · simpa only [hcount, getElem!_pos, hctor] using hfields.total

theorem SafeInductiveRestorationMetadata.originalRecursorRecordStages {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment)
      (stats : InductiveStats) (root : AddInductive.Context) (constructors : Environment)
      (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      source.lparams = lparams ∧ RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRecords nparams types preprocessing.types.toArray stats elimLevel infos source isK staged ∧
      InductiveFrontendBranch preprocessing staged types env result ∧ OriginalRecursorNames types staged ∧
      OriginalRecursorRecords nparams types preprocessing.types.toArray stats elimLevel infos source isK
        preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, _, _, _, hbranch, hinstalled⟩ :=
    metadata.completeStages
  have hprefix := inductivePreprocessing.arities env lparams nparams types fuel preprocessing hpre
  have hnodup := AddInductive.run.datatypeNamesNodup nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) metadata.originalWF staged hrun
  have hnames := hscope.originalRecursorNames hprefix.toInductiveNamePrefix
    (by simpa only [List.toList_toArray] using hnodup)
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hindexing, hdistinct, hrecords⟩ :=
    hscope.sourceRecursorRecords hprefix
  have hlevels : source.lparams = lparams :=
    hframe.toHeaderFrame.lparams.trans hscope.rootScope.toHeaderFrame.lparams
  have hlookups : SourceRecursorRuleLookups nparams source.lparams types preprocessing staged result := by
    intro index hindex
    obtain ⟨recursor, hlookup, hname, _, hrules, hconstructors⟩ := hrecords.ruleSources index hindex
    refine ⟨recursor, hlookup, hname, hrules, hconstructors, ?_, ?_⟩
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
  exact ⟨preprocessing, staged, stats, root, constructors, elimLevel, infos, source, isK,
    hpre, hrun, hscope, hprefix, hframe, hlevels, hcounts, hindexing, hdistinct, hrecords, hbranch, hnames,
    hrecords.restoredRecords hcounts hprefix.toInductiveNamePrefix hscope.registration.traces.2.1 hnames
      (hlookups.originalNames hnames)⟩

theorem SafeInductiveRestorationMetadata.originalRecursorRecords {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment) (stats : InductiveStats)
      (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
      OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
        stats elimLevel infos source isK preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, _, _, elimLevel, infos, source, isK,
    hpre, hrun, _, _, _, hlevels, _, _, _, _, _, hnames, hrecords⟩ := metadata.originalRecursorRecordStages
  exact ⟨preprocessing, staged, stats, elimLevel, infos, source, isK, hpre, hrun, hlevels, hnames, hrecords⟩

theorem Environment.addInductive.safeOriginalRecursorRecords (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment) (stats : InductiveStats)
        (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
        OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
          stats elimLevel infos source isK preprocessing staged result :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.originalRecursorRecords

theorem addDecl.safeInductiveOriginalRecursorRecords (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment) (stats : InductiveStats)
        (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
        OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
          stats elimLevel infos source isK preprocessing staged result :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.originalRecursorRecords⟩

end Lean4Lean
