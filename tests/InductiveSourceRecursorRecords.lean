import Lean4Lean.Verify.InductiveRestorationRecursors
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open AddInductive.declareConstructors

namespace InductiveSourceRecursorRecordsTest

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {staged : Kernel.Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged) :
    SourceRecursorRuleSources nparams types rewritten stats elimLevel infos source staged := records.ruleSources

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts rewritten infos ∧ RecursorMinorIndexing rewritten infos ∧
      LocalRecursorRuleRhsDistinct stats rewritten infos source staged ∧
      SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged :=
  scope.sourceRecursorRecords hprefix

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (nameMap : NameMap Name) (recName : Name) (rule : RecursorRule)
    (hidentity : nameMap.getD recName recName = recName) :
    restoredRecursorRule preprocessing staged nameMap recName rule =
      { rule with rhs := preprocessing.restoreNested staged rule.rhs nameMap } :=
  restoredRecursorRule.originalRecord preprocessing staged nameMap recName rule hidentity

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (types : List InductiveType)
    (before : RecursorVal) (haux : preprocessing.aux2nested.size = 0) :
    OriginalRecursorRestoration preprocessing staged types before before := by
  simp only [OriginalRecursorRestoration, haux, ↓reduceIte]

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (types : List InductiveType)
    (before : RecursorVal) (haux : preprocessing.aux2nested.size ≠ 0) :
    OriginalRecursorRestoration preprocessing staged types before
      { before with
        type := preprocessing.restoreNested staged before.type (mkAuxRecNameMap staged types).2
        all := types.map (·.name)
        rules := before.rules.map fun rule =>
          { rule with rhs := preprocessing.restoreNested staged rule.rhs (mkAuxRecNameMap staged types).2 } } := by
  simp only [OriginalRecursorRestoration, if_neg haux]

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat}
    {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index before) :
    RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index after := restoration.header header

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after) :
    after.type = if preprocessing.aux2nested.size = 0 then before.type else
      preprocessing.restoreNested staged before.type (mkAuxRecNameMap staged types).2 := restoration.type

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after) :
    after.all = if preprocessing.aux2nested.size = 0 then before.all else types.map (·.name) := restoration.all

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (index : Nat) (rule : RecursorRule) (hrule : before.rules[index]? = some rule) :
    after.rules[index]? = some (if preprocessing.aux2nested.size = 0 then rule else
      { rule with rhs := preprocessing.restoreNested staged rule.rhs (mkAuxRecNameMap staged types).2 }) :=
  restoration.ruleAt index rule hrule

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info) :
    info.name = mkRecName name := header.name

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info) :
    info.levelParams = getRecLevelParams elimLevel lparams := header.levelParams

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info) :
    info.numParams = nparams ∧ info.numIndices = stats.nindices[index]! := ⟨header.numParams, header.numIndices⟩

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info) :
    info.numMotives = rewritten.size ∧ info.numMinors = (rewritten.toList.flatMap (·.ctors)).length :=
  ⟨header.numMotives, header.numMinors⟩

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info) :
    info.k = isK ∧ info.isUnsafe = false := ⟨header.k, header.isUnsafe⟩

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {staged : Kernel.Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged)
    (hcounts : RecursorInfoCounts rewritten infos) (hparams : stats.params.size = nparams)
    (index : Nat) (hindex : index < types.length) (recursor : RecursorVal)
    (hlookup : staged.find? (mkRecName types[index].name) = some (.recInfo recursor)) :
    RecursorHeaderMetadata nparams source.lparams types[index].name rewritten stats elimLevel isK index recursor :=
  records.header hcounts hparams index hindex recursor hlookup

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (lookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (names : OriginalRecursorNames types staged) (index : Nat) (hindex : index < types.length)
    (before : RecursorVal) (hbefore : staged.find? (mkRecName types[index].name) = some (.recInfo before))
    (hname : before.name = mkRecName types[index].name) :
    ∃ after : RecursorVal, result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
      OriginalRecursorRestoration preprocessing staged types before after ∧
      SourceRecursorRules nparams types[index].ctors after.rules ∧
      SourceRecursorRuleConstructors nparams lparams types[index] after.rules staged :=
  lookups.restoration names index hindex before hbefore hname

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (records : SourceRecursorRecords nparams types rewritten stats elimLevel infos source isK staged)
    (hcounts : RecursorInfoCounts rewritten infos) (hprefix : InductiveNamePrefix types.toArray rewritten)
    (hparams : stats.ParamsCount nparams rewritten.size) (names : OriginalRecursorNames types staged)
    (lookups : OriginalRecursorRuleLookups nparams source.lparams types preprocessing staged result) :
    OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result :=
  records.restoredRecords hcounts hprefix hparams names lookups

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
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
          (mkAuxRecNameMap staged types).2) := records.finalHeader index hindex

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (records : OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat) (hctor : ctorIndex < types[index].ctors.length) :
    ∃ (before after : RecursorVal) (sourceRule finalRule : RecursorRule) (info : ConstructorVal),
      staged.find? (mkRecName types[index].name) = some (.recInfo before) ∧
      result.find? (mkRecName types[index].name) = some (.recInfo after) ∧
      before.rules[ctorIndex]? = some sourceRule ∧ after.rules[ctorIndex]? = some finalRule ∧
      finalRule.ctor = types[index].ctors[ctorIndex].name ∧ finalRule.ctor = sourceRule.ctor ∧
      finalRule.nfields = sourceRule.nfields ∧ finalRule.rhs = (if preprocessing.aux2nested.size = 0 then sourceRule.rhs else
        preprocessing.restoreNested staged sourceRule.rhs (mkAuxRecNameMap staged types).2) ∧
      staged.find? finalRule.ctor = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams source.lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧ finalRule.nfields = info.numFields ∧
      nparams + finalRule.nfields = arity 0 types[index].ctors[ctorIndex].type := records.ruleAt index hindex ctorIndex hctor

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (stats : InductiveStats)
      (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
      OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
        stats elimLevel infos source isK preprocessing staged result := metadata.originalRecursorRecords

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (stats : InductiveStats)
        (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
        OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
          stats elimLevel infos source isK preprocessing staged result :=
  Lean4Lean.Environment.addInductive.safeOriginalRecursorRecords env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (stats : InductiveStats)
        (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧ source.lparams = lparams ∧
        OriginalRecursorNames types staged ∧ OriginalRecursorRecords nparams types preprocessing.types.toArray
          stats elimLevel infos source isK preprocessing staged result :=
  Lean4Lean.addDecl.safeInductiveOriginalRecursorRecords env lparams nparams types check fuel hmap

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment) (stats : InductiveStats)
      (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool),
      source.lparams = lparams ∧ RecursorInfoCounts preprocessing.types.toArray infos ∧
      RecursorMinorIndexing preprocessing.types.toArray infos ∧
      LocalRecursorRuleRhsDistinct stats preprocessing.types.toArray infos source staged ∧
      SourceRecursorRecords nparams types preprocessing.types.toArray stats elimLevel infos source isK staged ∧
      OriginalRecursorRecords nparams types preprocessing.types.toArray stats elimLevel infos source isK
        preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, _, _, elimLevel, infos, source, isK,
    _, _, _, _, _, hlevels, hcounts, hindexing, hdistinct, hsource, _, _, hrecords⟩ :=
    metadata.originalRecursorRecordStages
  exact ⟨preprocessing, staged, stats, elimLevel, infos, source, isK,
    hlevels, hcounts, hindexing, hdistinct, hsource, hrecords⟩

example (nparams : Nat) (rewritten : Array InductiveType) (stats : InductiveStats) (elimLevel : Level)
    (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool) (staged : Kernel.Environment) :
    SourceRecursorRecords nparams [] rewritten stats elimLevel infos source isK staged := by
  intro index hindex
  simp at hindex

example (nparams : Nat) (rewritten : Array InductiveType) (stats : InductiveStats) (elimLevel : Level)
    (infos : Array RecInfo) (source : AddInductive.Context) (isK : Bool) (preprocessing : ElimNestedInductive.Result)
    (staged result : Kernel.Environment) : OriginalRecursorRecords nparams [] rewritten stats elimLevel infos source isK
      preprocessing staged result := by
  intro index hindex
  simp at hindex

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.numIndices ≠ stats.nindices[index]!) : False := hwrong header.numIndices

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.numMotives ≠ rewritten.size) : False := hwrong header.numMotives

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.numMinors ≠ (rewritten.toList.flatMap (·.ctors)).length) : False := hwrong header.numMinors

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.k ≠ isK) : False := hwrong header.k

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.levelParams ≠ getRecLevelParams elimLevel lparams) : False := hwrong header.levelParams

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (haux : preprocessing.aux2nested.size ≠ 0)
    (hwrong : after.type ≠ preprocessing.restoreNested staged before.type (mkAuxRecNameMap staged types).2) : False :=
  hwrong (by simpa only [if_neg haux] using restoration.type)

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (index : Nat) (sourceRule finalRule : RecursorRule) (hsource : before.rules[index]? = some sourceRule)
    (hfinal : after.rules[index]? = some finalRule) (haux : preprocessing.aux2nested.size ≠ 0)
    (hwrong : finalRule.rhs ≠ preprocessing.restoreNested staged sourceRule.rhs (mkAuxRecNameMap staged types).2) : False := by
  have hsame := hfinal.symm.trans (restoration.ruleAt index sourceRule hsource)
  simp only [if_neg haux] at hsame
  exact hwrong (congrArg RecursorRule.rhs (Option.some.inj hsame))

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (index : Nat) (rule : RecursorRule) (hsource : before.rules[index]? = some rule)
    (hmissing : after.rules[index]? = none) : False := by
  have hfinal := restoration.ruleAt index rule hsource
  rw [hmissing] at hfinal
  cases hfinal

example {nparams : Nat} {lparams : List Name} {name : Name} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {isK : Bool} {index : Nat} {info : RecursorVal}
    (header : RecursorHeaderMetadata nparams lparams name rewritten stats elimLevel isK index info)
    (hwrong : info.isUnsafe = true) : False := by
  have hfalse := header.isUnsafe.symm.trans hwrong
  cases hfalse

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (haux : preprocessing.aux2nested.size = 0) (hwrong : after.type ≠ before.type) : False :=
  hwrong (by simpa only [if_pos haux] using restoration.type)

example {preprocessing : ElimNestedInductive.Result} {staged : Kernel.Environment} {types : List InductiveType}
    {before after : RecursorVal} (restoration : OriginalRecursorRestoration preprocessing staged types before after)
    (haux : preprocessing.aux2nested.size ≠ 0) (hwrong : after.all ≠ types.map (·.name)) : False :=
  hwrong (by simpa only [if_neg haux] using restoration.all)

example {nparams : Nat} {types : List InductiveType} {rewritten : Array InductiveType}
    {stats : InductiveStats} {elimLevel : Level} {infos : Array RecInfo} {source : AddInductive.Context}
    {isK : Bool} {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (records : OriginalRecursorRecords nparams types rewritten stats elimLevel infos source isK preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hmissing : result.find? (mkRecName types[index].name) = none) : False := by
  obtain ⟨_, _, _, hlookup, _⟩ := records index hindex
  rw [hmissing] at hlookup
  cases hlookup

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq, ``Lean.PersistentArray.toList'_push,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome, `Lean.Expr.mkAppRangeAux.eq_def, ``Expr.abstract_eq]
  let frontend := binding ++ [``Expr.eqv_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``SourceRecursorRecords.ruleSources
  audit ``InductiveStats.SafeRunScope.sourceRecursorRecords [``Expr.instantiate1_eq]
  audit ``restoredRecursorRule.originalRecord
  audit ``OriginalRecursorRuleLookups.restoration
  audit ``SourceRecursorRecords.header
  audit ``OriginalRecursorRestoration.header
  audit ``OriginalRecursorRestoration.type
  audit ``OriginalRecursorRestoration.all
  audit ``OriginalRecursorRestoration.ruleAt
  audit ``SourceRecursorRecords.restoredRecords
  audit ``OriginalRecursorRecords.finalHeader
  audit ``OriginalRecursorRecords.ruleAt
  audit ``SafeInductiveRestorationMetadata.originalRecursorRecordStages binding
  audit ``SafeInductiveRestorationMetadata.originalRecursorRecords binding
  audit ``Lean4Lean.Environment.addInductive.safeOriginalRecursorRecords frontend
  audit ``Lean4Lean.addDecl.safeInductiveOriginalRecursorRecords frontend

end InductiveSourceRecursorRecordsTest
