import Lean4Lean.Verify.InductiveRestorationRules
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open AddInductive.declareConstructors

namespace InductiveSourceRulesTest

example {original rewritten : Array InductiveType} (hprefix : InductiveSignaturePrefix original rewritten)
    (index : Nat) (hindex : index ≤ original.size) :
    recursorMinorOffset rewritten index = recursorMinorOffset original index := hprefix.minorOffset index hindex

example {original rewritten : Array InductiveType} (hprefix : InductiveSignaturePrefix original rewritten) :
    recursorMinorOffset rewritten original.size = recursorMinorOffset original original.size :=
  hprefix.minorOffset original.size (Nat.le_refl _)

example {original rewritten : Array InductiveType} {infos : Array RecInfo}
    (hprefix : InductiveSignaturePrefix original rewritten) (hindexing : RecursorMinorIndexing rewritten infos)
    (parent : Nat) (hparent : parent < original.size) (index : Nat)
    (hindex : index < original[parent]!.ctors.length) :
    ∃ minor, infos[parent]!.minors[index]? = some minor ∧
      (infos.flatMap (·.minors))[recursorMinorOffset original parent + index]? = some minor :=
  hprefix.sourceMinor hindexing parent hparent index hindex

example {original rewritten : Array InductiveType} (hprefix : InductiveArityPrefix original rewritten)
    (nparams index : Nat) (hindex : index < original.size) :
    rewritten[index]!.ctors.map (fun ctor => (ctor.name, arity 0 ctor.type - nparams)) =
      original[index]!.ctors.map (fun ctor => (ctor.name, arity 0 ctor.type - nparams)) :=
  hprefix.constructorFields nparams index hindex

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) : rules.length = ctors.length := hrules.count

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) : rules.map (·.ctor) = ctors.map (·.name) := hrules.names

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) :
    rules.map (·.nfields) = ctors.map (fun ctor => arity 0 ctor.type - nparams) := hrules.fieldCounts

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (index : Nat) (ctor : Constructor)
    (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧ rule.ctor = ctor.name ∧ rule.nfields = arity 0 ctor.type - nparams :=
  hrules.at index ctor hctor

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) (index : Nat) (hindex : index < types.length)
    (rules : List RecursorRule) (hrules : SourceRecursorRules nparams types[index].ctors rules) :
    SourceRecursorRuleConstructors nparams original.lparams types[index] rules staged :=
  scope.sourceRuleConstructors hprefix index hindex rules hrules

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : AddInductive.Context),
      ({ root with env := constructors } : AddInductive.Context).RecursorScopeFrame source ∧
      RecursorInfoCounts rewritten infos ∧ RecursorMinorIndexing rewritten infos ∧
      LocalRecursorRuleRhsDistinct stats rewritten infos source staged ∧
      SourceRecursorRuleSources nparams types rewritten stats elimLevel infos source staged :=
  scope.sourceRuleSources hprefix

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (nameMap : NameMap Name) (recName : Name) (rule : RecursorRule) :
    (restoredRecursorRule preprocessing staged nameMap recName rule).nfields = rule.nfields :=
  restoredRecursorRule.fieldCount preprocessing staged nameMap recName rule

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allNames : List Name) (nameMap : NameMap Name) (recName : Name) (recursor : RecursorVal)
    (index : Nat) (rule : RecursorRule) (hrule : recursor.rules[index]? = some rule) :
    (restoredRecursorVal preprocessing staged allNames nameMap recName recursor).rules[index]? =
      some (restoredRecursorRule preprocessing staged nameMap recName rule) :=
  restoredRecursorVal.ruleAt preprocessing staged allNames nameMap recName recursor index rule hrule

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Kernel.Environment) (nameMap : NameMap Name) (recName : Name) :
    (rules.map (restoredRecursorRule preprocessing staged nameMap recName)).map (fun rule => (rule.ctor, rule.nfields)) =
      ctors.map (fun ctor =>
        (if nameMap.getD recName recName == recName then ctor.name else preprocessing.restoreCtorName staged ctor.name,
          arity 0 ctor.type - nparams)) := hrules.restoredPairs preprocessing staged nameMap recName

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Kernel.Environment) (nameMap : NameMap Name) (recName : Name)
    (hunchanged : nameMap.getD recName recName = recName) :
    SourceRecursorRules nparams ctors (rules.map (restoredRecursorRule preprocessing staged nameMap recName)) := by
  simpa only [hunchanged, BEq.rfl, ↓reduceIte] using hrules.restoredPairs preprocessing staged nameMap recName

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Kernel.Environment) (nameMap : NameMap Name) (recName : Name)
    (hrenamed : nameMap.getD recName recName ≠ recName) :
    (rules.map (restoredRecursorRule preprocessing staged nameMap recName)).map (·.ctor) =
      ctors.map (fun ctor => preprocessing.restoreCtorName staged ctor.name) := by
  have hpairs := hrules.restoredPairs preprocessing staged nameMap recName
  simpa only [List.map_map, beq_eq_false_iff_ne.mpr hrenamed, Bool.false_eq_true, ↓reduceIte] using
    congrArg (List.map Prod.fst) hpairs

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
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
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type := hlookups.finalRule index hindex ctorIndex hctor

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) :
    ∃ recursor : RecursorVal,
      result.find? recursor.name = some (.recInfo recursor) ∧ recursor.rules.length = types[index].ctors.length ∧
      recursor.rules.map (·.nfields) = types[index].ctors.map (fun ctor => arity 0 ctor.type - nparams) :=
  hlookups.finalRecursor index hindex

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hempty : types[index].ctors = []) :
    ∃ recursor : RecursorVal, result.find? recursor.name = some (.recInfo recursor) ∧ recursor.rules = [] := by
  obtain ⟨recursor, hlookup, hcount, _⟩ := hlookups.finalRecursor index hindex
  exact ⟨recursor, hlookup, List.length_eq_zero_iff.mp (by simpa only [hempty, List.length_nil] using hcount)⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
      (stats : InductiveStats) (root : AddInductive.Context) (constructors : Kernel.Environment)
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
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result := metadata.sourceRecursorRuleStages

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceRecursorRuleLookups nparams lparams types preprocessing staged result := metadata.sourceRecursorRules

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceRecursorRuleLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.Environment.addInductive.safeSourceRecursorRules env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceRecursorRuleLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.addDecl.safeInductiveSourceRecursorRules env lparams nparams types check fuel hmap

example (nparams : Nat) : SourceRecursorRules nparams [] [] := rfl

example (nparams : Nat) (lparams : List Name) (preprocessing : ElimNestedInductive.Result)
    (staged result : Kernel.Environment) : SourceRecursorRuleLookups nparams lparams [] preprocessing staged result := by
  intro index hindex
  simp at hindex

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hcount : rules.length ≠ ctors.length) : ¬ SourceRecursorRules nparams ctors rules := fun hrules => hcount hrules.count

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hnames : rules.map (·.ctor) ≠ ctors.map (·.name)) : ¬ SourceRecursorRules nparams ctors rules :=
  fun hrules => hnames hrules.names

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (index : Nat) (ctor : Constructor)
    (hctor : ctors[index]? = some ctor) (hmissing : rules[index]? = none) : False := by
  obtain ⟨rule, hrule, _, _⟩ := hrules.at index ctor hctor
  rw [hmissing] at hrule
  cases hrule

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (index : Nat) (ctor : Constructor) (rule : RecursorRule)
    (hctor : ctors[index]? = some ctor) (hrule : rules[index]? = some rule)
    (hwrong : rule.nfields ≠ arity 0 ctor.type - nparams) : False := by
  obtain ⟨actual, hactual, _, hfields⟩ := hrules.at index ctor hctor
  have heq : actual = rule := Option.some.inj (hactual.symm.trans hrule)
  exact hwrong (heq ▸ hfields)

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index ≤ original.size)
    (hchanged : recursorMinorOffset rewritten index ≠ recursorMinorOffset original index) :
    ¬ InductiveSignaturePrefix original rewritten := fun hprefix => hchanged (hprefix.minorOffset index hindex)

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length)
    (hmissing : ∀ recursor : RecursorVal, result.find? recursor.name ≠ some (.recInfo recursor)) : False := by
  obtain ⟨recursor, hlookup, _, _⟩ := hlookups.finalRecursor index hindex
  exact hmissing recursor hlookup

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let arity := [``Expr.instantiate1_eq]
  let binding := arity ++ [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert, `Lean.Expr.mkAppRangeAux.eq_def, ``Expr.abstract_eq]
  let frontend := binding ++ [``Lean.PersistentHashMap.findAux_isSome, ``Expr.eqv_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``InductiveSignaturePrefix.minorOffset
  audit ``InductiveSignaturePrefix.sourceMinor
  audit ``InductiveArityPrefix.constructorFields
  audit ``SourceRecursorRules.count
  audit ``SourceRecursorRules.names
  audit ``SourceRecursorRules.fieldCounts
  audit ``SourceRecursorRules.at
  audit ``InductiveStats.SafeRunScope.sourceRuleConstructors
  audit ``InductiveStats.SafeRunScope.sourceRuleSources arity
  audit ``restoredRecursorRule.fieldCount
  audit ``restoredRecursorVal.ruleAt
  audit ``SourceRecursorRules.restoredPairs
  audit ``SourceRecursorRuleLookups.finalRule
  audit ``SourceRecursorRuleLookups.finalRecursor
  audit ``SafeInductiveRestorationMetadata.sourceRecursorRuleStages binding
  audit ``SafeInductiveRestorationMetadata.sourceRecursorRules binding
  audit ``Lean4Lean.Environment.addInductive.safeSourceRecursorRules frontend
  audit ``Lean4Lean.addDecl.safeInductiveSourceRecursorRules frontend

end InductiveSourceRulesTest
