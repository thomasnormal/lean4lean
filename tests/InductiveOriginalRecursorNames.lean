import Lean4Lean.Verify.InductiveRestorationRuleNames
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open AddInductive.declareConstructors

namespace InductiveOriginalRecursorNamesTest

example (stats : InductiveStats) (nparams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (ctx : AddInductive.Context)
    (hmap : ctx.env.constants.WF) (hsize : stats.nindices.size = types.size) :
    (declareInductiveTypes stats nparams types numNested isUnsafe ctx).WF fun _ =>
      (types.toList.map (·.name)).Nodup :=
  declareInductiveTypes.namesNodup stats nparams types numNested isUnsafe ctx hmap hsize

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : AddInductive.Context) (hmap : ctx.env.constants.WF) :
    (AddInductive.run nparams types numNested ctx).WF fun _ => (types.map (·.name)).Nodup :=
  AddInductive.run.datatypeNamesNodup nparams types numNested ctx hmap

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : AddInductive.Context) (result : Kernel.Environment) (hmap : ctx.env.constants.WF)
    (hrun : AddInductive.run nparams types numNested ctx = .ok result) :
    (types.map (·.name)).Nodup := AddInductive.run.datatypeNamesNodup nparams types numNested ctx hmap result hrun

example {original rewritten : Array InductiveType} (hprefix : InductiveNamePrefix original rewritten)
    (hnodup : (rewritten.toList.map (·.name)).Nodup) (index : Nat) (hindex : index < original.size) :
    original[index]!.name ∉ (rewritten.toList.map (·.name)).drop original.size :=
  hprefix.suffixNotMem hnodup index hindex

example {first second : Name} (heq : mkRecName first = mkRecName second) : first = second :=
  mkRecName_injective heq

example (env : Kernel.Environment) (types : List InductiveType) (key : Name)
    (hnot : key ∉ (mkAuxRecNameMap env types).1) :
    (mkAuxRecNameMap env types).2.find? key = none := mkAuxRecNameMap.find?_eq_none env types key hnot

example (env : Kernel.Environment) (types : List InductiveType) (key : Name)
    (hnot : key ∉ (mkAuxRecNameMap env types).1) :
    (mkAuxRecNameMap env types).2.getD key key = key := mkAuxRecNameMap.getD_eq_self env types key hnot

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveNamePrefix types.toArray rewritten) (hnodup : (rewritten.toList.map (·.name)).Nodup) :
    OriginalRecursorNames types staged := scope.originalRecursorNames hprefix hnodup

example {types : List InductiveType} {staged : Kernel.Environment} (hnames : OriginalRecursorNames types staged)
    (index : Nat) (hindex : index < types.length) :
    mkRecName types[index].name ∉ (mkAuxRecNameMap staged types).1 := hnames.outside index hindex

example {types : List InductiveType} {staged : Kernel.Environment} (hnames : OriginalRecursorNames types staged)
    (index : Nat) (hindex : index < types.length) :
    (mkAuxRecNameMap staged types).2.find? (mkRecName types[index].name) = none := hnames.absent index hindex

example {types : List InductiveType} {staged : Kernel.Environment} (hnames : OriginalRecursorNames types staged)
    (index : Nat) (hindex : index < types.length) :
    (mkAuxRecNameMap staged types).2.getD (mkRecName types[index].name) (mkRecName types[index].name) =
      mkRecName types[index].name := hnames.identity index hindex

example {nparams : Nat} {ctors : List Constructor} {rules : List RecursorRule}
    (hrules : SourceRecursorRules nparams ctors rules) (preprocessing : ElimNestedInductive.Result)
    (staged : Kernel.Environment) (nameMap : NameMap Name) (recName : Name)
    (hidentity : nameMap.getD recName recName = recName) :
    SourceRecursorRules nparams ctors (rules.map (restoredRecursorRule preprocessing staged nameMap recName)) :=
  hrules.restoreOriginal preprocessing staged nameMap recName hidentity

example {nparams : Nat} {lparams : List Name} {parent : InductiveType} {rules : List RecursorRule}
    {staged : Kernel.Environment} (hconstructors : SourceRecursorRuleConstructors nparams lparams parent rules staged)
    (preprocessing : ElimNestedInductive.Result) (nameMap : NameMap Name) (recName : Name)
    (hidentity : nameMap.getD recName recName = recName) :
    SourceRecursorRuleConstructors nparams lparams parent
      (rules.map (restoredRecursorRule preprocessing staged nameMap recName)) staged :=
  hconstructors.restoreOriginal preprocessing nameMap recName hidentity

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceRecursorRuleLookups nparams lparams types preprocessing staged result)
    (hnames : OriginalRecursorNames types staged) :
    OriginalRecursorRuleLookups nparams lparams types preprocessing staged result := hlookups.originalNames hnames

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (ctorIndex : Nat) (hctor : ctorIndex < types[index].ctors.length) :
    ∃ (recursor : RecursorVal) (rule : RecursorRule) (info : ConstructorVal),
      result.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      recursor.rules.length = types[index].ctors.length ∧ recursor.rules[ctorIndex]? = some rule ∧
      rule.ctor = types[index].ctors[ctorIndex].name ∧ staged.find? rule.ctor = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[index] ctorIndex info ∧
      SourceConstructorFields nparams types[index] ctorIndex info ∧ rule.nfields = info.numFields ∧
      nparams + rule.nfields = arity 0 types[index].ctors[ctorIndex].type := hlookups.at index hindex ctorIndex hctor

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) :
    ∃ recursor : RecursorVal, result.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      recursor.name = mkRecName types[index].name ∧ recursor.rules.map (·.ctor) = types[index].ctors.map (·.name) ∧
      recursor.rules.map (·.nfields) = types[index].ctors.map (fun ctor => arity 0 ctor.type - nparams) := by
  obtain ⟨_, final, _, hlookup, hname, hrules, _⟩ := hlookups index hindex
  exact ⟨final, hlookup, hname, hrules.names, hrules.fieldCounts⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
      OriginalRecursorRuleLookups nparams lparams types preprocessing staged result := metadata.originalRecursorRules

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
        OriginalRecursorRuleLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.Environment.addInductive.safeOriginalRecursorRules env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧ OriginalRecursorNames types staged ∧
        OriginalRecursorRuleLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.addDecl.safeInductiveOriginalRecursorRules env lparams nparams types check fuel hmap

example (env : Kernel.Environment) (key : Name) : (mkAuxRecNameMap env []).2.find? key = none :=
  mkAuxRecNameMap.find?_eq_none env [] key (by change key ∉ ([] : List Name); simp)

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType) (key : Name)
    (hlookup : env.find? type.name = none) : (mkAuxRecNameMap env (type :: types)).2.getD key key = key :=
  mkAuxRecNameMap.getD_eq_self env (type :: types) key (by
    simp only [mkAuxRecNameMap, hlookup]
    change key ∉ ([] : List Name)
    simp)

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType) (key : Name)
    (info : AxiomVal) (hlookup : env.find? type.name = some (.axiomInfo info)) :
    (mkAuxRecNameMap env (type :: types)).2.find? key = none :=
  mkAuxRecNameMap.find?_eq_none env (type :: types) key (by
    simp only [mkAuxRecNameMap, hlookup]
    change key ∉ ([] : List Name)
    simp)

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType) (key : Name)
    (info : InductiveVal) (hlookup : env.find? type.name = some (.inductInfo info))
    (hshort : info.all.length ≤ (type :: types).length) :
    (mkAuxRecNameMap env (type :: types)).2.getD key key = key :=
  mkAuxRecNameMap.getD_eq_self env (type :: types) key (by
    rw [mkAuxRecNameMap.names env type types info hlookup, if_neg (Nat.not_lt.mpr hshort)]
    simp)

example (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : AddInductive.Context) (result : Kernel.Environment) (hmap : ctx.env.constants.WF)
    (hduplicate : ¬ (types.map (·.name)).Nodup) : AddInductive.run nparams types numNested ctx ≠ .ok result :=
  fun hrun => hduplicate (AddInductive.run.datatypeNamesNodup nparams types numNested ctx hmap result hrun)

example {original rewritten : Array InductiveType} (hprefix : InductiveNamePrefix original rewritten)
    (index : Nat) (hindex : index < original.size)
    (hoverlap : original[index]!.name ∈ (rewritten.toList.map (·.name)).drop original.size) :
    ¬ (rewritten.toList.map (·.name)).Nodup := fun hnodup => hprefix.suffixNotMem hnodup index hindex hoverlap

example {types : List InductiveType} {staged : Kernel.Environment} (index : Nat) (hindex : index < types.length)
    (hoverlap : mkRecName types[index].name ∈ (mkAuxRecNameMap staged types).1) :
    ¬ OriginalRecursorNames types staged := fun hnames => hnames.outside index hindex hoverlap

example {types : List InductiveType} {staged : Kernel.Environment} (index : Nat) (hindex : index < types.length)
    (hchanged : (mkAuxRecNameMap staged types).2.getD (mkRecName types[index].name) (mkRecName types[index].name) ≠
      mkRecName types[index].name) : ¬ OriginalRecursorNames types staged := fun hnames => hchanged (hnames.identity index hindex)

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hmissing : result.find? (mkRecName types[index].name) = none) : False := by
  obtain ⟨_, _, _, hlookup, _⟩ := hlookups index hindex
  rw [hmissing] at hlookup
  cases hlookup

example (nparams : Nat) (lparams : List Name) (preprocessing : ElimNestedInductive.Result)
    (staged result : Kernel.Environment) : OriginalRecursorRuleLookups nparams lparams [] preprocessing staged result := by
  intro index hindex
  simp at hindex

example (env : Kernel.Environment) (type : InductiveType) (info : InductiveVal)
    (hlookup : env.find? type.name = some (.inductInfo info)) (hall : info.all = [type.name, type.name]) :
    ¬ OriginalRecursorNames [type] env := by
  intro hnames
  have hnot := hnames.outside 0 (by simp)
  rw [mkAuxRecNameMap.names env type [] info hlookup] at hnot
  simp [hall] at hnot

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hempty : types[index].ctors = []) :
    ∃ recursor : RecursorVal, result.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      recursor.rules = [] := by
  obtain ⟨_, final, _, hlookup, _, hrules, _⟩ := hlookups index hindex
  exact ⟨final, hlookup, List.eq_nil_of_length_eq_zero (by simpa only [hempty, List.length_nil] using hrules.count)⟩

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hdirect : preprocessing.aux2nested.size = 0) :
    ∃ recursor : RecursorVal, staged.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      result.find? (mkRecName types[index].name) = some (.recInfo recursor) := by
  obtain ⟨source, final, hsource, hfinal, _, _, _, heq, _⟩ := hlookups index hindex
  exact ⟨source, hsource, by simpa only [heq hdirect] using hfinal⟩

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : OriginalRecursorRuleLookups nparams lparams types preprocessing staged result)
    (index : Nat) (hindex : index < types.length) (hnested : preprocessing.aux2nested.size ≠ 0) :
    ∃ recursor : RecursorVal, staged.find? (mkRecName types[index].name) = some (.recInfo recursor) ∧
      result.find? (mkRecName types[index].name) = some (.recInfo
        (restoredRecursorVal preprocessing staged (types.map (·.name)) (mkAuxRecNameMap staged types).2
          (mkRecName types[index].name) recursor)) := by
  obtain ⟨source, final, hsource, hfinal, _, _, _, _, heq⟩ := hlookups index hindex
  exact ⟨source, hsource, by simpa only [heq hnested] using hfinal⟩

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let maps := [``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome]
  let binding := maps ++ [``Expr.instantiate1_eq, ``Lean.PersistentArray.toList'_push,
    `Lean.Expr.mkAppRangeAux.eq_def, ``Expr.abstract_eq]
  let frontend := binding ++ [``Expr.eqv_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``declareInductiveTypes.namesNodup maps
  audit ``AddInductive.run.datatypeNamesNodup maps
  audit ``InductiveNamePrefix.suffixNotMem
  audit ``mkAuxRecNameMap.find?_eq_none
  audit ``mkAuxRecNameMap.getD_eq_self
  audit ``mkRecName_injective
  audit ``InductiveStats.SafeRunScope.originalRecursorNames
  audit ``SourceRecursorRules.restoreOriginal
  audit ``SourceRecursorRuleConstructors.restoreOriginal
  audit ``SourceRecursorRuleLookups.originalNames
  audit ``OriginalRecursorRuleLookups.at
  audit ``SafeInductiveRestorationMetadata.originalRecursorRuleStages binding
  audit ``SafeInductiveRestorationMetadata.originalRecursorRules binding
  audit ``Lean4Lean.Environment.addInductive.safeOriginalRecursorRules frontend
  audit ``Lean4Lean.addDecl.safeInductiveOriginalRecursorRules frontend

end InductiveOriginalRecursorNamesTest
