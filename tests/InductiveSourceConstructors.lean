import Lean4Lean.Verify.InductiveRestorationConstructors
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveSourceConstructorsTest

example (types : Array InductiveType) : ElimNestedInductive.TypePrefix types types := .refl types

example {first second third : Array InductiveType} (hfirst : ElimNestedInductive.TypePrefix first second)
    (hsecond : ElimNestedInductive.TypePrefix second third) : ElimNestedInductive.TypePrefix first third :=
  hfirst.trans hsecond

example (types : Array InductiveType) (type : InductiveType) : ElimNestedInductive.TypePrefix types (types.push type) :=
  .push types type

example {original rewritten : Array InductiveType} (hprefix : ElimNestedInductive.TypePrefix original rewritten) :
    InductiveSignaturePrefix original rewritten := hprefix.toSignature

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceIfNested lctx params sourceParams type env state).WF fun result =>
      ElimNestedInductive.TypePrefix state.newTypes result.2.newTypes :=
  ElimNestedInductive.replaceIfNested.typesPrefix lctx params sourceParams type env state

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceAllNested lctx params sourceParams type env state).WF fun result =>
      ElimNestedInductive.TypePrefix state.newTypes result.2.newTypes :=
  ElimNestedInductive.replaceAllNested.typesPrefix lctx params sourceParams type env state

example (type : Expr) (nparams : Nat)
    (next : LocalContext → Expr → Array Expr → ElimNestedInductive.M Value)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) (post : Value × ElimNestedInductive.State → Prop)
    (hnext : ∀ lctx remainder params current, current.newTypes = state.newTypes →
      (next lctx remainder params env current).WF post) :
    (ElimNestedInductive.withParams type nparams next env state).WF post :=
  ElimNestedInductive.withParams.newTypesFrame type nparams next env state post hnext

example (types : Array InductiveType) : InductiveSignaturePrefix types types := .refl types

example {first second third : Array InductiveType} (hfirst : InductiveSignaturePrefix first second)
    (hsecond : InductiveSignaturePrefix second third) : InductiveSignaturePrefix first third := hfirst.trans hsecond

example {original rewritten : Array InductiveType} (hprefix : InductiveSignaturePrefix original rewritten)
    (index : Nat) (hindex : index < original.size) (type : InductiveType)
    (hname : type.name = original[index]!.name) (hheader : type.type = original[index]!.type)
    (hctors : type.ctors.map (·.name) = original[index]!.ctors.map (·.name)) :
    InductiveSignaturePrefix original (rewritten.set! index type) := hprefix.set index hindex type hname hheader hctors

example {original rewritten : Array InductiveType} (hprefix : InductiveSignaturePrefix original rewritten)
    (index : Nat) (hindex : index < original.size) :
    rewritten[index]!.ctors.length = original[index]!.ctors.length := hprefix.constructorCount index hindex

example {original rewritten : Array InductiveType} (hprefix : InductiveSignaturePrefix original rewritten)
    (index : Nat) (hindex : index < original.size) (ctorIndex : Nat)
    (hctor : ctorIndex < original[index]!.ctors.length) :
    rewritten[index]!.ctors[ctorIndex]!.name = original[index]!.ctors[ctorIndex]!.name :=
  hprefix.constructorNameAt index hindex ctorIndex hctor

example (fuel nparams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (StateT.run' (ElimNestedInductive.run fuel nparams types env) state).WF fun result =>
      InductiveSignaturePrefix state.newTypes result.types.toArray :=
  ElimNestedInductive.run.signatures_run' fuel nparams types env state

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (fuel : FuelConfig) (preprocessing : ElimNestedInductive.Result)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing) :
    InductiveSignaturePrefix types.toArray preprocessing.types.toArray :=
  inductivePreprocessing.signatures env lparams nparams types fuel preprocessing hpre

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveSignaturePrefix types.toArray rewritten)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) :
    ∃ (header : InductiveVal) (info : ConstructorVal),
      staged.find? types[typeIndex].name = some (.inductInfo header) ∧
      header.type = types[typeIndex].type ∧ header.ctors = types[typeIndex].ctors.map (·.name) ∧
      staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams original.lparams types[typeIndex] ctorIndex info :=
  scope.sourceConstructor hprefix typeIndex htype ctorIndex hctor

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
      (stats : InductiveStats) (root : AddInductive.Context) (constructors : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      SourceConstructorLookups nparams lparams types preprocessing staged result := metadata.constructorStages

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
      SourceConstructorLookups nparams lparams types preprocessing staged result := metadata.sourceConstructors

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.Environment.addInductive.safeSourceConstructorMetadata env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.addDecl.safeInductiveSourceConstructorMetadata env lparams nparams types check fuel hmap

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceConstructorLookups nparams lparams types preprocessing staged result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) (hnoaux : preprocessing.aux2nested.size = 0) :
    ∃ info : ConstructorVal, SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      result.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) := by
  obtain ⟨info, _, hmetadata, hdirect, _⟩ := hlookups typeIndex htype ctorIndex hctor
  exact ⟨info, hmetadata, hdirect hnoaux⟩

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceConstructorLookups nparams lparams types preprocessing staged result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) (hnested : preprocessing.aux2nested.size ≠ 0) :
    ∃ info : ConstructorVal, SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      result.find? types[typeIndex].ctors[ctorIndex].name =
        some (.ctorInfo { info with type := preprocessing.restoreNested staged info.type }) := by
  obtain ⟨info, _, hmetadata, _, hrestored⟩ := hlookups typeIndex htype ctorIndex hctor
  exact ⟨info, hmetadata, hrestored hnested⟩

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index < original.size)
    (htype : rewritten[index]!.type ≠ original[index]!.type) : ¬ InductiveSignaturePrefix original rewritten :=
  fun hprefix => htype (hprefix.headers index hindex)

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index < original.size)
    (hctors : rewritten[index]!.ctors.map (·.name) ≠ original[index]!.ctors.map (·.name)) :
    ¬ InductiveSignaturePrefix original rewritten := fun hprefix => hctors (hprefix.constructors index hindex)

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index < original.size)
    (hcount : rewritten[index]!.ctors.length ≠ original[index]!.ctors.length) :
    ¬ InductiveSignaturePrefix original rewritten := fun hprefix => hcount (hprefix.constructorCount index hindex)

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveSignaturePrefix types.toArray rewritten)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length)
    (hmissing : staged.find? types[typeIndex].ctors[ctorIndex].name = none) : False := by
  obtain ⟨_, _, _, _, _, hlookup, _⟩ := scope.sourceConstructor hprefix typeIndex htype ctorIndex hctor
  rw [hmissing] at hlookup
  cases hlookup

private def audit (theoremName : Name) (publicProof := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if publicProof then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentArray.toList'_push,
    ``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``ElimNestedInductive.TypePrefix.refl
  audit ``ElimNestedInductive.TypePrefix.trans
  audit ``ElimNestedInductive.TypePrefix.push
  audit ``ElimNestedInductive.TypePrefix.toNames
  audit ``ElimNestedInductive.TypePrefix.toSignature
  audit ``ElimNestedInductive.withParams.newTypesFrame
  audit ``ElimNestedInductive.withParams.typesPrefix
  audit ``ElimNestedInductive.replaceParams.typesPrefix
  audit ``ElimNestedInductive.replaceIfNested.typesPrefix
  audit ``ElimNestedInductive.replaceAllNested.typesPrefix
  audit ``InductiveSignaturePrefix.refl
  audit ``InductiveSignaturePrefix.trans
  audit ``InductiveSignaturePrefix.set
  audit ``InductiveSignaturePrefix.constructorCount
  audit ``InductiveSignaturePrefix.constructorNameAt
  audit ``ElimNestedInductive.run.loop.signatures
  audit ``ElimNestedInductive.run.signatures
  audit ``ElimNestedInductive.run.signatures_run'
  audit ``inductivePreprocessing.signatures
  audit ``InductiveStats.SafeRunScope.sourceConstructor
  audit ``SafeInductiveRestorationMetadata.constructorStages
  audit ``SafeInductiveRestorationMetadata.sourceConstructors
  audit ``Lean4Lean.Environment.addInductive.safeSourceConstructorMetadata true
  audit ``Lean4Lean.addDecl.safeInductiveSourceConstructorMetadata true

end InductiveSourceConstructorsTest
