import Lean4Lean.Verify.InductiveRestorationArity
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open AddInductive.declareConstructors

namespace InductiveSourceArityTest

example (head : Expr) (args : List Expr) (hhead : arity 0 head = 0) :
    arity 0 (Expr.mkAppList head args) = 0 := ElimNestedInductive.mkAppList_arity head args hhead

example (head : Expr) (args : Array Expr) (hhead : arity 0 head = 0) :
    arity 0 (mkAppN head args) = 0 := ElimNestedInductive.mkAppN_arity head args hhead

example (head : Expr) (args : Array Expr) (start : Nat) (hstart : start ≤ args.size)
    (hhead : arity 0 head = 0) : arity 0 (mkAppRange head start args.size args) = 0 :=
  ElimNestedInductive.mkAppRange_tail_arity head args start hstart hhead

example (name : Name) (levels : List Level) (args : Array Expr) :
    arity 0 (mkAppN (.const name levels) args) = 0 := ElimNestedInductive.mkAppN_arity _ _ rfl

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceIfNested lctx params sourceParams type env state).WF fun result =>
      ∀ rewritten, result.1 = some rewritten → arity 0 rewritten = arity 0 type :=
  ElimNestedInductive.replaceIfNested.arity lctx params sourceParams type env state

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceAllNested lctx params sourceParams type env state).WF fun result =>
      arity 0 result.1 = arity 0 type :=
  ElimNestedInductive.replaceAllNested.arity lctx params sourceParams type env state

example (type : Expr) (nparams : Nat)
    (next : LocalContext → Expr → Array Expr → ElimNestedInductive.M Value) :
    ElimNestedInductive.withParams type nparams next =
      (ElimNestedInductive.withParams type nparams (fun lctx remainder params => pure (lctx, remainder, params)) >>=
        fun result => next result.1 result.2.1 result.2.2) := ElimNestedInductive.withParams.bind type nparams next

example (type : Expr) (nparams : Nat) (params : Array Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.withParams type nparams (fun lctx remainder sourceParams => do
      return lctx.mkForall sourceParams (← ElimNestedInductive.replaceAllNested lctx params sourceParams remainder))
      env state).WF fun result => arity 0 result.1 = arity 0 type :=
  ElimNestedInductive.withParams.replaceAllNested_arity type nparams params env state

example (ctor : Constructor) (nparams : Nat) (params : Array Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.withParams ctor.type nparams (fun lctx remainder sourceParams => do
      return { ctor with type := lctx.mkForall sourceParams (← ElimNestedInductive.replaceAllNested lctx params sourceParams remainder) })
      env state).WF fun result =>
      result.1.name = ctor.name ∧ arity 0 result.1.type = arity 0 ctor.type ∧
        ElimNestedInductive.TypePrefix state.newTypes result.2.newTypes :=
  ElimNestedInductive.withParams.rewriteConstructor ctor nparams params env state

example (types : Array InductiveType) : InductiveArityPrefix types types := .refl types

example {first second third : Array InductiveType} (hfirst : InductiveArityPrefix first second)
    (hsecond : InductiveArityPrefix second third) : InductiveArityPrefix first third := hfirst.trans hsecond

example {original rewritten : Array InductiveType} (hprefix : ElimNestedInductive.TypePrefix original rewritten) :
    InductiveArityPrefix original rewritten := hprefix.toArity

example {original rewritten : Array InductiveType} (hprefix : InductiveArityPrefix original rewritten) :
    InductiveSignaturePrefix original rewritten := hprefix.toInductiveSignaturePrefix

example {original rewritten : Array InductiveType} (hprefix : InductiveArityPrefix original rewritten)
    (index : Nat) (hindex : index < original.size) (type : InductiveType)
    (hname : type.name = original[index]!.name) (hheader : type.type = original[index]!.type)
    (hctors : type.ctors.map (·.name) = original[index]!.ctors.map (·.name))
    (harities : type.ctors.map (fun ctor => arity 0 ctor.type) =
      original[index]!.ctors.map (fun ctor => arity 0 ctor.type)) :
    InductiveArityPrefix original (rewritten.set! index type) := hprefix.set index hindex type hname hheader hctors harities

example {original rewritten : Array InductiveType} (hprefix : InductiveArityPrefix original rewritten)
    (index : Nat) (hindex : index < original.size) (ctorIndex : Nat)
    (hctor : ctorIndex < original[index]!.ctors.length) :
    arity 0 rewritten[index]!.ctors[ctorIndex]!.type = arity 0 original[index]!.ctors[ctorIndex]!.type :=
  hprefix.constructorArityAt index hindex ctorIndex hctor

example (nparams : Nat) (lctx : LocalContext) (params : Array Expr) (index fuel : Nat)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.run.loop nparams lctx params index fuel env state).WF fun result =>
      InductiveArityPrefix state.newTypes result.1.types.toArray :=
  ElimNestedInductive.run.loop.arities nparams lctx params index fuel env state

example (fuel nparams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.run fuel nparams types env state).WF fun result =>
      InductiveArityPrefix state.newTypes result.1.types.toArray :=
  ElimNestedInductive.run.arities fuel nparams types env state

example (fuel nparams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (StateT.run' (ElimNestedInductive.run fuel nparams types env) state).WF fun result =>
      InductiveArityPrefix state.newTypes result.types.toArray :=
  ElimNestedInductive.run.arities_run' fuel nparams types env state

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (fuel : FuelConfig) : (inductivePreprocessing env lparams nparams types fuel).WF fun result =>
      InductiveArityPrefix types.toArray result.types.toArray := inductivePreprocessing.arities env lparams nparams types fuel

example {nparams : Nat} {parent : InductiveType} {index : Nat} {info : ConstructorVal}
    (hfields : SourceConstructorFields nparams parent index info) (type : Expr) :
    SourceConstructorFields nparams parent index { info with type } := hfields.restore type

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten) (typeIndex : Nat) (htype : typeIndex < types.length)
    (ctorIndex : Nat) (hctor : ctorIndex < types[typeIndex].ctors.length) (info : ConstructorVal)
    (hlookup : staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info)) :
    SourceConstructorFields nparams types[typeIndex] ctorIndex info :=
  scope.sourceConstructorFields hprefix typeIndex htype ctorIndex hctor info hlookup

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
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      SourceConstructorFieldLookups nparams lparams types preprocessing staged result := metadata.constructorFieldStages

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceConstructorFieldLookups nparams lparams types preprocessing staged result := metadata.sourceConstructorFields

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorFieldLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.Environment.addInductive.safeSourceConstructorFields env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorFieldLookups nparams lparams types preprocessing staged result :=
  Lean4Lean.addDecl.safeInductiveSourceConstructorFields env lparams nparams types check fuel hmap

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceConstructorFieldLookups nparams lparams types preprocessing staged result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) :
    ∃ info : ConstructorVal,
      result.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      SourceConstructorFields nparams types[typeIndex] ctorIndex info := hlookups.finalFields typeIndex htype ctorIndex hctor

example {nparams : Nat} {parent : InductiveType} {index : Nat} {info : ConstructorVal}
    (hfields : SourceConstructorFields nparams parent index info) : nparams ≤ arity 0 parent.ctors[index]!.type := by
  have htotal := hfields.total
  omega

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index < original.size)
    (hchanged : rewritten[index]!.ctors.map (fun ctor => arity 0 ctor.type) ≠
      original[index]!.ctors.map (fun ctor => arity 0 ctor.type)) : ¬ InductiveArityPrefix original rewritten :=
  fun hprefix => hchanged (hprefix.arities index hindex)

example {nparams : Nat} {parent : InductiveType} {index : Nat} {info : ConstructorVal}
    (hwrong : info.numFields ≠ arity 0 parent.ctors[index]!.type - nparams) :
    ¬ SourceConstructorFields nparams parent index info := fun hfields => hwrong hfields.fields

example {nparams : Nat} {parent : InductiveType} {index : Nat} {info : ConstructorVal}
    (htooshort : arity 0 parent.ctors[index]!.type < nparams) : ¬ SourceConstructorFields nparams parent index info := by
  intro hfields
  have htotal := hfields.total
  omega

example {nparams : Nat} {lparams : List Name} {types : List InductiveType}
    {preprocessing : ElimNestedInductive.Result} {staged result : Kernel.Environment}
    (hlookups : SourceConstructorFieldLookups nparams lparams types preprocessing staged result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length)
    (hmissing : result.find? types[typeIndex].ctors[ctorIndex].name = none) : False := by
  obtain ⟨_, hlookup, _, _⟩ := hlookups.finalFields typeIndex htype ctorIndex hctor
  rw [hmissing] at hlookup
  cases hlookup

example (name : Name) (domain body : Expr) (bi : BinderInfo) (data : MData) :
    arity 0 (.mdata data (.forallE name domain body bi)) = 0 := rfl

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ interfaces
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let shape := [`Lean.Expr.mkAppRangeAux.eq_def]
  let binding := shape ++ [``Lean.PersistentArray.toList'_push, ``Expr.instantiate1_eq,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert, ``Expr.abstract_eq]
  let frontend := binding ++ [``Lean.PersistentHashMap.findAux_isSome, ``Expr.eqv_eq,
    ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq]
  audit ``ElimNestedInductive.mkAppList_arity
  audit ``ElimNestedInductive.mkAppN_arity
  audit ``ElimNestedInductive.mkAppRange_tail_arity shape
  audit ``ElimNestedInductive.replaceIfNested.arity shape
  audit ``ElimNestedInductive.replaceAllNested.arity shape
  audit ``ElimNestedInductive.withParams.bind
  audit ``ElimNestedInductive.withParams.replaceAllNested_arity binding
  audit ``ElimNestedInductive.withParams.rewriteConstructor binding
  audit ``InductiveArityPrefix.refl
  audit ``InductiveArityPrefix.trans
  audit ``ElimNestedInductive.TypePrefix.toArity
  audit ``InductiveArityPrefix.set
  audit ``InductiveArityPrefix.constructorArityAt
  audit ``ElimNestedInductive.run.loop.arities binding
  audit ``ElimNestedInductive.run.arities binding
  audit ``ElimNestedInductive.run.arities_run' binding
  audit ``inductivePreprocessing.arities binding
  audit ``SourceConstructorFields.restore
  audit ``InductiveStats.SafeRunScope.sourceConstructorFields
  audit ``SourceConstructorFieldLookups.finalFields
  audit ``SafeInductiveRestorationMetadata.constructorFieldStages binding
  audit ``SafeInductiveRestorationMetadata.sourceConstructorFields binding
  audit ``Lean4Lean.Environment.addInductive.safeSourceConstructorFields frontend
  audit ``Lean4Lean.addDecl.safeInductiveSourceConstructorFields frontend

end InductiveSourceArityTest
