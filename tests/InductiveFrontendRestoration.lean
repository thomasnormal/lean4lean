import Lean4Lean.Verify.InductiveRestorationConstructors
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveFrontendRestorationTest

example {allowed : ConstantInfo → Prop} {original current result : Kernel.Environment}
    (first : FreshRegistrationTrace allowed original current)
    (second : FreshRegistrationTrace allowed current result) : FreshRegistrationTrace allowed original result :=
  first.trans second

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF) :
    result.constants.WF ∧ (∀ name info, original.find? name = some info → result.find? name = some info) :=
  trace.preserves hwf

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (hlookup : result.find? name = some info) :
    original.find? name = some info ∨ allowed info := trace.lookup hwf name info hlookup

example {allowed : ConstantInfo → Prop} {original result : Kernel.Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (habsent : original.find? name = none)
    (hlookup : result.find? name = some info) : allowed info := trace.newLookup hwf name info habsent hlookup

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (recName : Name) (env : Kernel.Environment) :
    (restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive recName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveRecursor.trace preprocessing staged allIndNames recNameMap allowPrimitive recName env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (ctorName : Name) (env : Kernel.Environment) :
    (restoreInductiveConstructor preprocessing staged allowPrimitive ctorName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveConstructor.trace preprocessing staged allIndNames recNameMap allowPrimitive ctorName env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) (env : Kernel.Environment) :
    (restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 :=
  restoreInductiveDatatype.trace preprocessing staged allIndNames recNameMap allowPrimitive indType env

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (env : Kernel.Environment) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2) env result.2 :=
  restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel env

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result) :
    result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) := scope.preserves

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.Environment.addInductive.safeFrontend env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  Lean4Lean.Environment.addInductive.safePreserves env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.addDecl.safeInductiveFrontend env lparams nparams types check fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  Lean4Lean.addDecl.safeInductivePreserves env lparams nparams types check fuel hmap

example {records : List ConstantInfo} {env result : Kernel.Environment}
    (installed : RestoredRecordsInstalled records env)
    (preserves : ∀ name info, env.find? name = some info → result.find? name = some info) :
    RestoredRecordsInstalled records result := installed.mono preserves

example (env : Kernel.Environment) (hwf : env.constants.WF) : RestoredRegistrationReceipt env [] env :=
  .empty env hwf

example {original current result : Kernel.Environment} {first second : List ConstantInfo}
    (left : RestoredRegistrationReceipt original first current)
    (right : RestoredRegistrationReceipt current second result) :
    RestoredRegistrationReceipt original (first ++ second) result := left.trans right

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (name : Name) (info : RecursorVal) (hlookup : staged.find? name = some (.recInfo info))
    (env : Kernel.Environment) (hwf : env.constants.WF) :
    (restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive name env).WF fun result =>
      RestoredRegistrationReceipt env
        (restoredRecursorRecords preprocessing staged allIndNames recNameMap name) result.2 :=
  restoreInductiveRecursor.installed preprocessing staged allIndNames recNameMap allowPrimitive name info hlookup env hwf

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allowPrimitive : Bool) (name : Name) (info : ConstructorVal)
    (hlookup : staged.find? name = some (.ctorInfo info)) (env : Kernel.Environment) (hwf : env.constants.WF) :
    (restoreInductiveConstructor preprocessing staged allowPrimitive name env).WF fun result =>
      result.1 = .yield PUnit.unit ∧ RestoredRegistrationReceipt env
        (restoredConstructorRecords preprocessing staged name) result.2 :=
  restoreInductiveConstructor.installed preprocessing staged allowPrimitive name info hlookup env hwf

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) (hsources : RestorationDatatypeSources staged indType)
    (env : Kernel.Environment) (hwf : env.constants.WF) :
    (restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType env).WF fun result =>
      result.1 = .yield PUnit.unit ∧ RestoredRegistrationReceipt env
        (restoredDatatypeRecords preprocessing staged allIndNames recNameMap indType) result.2 :=
  restoreInductiveDatatype.installed preprocessing staged allIndNames recNameMap allowPrimitive indType hsources env hwf

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hsources : RestorationSources staged types) (env : Kernel.Environment) (hwf : env.constants.WF) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result.2 :=
  restoreInductiveEnvironment.installed preprocessing staged types lparams allowPrimitive fuel hsources env hwf

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hlookup : staged.find? indType.name = some (.inductInfo info)) :
    result.find? info.name = some (.inductInfo { info with all := types.map (·.name) }) :=
  receipt.header indType hmem info hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hheader : staged.find? indType.name = some (.inductInfo info))
    (name : Name) (hctorMem : name ∈ info.ctors) (ctor : ConstructorVal)
    (hlookup : staged.find? name = some (.ctorInfo ctor)) :
    result.find? ctor.name = some (.ctorInfo { ctor with type := preprocessing.restoreNested staged ctor.type }) :=
  receipt.constructor indType hmem info hheader name hctorMem ctor hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hheader : staged.find? indType.name = some (.inductInfo info)) (recursor : RecursorVal)
    (hlookup : staged.find? (mkRecName indType.name) = some (.recInfo recursor)) :
    let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 (mkRecName indType.name) recursor
    result.find? restored.name = some (.recInfo restored) := receipt.mainRecursor indType hmem info hheader recursor hlookup

example {preprocessing : ElimNestedInductive.Result} {staged original result : Kernel.Environment}
    {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (name : Name) (hmem : name ∈ (mkAuxRecNameMap staged types).1) (info : RecursorVal)
    (hlookup : staged.find? name = some (.recInfo info)) :
    let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 name info
    result.find? restored.name = some (.recInfo restored) := receipt.auxiliaryRecursor name hmem info hlookup

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result := metadata.toFrontendScope

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  metadata.installed coverage

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result :=
  Lean4Lean.addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap

example (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment)
    (name : Name) (hmissing : staged.find? name = none) :
    restoredConstructorRecords preprocessing staged name = [] := by
  simp only [restoredConstructorRecords, hmissing]

example (staged : Kernel.Environment) (indType : InductiveType) (hmissing : staged.find? indType.name = none) :
    ¬ RestorationDatatypeSources staged indType := by
  rintro ⟨info, hlookup, _⟩
  rw [hmissing] at hlookup
  cases hlookup

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (coverage : RestorationNameCoverage rewritten staged types) : RestorationSources staged types :=
  scope.restorationSources coverage

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → RestorationNameCoverage preprocessing.types.toArray staged types) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  metadata.installedFromNames coverage

example (staged : Kernel.Environment) (indType : InductiveType) (info : InductiveVal)
    (hheader : staged.find? indType.name = some (.inductInfo info)) (name : Name)
    (hmem : name ∈ info.ctors) (hmissing : staged.find? name = none) :
    ¬ RestorationDatatypeSources staged indType := by
  rintro ⟨other, hother, hctors, _⟩
  have heq : info = other := ConstantInfo.inductInfo.inj (Option.some.inj (hheader.symm.trans hother))
  subst other
  obtain ⟨ctor, hlookup⟩ := hctors name hmem
  rw [hmissing] at hlookup
  cases hlookup

example (staged : Kernel.Environment) (indType : InductiveType)
    (hmissing : staged.find? (mkRecName indType.name) = none) : ¬ RestorationDatatypeSources staged indType := by
  rintro ⟨_, _, _, info, hlookup⟩
  rw [hmissing] at hlookup
  cases hlookup

example (staged : Kernel.Environment) (types : List InductiveType) (name : Name)
    (hmem : name ∈ (mkAuxRecNameMap staged types).1) (hmissing : staged.find? name = none) :
    ¬ RestorationSources staged types := by
  intro sources
  obtain ⟨info, hlookup⟩ := sources.auxiliaries name hmem
  rw [hmissing] at hlookup
  cases hlookup

example (types : Array InductiveType) : InductiveNamePrefix types types := .refl types

example {first second third : Array InductiveType} (hfirst : InductiveNamePrefix first second)
    (hsecond : InductiveNamePrefix second third) : InductiveNamePrefix first third := hfirst.trans hsecond

example (types : Array InductiveType) (type : InductiveType) : InductiveNamePrefix types (types.push type) :=
  .push types type

example {original rewritten : Array InductiveType} (hprefix : InductiveNamePrefix original rewritten)
    (index : Nat) (hindex : index < original.size) (type : InductiveType)
    (hname : type.name = original[index]!.name) : InductiveNamePrefix original (rewritten.set! index type) :=
  hprefix.set index hindex type hname

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceIfNested lctx params sourceParams type env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes :=
  ElimNestedInductive.replaceIfNested.names lctx params sourceParams type env state

example (lctx : LocalContext) (params sourceParams : Array Expr) (type : Expr)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceAllNested lctx params sourceParams type env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes :=
  ElimNestedInductive.replaceAllNested.names lctx params sourceParams type env state

example (fuel nparams : Nat) (types : List InductiveType)
    (env : Kernel.Environment) (state : ElimNestedInductive.State) :
    (StateT.run' (ElimNestedInductive.run fuel nparams types env) state).WF fun result =>
      InductiveNamePrefix state.newTypes result.types.toArray :=
  ElimNestedInductive.run.names_run' fuel nparams types env state

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (fuel : FuelConfig) (preprocessing : ElimNestedInductive.Result)
    (hpre : inductivePreprocessing env lparams nparams types fuel = .ok preprocessing) :
    InductiveNamePrefix types.toArray preprocessing.types.toArray :=
  inductivePreprocessing.names env lparams nparams types fuel preprocessing hpre

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType) (info : InductiveVal)
    (hlookup : env.find? type.name = some (.inductInfo info)) :
    (mkAuxRecNameMap env (type :: types)).1 =
      if (type :: types).length < info.all.length then
        (info.all.drop (type :: types).length).map mkRecName else [] :=
  mkAuxRecNameMap.names env type types info hlookup

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType) (info : InductiveVal)
    (hlookup : env.find? type.name = some (.inductInfo info))
    (hlength : info.all.length ≤ (type :: types).length) : (mkAuxRecNameMap env (type :: types)).1 = [] := by
  rw [mkAuxRecNameMap.names env type types info hlookup, if_neg (Nat.not_lt.mpr hlength)]

example (env : Kernel.Environment) : (mkAuxRecNameMap env []).1 = [] := rfl

example (env : Kernel.Environment) (type : InductiveType) (types : List InductiveType)
    (hmissing : env.find? type.name = none) : (mkAuxRecNameMap env (type :: types)).1 = [] := by
  simp only [mkAuxRecNameMap, hmissing]
  rfl

example {original rewritten : Array InductiveType} (hsize : rewritten.size < original.size) :
    ¬ InductiveNamePrefix original rewritten := fun hprefix => Nat.not_le.mpr hsize hprefix.size

example {original rewritten : Array InductiveType} (index : Nat) (hindex : index < original.size)
    (hname : rewritten[index]!.name ≠ original[index]!.name) : ¬ InductiveNamePrefix original rewritten :=
  fun hprefix => hname (hprefix.names index hindex)

example {stats : InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Kernel.Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveNamePrefix types.toArray rewritten) : RestorationNameCoverage rewritten staged types :=
  scope.restorationNameCoverage hprefix

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveNamePrefix types.toArray preprocessing.types.toArray ∧
      RestorationNameCoverage preprocessing.types.toArray staged types ∧
      RestorationSources staged types := by
  obtain ⟨preprocessing, staged, _, _, _, hpre, hrun, _, hprefix, hcoverage, hsources, _, _⟩ := metadata.completeStages
  exact ⟨preprocessing, staged, hpre, hrun, hprefix, hcoverage, hsources⟩

example {env result : Kernel.Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  metadata.installedComplete

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (allowPrimitive : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        (preprocessing.aux2nested.size ≠ 0 →
          RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  Lean4Lean.Environment.addInductive.safeInstalledMetadata env lparams nparams types allowPrimitive fuel hmap

example (env : Kernel.Environment) (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (check : Bool) (fuel : FuelConfig) (hmap : env.constants.WF) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Kernel.Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        (preprocessing.aux2nested.size ≠ 0 →
          RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  Lean4Lean.addDecl.safeInductiveInstalledMetadata env lparams nparams types check fuel hmap

private def sortType : Expr := .sort (.succ .zero)

private def closeParams (count : Nat) (body : Expr) : Expr :=
  (List.range count).foldr (fun _ result => .forallE `A sortType result .default) body

private def family (name : Name) (count shift : Nat) : Expr :=
  mkAppN (.const name []) ((List.range count).toArray.map fun index => .bvar (count - 1 - index + shift))

private def nestedType (name : Name) (count fields : Nat) (nested := true) : InductiveType :=
  let domain : Expr := if nested then .app (.const ``List [.zero]) (family name count 0) else .const ``Nat []
  let ctorType := (List.range fields).foldr (fun index body =>
    .forallE `field (domain.liftLooseBVars 0 index) body .default) (family name count fields)
  { name, type := closeParams count sortType, ctors := [{ name := name ++ `mk, type := closeParams count ctorType }] }

private def multiConstructorType (name : Name) (count : Nat) (nested := true) : InductiveType :=
  let constructor fields suffix := { (nestedType name count fields nested).ctors.head! with name := name ++ suffix }
  { (nestedType name count 1 nested) with ctors := [constructor 0 `leaf, constructor 1 `branch, constructor 3 `fork] }

private def compareHeader (first second : InductiveVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.all == second.all && first.ctors == second.ctors && first.numNested == second.numNested &&
      first.isRec == second.isRec && first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive do
    throwError "nested frontend changed restored header metadata"

private def compareConstructor (first second : ConstructorVal) : MetaM Unit := do
  unless first.induct == second.induct && first.cidx == second.cidx && first.numParams == second.numParams &&
      first.numFields == second.numFields && first.isUnsafe == second.isUnsafe do
    throwError "nested frontend changed restored constructor metadata"

private def compareRecursor (first second : RecursorVal) : MetaM Unit := do
  unless first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.numMotives == second.numMotives && first.numMinors == second.numMinors && first.all == second.all &&
      first.k == second.k && first.isUnsafe == second.isUnsafe && first.rules.length == second.rules.length do
    throwError "nested frontend changed restored recursor metadata"
  for (left, right) in first.rules.zip second.rules do
    unless left.ctor == right.ctor && left.nfields == right.nfields && left.rhs == right.rhs do
      throwError "nested frontend changed restored recursor rule"

private def compareConstant (expected actual : ConstantInfo) : MetaM Unit := do
  unless expected.name == actual.name && expected.type == actual.type &&
      expected.levelParams == actual.levelParams do throwError "nested frontend changed exact restored record"
  match expected, actual with
  | .inductInfo first, .inductInfo second => compareHeader first second
  | .ctorInfo first, .ctorInfo second => compareConstructor first second
  | .recInfo first, .recInfo second => compareRecursor first second
  | _, _ => throwError "nested frontend changed restored record kind"

private def checkLookup (env : Kernel.Environment) (info : ConstantInfo) : MetaM Unit := do
  let some actual := env.find? info.name | throwError "missing restored record {info.name}"
  compareConstant info actual

private def checkOld (original result : Kernel.Environment) : MetaM Unit := do
  for name in [``Nat, ``Nat.rec, ``List, ``List.rec, ``Bool, ``Bool.rec] do
    if let some before := original.find? name then
      let some after := result.find? name | throwError "nested frontend dropped old lookup {name}"
      compareConstant before after

private def checkRestoredRecords (original staged result : Kernel.Environment)
    (preprocessing : ElimNestedInductive.Result) (types : List InductiveType) : MetaM Unit := do
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  unless recNames == (preprocessing.types.drop types.length).map (mkRecName ∘ (·.name)) do
    throwError "auxiliary recursor names do not enumerate the exact rewritten suffix"
  let allIndNames := types.map (·.name)
  let mut constructorCount := 0
  for indType in types do
    let some (.inductInfo info) := staged.find? indType.name | throwError "missing staged nested header"
    unless preprocessing.types.any (fun rewritten => rewritten.name == indType.name) do
      throwError "original datatype is outside rewritten name coverage"
    constructorCount := constructorCount + info.ctors.length
    checkLookup result (.inductInfo { info with all := allIndNames })
    for ctorName in info.ctors do
      let some (.ctorInfo ctor) := staged.find? ctorName | throwError "missing staged nested constructor"
      checkLookup result (.ctorInfo { ctor with type := preprocessing.restoreNested staged ctor.type })
  for name in types.map (mkRecName ∘ (·.name)) ++ recNames do
    unless preprocessing.types.any (fun rewritten => mkRecName rewritten.name == name) do
      throwError "restoration recursor is outside rewritten name coverage"
    let some (.recInfo info) := staged.find? name | throwError "missing staged nested recursor"
    checkLookup result (.recInfo (restoredRecursorVal preprocessing staged allIndNames recNameMap name info))
  for indType in preprocessing.types.drop types.length do
    unless (result.find? indType.name).isNone do throwError "staged auxiliary header leaked into public result"
    for ctor in indType.ctors do
      unless (result.find? ctor.name).isNone do throwError "staged auxiliary constructor leaked into public result"
  let records := restoredEnvironmentRecords preprocessing staged types
  unless records.length == 2 * types.length + constructorCount + recNames.length do
    throwError "complete restoration recipe omitted an expected staged source record"
  unless (records.map (·.name)).eraseDups.length == records.length do
    throwError "complete restoration receipt contains colliding output names"
  for record in records do
    checkLookup result record
  checkOld original result

private def checkSourceSignature (types : List InductiveType) (preprocessing : ElimNestedInductive.Result) : MetaM Unit := do
  unless types.length ≤ preprocessing.types.length do throwError "preprocessing shortened the source signature"
  for (sourceType, rewrittenType) in types.zip preprocessing.types do
    unless sourceType.type == rewrittenType.type &&
        sourceType.ctors.map (·.name) == rewrittenType.ctors.map (·.name) do
      throwError "preprocessing changed an original header type or constructor-name order"

private def checkSourceConstructors (nparams : Nat) (lparams : List Name) (types : List InductiveType)
    (preprocessing : ElimNestedInductive.Result) (staged result : Kernel.Environment) : MetaM Unit := do
  for sourceType in types do
    let some (.inductInfo header) := staged.find? sourceType.name | throwError "missing source-indexed staged header"
    unless header.type == sourceType.type && header.ctors == sourceType.ctors.map (·.name) do
      throwError "staged header lost the source signature"
    for (sourceCtor, index) in sourceType.ctors.zipIdx do
      let some (.ctorInfo info) := staged.find? sourceCtor.name | throwError "missing source-indexed staged constructor"
      unless info.name == sourceCtor.name && info.induct == sourceType.name && info.cidx == index &&
          info.numParams == nparams && info.levelParams == lparams && info.isUnsafe == false do
        throwError "staged constructor lost source name/parent/position/parameters/levels/safety"
      let expected := if preprocessing.aux2nested.size = 0 then info else
        { info with type := preprocessing.restoreNested staged info.type }
      checkLookup result (.ctorInfo expected)

private def checkFrontend (env : Kernel.Environment) (nparams : Nat) (types : List InductiveType)
    (nested : Bool) (lparams : List Name := []) : MetaM Unit := do
  unless ((← Lean.getEnv).addDeclCore 0 (.inductDecl lparams nparams types false) none).isOk do
    throwError "restoration fixture fails native kernel validation"
  let preprocessing ← match inductivePreprocessing env lparams nparams types {} with
    | .ok result => pure result
    | .error exception => throwError "restoration preprocessing failed for {types.map (·.name)}: {exception.toMessageData {}}"
  unless (preprocessing.types.take types.length).map (·.name) == types.map (·.name) do
    throwError "preprocessing did not retain the original names at their original positions"
  checkSourceSignature types preprocessing
  unless (preprocessing.aux2nested.size > 0) == nested do throwError "fixture has wrong restoration branch"
  let .ok allowPrimitive := Lean4Lean.Environment.checkPrimitiveInductive env lparams nparams types false
    | throwError "restoration primitive dispatch failed"
  let .ok staged := AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams allowPrimitive {}) | throwError "restoration staged run failed"
  let expected ← if nested then do
    let .ok (_, restored) := restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive {} env
      | throwError "explicit restoration failed"
    pure restored
  else pure staged
  for check in [false, true] do
    let .ok added := Lean4Lean.addDecl env (.inductDecl lparams nparams types false) check
      | throwError "public restoration failed with check={check}"
    checkSourceConstructors nparams lparams types preprocessing staged added
    if nested then
      checkRestoredRecords env staged added preprocessing types
      checkRestoredRecords env staged expected preprocessing types
    else
      for indType in types do
        for name in indType.name :: mkRecName indType.name :: indType.ctors.map (·.name) do
          let some record := expected.find? name | throwError "missing direct staged record"
          checkLookup added record
      checkOld env added
  let .ok publicResult := Lean4Lean.Environment.addInductive env lparams nparams types false allowPrimitive
    | throwError "public safe restoration failed"
  checkSourceConstructors nparams lparams types preprocessing staged publicResult
  if nested then checkRestoredRecords env staged publicResult preprocessing types
  else checkOld env publicResult

private def fixtures (env : Kernel.Environment) : MetaM Unit := do
  for count in [0, 1, 2] do
    for fields in [1, 2, 5] do
      checkFrontend env count [nestedType `RestoredNested count fields] true
    checkFrontend env count [nestedType `RestoredPlain count 2 false] false
  checkFrontend env 0 [nestedType `RestoredNested 0 1, {
    name := `RestoredEmpty, type := sortType, ctors := [] }] true
  let name := `RestoredIndexed
  let indexed : InductiveType := {
    name
    type := .forallE `index (.const ``Nat []) sortType .default
    ctors := [{
      name := name ++ `mk
      type := .forallE `index (.const ``Nat [])
        (.forallE `field (.app (.const ``List [.zero]) (.app (.const name []) (.const ``Nat.zero [])))
          (.app (.const name []) (.bvar 1)) .default) .default }] }
  checkFrontend env 0 [indexed] true
  let poly : InductiveType := {
    name := `RestoredPoly
    type := .forallE `A (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default
    ctors := [{
      name := `RestoredPoly.mk
      type := .forallE `A (.sort (.succ (.param `u)))
        (.forallE `field (.app (.const ``List [.param `u]) (.app (.const `RestoredPoly [.param `u]) (.bvar 0)))
          (.app (.const `RestoredPoly [.param `u]) (.bvar 1)) .default) .default }] }
  checkFrontend env 1 [poly] true [`u]
  checkFrontend env 0 [nestedType `RestoredLeft 0 2, nestedType `RestoredRight 0 1,
    { name := `RestoredThird, type := sortType, ctors := [] }] true
  checkFrontend env 0 [nestedType `RestoredDirectLeft 0 1 false, nestedType `RestoredDirectRight 0 2 false,
    { name := `RestoredDirectThird, type := sortType, ctors := [] }] false
  let deep : InductiveType := {
    name := `RestoredDeep, type := sortType, ctors := [{
      name := `RestoredDeep.mk
      type := .forallE `field (.app (.const ``List [.zero])
        (.app (.const ``List [.zero]) (.const `RestoredDeep []))) (.const `RestoredDeep []) .default }] }
  checkFrontend env 0 [deep] true
  checkFrontend env 0 [multiConstructorType `RestoredEnum 0] true
  checkFrontend env 1 [multiConstructorType `RestoredParamEnum 1] true
  checkFrontend env 2 [multiConstructorType `RestoredDirectEnum 2 false] false
  checkFrontend env 0 [multiConstructorType `RestoredMutualEnum 0, multiConstructorType `RestoredMutualEnumRight 0,
    { name := `RestoredMutualEnumEmpty, type := sortType, ctors := [] }] true
  logInfo "22 frontend fixtures passed source header/constructor signatures, original constructor counts/order/indices, exact direct/nested source-indexed records, both flags and auxiliary-rec suffixes"

private def failures (env : Kernel.Environment) : MetaM Unit := do
  let types := [nestedType `RestoredNested 0 1]
  let .ok preprocessing := inductivePreprocessing env [] 0 types {} | throwError "missing failure preparation"
  let .ok staged := AddInductive.run 0 preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env [] false {}) | throwError "missing staged failure preparation"
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  let .ok (_, result) := restoreInductiveEnvironment preprocessing staged types [] false {} env
    | throwError "missing successful restoration preparation"
  if (restoreInductiveEnvironment preprocessing staged types [] false {} result).isOk then
    throwError "restoration accepted a colliding installed header"
  for name in `RestoredNested.rec :: recNames do
    let .ok (_, next) := restoreInductiveRecursor preprocessing staged [`RestoredNested] recNameMap false name env
      | throwError "individual restored recursor failed"
    if (restoreInductiveRecursor preprocessing staged [`RestoredNested] recNameMap false name next).isOk then
      throwError "restoration accepted a colliding main/auxiliary recursor"
  let .ok (_, next) := restoreInductiveConstructor preprocessing staged false `RestoredNested.mk env
    | throwError "individual restored constructor failed"
  if (restoreInductiveConstructor preprocessing staged false `RestoredNested.mk next).isOk then
    throwError "restoration accepted a colliding constructor"
  for check in [false, true] do
    if (Lean4Lean.addDecl env (.inductDecl [] 0 types false) check { inductiveFuel := 0 }).isOk then
      throwError "nested frontend accepted zero preprocessing fuel"
    let poisoned := { types.head! with type := .fvar ⟨`RestorationPoison⟩ }
    let .error (.declHasFVars _ _ _) := Lean4Lean.addDecl env (.inductDecl [] 0 [poisoned] false) check
      | throwError "nested frontend bypassed original-source guard"
  let .error .deepRecursion := restoreInductiveEnvironment preprocessing staged types [] false
      { recDepth := 0 } env | throwError "restoration lost final auxiliary-check fuel failure"
  logInfo "restoration collision controls and public preflight/preprocessing/final auxiliary-check failures passed"

private def audit (theoremName : Name) (maps := false) (full := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if maps then [
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentHashMap.findAux_isSome] else []
  let allowed := allowed ++ if full then [
    ``Lean.PersistentArray.toList'_push,
    ``Expr.eqv_eq, ``Expr.instantiate1_eq, ``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq,
    ``Expr.hasLevelMVar_eq, ``Level.hasMVar_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``InductiveNamePrefix.refl
  audit ``InductiveNamePrefix.trans
  audit ``InductiveNamePrefix.push
  audit ``InductiveNamePrefix.set
  audit ``ElimNestedInductive.withParams.names
  audit ``ElimNestedInductive.replaceParams.names
  audit ``ElimNestedInductive.replaceIfNested.names
  audit ``ElimNestedInductive.replaceAllNested.names
  audit ``ElimNestedInductive.run.loop.names
  audit ``ElimNestedInductive.run.names
  audit ``ElimNestedInductive.run.names_run'
  audit ``inductivePreprocessing.names
  audit ``mkAuxRecNameMap.names
  audit ``InductiveStats.SafeRunScope.restorationNameCoverage
  audit ``SafeInductiveRestorationMetadata.completeStages
  audit ``SafeInductiveRestorationMetadata.installedComplete
  audit ``Lean4Lean.Environment.addInductive.safeInstalledMetadata true true
  audit ``Lean4Lean.addDecl.safeInductiveInstalledMetadata true true
  audit ``RestoredRecordsInstalled.mono
  audit ``RestoredRegistrationReceipt.empty
  audit ``RestoredRegistrationReceipt.trans
  audit ``restoreInductiveRecursor.installed true
  audit ``restoreInductiveConstructor.installed true
  audit ``restoreInductiveDatatype.installed true
  audit ``restoreInductiveEnvironment.installed true
  audit ``RestoredRegistrationReceipt.header
  audit ``RestoredRegistrationReceipt.constructor
  audit ``RestoredRegistrationReceipt.mainRecursor
  audit ``RestoredRegistrationReceipt.auxiliaryRecursor
  audit ``SafeInductiveRestorationMetadata.toFrontendScope
  audit ``SafeInductiveRestorationMetadata.installed
  audit ``InductiveStats.SafeRunScope.restorationSources
  audit ``SafeInductiveRestorationMetadata.installedFromNames
  audit ``Lean4Lean.Environment.addInductive.safeRestorationStages true true
  audit ``Lean4Lean.addDecl.safeInductiveRestorationStages true true
  audit ``AddInductive.restorationAddFresh true
  audit ``FreshRegistrationTrace.trans
  audit ``FreshRegistrationTrace.preserves true
  audit ``FreshRegistrationTrace.lookup true
  audit ``FreshRegistrationTrace.newLookup true
  audit ``restoreInductiveRecursor.trace true
  audit ``restoreInductiveConstructor.trace true
  audit ``restoreInductiveDatatype.trace true
  audit ``restoreInductiveEnvironment.trace true
  audit ``SafeInductiveFrontendScope.preserves true
  audit ``Lean4Lean.Environment.addInductive.safeFrontend true true
  audit ``Lean4Lean.Environment.addInductive.safePreserves true true
  audit ``Lean4Lean.addDecl.safeInductiveFrontend true true
  audit ``Lean4Lean.addDecl.safeInductivePreserves true true
  let env := (← Lean.getEnv).toKernelEnv
  fixtures env
  failures env

end InductiveFrontendRestorationTest
