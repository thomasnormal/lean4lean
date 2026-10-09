import Lean4Lean.Verify.InductiveFrontendRestoration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.registerRestored Lean4Lean.restorationExceptBind
  from Lean4Lean.Verify.InductiveFrontendRestoration

def RestoredRecordsInstalled (records : List ConstantInfo) (env : Environment) : Prop :=
  ∀ info ∈ records, env.find? info.name = some info

theorem RestoredRecordsInstalled.mono {records : List ConstantInfo} {env result : Environment}
    (installed : RestoredRecordsInstalled records env)
    (preserves : ∀ name info, env.find? name = some info → result.find? name = some info) :
    RestoredRecordsInstalled records result :=
  fun info hmem => preserves info.name info (installed info hmem)

structure RestoredRegistrationReceipt (original : Environment) (records : List ConstantInfo)
    (result : Environment) : Prop where
  wf : result.constants.WF
  preserves : ∀ name info, original.find? name = some info → result.find? name = some info
  installed : RestoredRecordsInstalled records result

theorem RestoredRegistrationReceipt.empty (env : Environment) (hwf : env.constants.WF) :
    RestoredRegistrationReceipt env [] env :=
  ⟨hwf, fun _ _ hold => hold, by simp [RestoredRecordsInstalled]⟩

theorem RestoredRegistrationReceipt.trans {original current result : Environment}
    {first second : List ConstantInfo}
    (left : RestoredRegistrationReceipt original first current)
    (right : RestoredRegistrationReceipt current second result) :
    RestoredRegistrationReceipt original (first ++ second) result := by
  refine ⟨right.wf, fun name info hold => right.preserves name info (left.preserves name info hold), ?_⟩
  intro info hmem
  rcases List.mem_append.mp hmem with hfirst | hsecond
  · exact left.installed.mono right.preserves info hfirst
  · exact right.installed info hsecond

def restoredConstructorRecords (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (name : Name) : List ConstantInfo :=
  match staged.find? name with
  | some (.ctorInfo info) => [.ctorInfo { info with type := preprocessing.restoreNested staged info.type }]
  | _ => []

def restoredRecursorRecords (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (name : Name) : List ConstantInfo :=
  match staged.find? name with
  | some (.recInfo info) => [.recInfo (restoredRecursorVal preprocessing staged allIndNames recNameMap name info)]
  | _ => []

def restoredDatatypeRecords (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (indType : InductiveType) : List ConstantInfo :=
  match staged.find? indType.name with
  | some (.inductInfo info) =>
    [.inductInfo { info with all := allIndNames }] ++
      info.ctors.flatMap (restoredConstructorRecords preprocessing staged) ++
      restoredRecursorRecords preprocessing staged allIndNames recNameMap (mkRecName indType.name)
  | _ => []

def restoredEnvironmentRecords (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) : List ConstantInfo :=
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  types.flatMap (restoredDatatypeRecords preprocessing staged (types.map (·.name)) recNameMap) ++
    recNames.flatMap (restoredRecursorRecords preprocessing staged (types.map (·.name)) recNameMap)

def RestorationDatatypeSources (staged : Environment) (indType : InductiveType) : Prop :=
  ∃ info : InductiveVal, staged.find? indType.name = some (.inductInfo info) ∧
    (∀ name ∈ info.ctors, ∃ ctor : ConstructorVal, staged.find? name = some (.ctorInfo ctor)) ∧
    ∃ recursor : RecursorVal, staged.find? (mkRecName indType.name) = some (.recInfo recursor)

structure RestorationSources (staged : Environment) (types : List InductiveType) : Prop where
  datatypes : ∀ indType ∈ types, RestorationDatatypeSources staged indType
  auxiliaries : ∀ name ∈ (mkAuxRecNameMap staged types).1,
    ∃ info : RecursorVal, staged.find? name = some (.recInfo info)

structure RestorationNameCoverage (rewritten : Array InductiveType) (staged : Environment)
    (types : List InductiveType) : Prop where
  originals : ∀ indType ∈ types, ∃ index, index < rewritten.size ∧ rewritten[index]!.name = indType.name
  auxiliaries : ∀ name ∈ (mkAuxRecNameMap staged types).1,
    ∃ index, index < rewritten.size ∧ mkRecName rewritten[index]!.name = name

theorem AddInductive.InductiveStats.SafeRunScope.restorationSources
    {stats : AddInductive.InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (coverage : RestorationNameCoverage rewritten staged types) : RestorationSources staged types := by
  obtain ⟨_, _, _, _, _, hrecursors⟩ := scope.minorOffsets.sourceRules
  refine ⟨?_, ?_⟩
  · intro indType hmem
    obtain ⟨index, hindex, hname⟩ := coverage.originals indType hmem
    let info := AddInductive.declareInductiveTypes.metadataVal stats nparams rewritten numNested false
      original.lparams rewritten[index] stats.nindices[index]!
    refine ⟨info, ?_, ?_, ?_⟩
    · have hfind : staged.find? rewritten[index]!.name = some (.inductInfo info) := by
        simpa only [getElem!_pos, hindex] using scope.toSafeRunRegistration.headerMetadata index hindex
      exact hname ▸ hfind
    · intro name hctorName
      change name ∈ rewritten[index].ctors.map (·.name) at hctorName
      obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hctorName
      obtain ⟨ctorIndex, hctorIndex, rfl⟩ := List.mem_iff_getElem.mp hctor
      have hlookup := scope.toSafeRunRegistration.constructorMetadata rewritten[index]
        (Array.getElem_mem hindex) ctorIndex rewritten[index].ctors[ctorIndex]
        (by simp only [List.getElem?_eq_getElem hctorIndex])
      exact ⟨_, hlookup.1⟩
    · obtain ⟨recursor, hlookup, _⟩ := hrecursors index hindex
      exact ⟨recursor, by simpa only [hname] using hlookup⟩
  · intro name hmem
    obtain ⟨index, hindex, hname⟩ := coverage.auxiliaries name hmem
    obtain ⟨info, hlookup, _⟩ := hrecursors index hindex
    exact ⟨info, by simpa only [hname] using hlookup⟩

private theorem registrationBind {action : InductiveRestorationM α} {next : α → InductiveRestorationM β}
    {env : Environment} {first second : List ConstantInfo}
    (haction : (action env).WF fun result => RestoredRegistrationReceipt env first result.2)
    (hnext : ∀ value current, current.constants.WF →
      (next value current).WF fun result => RestoredRegistrationReceipt current second result.2) :
    ((action >>= next) env).WF fun result => RestoredRegistrationReceipt env (first ++ second) result.2 :=
  haction.bind fun result hfirst => (hnext result.1 result.2 hfirst.wf).mono fun _ hsecond => hfirst.trans hsecond

private theorem registerRestored.installed (info : ConstantInfo) (allowPrimitive : Bool)
    (env : Environment) (hwf : env.constants.WF) :
    (Lean4Lean.registerRestored info allowPrimitive env).WF fun result =>
      RestoredRegistrationReceipt env [info] result.2 := by
  unfold Lean4Lean.registerRestored
  change ((liftM (env.checkName info.name allowPrimitive) >>= fun _ =>
    modify (fun current : Environment => current.add info) : InductiveRestorationM PUnit) env).WF _
  refine Lean4Lean.restorationExceptBind (checkName.WF env info.name allowPrimitive) ?_
  rintro _ ⟨hfresh, _⟩
  obtain ⟨hnext, hself, hkeep⟩ := AddInductive.restorationAddFresh env info hwf hfresh
  exact .pure ⟨hnext, hkeep, by simpa [RestoredRecordsInstalled] using hself⟩

private theorem restorationForInInstalled (items : List α)
    (step : α → InductiveRestorationM (ForInStep PUnit)) (records : α → List ConstantInfo)
    (env : Environment) (hwf : env.constants.WF)
    (hstep : ∀ item ∈ items, ∀ current, current.constants.WF →
      (step item current).WF fun result => result.1 = .yield PUnit.unit ∧
        RestoredRegistrationReceipt current (records item) result.2) :
    (forIn (m := InductiveRestorationM) items PUnit.unit (fun item _ => step item) env).WF
      fun result => RestoredRegistrationReceipt env (items.flatMap records) result.2 := by
  induction items generalizing env with
  | nil => exact .pure (.empty env hwf)
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item (by simp) env hwf).bind ?_
    rintro ⟨_, current⟩ ⟨rfl, hfirst⟩
    exact (ih current hfirst.wf (fun entry hmem => hstep entry (by simp [hmem]))).mono
      fun _ hrest => hfirst.trans hrest

private theorem restorationForMInstalled (items : List α)
    (step : α → InductiveRestorationM PUnit) (records : α → List ConstantInfo)
    (env : Environment) (hwf : env.constants.WF)
    (hstep : ∀ item ∈ items, ∀ current, current.constants.WF →
      (step item current).WF fun result => RestoredRegistrationReceipt current (records item) result.2) :
    (items.forM step env).WF fun result => RestoredRegistrationReceipt env (items.flatMap records) result.2 := by
  simp only [List.forM_eq_forM]
  induction items generalizing env with
  | nil => exact .pure (.empty env hwf)
  | cons item items ih =>
    rw [List.forM_cons]
    exact registrationBind (hstep item (by simp) env hwf)
      fun _ current hcurrent => ih current hcurrent (fun entry hmem => hstep entry (by simp [hmem]))

theorem restoreInductiveRecursor.installed (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (name : Name) (info : RecursorVal) (hlookup : staged.find? name = some (.recInfo info))
    (env : Environment) (hwf : env.constants.WF) :
    (restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive name env).WF fun result =>
      RestoredRegistrationReceipt env
        (restoredRecursorRecords preprocessing staged allIndNames recNameMap name) result.2 := by
  simp only [restoreInductiveRecursor, hlookup, List.mapM_pure, pure_bind,
    restoredRecursorRecords]
  exact registerRestored.installed _ allowPrimitive env hwf

theorem restoreInductiveConstructor.installed (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allowPrimitive : Bool) (name : Name) (info : ConstructorVal)
    (hlookup : staged.find? name = some (.ctorInfo info)) (env : Environment) (hwf : env.constants.WF) :
    (restoreInductiveConstructor preprocessing staged allowPrimitive name env).WF fun result =>
      result.1 = .yield PUnit.unit ∧ RestoredRegistrationReceipt env
        (restoredConstructorRecords preprocessing staged name) result.2 := by
  simp only [restoreInductiveConstructor, hlookup, restoredConstructorRecords]
  refine (registerRestored.installed _ allowPrimitive env hwf).bind ?_
  intro result hreceipt
  exact .pure ⟨rfl, hreceipt⟩

theorem restoreInductiveDatatype.installed (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) (hsources : RestorationDatatypeSources staged indType)
    (env : Environment) (hwf : env.constants.WF) :
    (restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType env).WF fun result =>
      result.1 = .yield PUnit.unit ∧ RestoredRegistrationReceipt env
        (restoredDatatypeRecords preprocessing staged allIndNames recNameMap indType) result.2 := by
  obtain ⟨info, hlookup, hctors, recursor, hrecursor⟩ := hsources
  simp only [restoreInductiveDatatype, hlookup, restoredDatatypeRecords]
  refine (registerRestored.installed _ allowPrimitive env hwf).bind ?_
  intro headers hheaders
  refine (restorationForInInstalled info.ctors _ (restoredConstructorRecords preprocessing staged)
    headers.2 hheaders.wf ?_).bind ?_
  · intro name hmem current hcurrent
    obtain ⟨ctor, hctor⟩ := hctors name hmem
    exact restoreInductiveConstructor.installed preprocessing staged allowPrimitive name ctor hctor current hcurrent
  · intro constructors hconstructors
    refine (restoreInductiveRecursor.installed preprocessing staged allIndNames recNameMap allowPrimitive
      (mkRecName indType.name) recursor hrecursor constructors.2 hconstructors.wf).bind ?_
    intro result hrec
    exact .pure ⟨rfl, (hheaders.trans hconstructors).trans hrec⟩

theorem restoreInductiveEnvironment.installed (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hsources : RestorationSources staged types) (env : Environment) (hwf : env.constants.WF) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result.2 := by
  unfold restoreInductiveEnvironment
  dsimp only
  refine (restorationForInInstalled types _
    (restoredDatatypeRecords preprocessing staged (types.map (·.name)) (mkAuxRecNameMap staged types).2)
    env hwf ?_).bind ?_
  · intro indType hmem current hcurrent
    exact restoreInductiveDatatype.installed preprocessing staged _ _ allowPrimitive indType
      (hsources.datatypes indType hmem) current hcurrent
  · intro datatypes hdatatypes
    refine (restorationForMInstalled _ _
      (restoredRecursorRecords preprocessing staged (types.map (·.name)) (mkAuxRecNameMap staged types).2)
      datatypes.2 hdatatypes.wf ?_).bind ?_
    · intro name hmem current hcurrent
      obtain ⟨info, hlookup⟩ := hsources.auxiliaries name hmem
      exact restoreInductiveRecursor.installed preprocessing staged _ _ allowPrimitive name info hlookup current hcurrent
    · intro recursors hrecursors
      change ((TypeChecker.M.run recursors.2 (safety := .safe) (lctx := preprocessing.lctx)
        (lparams := lparams) (fuel := fuel) do
          preprocessing.aux2nested.forM fun _ type => do _ ← TypeChecker.checkType (preprocessing.openAux type)) >>=
            fun value => pure (value, recursors.2)).WF _
      exact Except.WF.bind (fun _ _ => trivial) fun _ _ => .pure (hdatatypes.trans hrecursors)

theorem RestoredRegistrationReceipt.header {preprocessing : ElimNestedInductive.Result}
    {staged original result : Environment} {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hlookup : staged.find? indType.name = some (.inductInfo info)) :
    result.find? info.name = some (.inductInfo { info with all := types.map (·.name) }) := by
  apply receipt.installed (.inductInfo { info with all := types.map (·.name) })
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨indType, hmem, by simp [restoredDatatypeRecords, hlookup]⟩

theorem RestoredRegistrationReceipt.constructor {preprocessing : ElimNestedInductive.Result}
    {staged original result : Environment} {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hheader : staged.find? indType.name = some (.inductInfo info))
    (name : Name) (hctorMem : name ∈ info.ctors) (ctor : ConstructorVal)
    (hlookup : staged.find? name = some (.ctorInfo ctor)) :
    result.find? ctor.name = some (.ctorInfo { ctor with type := preprocessing.restoreNested staged ctor.type }) := by
  apply receipt.installed (.ctorInfo { ctor with type := preprocessing.restoreNested staged ctor.type })
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨indType, hmem, ?_⟩
  simp only [restoredDatatypeRecords, hheader]
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨name, hctorMem, by simp [restoredConstructorRecords, hlookup]⟩

theorem RestoredRegistrationReceipt.mainRecursor {preprocessing : ElimNestedInductive.Result}
    {staged original result : Environment} {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (indType : InductiveType) (hmem : indType ∈ types) (info : InductiveVal)
    (hheader : staged.find? indType.name = some (.inductInfo info)) (recursor : RecursorVal)
    (hlookup : staged.find? (mkRecName indType.name) = some (.recInfo recursor)) :
    let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 (mkRecName indType.name) recursor
    result.find? restored.name = some (.recInfo restored) := by
  apply receipt.installed (.recInfo (restoredRecursorVal preprocessing staged (types.map (·.name))
    (mkAuxRecNameMap staged types).2 (mkRecName indType.name) recursor))
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨indType, hmem, ?_⟩
  simp only [restoredDatatypeRecords, hheader]
  apply List.mem_append_right
  simp only [restoredRecursorRecords, hlookup, List.mem_singleton]
  rfl

theorem RestoredRegistrationReceipt.auxiliaryRecursor {preprocessing : ElimNestedInductive.Result}
    {staged original result : Environment} {types : List InductiveType}
    (receipt : RestoredRegistrationReceipt original (restoredEnvironmentRecords preprocessing staged types) result)
    (name : Name) (hmem : name ∈ (mkAuxRecNameMap staged types).1) (info : RecursorVal)
    (hlookup : staged.find? name = some (.recInfo info)) :
    let restored := restoredRecursorVal preprocessing staged (types.map (·.name))
      (mkAuxRecNameMap staged types).2 name info
    result.find? restored.name = some (.recInfo restored) := by
  apply receipt.installed (.recInfo (restoredRecursorVal preprocessing staged (types.map (·.name))
    (mkAuxRecNameMap staged types).2 name info))
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨name, hmem, by simp only [restoredRecursorRecords, hlookup, List.mem_singleton]; rfl⟩

structure SafeInductiveRestorationMetadata (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (result : Environment) : Prop where
  originalWF : env.constants.WF
  sources : InductiveSourcesNoMVarNoFVar types
  stages : ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
    inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
    AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
    ∃ (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 → RestorationSources staged types →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result)

theorem SafeInductiveRestorationMetadata.toFrontendScope {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result := by
  obtain ⟨preprocessing, staged, hpre, _, stats, root, constructors, hrun, hbranch, _⟩ := metadata.stages
  exact ⟨metadata.originalWF, metadata.sources, preprocessing, hpre, staged, stats, root, constructors, hrun, hbranch⟩

def InductiveRestorationSourceCoverage (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) : Prop :=
  ∀ preprocessing staged,
    inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
    AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
    preprocessing.aux2nested.size ≠ 0 → RestorationSources staged types

theorem SafeInductiveRestorationMetadata.installed {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : InductiveRestorationSourceCoverage env lparams nparams types allowPrimitive fuel) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) := by
  obtain ⟨preprocessing, staged, hpre, hrun, _, _, _, _, _, hinstalled⟩ := metadata.stages
  exact ⟨preprocessing, staged, hpre, hrun, fun hnested =>
    hinstalled hnested (coverage preprocessing staged hpre hrun hnested)⟩

theorem SafeInductiveRestorationMetadata.installedFromNames {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result)
    (coverage : ∀ preprocessing staged,
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing →
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged →
      preprocessing.aux2nested.size ≠ 0 → RestorationNameCoverage preprocessing.types.toArray staged types) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) := by
  obtain ⟨preprocessing, staged, hpre, hrun, _, _, _, hscope, _, hinstalled⟩ := metadata.stages
  exact ⟨preprocessing, staged, hpre, hrun, fun hnested =>
    hinstalled hnested (hscope.restorationSources (coverage preprocessing staged hpre hrun hnested))⟩

theorem Environment.addInductive.safeRestorationStages (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result := by
  unfold Environment.addInductive
  refine (Environment.checkInductiveSources.WF env types).bind ?_
  intro _ hsources
  refine Except.WF.bind (Q := fun preprocessing =>
    inductivePreprocessing env lparams nparams types fuel = .ok preprocessing) (fun _ hpre => hpre) ?_
  intro preprocessing hpre
  dsimp only
  have hchecked := AddInductive.run.safeScope nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) rfl hmap .nil
    (ElimNestedInductive.ContextReserved.empty _)
  refine Except.WF.bind (Q := fun staged =>
    AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
      (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
    ∃ (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged)
    (fun staged hrun => ⟨hrun, hchecked staged hrun⟩) ?_
  rintro staged ⟨hrun, stats, root, constructors, hscope⟩
  split
  · rename_i hnoaux
    exact .pure ⟨hmap, hsources, preprocessing, staged, hpre, hrun, stats, root, constructors, hscope,
      .direct hnoaux, fun hnested _ => False.elim (hnested hnoaux)⟩
  · rename_i hnested
    have hrestored : ((·.2) <$> restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF
        (fun result => SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) := by
      intro result hresult
      have htrace := (restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel env).map
        (fun _ htrace => htrace) result hresult
      refine ⟨hmap, hsources, preprocessing, staged, hpre, hrun, stats, root, constructors, hscope,
        .nested hnested htrace, ?_⟩
      intro _ hcoverage
      exact (restoreInductiveEnvironment.installed preprocessing staged types lparams allowPrimitive fuel
        hcoverage env hmap).map (fun _ hreceipt => hreceipt) result hresult
    dsimp only [restoreInductiveEnvironment, restoreInductiveDatatype, restoreInductiveConstructor,
      restoreInductiveRecursor, Lean4Lean.registerRestored, StateT.run] at hrestored
    simpa only [StateT.run, ConstantInfo.name, ConstantInfo.toConstantVal, List.mapM_pure, pure_bind,
      panicWithPosWithDecl, panic, panicCore, bind_assoc, Bool.false_eq_true, if_false] using hrestored

theorem addDecl.safeInductiveRestorationStages (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result := by
  unfold addDecl
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro allowPrimitive _
  exact (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => ⟨allowPrimitive, metadata⟩

end Lean4Lean
