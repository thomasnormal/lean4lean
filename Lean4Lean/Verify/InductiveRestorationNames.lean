import Lean4Lean.Verify.InductiveRestorationMetadata
import Lean4Lean.Verify.InductiveNestedRewrite

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

structure InductiveNamePrefix (original rewritten : Array InductiveType) : Prop where
  size : original.size ≤ rewritten.size
  names : ∀ index, index < original.size → rewritten[index]!.name = original[index]!.name

theorem InductiveNamePrefix.refl (types : Array InductiveType) : InductiveNamePrefix types types :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem InductiveNamePrefix.trans {first second third : Array InductiveType}
    (hfirst : InductiveNamePrefix first second) (hsecond : InductiveNamePrefix second third) :
    InductiveNamePrefix first third :=
  ⟨Nat.le_trans hfirst.size hsecond.size, fun index hindex =>
    (hsecond.names index (Nat.lt_of_lt_of_le hindex hfirst.size)).trans (hfirst.names index hindex)⟩

theorem InductiveNamePrefix.push (types : Array InductiveType) (type : InductiveType) :
    InductiveNamePrefix types (types.push type) := by
  refine ⟨by simp, ?_⟩
  intro index hindex
  simp [getElem!_pos, hindex, Nat.lt_succ_of_lt hindex, Array.getElem_push_lt]

theorem InductiveNamePrefix.set {original rewritten : Array InductiveType}
    (hprefix : InductiveNamePrefix original rewritten) (index : Nat) (hindex : index < original.size)
    (type : InductiveType) (hname : type.name = original[index]!.name) :
    InductiveNamePrefix original (rewritten.set! index type) := by
  refine ⟨by simpa using hprefix.size, ?_⟩
  intro position hposition
  have hrewritten := Nat.lt_of_lt_of_le hposition hprefix.size
  have hset := Nat.lt_of_lt_of_le hindex hprefix.size
  by_cases heq : position = index
  · subst position
    simpa [Array.set!, getElem!_pos, hset] using hname
  · simpa [Array.set!, getElem!_pos, hrewritten, hset, heq, Ne.symm heq] using hprefix.names position hposition

namespace ElimNestedInductive

open private Lean4Lean.ElimNestedInductive.get_bind Lean4Lean.ElimNestedInductive.read_bind
  Lean4Lean.ElimNestedInductive.modify_bind
  Lean4Lean.ElimNestedInductive.liftM_ok_eq from Lean4Lean.Verify.InductiveNestedRewrite

private theorem nameBind {action : M Value} {next : Value → M ResultValue}
    {env : Environment} {state : State}
    (haction : (action env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes)
    (hnext : ∀ value current, (next value env current).WF fun result =>
      InductiveNamePrefix current.newTypes result.2.newTypes) :
    ((action >>= next) env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes :=
  haction.bind fun current hfirst => (hnext current.1 current.2).mono fun _ hsecond => hfirst.trans hsecond

private theorem liftNames (action : Except Exception Value) (env : Environment) (state : State) :
    ((liftM action : M Value) env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes := by
  cases action with
  | error exception => exact .throw
  | ok value => exact .pure (.refl _)

private theorem mapMNames (items : List Value) (step : Value → M ResultValue) (env : Environment) (state : State)
    (hstep : ∀ item current, (step item env current).WF fun result =>
      InductiveNamePrefix current.newTypes result.2.newTypes) :
    (items.mapM step env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes := by
  induction items generalizing state with
  | nil => exact .pure (.refl _)
  | cons item items ih =>
    rw [List.mapM_cons]
    apply nameBind (hstep item state)
    intro value current
    exact (ih current).bind fun result hresult => .pure hresult

private theorem forInNames (items : List Value) (initial : ResultValue)
    (step : Value → ResultValue → M (ForInStep ResultValue)) (env : Environment) (state : State)
    (hstep : ∀ item value current, (step item value env current).WF fun result =>
      InductiveNamePrefix current.newTypes result.2.newTypes) :
    (forIn items initial step env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes := by
  induction items generalizing initial state with
  | nil => exact .pure (.refl _)
  | cons item items ih =>
    rw [List.forIn_cons]
    apply nameBind (hstep item initial state)
    intro next current
    cases next with
    | done value => exact .pure (.refl _)
    | yield value => exact ih value current

private theorem withParamsLoopNamePost (remaining : Nat) (type : Expr) (lctx : LocalContext)
    (params : Array Expr) (next : LocalContext → Expr → Array Expr → M Value)
    (env : Environment) (state : State) (post : Value × State → Prop)
    (hnext : ∀ lctx remainder params current, current.newTypes = state.newTypes →
      (next lctx remainder params env current).WF post) :
    (withParams.loop next lctx type params remaining env state).WF post := by
  induction remaining generalizing type lctx params state with
  | zero => exact hnext lctx type params state rfl
  | succ remaining ih =>
    cases type with
    | forallE name domain body bi =>
      exact ih (body.instantiate1 (.fvar ⟨state.ngen.curr⟩))
        (lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain bi)
        (params.push (.fvar ⟨state.ngen.curr⟩)) { state with ngen := state.ngen.next } hnext
    | _ => exact .throw

theorem withParams.names (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M Value) (env : Environment) (state : State)
    (hnext : ∀ lctx remainder params current, (next lctx remainder params env current).WF fun result =>
      InductiveNamePrefix current.newTypes result.2.newTypes) :
    (withParams type numParams next env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes := by
  apply withParamsLoopNamePost numParams type {} #[] next env state
  intro lctx remainder params current hframe
  simpa only [hframe] using hnext lctx remainder params current

theorem replaceParams.names (params : Array Expr) (type : Expr) (sourceParams : Array Expr)
    (env : Environment) (state : State) :
    (replaceParams params type sourceParams env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes := by
  unfold replaceParams
  split <;> exact .pure (.refl _)

private theorem nestedConstructorNames (info : InductiveVal) (parentName : Name) (levels : List Level)
    (numParams : Nat) (args : Array Expr) (lctx : LocalContext) (params : Array Expr)
    (auxName : Name) (env : Environment) (state : State) :
    (info.ctors.mapM (fun name => (do
      let ctor ← env.get name
      let type ← instantiateForallParams (ctor.type.instantiateLevelParams ctor.levelParams levels) numParams args
      pure { name := name.replacePrefix parentName auxName, type := lctx.mkForall params type } : M Constructor))
      env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes := by
  apply mapMNames
  intro name current
  apply nameBind (liftNames (env.get name) env current)
  intro ctor current'
  apply nameBind (liftNames
    (instantiateForallParams (ctor.type.instantiateLevelParams ctor.levelParams levels) numParams args) env current')
  intro type current''
  exact .pure (.refl _)

private theorem nestedIterationNames (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (info : InductiveVal) (headName : Name) (levels : List Level)
    (name : Name) (result : Option Expr) (env : Environment) (state : State) :
    ((do
      let .inductInfo nestedInfo ← env.get name | do
        (unreachable! : M PUnit)
        pure (.yield result)
      let nested := Expr.const name levels
      let nestedApp := mkAppRange nested 0 info.numParams type.getAppArgs
      let auxName ← mkUniqueName (`_nested ++ name)
      let auxType ← instantiateForallParams
        (nestedInfo.type.instantiateLevelParams nestedInfo.levelParams levels) info.numParams type.getAppArgs
      let nestedApp' ← replaceParams params nestedApp sourceParams
      modify fun current => { current with nestedAux := current.nestedAux.push (nestedApp', auxName) }
      let mut result := result
      if name == headName then
        result := some (mkAppRange (mkAppN (.const auxName (← get).lvls) sourceParams)
          info.numParams type.getAppArgs.size type.getAppArgs)
      let ctors ← nestedInfo.ctors.mapM fun ctorName => do
        let ctor ← env.get ctorName
        let ctorType ← instantiateForallParams
          (ctor.type.instantiateLevelParams ctor.levelParams levels) info.numParams type.getAppArgs
        pure { name := ctorName.replacePrefix name auxName, type := lctx.mkForall sourceParams ctorType }
      let newType : InductiveType := { name := auxName, type := lctx.mkForall sourceParams auxType, ctors }
      modify fun current => { current with newTypes := current.newTypes.push newType }
      pure (.yield result) : M (ForInStep (Option Expr))) env state).WF fun returned =>
      InductiveNamePrefix state.newTypes returned.2.newTypes := by
  generalize hget : env.get name = found
  cases found with
  | error exception => exact .throw
  | ok constant =>
    cases constant with
    | inductInfo nestedInfo =>
      rw [Lean4Lean.ElimNestedInductive.liftM_ok_eq]
      simp only [pure_bind]
      apply nameBind ((mkUniqueName.frame (`_nested ++ name) env state).mono fun _ hframe =>
        hframe.2.1 ▸ InductiveNamePrefix.refl _)
      intro auxName current
      apply nameBind (liftNames
        (instantiateForallParams (nestedInfo.type.instantiateLevelParams nestedInfo.levelParams levels)
          info.numParams type.getAppArgs) env current)
      intro auxType current'
      apply nameBind (replaceParams.names params _ sourceParams env current')
      intro nestedApp current''
      rw [Lean4Lean.ElimNestedInductive.modify_bind]
      split
      · rw [Lean4Lean.ElimNestedInductive.get_bind]
        dsimp only
        apply nameBind
        · exact nestedConstructorNames nestedInfo name levels info.numParams type.getAppArgs
            lctx sourceParams auxName env _
        · intro ctors next
          rw [Lean4Lean.ElimNestedInductive.modify_bind]
          exact .pure (.push _ _)
      · apply nameBind
        · exact nestedConstructorNames nestedInfo name levels info.numParams type.getAppArgs
            lctx sourceParams auxName env _
        · intro ctors next
          rw [Lean4Lean.ElimNestedInductive.modify_bind]
          exact .pure (.push _ _)
    | _ => exact .pure (.refl _)

theorem replaceIfNested.names (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (env : Environment) (state : State) :
    (replaceIfNested lctx params sourceParams type env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes := by
  unfold replaceIfNested
  refine (isNestedInductiveApp?.scope type env state).bind ?_
  rintro ⟨selected, current⟩ ⟨hframe, hselected⟩
  dsimp only at hframe hselected
  subst current
  cases selected with
  | none => exact .pure (.refl _)
  | some info =>
    dsimp only
    rw [Expr.withApp_eq]
    obtain ⟨⟨headName, levels, hhead⟩, harity, _⟩ := hselected info rfl
    rw [hhead]
    simp only [if_pos harity]
    apply nameBind (replaceParams.names params _ sourceParams env state)
    intro replaced current
    rw [Lean4Lean.ElimNestedInductive.get_bind]
    generalize hfound : Array.findSome? _ current.nestedAux = found
    cases found with
    | some auxName => exact .pure (.refl _)
    | none =>
      simp only [pure_bind]
      rw [Lean4Lean.ElimNestedInductive.read_bind]
      apply nameBind
      · apply forInNames
        intro name result next
        simpa only [panicWithPosWithDecl, panic, panicCore, pure_bind] using
          nestedIterationNames lctx params sourceParams type info headName levels name result env next
      · intro result next
        cases result <;> exact .pure (.refl _)

private theorem replaceMNames (step : Expr → M (Option Expr))
    (hstep : ∀ type current, (step type env current).WF fun result =>
      InductiveNamePrefix current.newTypes result.2.newTypes) (type : Expr) (state : State) :
    (type.replaceM step env state).WF fun result => InductiveNamePrefix state.newTypes result.2.newTypes := by
  unfold Expr.replaceM
  induction type generalizing state <;> unfold Expr.replaceNoCacheT <;>
    apply nameBind (hstep _ _) <;> intro selected current <;> cases selected
  all_goals
    repeat' first
    | exact .pure (.refl _)
    | apply nameBind (by solve_by_elim)
      intro rewritten next

theorem replaceAllNested.names (lctx : LocalContext) (params sourceParams : Array Expr)
    (type : Expr) (env : Environment) (state : State) :
    (replaceAllNested lctx params sourceParams type env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.2.newTypes :=
  replaceMNames (replaceIfNested lctx params sourceParams)
    (fun type current => replaceIfNested.names lctx params sourceParams type env current) type state

theorem run.loop.names (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Environment) (state : State) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.1.types.toArray := by
  induction fuel generalizing index state with
  | zero => exact .throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    rw [Lean4Lean.ElimNestedInductive.get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      refine (mapMNames state.newTypes[index].ctors _ env state ?_).bind ?_
      · intro ctor current
        apply withParams.names
        intro ctorContext ctorType sourceParams next
        exact (replaceAllNested.names ctorContext params sourceParams ctorType env next).bind
          fun result hresult => .pure hresult
      · rintro ⟨ctors, current⟩ hprefix
        dsimp only
        rw [Lean4Lean.ElimNestedInductive.modify_bind]
        have hset := hprefix.set index hindex { state.newTypes[index] with ctors }
          (by simp only [getElem!_pos, hindex])
        exact (ih (index + 1) _).mono fun _ hresult => hset.trans hresult
    · exact .pure (by simpa using InductiveNamePrefix.refl state.newTypes)

theorem run.names (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result =>
      InductiveNamePrefix state.newTypes result.1.types.toArray := by
  cases types with
  | nil => exact .throw
  | cons type types =>
    unfold run
    apply withParamsLoopNamePost numParams type.type {} #[] _ env state
    intro lctx remainder params current hframe
    simpa only [hframe] using run.loop.names numParams lctx params 0 fuel env current

theorem run.names_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      InductiveNamePrefix state.newTypes result.types.toArray :=
  (run.names fuel numParams types env state).map fun _ hprefix => hprefix

end ElimNestedInductive

theorem inductivePreprocessing.names (env : Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) :
    (inductivePreprocessing env lparams numParams types fuel).WF fun result =>
      InductiveNamePrefix types.toArray result.types.toArray :=
  ElimNestedInductive.run.names_run' fuel.inductiveFuel numParams types env
    { lvls := lparams.map .param, newTypes := types.toArray }

private theorem auxRecNameLoop (names : List Name) (mainName : Name) (nextIndex : Nat)
    (oldNames : Array Name) (nameMap : NameMap Name) :
    (forIn (m := Id) names (⟨nextIndex, oldNames, nameMap⟩ : MProd Nat (MProd (Array Name) (NameMap Name)))
      (fun name current =>
        pure (.yield ⟨current.fst + 1, current.snd.fst.push (mkRecName name),
          current.snd.snd.insert (mkRecName name) ((mkRecName mainName).appendIndexAfter current.fst)⟩))).run.snd.fst.toList =
      oldNames.toList ++ names.map mkRecName := by
  induction names generalizing nextIndex oldNames nameMap with
  | nil => simp
  | cons name names ih =>
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih]
    simp [Array.toList_push, List.append_assoc]

theorem mkAuxRecNameMap.names (env : Environment) (type : InductiveType) (types : List InductiveType)
    (info : InductiveVal) (hlookup : env.find? type.name = some (.inductInfo info)) :
    (mkAuxRecNameMap env (type :: types)).1 =
      if (type :: types).length < info.all.length then
        (info.all.drop (type :: types).length).map mkRecName else [] := by
  unfold mkAuxRecNameMap
  simp only [hlookup]
  split
  · simpa only [pure_bind, List.nil_append, Array.toList_empty] using
      auxRecNameLoop (info.all.drop (type :: types).length) type.name 1 #[] {}
  · rfl

theorem AddInductive.InductiveStats.SafeRunScope.restorationNameCoverage
    {stats : AddInductive.InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveNamePrefix types.toArray rewritten) : RestorationNameCoverage rewritten staged types := by
  refine ⟨?_, ?_⟩
  · intro type hmem
    obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hmem
    have harray : index < types.toArray.size := by simpa using hindex
    refine ⟨index, Nat.lt_of_lt_of_le harray hprefix.size, ?_⟩
    simpa only [getElem!_pos, harray, List.getElem_toArray] using hprefix.names index harray
  · intro name hmem
    cases types with
    | nil =>
      have hempty : (mkAuxRecNameMap staged []).1 = [] := rfl
      rw [hempty] at hmem
      cases hmem
    | cons type types =>
      have hzero : 0 < (type :: types).toArray.size := by simp
      have hrewritten : 0 < rewritten.size := Nat.lt_of_lt_of_le hzero hprefix.size
      let info := AddInductive.declareInductiveTypes.metadataVal stats nparams rewritten numNested false
        original.lparams rewritten[0] stats.nindices[0]!
      have hname : rewritten[0].name = type.name := by
        simpa only [getElem!_pos, hzero, hrewritten, List.getElem_toArray, List.getElem_cons_zero] using
          hprefix.names 0 hzero
      have hlookup : staged.find? type.name = some (.inductInfo info) := by
        simpa only [hname] using scope.toSafeRunRegistration.headerMetadata 0 hrewritten
      rw [mkAuxRecNameMap.names staged type types info hlookup] at hmem
      split at hmem
      · obtain ⟨indName, hnames, rfl⟩ := List.mem_map.mp hmem
        have hall : indName ∈ (rewritten.map (·.name)).toList := List.mem_of_mem_drop hnames
        have hmap : indName ∈ rewritten.toList.map (·.name) := by simpa using hall
        obtain ⟨indType, htype, hname⟩ := List.mem_map.mp hmap
        have harray : indType ∈ rewritten := by simpa using htype
        obtain ⟨index, hindex, rfl⟩ := Array.mem_iff_getElem.mp harray
        exact ⟨index, hindex, by simp only [getElem!_pos, hindex, hname]⟩
      · cases hmem

theorem SafeInductiveRestorationMetadata.completeStages {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveNamePrefix types.toArray preprocessing.types.toArray ∧
      RestorationNameCoverage preprocessing.types.toArray staged types ∧
      RestorationSources staged types ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) := by
  obtain ⟨preprocessing, staged, hpre, hrun, stats, root, constructors, hscope, hbranch, hinstalled⟩ := metadata.stages
  have hprefix := inductivePreprocessing.names env lparams nparams types fuel preprocessing hpre
  have hcoverage := hscope.restorationNameCoverage hprefix
  have hsources := hscope.restorationSources hcoverage
  exact ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, hprefix, hcoverage, hsources,
    hbranch, fun hnested => hinstalled hnested hsources⟩

theorem SafeInductiveRestorationMetadata.installedComplete {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      (preprocessing.aux2nested.size ≠ 0 →
        RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) := by
  obtain ⟨preprocessing, staged, _, _, _, hpre, hrun, _, _, _, _, _, hinstalled⟩ := metadata.completeStages
  exact ⟨preprocessing, staged, hpre, hrun, hinstalled⟩

theorem Environment.addInductive.safeInstalledMetadata (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        (preprocessing.aux2nested.size ≠ 0 →
          RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.installedComplete

theorem addDecl.safeInductiveInstalledMetadata (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        (preprocessing.aux2nested.size ≠ 0 →
          RestoredRegistrationReceipt env (restoredEnvironmentRecords preprocessing staged types) result) :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.installedComplete⟩

end Lean4Lean
