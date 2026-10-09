import Lean4Lean.Verify.InductiveRestorationNames

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

structure InductiveSignaturePrefix (original rewritten : Array InductiveType) : Prop
    extends InductiveNamePrefix original rewritten where
  headers : ∀ index, index < original.size → rewritten[index]!.type = original[index]!.type
  constructors : ∀ index, index < original.size →
    rewritten[index]!.ctors.map (·.name) = original[index]!.ctors.map (·.name)

theorem InductiveSignaturePrefix.refl (types : Array InductiveType) : InductiveSignaturePrefix types types :=
  ⟨.refl types, fun _ _ => rfl, fun _ _ => rfl⟩

theorem InductiveSignaturePrefix.trans {first second third : Array InductiveType}
    (hfirst : InductiveSignaturePrefix first second) (hsecond : InductiveSignaturePrefix second third) :
    InductiveSignaturePrefix first third :=
  ⟨hfirst.toInductiveNamePrefix.trans hsecond.toInductiveNamePrefix,
    fun index hindex => (hsecond.headers index (Nat.lt_of_lt_of_le hindex hfirst.size)).trans (hfirst.headers index hindex),
    fun index hindex => (hsecond.constructors index (Nat.lt_of_lt_of_le hindex hfirst.size)).trans
      (hfirst.constructors index hindex)⟩

theorem ElimNestedInductive.TypePrefix.toSignature {original rewritten : Array InductiveType}
    (hprefix : ElimNestedInductive.TypePrefix original rewritten) : InductiveSignaturePrefix original rewritten :=
  ⟨hprefix.toNames, fun index hindex => congrArg InductiveType.type (hprefix.types index hindex),
    fun index hindex => congrArg (fun type => type.ctors.map (·.name)) (hprefix.types index hindex)⟩

theorem InductiveSignaturePrefix.set {original rewritten : Array InductiveType}
    (hprefix : InductiveSignaturePrefix original rewritten) (index : Nat) (hindex : index < original.size)
    (type : InductiveType) (hname : type.name = original[index]!.name)
    (hheader : type.type = original[index]!.type)
    (hctors : type.ctors.map (·.name) = original[index]!.ctors.map (·.name)) :
    InductiveSignaturePrefix original (rewritten.set! index type) := by
  refine ⟨hprefix.toInductiveNamePrefix.set index hindex type hname, ?_, ?_⟩
  all_goals
    intro position hposition
    have hrewritten := Nat.lt_of_lt_of_le hposition hprefix.size
    have hset := Nat.lt_of_lt_of_le hindex hprefix.size
    by_cases heq : position = index
    · subst position
      simpa [Array.set!, getElem!_pos, hset] using (by assumption)
    · first
      | simpa [Array.set!, getElem!_pos, hrewritten, hset, heq, Ne.symm heq] using hprefix.headers position hposition
      | simpa [Array.set!, getElem!_pos, hrewritten, hset, heq, Ne.symm heq] using hprefix.constructors position hposition

theorem InductiveSignaturePrefix.constructorCount {original rewritten : Array InductiveType}
    (hprefix : InductiveSignaturePrefix original rewritten) (index : Nat) (hindex : index < original.size) :
    rewritten[index]!.ctors.length = original[index]!.ctors.length := by
  simpa only [List.length_map] using congrArg List.length (hprefix.constructors index hindex)

theorem InductiveSignaturePrefix.constructorNameAt {original rewritten : Array InductiveType}
    (hprefix : InductiveSignaturePrefix original rewritten) (index : Nat) (hindex : index < original.size)
    (ctorIndex : Nat) (hctor : ctorIndex < original[index]!.ctors.length) :
    rewritten[index]!.ctors[ctorIndex]!.name = original[index]!.ctors[ctorIndex]!.name := by
  have hrewritten : ctorIndex < rewritten[index]!.ctors.length := by
    rw [hprefix.constructorCount index hindex]
    exact hctor
  have hnames := congrArg (fun names : List Name => names[ctorIndex]?) (hprefix.constructors index hindex)
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hctor, List.getElem?_eq_getElem hrewritten,
    Option.map_some, Option.some.injEq, getElem!_pos, hctor, hrewritten] using hnames

namespace ElimNestedInductive
open private Lean4Lean.ElimNestedInductive.get_bind Lean4Lean.ElimNestedInductive.modify_bind
  from Lean4Lean.Verify.InductiveNestedRewrite

private theorem mapMConstructorNames (ctors : List Constructor) (step : Constructor → M Constructor)
    (env : Environment) (state : State)
    (hstep : ∀ ctor current, (step ctor env current).WF fun result =>
      result.1.name = ctor.name ∧ TypePrefix current.newTypes result.2.newTypes) :
    (ctors.mapM step env state).WF fun result =>
      result.1.map (·.name) = ctors.map (·.name) ∧ TypePrefix state.newTypes result.2.newTypes := by
  induction ctors generalizing state with
  | nil => exact .pure ⟨rfl, .refl _⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine (hstep ctor state).bind ?_
    rintro ⟨rewritten, current⟩ ⟨hname, hprefix⟩
    refine (ih current).bind ?_
    rintro ⟨rest, next⟩ ⟨hnames, hrest⟩
    dsimp only at hname hnames hprefix hrest
    exact .pure ⟨by simp only [List.map_cons, hname, hnames], hprefix.trans hrest⟩

theorem run.loop.signatures (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Environment) (state : State) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      InductiveSignaturePrefix state.newTypes result.1.types.toArray := by
  induction fuel generalizing index state with
  | zero => exact .throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    rw [Lean4Lean.ElimNestedInductive.get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      refine (mapMConstructorNames state.newTypes[index].ctors _ env state ?_).bind ?_
      · intro ctor current
        apply withParams.newTypesFrame ctor.type numParams _ env current
        intro ctorContext ctorType sourceParams next hframe
        refine (replaceAllNested.typesPrefix ctorContext params sourceParams ctorType env next).bind ?_
        rintro ⟨type, final⟩ hprefix
        exact .pure ⟨rfl, by simpa only [hframe] using hprefix⟩
      · rintro ⟨ctors, current⟩ ⟨hnames, hprefix⟩
        dsimp only
        rw [Lean4Lean.ElimNestedInductive.modify_bind]
        have hset := hprefix.toSignature.set index hindex { state.newTypes[index] with ctors }
          (by simp only [getElem!_pos, hindex]) (by simp only [getElem!_pos, hindex])
          (by simpa only [getElem!_pos, hindex] using hnames)
        exact (ih (index + 1) _).mono fun _ hresult => hset.trans hresult
    · exact .pure (by simpa using InductiveSignaturePrefix.refl state.newTypes)

theorem run.signatures (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result =>
      InductiveSignaturePrefix state.newTypes result.1.types.toArray := by
  cases types with
  | nil => exact .throw
  | cons type types =>
    unfold run
    apply withParams.newTypesFrame type.type numParams _ env state
    intro lctx remainder params current hframe
    simpa only [hframe] using run.loop.signatures numParams lctx params 0 fuel env current

theorem run.signatures_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      InductiveSignaturePrefix state.newTypes result.types.toArray :=
  (run.signatures fuel numParams types env state).map fun _ hprefix => hprefix

end ElimNestedInductive

theorem inductivePreprocessing.signatures (env : Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) :
    (inductivePreprocessing env lparams numParams types fuel).WF fun result =>
      InductiveSignaturePrefix types.toArray result.types.toArray :=
  ElimNestedInductive.run.signatures_run' fuel.inductiveFuel numParams types env
    { lvls := lparams.map .param, newTypes := types.toArray }

structure SourceConstructorMetadata (nparams : Nat) (lparams : List Name)
    (parent : InductiveType) (index : Nat) (info : ConstructorVal) : Prop where
  name : info.name = parent.ctors[index]!.name
  induct : info.induct = parent.name
  position : info.cidx = index
  params : info.numParams = nparams
  levels : info.levelParams = lparams
  safe : info.isUnsafe = false

theorem AddInductive.InductiveStats.SafeRunScope.sourceConstructor
    {stats : AddInductive.InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveSignaturePrefix types.toArray rewritten)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) :
    ∃ (header : InductiveVal) (info : ConstructorVal),
      staged.find? types[typeIndex].name = some (.inductInfo header) ∧
      header.type = types[typeIndex].type ∧ header.ctors = types[typeIndex].ctors.map (·.name) ∧
      staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams original.lparams types[typeIndex] ctorIndex info := by
  have harray : typeIndex < types.toArray.size := by simpa using htype
  have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
  have hname : rewritten[typeIndex].name = types[typeIndex].name := by
    simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.names typeIndex harray
  have hheader : rewritten[typeIndex].type = types[typeIndex].type := by
    simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.headers typeIndex harray
  have hctors : rewritten[typeIndex].ctors.map (·.name) = types[typeIndex].ctors.map (·.name) := by
    simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.constructors typeIndex harray
  have hcount : rewritten[typeIndex].ctors.length = types[typeIndex].ctors.length := by
    simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.constructorCount typeIndex harray
  have hctorRewritten : ctorIndex < rewritten[typeIndex].ctors.length := by rw [hcount]; exact hctor
  have hctorName : rewritten[typeIndex].ctors[ctorIndex].name = types[typeIndex].ctors[ctorIndex].name := by
    have hctorArray : ctorIndex < types.toArray[typeIndex]!.ctors.length := by
      simpa only [getElem!_pos, harray, List.getElem_toArray] using hctor
    simpa only [getElem!_pos, harray, hrewritten, hctorRewritten, hctor, List.getElem_toArray] using
      hprefix.constructorNameAt typeIndex harray ctorIndex hctorArray
  let header := AddInductive.declareInductiveTypes.metadataVal stats nparams rewritten numNested false
    original.lparams rewritten[typeIndex] stats.nindices[typeIndex]!
  let info := AddInductive.declareConstructors.metadataVal stats original.lparams false
    rewritten[typeIndex].name ctorIndex rewritten[typeIndex].ctors[ctorIndex]
  have hparams : stats.params.size = nparams := by
    have hnonzero : rewritten.size ≠ 0 := by omega
    simpa only [AddInductive.InductiveStats.ParamsCount, if_neg hnonzero] using
      scope.toSafeRunRegistration.registration.traces.2.1
  refine ⟨header, info, ?_, hheader, hctors, ?_, ?_⟩
  · simpa only [hname] using scope.toSafeRunRegistration.headerMetadata typeIndex hrewritten
  · have hlookup := scope.toSafeRunRegistration.constructorMetadata rewritten[typeIndex]
      (Array.getElem_mem hrewritten) ctorIndex rewritten[typeIndex].ctors[ctorIndex]
      (by simp only [List.getElem?_eq_getElem hctorRewritten])
    simpa only [hctorName] using hlookup.1
  · exact ⟨by simpa only [getElem!_pos, hctor] using hctorName, hname, rfl, hparams, rfl, rfl⟩

def SourceConstructorLookups (nparams : Nat) (lparams : List Name) (types : List InductiveType)
    (preprocessing : ElimNestedInductive.Result) (staged result : Environment) : Prop :=
  ∀ typeIndex (htype : typeIndex < types.length), ∀ ctorIndex
    (hctor : ctorIndex < types[typeIndex].ctors.length), ∃ info : ConstructorVal,
      staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      (preprocessing.aux2nested.size = 0 →
        result.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info)) ∧
      (preprocessing.aux2nested.size ≠ 0 →
        result.find? types[typeIndex].ctors[ctorIndex].name =
          some (.ctorInfo { info with type := preprocessing.restoreNested staged info.type }))

theorem SafeInductiveRestorationMetadata.constructorStages {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      SourceConstructorLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, _, _, _, hbranch, hinstalled⟩ :=
    metadata.completeStages
  have hprefix := inductivePreprocessing.signatures env lparams nparams types fuel preprocessing hpre
  refine ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, hprefix, hbranch, ?_⟩
  intro typeIndex htype ctorIndex hctor
  obtain ⟨header, info, hheader, _, hctors, hlookup, hmetadata⟩ :=
    hscope.sourceConstructor hprefix typeIndex htype ctorIndex hctor
  refine ⟨info, hlookup, hmetadata, ?_, ?_⟩
  · intro hnoaux
    cases hbranch with
    | direct _ => exact hlookup
    | nested hnested _ => exact False.elim (hnested hnoaux)
  · intro hnested
    have hmem : types[typeIndex].ctors[ctorIndex].name ∈ header.ctors := by
      rw [hctors]
      exact List.mem_map.mpr ⟨_, List.getElem_mem hctor, rfl⟩
    have hfinal := (hinstalled hnested).constructor types[typeIndex] (List.getElem_mem htype) header hheader
      types[typeIndex].ctors[ctorIndex].name hmem info hlookup
    simpa only [hmetadata.name, getElem!_pos, hctor] using hfinal

theorem SafeInductiveRestorationMetadata.sourceConstructors {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
      SourceConstructorLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, _, _, _, hpre, hrun, _, hprefix, _, hlookups⟩ := metadata.constructorStages
  exact ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩

theorem Environment.addInductive.safeSourceConstructorMetadata (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorLookups nparams lparams types preprocessing staged result :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.sourceConstructors

theorem addDecl.safeInductiveSourceConstructorMetadata (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveSignaturePrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorLookups nparams lparams types preprocessing staged result :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.sourceConstructors⟩

end Lean4Lean
