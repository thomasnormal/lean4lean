import Lean4Lean.Verify.InductiveNestedArity

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open AddInductive.declareConstructors

structure InductiveArityPrefix (original rewritten : Array InductiveType) : Prop
    extends InductiveSignaturePrefix original rewritten where
  arities : ∀ index, index < original.size →
    rewritten[index]!.ctors.map (fun ctor => arity 0 ctor.type) =
      original[index]!.ctors.map (fun ctor => arity 0 ctor.type)

theorem InductiveArityPrefix.refl (types : Array InductiveType) : InductiveArityPrefix types types :=
  ⟨.refl types, fun _ _ => rfl⟩

theorem InductiveArityPrefix.trans {first second third : Array InductiveType}
    (hfirst : InductiveArityPrefix first second) (hsecond : InductiveArityPrefix second third) :
    InductiveArityPrefix first third :=
  ⟨hfirst.toInductiveSignaturePrefix.trans hsecond.toInductiveSignaturePrefix,
    fun index hindex => (hsecond.arities index (Nat.lt_of_lt_of_le hindex hfirst.size)).trans
      (hfirst.arities index hindex)⟩

theorem ElimNestedInductive.TypePrefix.toArity {original rewritten : Array InductiveType}
    (hprefix : ElimNestedInductive.TypePrefix original rewritten) : InductiveArityPrefix original rewritten :=
  ⟨hprefix.toSignature, fun index hindex =>
    congrArg (fun type => type.ctors.map (fun ctor => arity 0 ctor.type)) (hprefix.types index hindex)⟩

theorem InductiveArityPrefix.set {original rewritten : Array InductiveType}
    (hprefix : InductiveArityPrefix original rewritten) (index : Nat) (hindex : index < original.size)
    (type : InductiveType) (hname : type.name = original[index]!.name)
    (hheader : type.type = original[index]!.type)
    (hctors : type.ctors.map (·.name) = original[index]!.ctors.map (·.name))
    (harities : type.ctors.map (fun ctor => arity 0 ctor.type) =
      original[index]!.ctors.map (fun ctor => arity 0 ctor.type)) :
    InductiveArityPrefix original (rewritten.set! index type) := by
  refine ⟨hprefix.toInductiveSignaturePrefix.set index hindex type hname hheader hctors, ?_⟩
  intro position hposition
  have hrewritten := Nat.lt_of_lt_of_le hposition hprefix.size
  have hset := Nat.lt_of_lt_of_le hindex hprefix.size
  by_cases heq : position = index
  · subst position
    simpa [Array.set!, getElem!_pos, hset] using harities
  · simpa [Array.set!, getElem!_pos, hrewritten, hset, heq, Ne.symm heq] using hprefix.arities position hposition

theorem InductiveArityPrefix.constructorArityAt {original rewritten : Array InductiveType}
    (hprefix : InductiveArityPrefix original rewritten) (index : Nat) (hindex : index < original.size)
    (ctorIndex : Nat) (hctor : ctorIndex < original[index]!.ctors.length) :
    arity 0 rewritten[index]!.ctors[ctorIndex]!.type = arity 0 original[index]!.ctors[ctorIndex]!.type := by
  have hrewritten : ctorIndex < rewritten[index]!.ctors.length := by
    rw [hprefix.constructorCount index hindex]
    exact hctor
  have harities := congrArg (fun arities : List Nat => arities[ctorIndex]?) (hprefix.arities index hindex)
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hctor, List.getElem?_eq_getElem hrewritten,
    Option.map_some, Option.some.injEq, getElem!_pos, hctor, hrewritten] using harities

namespace ElimNestedInductive
open private Lean4Lean.ElimNestedInductive.get_bind Lean4Lean.ElimNestedInductive.modify_bind
  from Lean4Lean.Verify.InductiveNestedRewrite

private theorem mapMConstructorArities (ctors : List Constructor) (step : Constructor → M Constructor)
    (env : Environment) (state : State)
    (hstep : ∀ ctor current, (step ctor env current).WF fun result =>
      result.1.name = ctor.name ∧ arity 0 result.1.type = arity 0 ctor.type ∧
        TypePrefix current.newTypes result.2.newTypes) :
    (ctors.mapM step env state).WF fun result =>
      result.1.map (·.name) = ctors.map (·.name) ∧
        result.1.map (fun ctor => arity 0 ctor.type) = ctors.map (fun ctor => arity 0 ctor.type) ∧
        TypePrefix state.newTypes result.2.newTypes := by
  induction ctors generalizing state with
  | nil => exact .pure ⟨rfl, rfl, .refl _⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine (hstep ctor state).bind ?_
    rintro ⟨rewritten, current⟩ ⟨hname, harity, hprefix⟩
    refine (ih current).bind ?_
    rintro ⟨rest, next⟩ ⟨hnames, harities, hrest⟩
    dsimp only at hname harity hnames harities hprefix hrest
    exact .pure ⟨by simp only [List.map_cons, hname, hnames],
      by simp only [List.map_cons, harity, harities], hprefix.trans hrest⟩

theorem run.loop.arities (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (index fuel : Nat) (env : Environment) (state : State) :
    (run.loop numParams lctx params index fuel env state).WF fun result =>
      InductiveArityPrefix state.newTypes result.1.types.toArray := by
  induction fuel generalizing index state with
  | zero => exact .throw
  | succ fuel ih =>
    rw [run.loop.eq_def]
    dsimp only
    rw [Lean4Lean.ElimNestedInductive.get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      refine (mapMConstructorArities state.newTypes[index].ctors _ env state ?_).bind ?_
      · intro ctor current
        exact withParams.rewriteConstructor ctor numParams params env current
      · rintro ⟨ctors, current⟩ ⟨hnames, harities, hprefix⟩
        dsimp only
        rw [Lean4Lean.ElimNestedInductive.modify_bind]
        have hset := hprefix.toArity.set index hindex { state.newTypes[index] with ctors }
          (by simp only [getElem!_pos, hindex]) (by simp only [getElem!_pos, hindex])
          (by simpa only [getElem!_pos, hindex] using hnames)
          (by simpa only [getElem!_pos, hindex] using harities)
        exact (ih (index + 1) _).mono fun _ hresult => hset.trans hresult
    · exact .pure (by simpa using InductiveArityPrefix.refl state.newTypes)

theorem run.arities (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result =>
      InductiveArityPrefix state.newTypes result.1.types.toArray := by
  cases types with
  | nil => exact .throw
  | cons type types =>
    unfold run
    apply withParams.newTypesFrame type.type numParams _ env state
    intro lctx remainder params current hframe
    simpa only [hframe] using run.loop.arities numParams lctx params 0 fuel env current

theorem run.arities_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result =>
      InductiveArityPrefix state.newTypes result.types.toArray :=
  (run.arities fuel numParams types env state).map fun _ hprefix => hprefix

end ElimNestedInductive

theorem inductivePreprocessing.arities (env : Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) :
    (inductivePreprocessing env lparams numParams types fuel).WF fun result =>
      InductiveArityPrefix types.toArray result.types.toArray :=
  ElimNestedInductive.run.arities_run' fuel.inductiveFuel numParams types env
    { lvls := lparams.map .param, newTypes := types.toArray }

structure SourceConstructorFields (nparams : Nat) (parent : InductiveType)
    (index : Nat) (info : ConstructorVal) : Prop where
  fields : info.numFields = arity 0 parent.ctors[index]!.type - nparams
  total : nparams + info.numFields = arity 0 parent.ctors[index]!.type

theorem SourceConstructorFields.restore {nparams : Nat} {parent : InductiveType} {index : Nat}
    {info : ConstructorVal} (hfields : SourceConstructorFields nparams parent index info) (type : Expr) :
    SourceConstructorFields nparams parent index { info with type } :=
  ⟨hfields.fields, hfields.total⟩

theorem AddInductive.InductiveStats.SafeRunScope.sourceConstructorFields
    {stats : AddInductive.InductiveStats} {nparams numNested : Nat} {rewritten : Array InductiveType}
    {original root : AddInductive.Context} {constructors staged : Environment} {types : List InductiveType}
    (scope : stats.SafeRunScope nparams rewritten numNested original root constructors staged)
    (hprefix : InductiveArityPrefix types.toArray rewritten)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) (info : ConstructorVal)
    (hlookup : staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info)) :
    SourceConstructorFields nparams types[typeIndex] ctorIndex info := by
  have harray : typeIndex < types.toArray.size := by simpa using htype
  have hrewritten := Nat.lt_of_lt_of_le harray hprefix.size
  have hcount : rewritten[typeIndex].ctors.length = types[typeIndex].ctors.length := by
    simpa only [getElem!_pos, harray, hrewritten, List.getElem_toArray] using hprefix.constructorCount typeIndex harray
  have hctorRewritten : ctorIndex < rewritten[typeIndex].ctors.length := by rw [hcount]; exact hctor
  have hctorArray : ctorIndex < types.toArray[typeIndex]!.ctors.length := by
    simpa only [getElem!_pos, harray, List.getElem_toArray] using hctor
  have hname : rewritten[typeIndex].ctors[ctorIndex].name = types[typeIndex].ctors[ctorIndex].name := by
    simpa only [getElem!_pos, harray, hrewritten, hctorRewritten, hctor, List.getElem_toArray] using
      hprefix.constructorNameAt typeIndex harray ctorIndex hctorArray
  have harity : arity 0 rewritten[typeIndex].ctors[ctorIndex].type =
      arity 0 types[typeIndex].ctors[ctorIndex]!.type := by
    simpa only [getElem!_pos, harray, hrewritten, hctorRewritten, hctor, List.getElem_toArray] using
      hprefix.constructorArityAt typeIndex harray ctorIndex hctorArray
  have hchecked := scope.toSafeRunRegistration.constructorMetadata rewritten[typeIndex]
    (Array.getElem_mem hrewritten) ctorIndex rewritten[typeIndex].ctors[ctorIndex]
    (by simp only [List.getElem?_eq_getElem hctorRewritten])
  have heq : info = AddInductive.declareConstructors.metadataVal stats original.lparams false
      rewritten[typeIndex].name ctorIndex rewritten[typeIndex].ctors[ctorIndex] := by
    simpa only [hname, hlookup, Option.some.injEq, ConstantInfo.ctorInfo.injEq] using hchecked.1
  have hparams : stats.params.size = nparams := by
    have hnonzero : rewritten.size ≠ 0 := by omega
    simpa only [AddInductive.InductiveStats.ParamsCount, if_neg hnonzero] using
      scope.toSafeRunRegistration.registration.traces.2.1
  subst info
  refine ⟨?_, ?_⟩
  · simp only [AddInductive.declareConstructors.metadataVal, hparams, harity]
  · simpa only [AddInductive.declareConstructors.metadataVal, hparams, harity] using hchecked.2

def SourceConstructorFieldLookups (nparams : Nat) (lparams : List Name) (types : List InductiveType)
    (preprocessing : ElimNestedInductive.Result) (staged result : Environment) : Prop :=
  ∀ typeIndex (htype : typeIndex < types.length), ∀ ctorIndex
    (hctor : ctorIndex < types[typeIndex].ctors.length), ∃ info : ConstructorVal,
      staged.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      SourceConstructorFields nparams types[typeIndex] ctorIndex info ∧
      (preprocessing.aux2nested.size = 0 →
        result.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info)) ∧
      (preprocessing.aux2nested.size ≠ 0 →
        result.find? types[typeIndex].ctors[ctorIndex].name =
          some (.ctorInfo { info with type := preprocessing.restoreNested staged info.type }))

theorem SourceConstructorFieldLookups.finalFields {nparams : Nat} {lparams : List Name}
    {types : List InductiveType} {preprocessing : ElimNestedInductive.Result} {staged result : Environment}
    (hlookups : SourceConstructorFieldLookups nparams lparams types preprocessing staged result)
    (typeIndex : Nat) (htype : typeIndex < types.length) (ctorIndex : Nat)
    (hctor : ctorIndex < types[typeIndex].ctors.length) :
    ∃ info : ConstructorVal,
      result.find? types[typeIndex].ctors[ctorIndex].name = some (.ctorInfo info) ∧
      SourceConstructorMetadata nparams lparams types[typeIndex] ctorIndex info ∧
      SourceConstructorFields nparams types[typeIndex] ctorIndex info := by
  obtain ⟨info, _, hmetadata, hfields, hdirect, hnested⟩ := hlookups typeIndex htype ctorIndex hctor
  by_cases haux : preprocessing.aux2nested.size = 0
  · exact ⟨info, hdirect haux, hmetadata, hfields⟩
  · exact ⟨{ info with type := preprocessing.restoreNested staged info.type }, hnested haux,
      ⟨hmetadata.name, hmetadata.induct, hmetadata.position, hmetadata.params, hmetadata.levels, hmetadata.safe⟩,
      hfields.restore _⟩

theorem SafeInductiveRestorationMetadata.constructorFieldStages {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment)
      (stats : AddInductive.InductiveStats) (root : AddInductive.Context) (constructors : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      InductiveFrontendBranch preprocessing staged types env result ∧
      SourceConstructorFieldLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, _, hbranch, hlookups⟩ :=
    metadata.constructorStages
  have hprefix := inductivePreprocessing.arities env lparams nparams types fuel preprocessing hpre
  refine ⟨preprocessing, staged, stats, root, constructors, hpre, hrun, hscope, hprefix, hbranch, ?_⟩
  intro typeIndex htype ctorIndex hctor
  obtain ⟨info, hlookup, hmetadata, hdirect, hnested⟩ := hlookups typeIndex htype ctorIndex hctor
  exact ⟨info, hlookup, hmetadata, hscope.sourceConstructorFields hprefix typeIndex htype ctorIndex hctor info hlookup,
    hdirect, hnested⟩

theorem SafeInductiveRestorationMetadata.sourceConstructorFields {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (metadata : SafeInductiveRestorationMetadata env lparams nparams types allowPrimitive fuel result) :
    ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
      inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
      AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
      InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
      SourceConstructorFieldLookups nparams lparams types preprocessing staged result := by
  obtain ⟨preprocessing, staged, _, _, _, hpre, hrun, _, hprefix, _, hlookups⟩ := metadata.constructorFieldStages
  exact ⟨preprocessing, staged, hpre, hrun, hprefix, hlookups⟩

theorem Environment.addInductive.safeSourceConstructorFields (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      ∃ (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorFieldLookups nparams lparams types preprocessing staged result :=
  (Environment.addInductive.safeRestorationStages env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ metadata => metadata.sourceConstructorFields

theorem addDecl.safeInductiveSourceConstructorFields (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ (allowPrimitive : Bool) (preprocessing : ElimNestedInductive.Result) (staged : Environment),
        inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
        AddInductive.run nparams preprocessing.types preprocessing.aux2nested.size
          (inductiveScopeContext env lparams allowPrimitive fuel) = .ok staged ∧
        InductiveArityPrefix types.toArray preprocessing.types.toArray ∧
        SourceConstructorFieldLookups nparams lparams types preprocessing staged result :=
  (addDecl.safeInductiveRestorationStages env lparams nparams types check fuel hmap).mono
    fun _ ⟨allowPrimitive, metadata⟩ => ⟨allowPrimitive, metadata.sourceConstructorFields⟩

end Lean4Lean
