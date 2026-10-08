import Lean4Lean.Verify.ConstructorMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata

def declareInductiveTypes.metadataVal (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) (indType : InductiveType) (numIndices : Nat) : InductiveVal := {
  name := indType.name, type := indType.type, levelParams := lparams,
  numParams, numIndices, numNested, isUnsafe,
  all := (indTypes.map (·.name)).toList, ctors := indType.ctors.map (·.name),
  isRec := isRec indTypes stats.indConsts, isReflexive := isReflexive indTypes stats.indConsts }

def InductiveStats.HeaderMetadata (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) (env : Kernel.Environment) : Prop :=
  ∀ (index : Nat) (hindex : index < indTypes.size),
    env.find? indTypes[index].name = some (.inductInfo
    (declareInductiveTypes.metadataVal stats numParams indTypes numNested isUnsafe lparams
      indTypes[index] stats.nindices[index]!))

def DeclaredParameterMetadata (numParams : Nat) (indTypes : Array InductiveType)
    (env : Kernel.Environment) : Prop :=
  ∀ (index : Nat) (hindex : index < indTypes.size), ∀ (ctorIndex : Nat) (ctor : Constructor),
    indTypes[index].ctors[ctorIndex]? = some ctor →
      ∃ (header : InductiveVal) (info : ConstructorVal),
        env.find? indTypes[index].name = some (.inductInfo header) ∧
        env.find? ctor.name = some (.ctorInfo info) ∧
        header.numParams = numParams ∧ info.numParams = numParams ∧
        info.numParams + info.numFields = declareConstructors.arity 0 ctor.type

def DeclaredHeaderArities (numParams : Nat) (indTypes : Array InductiveType)
    (env : Kernel.Environment) : Prop :=
  ∀ (index : Nat) (hindex : index < indTypes.size), ∃ header : InductiveVal,
    env.find? indTypes[index].name = some (.inductInfo header) ∧
      header.numParams = numParams ∧
      declareConstructors.arity 0 header.type ≤ header.numParams + header.numIndices

theorem InductiveStats.declaredHeaderArities (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) (env : Kernel.Environment)
    (harities : stats.HeaderArities numParams indTypes)
    (hheaders : stats.HeaderMetadata numParams indTypes numNested isUnsafe lparams env) :
    DeclaredHeaderArities numParams indTypes env := by
  intro index hindex
  exact ⟨_, hheaders index hindex, rfl, harities index hindex⟩

theorem InductiveStats.declaredParameterMetadata (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) (env : Kernel.Environment)
    (hcount : stats.ParamsCount numParams indTypes.size)
    (hheaders : stats.HeaderMetadata numParams indTypes numNested isUnsafe lparams env)
    (hctors : stats.ConstructorMetadata lparams indTypes isUnsafe env) :
    DeclaredParameterMetadata numParams indTypes env := by
  intro index hindex ctorIndex ctor hctor
  have hnonempty : indTypes.size ≠ 0 := by omega
  have hparams : stats.params.size = numParams := by
    simpa only [InductiveStats.ParamsCount, hnonempty, ite_false] using hcount
  have hmetadata := hctors indTypes[index] (Array.getElem_mem hindex) ctorIndex ctor hctor
  exact ⟨_, _, hheaders index hindex, hmetadata.1, rfl, hparams, hmetadata.2⟩

private theorem registerInductiveMetadata (infos : List InductiveVal)
    (env : Kernel.Environment) (allowPrimitive : Bool) (hwf : env.constants.WF) :
    (infos.foldlM (fun (env : Kernel.Environment) (info : InductiveVal) => do
      env.checkName info.name allowPrimitive
      pure (env.add (.inductInfo info))) env).WF fun env' => env'.constants.WF ∧
        (∀ name info, env.find? name = some info → env'.find? name = some info) ∧
        ∀ info ∈ infos, env'.find? info.name = some (ConstantInfo.inductInfo info) := by
  induction infos generalizing env with
  | nil => exact .pure ⟨hwf, fun _ _ hold => hold, by simp⟩
  | cons info infos ih =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (Lean4Lean.checkName.WF env info.name allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
    obtain ⟨hnext, hself, hpreserve⟩ :=
      Lean4Lean.AddInductive.addFresh env (.inductInfo info) hwf hfresh
    refine (ih _ hnext).mono ?_
    rintro env' ⟨hfinal, hkeep, hinfos⟩
    refine ⟨hfinal, fun name entry hold => hkeep _ _ (hpreserve name entry hold), ?_⟩
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact hkeep _ _ hself
    · exact hinfos entry hentry

theorem declareInductiveTypes.metadata (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF)
    (hsize : stats.nindices.size = indTypes.size) :
    (declareInductiveTypes stats numParams indTypes numNested isUnsafe ctx).WF fun env' =>
      env'.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env'.find? name = some info) ∧
        stats.HeaderMetadata numParams indTypes numNested isUnsafe ctx.lparams env' := by
  unfold declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  refine (registerInductiveMetadata _ ctx.env ctx.allowPrimitive hwf).mono ?_
  rintro env' ⟨hfinal, hkeep, hinfos⟩
  refine ⟨hfinal, hkeep, ?_⟩
  intro index hindex
  have hstats : index < stats.nindices.size := by omega
  refine hinfos (declareInductiveTypes.metadataVal stats numParams indTypes numNested
    isUnsafe ctx.lparams indTypes[index] stats.nindices[index]!) ?_
  rw [Array.mem_toList_iff]
  apply Array.mem_iff_getElem.mpr
  refine ⟨index, by simp [Array.size_zipWith]; omega, ?_⟩
  simp only [Array.getElem_zipWith, getElem!_pos stats.nindices index hstats,
    declareInductiveTypes.metadataVal]

theorem checkInductiveTypes.registeredHeaderArities (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      let headers ← declareInductiveTypes stats numParams indTypes numNested isUnsafe
      withEnv headers do
        checkConstructors indTypes stats isUnsafe
        let env ← declareConstructors stats indTypes isUnsafe
        pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
          (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
          result.1.HeaderMetadata numParams indTypes numNested isUnsafe ctx.lparams result.2 ∧
          result.1.ConstructorMetadata ctx.lparams indTypes isUnsafe result.2 ∧
          result.1.ParamsCount numParams indTypes.size ∧
          DeclaredParameterMetadata numParams indTypes result.2 ∧
          result.1.HeaderArities numParams indTypes ∧
          DeclaredHeaderArities numParams indTypes result.2 := by
  apply checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct
  intro stats current hsizes harities hcount hfvars hnodup hframe
  have hcurrent : current.env.constants.WF := by simpa only [hframe.env] using hwf
  refine (declareInductiveTypes.metadata stats numParams indTypes numNested isUnsafe current
    hcurrent hsizes.1).bind ?_
  rintro headers ⟨hheadersWF, hpreserve, hheaders⟩
  refine (checkConstructors.arity indTypes stats isUnsafe { current with env := headers }
    hfvars hnodup).bind fun _ hbound => ?_
  refine (declareConstructors.metadata stats indTypes isUnsafe { current with env := headers }
    hheadersWF hbound).bind ?_
  rintro env ⟨hfinal, hkeep, hctors⟩
  have hheaders' : stats.HeaderMetadata numParams indTypes numNested isUnsafe ctx.lparams env := by
    intro index hindex
    apply hkeep
    simpa only [hframe.lparams] using hheaders index hindex
  have hctors' : stats.ConstructorMetadata ctx.lparams indTypes isUnsafe env := by
    simpa only [hframe.lparams] using hctors
  refine .pure ⟨hfinal, ?_, hheaders', hctors', hcount,
    stats.declaredParameterMetadata numParams indTypes numNested isUnsafe ctx.lparams env
      hcount hheaders' hctors', harities,
    stats.declaredHeaderArities numParams indTypes numNested isUnsafe ctx.lparams env
      harities hheaders'⟩
  · intro name info hold
    exact hkeep _ _ (hpreserve name info (by simpa only [hframe.env] using hold))

theorem checkInductiveTypes.registeredParameterMetadata (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      let headers ← declareInductiveTypes stats numParams indTypes numNested isUnsafe
      withEnv headers do
        checkConstructors indTypes stats isUnsafe
        let env ← declareConstructors stats indTypes isUnsafe
        pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
          (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
          result.1.HeaderMetadata numParams indTypes numNested isUnsafe ctx.lparams result.2 ∧
          result.1.ConstructorMetadata ctx.lparams indTypes isUnsafe result.2 ∧
          result.1.ParamsCount numParams indTypes.size ∧
          DeclaredParameterMetadata numParams indTypes result.2 :=
  (checkInductiveTypes.registeredHeaderArities numParams indTypes numNested isUnsafe ctx
    hwf).mono fun _ hmetadata =>
      ⟨hmetadata.1, hmetadata.2.1, hmetadata.2.2.1, hmetadata.2.2.2.1,
        hmetadata.2.2.2.2.1, hmetadata.2.2.2.2.2.1⟩

theorem checkInductiveTypes.registeredConstructorMetadata (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (ctx : Context) (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      let headers ← declareInductiveTypes stats numParams indTypes numNested isUnsafe
      withEnv headers do
        checkConstructors indTypes stats isUnsafe
        let env ← declareConstructors stats indTypes isUnsafe
        pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
          (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
          result.1.HeaderMetadata numParams indTypes numNested isUnsafe ctx.lparams result.2 ∧
          result.1.ConstructorMetadata ctx.lparams indTypes isUnsafe result.2 :=
  (checkInductiveTypes.registeredParameterMetadata numParams indTypes numNested isUnsafe ctx
    hwf).mono fun _ hmetadata =>
      ⟨hmetadata.1, hmetadata.2.1, hmetadata.2.2.1, hmetadata.2.2.2.1⟩

end Lean4Lean.AddInductive
