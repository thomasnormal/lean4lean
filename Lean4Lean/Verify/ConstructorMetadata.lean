import Lean4Lean.Verify.ConstructorParams

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment

def declareConstructors.metadataVal (stats : InductiveStats) (lparams : List Name)
    (isUnsafe : Bool) (parent : Name) (index : Nat) (ctor : Constructor) : ConstructorVal := {
  name := ctor.name, levelParams := lparams, type := ctor.type, induct := parent,
  cidx := index, numParams := stats.params.size,
  numFields := declareConstructors.arity 0 ctor.type - stats.params.size, isUnsafe }

def InductiveStats.ConstructorMetadata (stats : InductiveStats) (lparams : List Name)
    (indTypes : Array InductiveType) (isUnsafe : Bool) (env : Kernel.Environment) : Prop :=
  ∀ indType ∈ indTypes, ∀ index ctor, indType.ctors[index]? = some ctor →
    let info := declareConstructors.metadataVal stats lparams isUnsafe indType.name index ctor
    env.find? ctor.name = some (.ctorInfo info) ∧
      info.numParams + info.numFields = declareConstructors.arity 0 ctor.type

private theorem addFresh (env : Kernel.Environment) (info : ConstantInfo)
    (hwf : env.constants.WF) (hfresh : env.constants.find? info.name = none) :
    (env.add info).constants.WF ∧ (env.add info).find? info.name = some info ∧
      ∀ name oldInfo, env.find? name = some oldInfo →
        (env.add info).find? name = some oldInfo := by
  have hnext : (env.add info).constants.WF := hwf.insert _ _ hfresh
  have hfind (name : Name) : (env.add info).find? name =
      if info.name == name then some info else env.find? name := by
    rw [Kernel.Environment.find?, hnext.find?'_eq_find?, Kernel.Environment.add_constants,
      hwf.find?_insert, ← hwf.find?'_eq_find?]
    rfl
  refine ⟨hnext, by simp [hfind], ?_⟩
  intro name oldInfo hold
  rw [hfind]
  split
  · have heq : info.name = name := LawfulBEq.eq_of_beq ‹_›
    subst name
    change env.constants.find?' info.name = some oldInfo at hold
    rw [hwf.find?'_eq_find?, hfresh] at hold
    cases hold
  · exact hold

private theorem registerConstructorsMetadata (ctors : List Constructor) (index : Nat)
    (env : Kernel.Environment) (allowPrimitive : Bool)
    (makeInfo : Nat → Constructor → ConstructorVal)
    (hname : ∀ index ctor, (makeInfo index ctor).name = ctor.name)
    (hwf : env.constants.WF) :
    (ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
      state.2.checkName ctor.name allowPrimitive
      pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo state.1 ctor)))) (index, env)).WF
      fun state => state.2.constants.WF ∧
        (∀ name info, env.find? name = some info → state.2.find? name = some info) ∧
        ∀ (offset : Nat) (ctor : Constructor), ctors[offset]? = some ctor →
          state.2.find? ctor.name = some (ConstantInfo.ctorInfo (makeInfo (index + offset) ctor)) := by
  induction ctors generalizing index env with
  | nil => exact .pure ⟨hwf, fun _ _ hold => hold, by simp⟩
  | cons ctor ctors ih =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (Lean4Lean.checkName.WF env ctor.name allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
    have hfreshInfo : env.constants.find? (ConstantInfo.ctorInfo (makeInfo index ctor)).name =
        none := by simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hname] using hfresh
    obtain ⟨hnext, hself, hpreserve⟩ := addFresh env (.ctorInfo (makeInfo index ctor)) hwf hfreshInfo
    refine (ih (index + 1) _ hnext).mono ?_
    rintro state ⟨hfinal, hkeep, hctors⟩
    refine ⟨hfinal, fun name info hold => hkeep _ _ (hpreserve name info hold), ?_⟩
    intro offset entry hentry
    cases offset with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hentry
      subst entry
      apply hkeep
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hname] using hself
    | succ offset =>
      simp only [List.getElem?_cons_succ] at hentry
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hctors offset entry hentry

private theorem registerTypesMetadata (types : List InductiveType) (env : Kernel.Environment)
    (allowPrimitive : Bool) (makeInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (hname : ∀ type index ctor, (makeInfo type index ctor).name = ctor.name)
    (hwf : env.constants.WF) :
    (types.foldlM (fun (env : Kernel.Environment) (type : InductiveType) => do
      let state ← type.ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
        state.2.checkName ctor.name allowPrimitive
        pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo type state.1 ctor)))) (0, env)
      pure state.2) env).WF fun env' => env'.constants.WF ∧
        (∀ name info, env.find? name = some info → env'.find? name = some info) ∧
        ∀ type ∈ types, ∀ (index : Nat) (ctor : Constructor), type.ctors[index]? = some ctor →
          env'.find? ctor.name = some (ConstantInfo.ctorInfo (makeInfo type index ctor)) := by
  induction types generalizing env with
  | nil => exact .pure ⟨hwf, fun _ _ hold => hold, by simp⟩
  | cons type types ih =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (registerConstructorsMetadata type.ctors 0 env allowPrimitive (makeInfo type)
      (hname type) hwf).bind ?_
    rintro state ⟨hnext, hpreserve, hctors⟩
    refine (ih state.2 hnext).mono ?_
    rintro env' ⟨hfinal, hkeep, htypes⟩
    refine ⟨hfinal, fun name info hold => hkeep _ _ (hpreserve name info hold), ?_⟩
    intro entry hentry index ctor hctor
    rcases List.mem_cons.mp hentry with rfl | hentry
    · apply hkeep
      simpa only [Nat.zero_add] using hctors index ctor hctor
    · exact htypes entry hentry index ctor hctor

theorem declareConstructors.metadata (stats : InductiveStats) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (harity : ∀ indType ∈ indTypes, ∀ ctor ∈ indType.ctors,
      stats.params.size ≤ declareConstructors.arity 0 ctor.type) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      env'.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env'.find? name = some info) ∧
        stats.ConstructorMetadata ctx.lparams indTypes isUnsafe env' := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  let makeInfo (type : InductiveType) (index : Nat) (ctor : Constructor) : ConstructorVal := {
    name := ctor.name, levelParams := ctx.lparams, type := ctor.type, induct := type.name,
    cidx := index, numParams := stats.params.size, isUnsafe
    numFields := assert! declareConstructors.arity 0 ctor.type ≥ stats.params.size;
      declareConstructors.arity 0 ctor.type - stats.params.size }
  refine (registerTypesMetadata indTypes.toList ctx.env ctx.allowPrimitive makeInfo
    (by intros; rfl) hwf).mono ?_
  rintro env' ⟨hfinal, hkeep, hctors⟩
  refine ⟨hfinal, hkeep, ?_⟩
  intro type htype index ctor hctor
  have hbound := harity type htype ctor (List.mem_of_getElem? hctor)
  have hlookup := hctors type (by simpa using htype) index ctor hctor
  refine ⟨?_, ?_⟩
  · simpa [makeInfo, declareConstructors.metadataVal, hbound] using hlookup
  · change stats.params.size + (declareConstructors.arity 0 ctor.type - stats.params.size) = _
    omega

theorem checkConstructors.declareMetadata (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.env.constants.WF) (hfvars : stats.ParamsAreFVars)
    (hnodup : stats.params.toList.Nodup) :
    ((checkConstructors indTypes stats isUnsafe >>= fun _ =>
      declareConstructors stats indTypes isUnsafe) ctx).WF fun env' => env'.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → env'.find? name = some info) ∧
        stats.ConstructorMetadata ctx.lparams indTypes isUnsafe env' :=
  (checkConstructors.arity indTypes stats isUnsafe ctx hfvars hnodup).bind fun _ hbound =>
    declareConstructors.metadata stats indTypes isUnsafe ctx hwf hbound

theorem checkInductiveTypes.checkedConstructorMetadata (nparams : Nat)
    (indTypes : Array InductiveType) (isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes nparams indTypes (fun stats => do
      checkConstructors indTypes stats isUnsafe
      let env ← declareConstructors stats indTypes isUnsafe
      pure (stats, env)) ctx).WF fun result => result.2.constants.WF ∧
        (∀ name info, ctx.env.find? name = some info → result.2.find? name = some info) ∧
        result.1.ConstructorMetadata ctx.lparams indTypes isUnsafe result.2 := by
  apply checkInductiveTypes.frameHeaderSizesParamsDistinct
  intro stats current _ hfvars hnodup hframe
  have hcurrent : current.env.constants.WF := by simpa [hframe.env] using hwf
  refine (checkConstructors.arity indTypes stats isUnsafe current hfvars hnodup).bind
    fun _ hbound => ?_
  refine (declareConstructors.metadata stats indTypes isUnsafe current hcurrent hbound).bind
    fun env hmetadata => .pure ?_
  simpa only [hframe.env, hframe.lparams] using hmetadata

end Lean4Lean.AddInductive
