import Lean4Lean.Theory.ConstructorHeaders
import Lean4Lean.Verify.InductiveHeaders

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.Aligned.constants_eq_none from Lean4Lean.Verify.InductiveHeaders

private theorem registerConstructorHeaders.WF {safety : DefinitionSafety}
    {env : Kernel.Environment} {venv : VEnv} {lparams : List Name}
    {ctors : List Constructor} {headers : List VConstVal} (index : Nat) (allowPrimitive : Bool)
    (makeInfo : Nat → Constructor → ConstructorVal)
    (hmap : ∀ venv index ctor header, TrConstructor venv lparams ctor header →
      (makeInfo index ctor).name = header.name ∧
        TrConstant safety venv (.ctorInfo (makeInfo index ctor)) header.toVConstant)
    (haligned : Aligned safety env.constants venv)
    (hctors : List.Forall₂ (TrConstructor venv lparams) ctors headers) :
    (ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
      state.2.checkName ctor.name allowPrimitive
      pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo state.1 ctor)))) (index, env)).WF
      fun state => ∃ venv', venv.addConstructorHeaders headers = some venv' ∧
        Aligned safety state.2.constants venv' := by
  induction ctors generalizing index env venv headers with
  | nil => cases hctors; exact .pure ⟨venv, rfl, haligned⟩
  | cons ctor ctors ih =>
    cases hctors with
    | cons hctor hrest =>
      rename_i header headers
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (checkName.WF env ctor.name allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
      obtain ⟨hname, hinfo⟩ := hmap venv index ctor header hctor
      have hvfresh : venv.constants header.name = none :=
        hctor.1 ▸ haligned.constants_eq_none hfresh
      obtain ⟨next, hstep⟩ : ∃ next, venv.addConst header.name header.toVConstant = some next := by
        simp [VEnv.addConst, hvfresh]
      have hnext := haligned.const
        (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hname, hctor.1] using hfresh) hinfo
        (hname.symm ▸ hstep) rfl
      have hle := VEnv.addConst_le hstep
      refine (ih (index + 1) hnext (hrest.imp fun _ _ htr => htr.mono hle)).mono ?_
      intro state hresult
      obtain ⟨venv', hadd, haligned'⟩ := hresult
      exact ⟨venv', by simpa [VEnv.addConstructorHeaders, hstep] using hadd, haligned'⟩

private theorem registerConstructorTypes.WF {safety : DefinitionSafety}
    {env : Kernel.Environment} {venv : VEnv} {lparams : List Name}
    {types : List InductiveType} {vtypes : List VInductiveType} (allowPrimitive : Bool)
    (makeInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (hmap : ∀ venv type index ctor header, TrConstructor venv lparams ctor header →
      (makeInfo type index ctor).name = header.name ∧
        TrConstant safety venv (.ctorInfo (makeInfo type index ctor)) header.toVConstant)
    (haligned : Aligned safety env.constants venv)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv lparams) type.ctors vtype.ctors) types vtypes) :
    (types.foldlM (fun (env : Kernel.Environment) (type : InductiveType) => do
      let state ← type.ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
        state.2.checkName ctor.name allowPrimitive
        pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo type state.1 ctor)))) (0, env)
      pure state.2) env).WF fun env' =>
        ∃ venv', venv.addConstructorHeaders
          (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
          Aligned safety env'.constants venv' := by
  induction types generalizing env venv vtypes with
  | nil => cases hctors; exact .pure ⟨venv, rfl, haligned⟩
  | cons type types ih =>
    cases hctors with
    | cons hctor hrest =>
      rename_i vtype vtypes
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (registerConstructorHeaders.WF 0 allowPrimitive (makeInfo type)
        (fun venv => hmap venv type) haligned hctor).bind fun state hresult => ?_
      obtain ⟨next, hstep, hnext⟩ := hresult
      have hle := VEnv.addConstructorHeaders.le hstep
      refine (ih hnext
        (hrest.imp fun _ _ hctors => hctors.imp fun _ _ htr => htr.mono hle)).mono ?_
      intro env' hresult
      obtain ⟨venv', hadd, haligned'⟩ := hresult
      exact ⟨venv', by simpa [List.flatMap_cons, VEnv.addConstructorHeaders.append, hstep]
        using hadd, haligned'⟩

theorem AddInductive.declareConstructors.refines (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        Aligned safety env'.constants venv' := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  let makeInfo (type : InductiveType) (index : Nat) (ctor : Constructor) : ConstructorVal := {
    name := ctor.name, levelParams := ctx.lparams, type := ctor.type, induct := type.name,
    cidx := index, numParams := stats.params.size, isUnsafe
    numFields := assert! AddInductive.declareConstructors.arity 0 ctor.type ≥ stats.params.size;
      AddInductive.declareConstructors.arity 0 ctor.type - stats.params.size }
  apply registerConstructorTypes.WF ctx.allowPrimitive makeInfo ?_ haligned hctors
  intro venv type index ctor header htr
  refine ⟨htr.1, ?_, htr.2.1, htr.2.2⟩
  simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial] using hsafety

theorem AddInductive.declareConstructors.ordered (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hordered : venv.Ordered)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        Aligned safety env'.constants venv' ∧ venv'.Ordered :=
  (declareConstructors.refines ctx stats indTypes isUnsafe haligned hsafety hctors).mono
    fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, haligned', VEnv.addConstructorHeaders.ordered hordered htypes hadd⟩

theorem AddInductive.declareConstructors.refinesWF (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        venv'.WF ∧ Aligned safety env'.constants venv' :=
  (declareConstructors.refines ctx stats indTypes isUnsafe haligned hsafety hctors).mono
    fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, VEnv.addConstructorHeaders.wf hvenv htypes hadd, haligned'⟩

theorem AddInductive.checkInductiveTypes.refinesHeaderConstructorWF
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (headerTypes : ∀ header ∈ headers, header.toVConstant.WF venv)
    (hctors : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
        List.Forall₂ (TrConstructor headerEnv ctx.lparams) type.ctors vtype.ctors)
        indTypes.toList vtypes)
    (constructorTypes : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
        ctor.toVConstant.WF headerEnv) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      let nativeHeaders ← declareInductiveTypes stats numParams indTypes numNested isUnsafe
      withEnv nativeHeaders (declareConstructors stats indTypes isUnsafe)) ctx).WF fun env' =>
      ∃ headerEnv ctorEnv,
        venv.addInductHeaders headers = some headerEnv ∧ headerEnv.WF ∧
        headerEnv.addConstructorHeaders
          (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some ctorEnv ∧
        ctorEnv.WF ∧ Aligned safety env'.constants ctorEnv := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats ctx' hsizes hframe
  refine (declareInductiveTypes.refinesWF ctx' stats numParams indTypes numNested isUnsafe
    (by simpa [hframe.env] using haligned) hvenv hsafety hsizes.1
    (by simpa [hframe.lparams] using hheaders) headerTypes).bind ?_
  rintro nativeHeaders ⟨headerEnv, haddHeaders, headerWF, headerAligned⟩
  have hctorModels := hctors headerEnv haddHeaders
  have hconstructorTypes := constructorTypes headerEnv haddHeaders
  refine (declareConstructors.refinesWF { ctx' with env := nativeHeaders } stats indTypes isUnsafe
    (by simpa [hframe.env, headerAligned]) headerWF hsafety
    (by simpa [hframe.lparams] using hctorModels) hconstructorTypes).mono ?_
  rintro ctorNative ⟨ctorEnv, haddCtors, ctorWF, ctorAligned⟩
  exact ⟨headerEnv, ctorEnv, haddHeaders, headerWF, haddCtors, ctorWF, ctorAligned⟩

end Lean4Lean
